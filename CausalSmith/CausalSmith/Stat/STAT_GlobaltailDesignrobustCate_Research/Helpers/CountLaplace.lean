module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators
public import Causalean.Stat.Concentration.TailBounds.BinomialCount
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Count Laplace bounds

The binomial Laplace calculation and the minimum-count bound in equation (15)
of the finite-bandwidth roadmap. Subcell counts need not be independent.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The Laplace transform of the number of hits of a measurable event in an
independent product sample is its Bernoulli Laplace transform to the sample size. -/
-- @node: indicatorCount_laplace_pi
lemma indicatorCount_laplace_pi {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (E : Set Ω) (hE : MeasurableSet E)
    (n : ℕ) (s : ℝ) : (by
    classical
    exact (∫ sample : Fin n → Ω,
      Real.exp (-s * ((∑ i : Fin n, if sample i ∈ E then 1 else 0 : ℕ) : ℝ))
        ∂Measure.pi (fun _ => ν)) = (1 - ν.real E * (1 - Real.exp (-s))) ^ n) := by
  classical
  let f : Ω → ℝ := E.indicator (fun _ => 1)
  have hf : Measurable f := by fun_prop
  have hmean : ∫ x, f x ∂ν = ν.real E := by
    simp [f, integral_indicator hE, measureReal_def]
  have hone : ∫ x, Real.exp (-s * f x) ∂ν =
      1 - ν.real E * (1 - Real.exp (-s)) := by
    have h := Causalean.Stat.Concentration.mgf_eq_of_mem_zero_one hf.aemeasurable
      (ae_of_all ν (fun x => by by_cases hx : x ∈ E <;> simp [f, hx]))
      (ν.real E) (-s) hmean
    dsimp [mgf] at h
    rw [h]
    ring
  have hfun : (fun sample : Fin n → Ω =>
      Real.exp (-s * ((∑ i : Fin n, if sample i ∈ E then 1 else 0 : ℕ) : ℝ))) =
      (fun sample => ∏ i : Fin n, Real.exp (-s * f (sample i))) := by
    funext sample
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    simp [f, Set.indicator]
  rw [hfun, integral_fintype_prod_eq_prod (fun _i : Fin n => fun x : Ω => Real.exp (-s * f x))]
  simp_rw [hone]
  simp

/-- The count Laplace transform is bounded by the exponential of minus the
sample size times the event mass times one minus the exponential tilt. -/
-- @node: indicatorCount_laplace_pi_le
lemma indicatorCount_laplace_pi_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (E : Set Ω) (hE : MeasurableSet E)
    (n : ℕ) (s : ℝ) : (by
    classical
    exact (∫ sample : Fin n → Ω,
      Real.exp (-s * ((∑ i : Fin n, if sample i ∈ E then 1 else 0 : ℕ) : ℝ))
        ∂Measure.pi (fun _ => ν)) ≤
      Real.exp (-(n : ℝ) * ν.real E * (1 - Real.exp (-s)))) := by
  classical
  rw [indicatorCount_laplace_pi ν E hE n s]
  have hp : ν.real E ≤ 1 := measureReal_le_one
  have hp0 : 0 ≤ ν.real E := measureReal_nonneg
  have hbase : 0 ≤ 1 - ν.real E * (1 - Real.exp (-s)) := by
    have := mul_nonneg hp0 (Real.exp_nonneg (-s))
    nlinarith
  calc
    _ ≤ (Real.exp (-(ν.real E) * (1 - Real.exp (-s)))) ^ n := by
      apply pow_le_pow_left₀ hbase
      have := Real.add_one_le_exp (-(ν.real E) * (1 - Real.exp (-s)))
      linarith
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A minimum count gives the largest exponential term, which is bounded by
the sum over subcells, including zero-count subcells. -/
-- @node: exp_minimumCellCount_le_sum
lemma exp_minimumCellCount_le_sum {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (s : ℝ) :
    Real.exp (-s * (minimumCellCount sample arm j m ε Q : ℝ)) ≤
      ∑ ℓ : MultiIndex d m, Real.exp (-s * (subcellCount sample arm j m ε Q ℓ : ℝ)) := by
  classical
  obtain ⟨ℓ, hℓ, heq⟩ := Finset.exists_mem_eq_inf'
    (by simp : (Finset.univ : Finset (MultiIndex d m)).Nonempty)
    (fun ℓ => subcellCount sample arm j m ε Q ℓ)
  unfold minimumCellCount
  rw [heq]
  exact Finset.single_le_sum (fun a _ => Real.exp_nonneg
    (-s * (subcellCount sample arm j m ε Q a : ℝ))) hℓ

/-- Consistency transfers measurability of the observed triple to the selected
pathwise observed-record version. -/
-- @node: observedRecord_aemeasurable
@[fun_prop] lemma observedRecord_aemeasurable {d : ℕ} (P : Law d)
    (hcons : Consistency P) : AEMeasurable P.observedRecord P.full := by
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    exact Measurable.ite
      ((by fun_prop : Measurable (fun u : Full d => u.2.1))
        (measurableSet_singleton true)) (by fun_prop) (by fun_prop)
  exact ho.aemeasurable.congr
    (show P.observedRecord =ᵐ[P.full] observe from hcons.1).symm

/-- The observed law has unit mass under iid sampling and consistency. -/
-- @node: obs_isProbabilityMeasure
lemma obs_isProbabilityMeasure {d : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) : IsProbabilityMeasure P.obs := by
  let : IsProbabilityMeasure P.full := hiid.1
  rw [hcons.2]
  exact Measure.isProbabilityMeasure_map (observedRecord_aemeasurable P hcons)

/-- Independent latent sampling and consistency give the product of the
one-observation observed law for every positive sample size. -/
-- @node: sample_eq_pi_obs
lemma sample_eq_pi_obs {d n : ℕ} (P : Law d) (hiid : IidSampling P)
    (hcons : Consistency P) (hn : 0 < n) :
    P.sample n = Measure.pi (fun _ : Fin n => P.obs) := by
  let : IsProbabilityMeasure P.full := hiid.1
  let : IsProbabilityMeasure (P.full.map P.observedRecord) :=
    Measure.isProbabilityMeasure_map (observedRecord_aemeasurable P hcons)
  rw [hiid.2.2 n hn, hiid.2.1 n hn,
    Measure.pi_map_pi (fun _ => observedRecord_aemeasurable P hcons), ← hcons.2]

/-- The half-open dyadic ownership map is measurable, including the outer
boundary where the floor index is truncated to the last cell. -/
-- @node: cellIndex_measurable
@[fun_prop] lemma cellIndex_measurable (d j : ℕ) : Measurable (cellIndex d j) := by
  apply measurable_pi_lambda
  intro i
  let g : ℕ → Fin (2 ^ j) := fun k =>
    ⟨min k (2 ^ j - 1), by
      have hp : 0 < 2 ^ j := by positivity
      omega⟩
  have hf : Measurable (fun x : Fin d → ℝ => Nat.floor ((2 : ℝ) ^ j * x i)) := by
    fun_prop
  exact (measurable_of_countable g).comp hf

/-- Each deterministic norming cube is a measurable intersection of coordinate
slabs. -/
-- @node: normingCube_measurableSet
lemma normingCube_measurableSet (d m : ℕ) (ε : ℝ) (ℓ : MultiIndex d m) :
    MeasurableSet (normingCube d m ε ℓ) := by
  unfold normingCube
  have heq : {u : Fin d → ℝ | ∀ i : Fin d, |u i - normingNode d m ℓ i| ≤ ε} =
      ⋂ i : Fin d, {u : Fin d → ℝ | |u i - normingNode d m ℓ i| ≤ ε} := by
    ext u
    simp
  rw [heq]
  exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)

/-- Every scaled norming subcell is measurable under the half-open dyadic
ownership convention. -/
-- @node: scaledSubcell_measurableSet
lemma scaledSubcell_measurableSet (d j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) :
    MeasurableSet (scaledSubcell d j m ε Q ℓ) := by
  have hQ : MeasurableSet (dyadicCell d j Q) :=
    (measurableSet_singleton Q).preimage (cellIndex_measurable d j)
  exact hQ.inter ((normingCube_measurableSet d m ε ℓ).preimage (by fun_prop))

/-- A measurable scaled subcell has a measurable arm-specific sample count. -/
-- @node: subcellCount_measurable
@[fun_prop] lemma subcellCount_measurable {d n : ℕ}
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (ℓ : MultiIndex d m) :
    Measurable (fun sample : Fin n → Obs d => subcellCount sample arm j m ε Q ℓ) := by
  classical
  have hcell := scaledSubcell_measurableSet d j m ε Q ℓ
  unfold subcellCount
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  exact ((measurableSet_singleton arm).preimage (by fun_prop)).inter
    (hcell.preimage (by fun_prop))

/-- The minimum over the fixed finite collection of measurable counts is a
measurable statistic, as needed for count-only admissibility. -/
-- @node: minimumCellCount_measurable
@[fun_prop] lemma minimumCellCount_measurable {d n : ℕ}
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    Measurable (fun sample : Fin n → Obs d => minimumCellCount sample arm j m ε Q) := by
  classical
  let g : (MultiIndex d m → ℕ) → ℕ := fun counts =>
    Finset.univ.inf' (by simp) counts
  exact (measurable_of_countable g).comp
    (measurable_pi_lambda _ (fun ℓ => subcellCount_measurable arm j m ε Q ℓ))

/-- Equation (15) for a single subcell, expressed using its observed arm mass.
This also includes zero counts and either treatment arm. -/
-- @node: subcellCount_laplace_le
lemma subcellCount_laplace_le {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (ℓ : MultiIndex d m) (s : ℝ) :
    (∫ sample, Real.exp (-s * (subcellCount sample arm j m ε Q ℓ : ℝ)) ∂P.sample n) ≤
      Real.exp (-(n : ℝ) * P.obs.real
        {o | o.2.1 = arm ∧ o.1 ∈ scaledSubcell d j m ε Q ℓ} * (1 - Real.exp (-s))) := by
  classical
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hiid hcons
  rw [sample_eq_pi_obs P hiid hcons hn]
  have hcell := scaledSubcell_measurableSet d j m ε Q ℓ
  have hE : MeasurableSet
      {o : Obs d | o.2.1 = arm ∧ o.1 ∈ scaledSubcell d j m ε Q ℓ} :=
    ((measurableSet_singleton arm).preimage (by fun_prop)).inter
      (hcell.preimage measurable_fst)
  have h := indicatorCount_laplace_pi_le
    P.obs {o : Obs d | o.2.1 = arm ∧ o.1 ∈ scaledSubcell d j m ε Q ℓ} hE n s
  convert h using 1
  congr 1
  funext sample
  congr 2
  unfold subcellCount
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ
  · simp [hx]
  · simp [hx]

/-- Equation (15): a common lower mass bound controls the minimum count's
Laplace transform, without independence between different subcell counts. -/
-- @node: minimumCellCount_laplace_le
lemma minimumCellCount_laplace_le {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (s p : ℝ) (hs : 0 ≤ s)
    (hmass : ∀ ℓ : MultiIndex d m,
      p ≤ P.obs.real {o | o.2.1 = arm ∧ o.1 ∈ scaledSubcell d j m ε Q ℓ}) :
    (∫ sample, Real.exp (-s * (minimumCellCount sample arm j m ε Q : ℝ)) ∂P.sample n) ≤
      (Fintype.card (MultiIndex d m) : ℝ) *
        Real.exp (-(n : ℝ) * p * (1 - Real.exp (-s))) := by
  classical
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hiid hcons
  have : IsProbabilityMeasure (P.sample n) := by
    rw [sample_eq_pi_obs P hiid hcons hn]
    infer_instance
  have hint (ℓ : MultiIndex d m) :
      Integrable (fun sample => Real.exp (-s * (subcellCount sample arm j m ε Q ℓ : ℝ)))
        (P.sample n) := by
    have hm : Measurable (fun sample : Fin n → Obs d =>
        Real.exp (-s * (subcellCount sample arm j m ε Q ℓ : ℝ))) := by
      have hN := subcellCount_measurable arm j m ε Q ℓ (n := n)
      have hcast : Measurable (fun sample : Fin n → Obs d =>
          (subcellCount sample arm j m ε Q ℓ : ℝ)) :=
        (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hN
      exact (hcast.const_mul (-s)).exp
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    apply ae_of_all
    intro sample
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Nat.cast_nonneg _)
  calc
    _ ≤ ∫ sample, ∑ ℓ : MultiIndex d m,
        Real.exp (-s * (subcellCount sample arm j m ε Q ℓ : ℝ)) ∂P.sample n :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => Real.exp_nonneg _))
        (integrable_finsetSum _ (fun ℓ _ => hint ℓ))
        (ae_of_all _ (fun sample => exp_minimumCellCount_le_sum sample arm j m ε Q s))
    _ = ∑ ℓ : MultiIndex d m, ∫ sample,
        Real.exp (-s * (subcellCount sample arm j m ε Q ℓ : ℝ)) ∂P.sample n := by
      exact integral_finsetSum _ (fun ℓ _ => hint ℓ)
    _ ≤ ∑ _ℓ : MultiIndex d m, Real.exp (-(n : ℝ) * p * (1 - Real.exp (-s))) := by
      apply Finset.sum_le_sum
      intro ℓ _
      apply (subcellCount_laplace_le P hiid hcons hn arm j m ε Q ℓ s).trans
      apply Real.exp_le_exp.mpr
      have hexp : 0 ≤ 1 - Real.exp (-s) := by
        have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
        linarith
      nlinarith [mul_le_mul_of_nonneg_right (hmass ℓ) hexp,
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    _ = _ := by simp

/-- Exponential Markov with the minimum-count Laplace bound controls
admissibility failures, including empty subcells. At tilt one this is the
count calculation in equation (5) of the adaptation roadmap. -/
-- @node: minimumCellCount_lower_tail_of_tilt
lemma minimumCellCount_lower_tail_of_tilt {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (s p a : ℝ) (hs : 0 ≤ s)
    (hmass : ∀ ℓ : MultiIndex d m,
      p ≤ P.obs.real {o | o.2.1 = arm ∧ o.1 ∈ scaledSubcell d j m ε Q ℓ}) :
    (P.sample n).real {sample | (minimumCellCount sample arm j m ε Q : ℝ) ≤ a} ≤
      (Fintype.card (MultiIndex d m) : ℝ) *
        Real.exp (s * a - (n : ℝ) * p * (1 - Real.exp (-s))) := by
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hiid hcons
  have : IsProbabilityMeasure (P.sample n) := by
    rw [sample_eq_pi_obs P hiid hcons hn]
    infer_instance
  let N : (Fin n → Obs d) → ℝ := fun sample => minimumCellCount sample arm j m ε Q
  have hmeas : Measurable N := by
    fun_prop
  have hint : Integrable (fun sample => Real.exp (-s * N sample)) (P.sample n) := by
    apply Integrable.of_bound (hmeas.const_mul (-s)).exp.aestronglyMeasurable 1
    apply ae_of_all
    intro sample
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Nat.cast_nonneg _))
  have hmarkov := measure_le_le_exp_mul_mgf a (neg_nonpos.mpr hs) hint
  have hlaplace := minimumCellCount_laplace_le P hiid hcons hn arm j m ε Q s p hs hmass
  change (P.sample n).real {sample | N sample ≤ a} ≤ _
  calc
    _ ≤ Real.exp (-(-s) * a) * mgf N (P.sample n) (-s) := hmarkov
    _ ≤ Real.exp (-(-s) * a) *
        ((Fintype.card (MultiIndex d m) : ℝ) *
          Real.exp (-(n : ℝ) * p * (1 - Real.exp (-s)))) :=
      mul_le_mul_of_nonneg_left hlaplace (Real.exp_nonneg _)
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- The compact-tilt comparison after equation (15), with an explicit positive
constant: one minus the negative exponential dominates a linear function on
any fixed positive interval. -/
-- @node: one_sub_exp_neg_lower_on_interval
lemma one_sub_exp_neg_lower_on_interval (S s : ℝ) (hS : 0 < S)
    (hs : 0 ≤ s) (hsS : s ≤ S) :
    (1 - Real.exp (-S)) / S * s ≤ 1 - Real.exp (-s) := by
  have hx : s / S ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs hS.le, (div_le_one hS).mpr hsS⟩
  have hsec := Causalean.Stat.Concentration.exp_mul_le_secant (s := -S) hx
  have hprod : -S * (s / S) = -s := by field_simp
  rw [hprod] at hsec
  have heq : (1 - Real.exp (-S)) / S * s = -(s / S * (Real.exp (-S) - 1)) := by
    ring
  rw [heq]
  linarith

end CausalSmith.Stat.GlobalTailDesignRobustCate
