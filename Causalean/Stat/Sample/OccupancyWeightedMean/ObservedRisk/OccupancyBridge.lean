module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.Basic
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.PoissonAggregate
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.PoissonCell
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.PoissonTransport

/-!
# Poissonization bridge for finite observed designs

This module separates the deterministic prefix monotonicity, independent
Poisson occupancy estimate, and half-intensity de-Poissonization needed for
uniform fixed-sample collision bounds. All laws here concern observed cell and
arm labels.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped NNReal

/-- Adding observations cannot decrease the number of observations lying in
cells where both observed arms are present. This includes the case in which a
previously unmatched cell becomes matched. -/
theorem usableTotal_prefix_mono {Ω κ : Type} [Fintype κ] [DecidableEq κ]
    {n N : ℕ} (hnN : n ≤ N) (X : Ω → κ) (A : Ω → Bool)
    (z : Fin N → Ω) :
    usableTotal X A (fun i : Fin n => z (Fin.castLE hnN i)) ≤ usableTotal X A z := by
  classical
  have hcount (a : Bool) (k : κ) :
      groupArmCount X A (fun i : Fin n => z (Fin.castLE hnN i)) a k ≤
        groupArmCount X A z a k := by
    unfold groupArmCount
    apply Finset.card_le_card_of_injOn (Fin.castLE hnN)
    · intro i hi
      simpa using hi
    · intro i _ j _ hij
      exact Fin.castLE_injective hnN hij
  unfold usableTotal usableGroupTotal
  apply Finset.sum_le_sum
  intro k _
  by_cases hp : usableGroup X A (fun i : Fin n => z (Fin.castLE hnN i)) k
  · have hfull : usableGroup X A z k := by
      exact ⟨lt_of_lt_of_le hp.1 (hcount false k),
        lt_of_lt_of_le hp.2 (hcount true k)⟩
    simp only [if_pos hp, if_pos hfull, groupCount]
    have hf := hcount false k
    have ht := hcount true k
    omega
  · simp [hp]

/-- The half-intensity Poisson sample has an exponentially small Laplace
transform of usable occupancy, uniformly over finite observed cell masses and
null cells under arm-cell overlap. The positive exponent constant depends only
on the overlap margin. -/
theorem poissonized_design_laplace_rate (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (ν : Measure (Fin d × Bool)) [IsProbabilityMeasure ν]
        (n : ℕ), 0 < n →
        (∀ a k, 0 < cellMass ν (fun v : Fin d × Bool => v.1) k →
          epsilon * cellMass ν (fun v : Fin d × Bool => v.1) k ≤
            armCellMass ν (fun v => v.1) (fun v => v.2) a k) →
        (∫ s : FiniteSample (Fin d × Bool),
          Real.exp (-(usableTotal (fun v : Fin d × Bool => v.1)
            (fun v => v.2) s.2 : ℝ))
          ∂finitePoissonSampleLaw ν ((n : ℝ≥0) / 2)) ≤
          Real.exp (-(c * (n : ℝ) ^ 2 /
            max (n : ℝ) (d : ℝ))) := by
  classical
  obtain ⟨c₀, hc₀, hrate⟩ :=
    independent_poisson_laplace_rate epsilon hepsilon hepsilon_half
  refine ⟨c₀ / 4, by positivity, ?_⟩
  intro d ν _ n hn hoverlap
  have hd : 0 < d := by
    by_contra h
    have hzero : d = 0 := by omega
    subst d
    have hempty : (Set.univ : Set (Fin 0 × Bool)) = ∅ := by
      ext ⟨k, a⟩
      exact Fin.elim0 k
    have hprob := measure_univ (μ := ν)
    rw [hempty, measure_empty] at hprob
    exact zero_ne_one hprob
  let lam : ℝ≥0 := (n : ℝ≥0) / 2
  let u : Fin d → ℝ≥0 := fun k => lam * (ν {(k, false)}).toNNReal
  let v : Fin d → ℝ≥0 := fun k => lam * (ν {(k, true)}).toNNReal
  let x : Fin d → ℝ := fun k => (u k : ℝ) + v k
  have hsplit (k : Fin d) :
      ν {(k, false)} + ν {(k, true)} =
        ν (groupEvent (fun w : Fin d × Bool => w.1) k) := by
    rw [← measure_union (by simp) (measurableSet_singleton _)]
    congr 1
    ext ⟨j, a⟩
    cases a <;> simp [groupEvent]
  have hx (k : Fin d) : x k = (lam : ℝ) * cellMass ν (fun w => w.1) k := by
    simp only [x, u, v, cellMass]
    rw [← NNReal.coe_add, ← mul_add, ← ENNReal.toNNReal_add (measure_ne_top ν _)
      (measure_ne_top ν _), hsplit]
    rfl
  have hsum : ∑ k, x k = (lam : ℝ) := by
    let p : FiniteMeasurablePartition (Fin d × Bool) (Fin d) :=
      ⟨Prod.fst, measurable_fst⟩
    have hp : ∑ k, cellMass ν (fun w : Fin d × Bool => w.1) k = 1 := by
      have h := p.sum_cellMass ν
      apply_fun (fun t : ℝ≥0 => (t : ℝ)) at h
      norm_cast at h
      calc
        _ = ∑ k, (p.cellMass ν k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k _
          rfl
        _ = 1 := by exact_mod_cast h
    simp_rw [hx]
    rw [← Finset.mul_sum, hp, mul_one]
  have hu (k : Fin d) : epsilon * x k ≤ u k := by
    by_cases hk : 0 < cellMass ν (fun w : Fin d × Bool => w.1) k
    · have hh := hoverlap false k hk
      rw [hx]
      have hle : (lam : ℝ) * (epsilon * cellMass ν (fun w => w.1) k) ≤
          (lam : ℝ) * armCellMass ν (fun w => w.1) (fun w => w.2) false k :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      convert hle using 1
      · ring
      · have hevent : armGroupEvent (fun w : Fin d × Bool => w.1)
            (fun w => w.2) false k = {(k, false)} := by
          ext ⟨j, a⟩
          cases a <;> simp [armGroupEvent]
        simp [u, armCellMass, hevent, ENNReal.toReal]
    · have hz : cellMass ν (fun w : Fin d × Bool => w.1) k = 0 := by
        have : 0 ≤ cellMass ν (fun w : Fin d × Bool => w.1) k := by
          unfold cellMass
          positivity
        exact le_antisymm (le_of_not_gt hk) this
      simp [hx, hz]
  have hv (k : Fin d) : epsilon * x k ≤ v k := by
    by_cases hk : 0 < cellMass ν (fun w : Fin d × Bool => w.1) k
    · have hh := hoverlap true k hk
      rw [hx]
      have hle : (lam : ℝ) * (epsilon * cellMass ν (fun w => w.1) k) ≤
          (lam : ℝ) * armCellMass ν (fun w => w.1) (fun w => w.2) true k :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      convert hle using 1
      · ring
      · have hevent : armGroupEvent (fun w : Fin d × Bool => w.1)
            (fun w => w.2) true k = {(k, true)} := by
          ext ⟨j, a⟩
          cases a <;> simp [armGroupEvent]
        simp [v, armCellMass, hevent, ENNReal.toReal]
    · have hz : cellMass ν (fun w : Fin d × Bool => w.1) k = 0 := by
        have : 0 ≤ cellMass ν (fun w : Fin d × Bool => w.1) k := by
          unfold cellMass
          positivity
        exact le_antisymm (le_of_not_gt hk) this
      simp [hx, hz]
  have hbound := hrate d hd u v x (lam : ℝ) (fun k => rfl) hu hv hsum
  let H : FiniteSample (Fin d × Bool) → Fin d → ℕ × ℕ := fun s k =>
    (groupArmCount (fun w : Fin d × Bool => w.1) (fun w => w.2) s.2 false k,
     groupArmCount (fun w : Fin d × Bool => w.1) (fun w => w.2) s.2 true k)
  have hH : Measurable H := by
    intro t ht
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet ((fun z : Fin m → Fin d × Bool => H ⟨m, z⟩) ⁻¹' t)
    exact (Set.to_countable _).measurableSet
  have hcount (s : FiniteSample (Fin d × Bool)) :
      (usableTotal (fun w : Fin d × Bool => w.1) (fun w => w.2) s.2 : ℝ) =
        ∑ k, (usablePoissonPairCount (H s k) : ℝ) := by
    unfold usableTotal usableGroupTotal usablePoissonPairCount usableGroup groupCount H
    push_cast
    rfl
  have htransport :
      (∫ s : FiniteSample (Fin d × Bool),
        Real.exp (-(usableTotal (fun w : Fin d × Bool => w.1)
          (fun w => w.2) s.2 : ℝ)) ∂finitePoissonSampleLaw ν lam) =
      ∫ z : Fin d → ℕ × ℕ,
        Real.exp (-(∑ k, (usablePoissonPairCount (z k) : ℝ)))
        ∂Measure.pi (fun k => (poissonMeasure (u k)).prod (poissonMeasure (v k))) := by
    rw [← poisson_arm_cell_count_law ν lam]
    rw [integral_map hH.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    congr 1
    funext s
    rw [hcount]
  rw [htransport]
  have hlam : (lam : ℝ) = (n : ℝ) / 2 := by
    simp [lam, NNReal.coe_div]
  rw [hlam] at hbound
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hdreal : (0 : ℝ) ≤ d := by positivity
  have hmax : 0 < max (n : ℝ) (d : ℝ) := lt_of_lt_of_le hnreal (le_max_left _ _)
  have hr : c₀ / 4 * (n : ℝ) ^ 2 / max (n : ℝ) (d : ℝ) ≤
      c₀ * ((n : ℝ) / 2) ^ 2 / max ((n : ℝ) / 2) (d : ℝ) := by
    have hmaxle : max ((n : ℝ) / 2) (d : ℝ) ≤ max (n : ℝ) (d : ℝ) :=
      max_le_max_right _ (by linarith)
    have hmaxhalf : 0 < max ((n : ℝ) / 2) (d : ℝ) := by
      apply lt_of_lt_of_le (by linarith : (0 : ℝ) < (n : ℝ) / 2)
      exact le_max_left _ _
    apply (div_le_div_iff₀ hmax hmaxhalf).2
    nlinarith [mul_nonneg (show 0 ≤ c₀ * (n : ℝ) ^ 2 by positivity)
      (sub_nonneg.mpr hmaxle)]
  exact le_trans hbound (Real.exp_le_exp.mpr (neg_le_neg hr))

/-- Given [a finite cell count and sample size](hyp:d,n) and [an observed
probability law on cell-arm pairs](hyp:ν), [the expectation of exp(−usable
total) under n independent draws is at most twice the expectation of the same
quantity for a Poissonized sample, in which the number of independent draws is
itself Poisson with mean n/2](goal). The usable total is the number of
observations in cells containing both arms; no overlap condition is assumed. -/
theorem fixed_design_laplace_le_poisson {d n : ℕ}
    (ν : Measure (Fin d × Bool)) [IsProbabilityMeasure ν] :
    (∫ z : Fin n → Fin d × Bool,
      Real.exp (-(usableTotal (fun v : Fin d × Bool => v.1)
        (fun v => v.2) z : ℝ))
      ∂Measure.pi (fun _ : Fin n => ν)) ≤
    2 * (∫ s : FiniteSample (Fin d × Bool),
      Real.exp (-(usableTotal (fun v : Fin d × Bool => v.1)
        (fun v => v.2) s.2 : ℝ))
      ∂finitePoissonSampleLaw ν ((n : ℝ≥0) / 2)) := by
  classical
  let X := Fin d × Bool
  let lam : ℝ≥0 := (n : ℝ≥0) / 2
  let G (m : ℕ) (z : Fin m → X) : ℝ :=
    Real.exp (-(usableTotal (fun v : X => v.1) (fun v => v.2) z : ℝ))
  let F (s : FiniteSample X) : ℝ := G s.1 s.2
  have hG (m : ℕ) : Measurable (G m) := measurable_of_countable _
  have hF : Measurable F := by
    intro t ht
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet ((fun z : Fin m → X => F ⟨m, z⟩) ⁻¹' t)
    exact ht.preimage (hG m)
  have hbounds (m : ℕ) (z : Fin m → X) : 0 ≤ G m z ∧ G m z ≤ 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (by positivity)
  have htail : (1 / 2 : ℝ) ≤ (poissonMeasure lam).real (Set.Iic n) := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := poissonMeasure lam) (f := fun k : ℕ => (k : ℝ))
      (ae_of_all _ fun k => Nat.cast_nonneg k)
      ((Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two lam).integrable
        (by norm_num)) ((n : ℝ) + 1)
    have hset : {k : ℕ | (n : ℝ) + 1 ≤ (k : ℝ)} = (Set.Iic n)ᶜ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Iic]
      norm_cast
      omega
    rw [hset, measureReal_compl measurableSet_Iic,
      Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment] at hmarkov
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hmarkov
    change ((n : ℝ) + 1) * (1 - (poissonMeasure lam).real (Set.Iic n)) ≤
      (lam : ℝ) at hmarkov
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 0 ≤ (poissonMeasure lam).real (Set.Iic n) := measureReal_nonneg
    have hlam : (lam : ℝ) = (n : ℝ) / 2 := by simp [lam, NNReal.coe_div]
    rw [hlam] at hmarkov
    nlinarith
  let μ : Measure (ℕ × (ℕ → X)) := poissonIIDStreamLaw ν lam
  let q (w : ℕ → X) : ℝ := G n (fun i => w i)
  let a (m : ℕ) : ℝ := if m ≤ n then 1 else 0
  have hq : Measurable q := (hG n).comp (by fun_prop)
  have ha : Measurable a := measurable_of_countable _
  have hqint : Integrable q (iidStreamLaw ν) := by
    apply Integrable.of_bound hq.aestronglyMeasurable 1
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hbounds n _).1]
    exact (hbounds n _).2
  have haint : Integrable a (poissonMeasure lam) := by
    apply Integrable.of_bound ha.aestronglyMeasurable 1
    filter_upwards with m
    simp only [a]
    split_ifs <;> norm_num
  have hFint : Integrable (fun z : ℕ × (ℕ → X) => F (streamToFiniteSample z)) μ := by
    apply Integrable.of_bound (hF.comp measurable_streamToFiniteSample).aestronglyMeasurable 1
    filter_upwards with z
    change ‖G z.1 (fun i : Fin z.1 => z.2 i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hbounds z.1 _).1]
    exact (hbounds z.1 _).2
  have hprodint : Integrable (fun z : ℕ × (ℕ → X) => a z.1 * q z.2) μ := by
    change Integrable (fun z : ℕ × (ℕ → X) => a z.1 * q z.2)
      ((poissonMeasure lam).prod (iidStreamLaw ν))
    exact haint.mul_prod hqint
  have hcomp : ∀ z : ℕ × (ℕ → X), a z.1 * q z.2 ≤ F (streamToFiniteSample z) := by
    intro z
    by_cases hz : z.1 ≤ n
    · have hm := usableTotal_prefix_mono hz (fun v : X => v.1) (fun v => v.2)
        (fun i : Fin n => z.2 i)
      have he : G n (fun i => z.2 i) ≤ G z.1 (fun i => z.2 i) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (by exact_mod_cast hm)
      simpa [a, q, F, G, streamToFiniteSample, hz] using he
    · have hp := (hbounds z.1 (fun i : Fin z.1 => z.2 i)).1
      simpa [a, F, G, streamToFiniteSample, hz] using hp
  have hmain := integral_mono hprodint hFint hcomp
  have hfactor : (∫ z : ℕ × (ℕ → X), a z.1 * q z.2 ∂μ) =
      (poissonMeasure lam).real (Set.Iic n) * ∫ w : ℕ → X, q w ∂iidStreamLaw ν := by
    change (∫ z : ℕ × (ℕ → X), a z.1 * q z.2
      ∂(poissonMeasure lam).prod (iidStreamLaw ν)) = _
    rw [integral_prod_mul]
    congr 1
    have haeq : a = (Set.Iic n).indicator (fun _ => (1 : ℝ)) := by
      funext m
      simp [a, Set.indicator, Set.mem_Iic]
    rw [haeq]
    rw [integral_indicator measurableSet_Iic]
    simp [measureReal_def]
  have hprefix : (∫ w : ℕ → X, q w ∂iidStreamLaw ν) =
      ∫ z : Fin n → X, G n z ∂Measure.pi (fun _ : Fin n => ν) := by
    rw [← iidStreamLaw_map_finPrefix ν n]
    exact (integral_map (by fun_prop : Measurable (fun w : ℕ → X =>
      fun i : Fin n => w i)).aemeasurable (hG n).aestronglyMeasurable).symm
  have hpoisson : (∫ s : FiniteSample X, F s ∂finitePoissonSampleLaw ν lam) =
      ∫ z : ℕ × (ℕ → X), F (streamToFiniteSample z) ∂μ := by
    exact integral_map measurable_streamToFiniteSample.aemeasurable
      hF.aestronglyMeasurable
  have hfixed_nonneg : 0 ≤ ∫ z : Fin n → X, G n z ∂Measure.pi (fun _ : Fin n => ν) :=
    integral_nonneg (fun z => (hbounds n z).1)
  have hhalf : (1 / 2 : ℝ) *
      (∫ z : Fin n → X, G n z ∂Measure.pi (fun _ : Fin n => ν)) ≤
      (poissonMeasure lam).real (Set.Iic n) *
      (∫ z : Fin n → X, G n z ∂Measure.pi (fun _ : Fin n => ν)) :=
    mul_le_mul_of_nonneg_right htail hfixed_nonneg
  change (∫ z : Fin n → X, G n z ∂Measure.pi (fun _ : Fin n => ν)) ≤
    2 * (∫ s : FiniteSample X, F s ∂finitePoissonSampleLaw ν lam)
  rw [hpoisson]
  rw [hfactor, hprefix] at hmain
  linarith

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
