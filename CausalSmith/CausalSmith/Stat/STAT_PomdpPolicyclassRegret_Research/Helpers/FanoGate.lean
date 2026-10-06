module
public import Causalean.Stat.Minimax.Fano

/-!
# Cited average testing gate

Tsybakov, A. B. (2009), *Introduction to Nonparametric Estimation*,
Lemma 2.10, Section 2.7.1, pp. 111–112, DOI:10.1007/b13794.
The source states the average-error entropy form of Fano's inequality.
The exact entropy inequality is obtained from Causalean's finite-alphabet Fano
inequality by pushing each experiment law through a measurable decoder and then
passing to the infimum over decoders.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory InformationTheory
open scoped BigOperators ENNReal
/-- [the fano mixture object](goal) is defined from [the sample space](hyp:Ω),
[the model](hyp:m), and [the probability law](hyp:P). -/

noncomputable def fanoMixture {Ω : Type*} [MeasurableSpace Ω] (m : Nat)
    (P : Fin m → Measure Ω) : Measure Ω :=
  ∑ i : Fin m, ((m : ℝ≥0∞)⁻¹) • P i
/-- [the fano average error quantity](goal) is defined from [the sample space](hyp:Ω),
[the model](hyp:m), and [the probability law](hyp:P). -/

noncomputable def fanoAverageError {Ω : Type*} [MeasurableSpace Ω]
    (m : Nat) (P : Fin m → Measure Ω) : ℝ :=
  ⨅ ψ : {ψ : Ω → Fin m // Measurable ψ},
    (m : ℝ)⁻¹ * ∑ i : Fin m, (P i).real {ω | ψ.1 ω ≠ i}

private lemma fanoMixture_eq_uniformMixture {Ω : Type*} [MeasurableSpace Ω]
    (m : Nat) [Nonempty (Fin m)] (P : Fin m → Measure Ω) :
    fanoMixture m P = Causalean.Stat.uniformMixture P := by
  ext A hA
  simp only [fanoMixture, Causalean.Stat.uniformMixture,
    Causalean.Stat.mixture, Fintype.card_fin]

private theorem fano_decoder_entropy
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (hcard : 2 ≤ Fintype.card ι) (decode : Ω → ι) (hdecode : Measurable decode) :
    Real.log (Fintype.card ι : ℝ) - Causalean.Stat.uniformMutualInformation P ≤
      Real.binEntropy ((Fintype.card ι : ℝ)⁻¹ *
          ∑ i, (P i).real {ω | decode ω ≠ i}) +
        ((Fintype.card ι : ℝ)⁻¹ * ∑ i, (P i).real {ω | decode ω ≠ i}) *
          Real.log ((Fintype.card ι : ℝ) - 1) := by
  classical
  let N : ℝ := Fintype.card ι
  let u : ℝ := N⁻¹
  let Pbar : Measure Ω := Causalean.Stat.uniformMixture P
  let R : ι → Measure ι := fun i => Measure.map decode (P i)
  let Rbar : Measure ι := Measure.map decode Pbar
  let r : ι → ι → ℝ := fun i y => (R i).real {y}
  let p : ι × ι → ℝ := fun z => u * r z.1 z.2
  let hPbar : IsProbabilityMeasure Pbar :=
    Causalean.Stat.uniformMixture_isProbabilityMeasure P
  let hR : ∀ i, IsProbabilityMeasure (R i) := fun _i =>
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  let hRbar : IsProbabilityMeasure Rbar :=
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  have hfin : ∀ i,
      InformationTheory.klDiv (P i) (Causalean.Stat.uniformMixture P) ≠ ⊤ :=
    Causalean.Stat.klDiv_uniformMixture_ne_top P
  have hr0 : ∀ i y, 0 ≤ r i y := fun _i _y => measureReal_nonneg
  have hrsum : ∀ i, ∑ y, r i y = 1 := by
    intro i
    simpa [r, probReal_univ] using
      (sum_measureReal_singleton (μ := R i) (Finset.univ : Finset ι))
  have hp0 : ∀ z, 0 ≤ p z := fun z => mul_nonneg (by positivity) (hr0 z.1 z.2)
  have hpsum : ∑ z, p z = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [p, ← Finset.mul_sum, hrsum]
    simp [u, N, Fintype.card_ne_zero]
  have hRbarMass : ∀ y, Rbar.real {y} = u * ∑ i, r i y := by
    intro y
    rw [show Rbar.real {y} = Pbar.real (decode ⁻¹' {y}) by
      simp [Rbar, Measure.real, Measure.map_apply hdecode (measurableSet_singleton y)]]
    simp only [Pbar, Causalean.Stat.uniformMixture, Causalean.Stat.mixture_apply,
      Measure.real]
    rw [ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [ENNReal.toReal_inv]
      simp only [ENNReal.toReal_natCast, r, R, Measure.real]
      rw [Measure.map_apply hdecode (measurableSet_singleton y)]
    · intro i _hi
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  have hRac : ∀ i, R i ≪ Rbar := fun i =>
    (Causalean.Stat.absolutelyContinuous_uniformMixture P i).map hdecode
  have hfiniteR : ∀ i, InformationTheory.klDiv (R i) Rbar ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (hfin i)
      (InformationTheory.klDiv_map_le (P i) Pbar hdecode)
  have hinfoEq :
      Real.log N - Causalean.Mathlib.InformationTheory.condEntropy p =
        u * ∑ i, (InformationTheory.klDiv (R i) Rbar).toReal := by
    rw [show Real.log N = Real.log (Fintype.card ι) by rfl,
      show u = (Fintype.card ι : ℝ)⁻¹ by rfl,
      Causalean.Mathlib.InformationTheory.uniform_condEntropy_kl_identity r hr0 hrsum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Causalean.Mathlib.InformationTheory.klDiv_toReal_eq_sum_measureReal
      (R i) Rbar (hRac i)]
    simp only [r]
    congr 1
    funext y
    rw [hRbarMass]
  have hinfoLe :
      u * ∑ i, (InformationTheory.klDiv (R i) Rbar).toReal ≤
        Causalean.Stat.uniformMutualInformation P := by
    simp only [Causalean.Stat.uniformMutualInformation, u, N]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _hi
    exact (ENNReal.toReal_le_toReal (hfiniteR i) (hfin i)).2
      (InformationTheory.klDiv_map_le (P i) (Causalean.Stat.uniformMixture P) hdecode)
  have hfano := Causalean.Mathlib.InformationTheory.fano_inequality
    hp0 hpsum hcard (fun y : ι => y)
  have herrorEq :
      Causalean.Mathlib.InformationTheory.errorProb p (fun y : ι => y) =
        u * ∑ i, (P i).real {ω | decode ω ≠ i} := by
    rw [Causalean.Mathlib.InformationTheory.errorProb_def, Fintype.sum_prod_type]
    simp only [p]
    calc
      (∑ i, ∑ y, if i = y then 0 else u * r i y) =
          ∑ i, u * ∑ y, (if i = y then 0 else r i y) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _hy
            by_cases hiy : i = y <;> simp [hiy]
      _ = u * ∑ i, (P i).real {ω | decode ω ≠ i} := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        congr 1
        have hinner : (∑ y, if i = y then 0 else r i y) = 1 - r i i := by
          calc
            (∑ y, if i = y then 0 else r i y) =
                ∑ y, (r i y - if y = i then r i y else 0) := by
                  apply Finset.sum_congr rfl
                  intro y _hy
                  by_cases hy : y = i
                  · simp [hy]
                  · simp [hy, Ne.symm hy]
            _ = (∑ y, r i y) - ∑ y, (if y = i then r i y else 0) := by
                  rw [Finset.sum_sub_distrib]
            _ = 1 - r i i := by rw [hrsum]; simp
        rw [hinner]
        have hset : {ω | decode ω ≠ i} = (decode ⁻¹' {i})ᶜ := by
          ext ω
          simp
        rw [hset, measureReal_compl (hdecode (measurableSet_singleton i)), probReal_univ]
        congr 1
        simp only [r, R, Measure.real]
        rw [Measure.map_apply hdecode (measurableSet_singleton i)]
  rw [herrorEq] at hfano
  refine le_trans ?_ hfano
  calc
    Real.log (Fintype.card ι : ℝ) - Causalean.Stat.uniformMutualInformation P ≤
        Real.log N - u * ∑ i, (InformationTheory.klDiv (R i) Rbar).toReal := by
      exact sub_le_sub_left hinfoLe _
    _ = Causalean.Mathlib.InformationTheory.condEntropy p := by linarith [hinfoEq]

/-- Tsybakov, A. B. (2009), *Introduction to Nonparametric Estimation*,
Lemma 2.10, Section 2.7.1, pp. 111–112, DOI:10.1007/b13794.
The displayed inequality is the relabeled `m`-measure specialization of the
source's `M+1`-measure average-error Fano inequality. -/
-- @node: lem:fano-average-testing
theorem FanoAverageTesting :
    ∀ (Ω : Type) [MeasurableSpace Ω] (m : Nat), 2 ≤ m →
      ∀ (P : Fin m → Measure Ω), (∀ i, IsProbabilityMeasure (P i)) →
        Real.binEntropy (fanoAverageError m P) +
          fanoAverageError m P * Real.log ((m - 1 : Nat) : ℝ) ≥
            Real.log (m : ℝ) -
              (m : ℝ)⁻¹ * ∑ i : Fin m,
                (InformationTheory.klDiv (P i) (fanoMixture m P)).toReal := by
  intro Ω _mΩ m hm P hP
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI : ∀ i, IsProbabilityMeasure (P i) := hP
  let Ψ := {ψ : Ω → Fin m // Measurable ψ}
  letI : Nonempty Ψ :=
    ⟨⟨fun _ => ⟨0, by omega⟩, measurable_const⟩⟩
  let err : Ψ → ℝ := fun ψ =>
    (m : ℝ)⁻¹ * ∑ i : Fin m, (P i).real {ω | ψ.1 ω ≠ i}
  let p : ℝ := ⨅ ψ : Ψ, err ψ
  have herr_nonneg : ∀ ψ, 0 ≤ err ψ := by
    intro ψ
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
  have hbdd : BddBelow (Set.range err) := by
    exact ⟨0, by rintro _ ⟨ψ, rfl⟩; exact herr_nonneg ψ⟩
  have hp_le : ∀ ψ, p ≤ err ψ := fun ψ => ciInf_le hbdd ψ
  have hnear : ∀ n : Nat, ∃ ψ : Ψ, err ψ < p + 1 / ((n : ℝ) + 1) := by
    intro n
    apply exists_lt_of_ciInf_lt
    dsimp [p]
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose ψ hψ using hnear
  have herr_tendsto : Filter.Tendsto (fun n => err (ψ n)) Filter.atTop (nhds p) := by
    have hupper : Filter.Tendsto (fun n : Nat => p + 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds p) := by
      convert (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) using 1 <;> simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => p) Filter.atTop (nhds p))
      hupper
    · exact Filter.Eventually.of_forall fun n => hp_le (ψ n)
    · exact Filter.Eventually.of_forall fun n => (hψ n).le
  let g : ℝ → ℝ := fun q =>
    Real.binEntropy q + q * Real.log ((m - 1 : Nat) : ℝ)
  have hg : Continuous g :=
    Real.binEntropy_continuous.add (continuous_id.mul continuous_const)
  have hg_tendsto : Filter.Tendsto (fun n => g (err (ψ n))) Filter.atTop (nhds (g p)) :=
    hg.continuousAt.tendsto.comp herr_tendsto
  have hdecoder : ∀ n, Real.log (m : ℝ) -
      (m : ℝ)⁻¹ * ∑ i : Fin m,
        (InformationTheory.klDiv (P i) (fanoMixture m P)).toReal ≤
      g (err (ψ n)) := by
    intro n
    letI : MeasurableSpace (Fin m) := ⊤
    have h := fano_decoder_entropy P (by simpa using hm) (ψ n).1 (ψ n).2
    rw [fanoMixture_eq_uniformMixture m P]
    simpa [g, err, Fintype.card_fin, Causalean.Stat.uniformMutualInformation,
      Nat.cast_sub (by omega : 1 ≤ m)] using h
  have hlimit := ge_of_tendsto hg_tendsto
    (Filter.Eventually.of_forall hdecoder)
  simpa [fanoAverageError, p, g, err] using hlimit

end CausalSmith.Stat.PomdpPolicyclassRegret
