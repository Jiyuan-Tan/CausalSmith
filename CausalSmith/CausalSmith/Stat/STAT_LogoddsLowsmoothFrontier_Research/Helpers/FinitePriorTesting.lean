module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.TwoPointLength

/-! # Finite-prior testing with the original records and independent seed

Uniform sign averaging preserves honesty and averages expected interval length.
Transferring coverage by total variation then gives the two-effect length lower
bound for every Borel honest procedure, including randomized procedures.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The prior draws its sign once, then supplies the original sample and seed. -/
-- @node: signPriorExperiment
def signPriorExperiment (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) : Measure (Experiment n) :=
  ENNReal.ofReal ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹) •
    ∑ σ, experimentLaw (laws σ) n

/-- Averaging the original-record laws and then tensoring the seed gives
exactly the finite prior of full experiments. [the documented result](goal) -/
-- @node: signPriorExperiment_eq_prod
lemma signPriorExperiment_eq_prod (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) :
    signPriorExperiment n k laws = (finiteSignMixture n k laws).prod uniformLaw := by
  unfold signPriorExperiment finiteSignMixture
  have hweight : (2 : ℝ)^(-(k+1 : ℕ) : ℤ) =
      (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast]
  rw [hweight, Measure.prod_smul_left]
  congr 1
  rw [← Measure.sum_fintype (fun σ =>
    Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (laws σ).measure n),
    Measure.prod_sum_left, Measure.sum_fintype]
  rfl

/-- A prior concentrated on one law gives its literal full experiment. [the stated conclusion](goal) holds. -/
-- @node: signPriorExperiment_const
lemma signPriorExperiment_const (n k : ℕ) (P : ObservedLaw) :
    signPriorExperiment n k (fun _ => P) = experimentLaw P n := by
  unfold signPriorExperiment
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_smul]

/-- The sign prior has exactly unit mass. [the stated conclusion](goal) holds. -/
-- @node: signPriorExperiment_probability
instance signPriorExperiment_probability (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) :
    IsProbabilityMeasure (signPriorExperiment n k laws) := by
  haveI : ∀ σ, IsProbabilityMeasure (experimentLaw (laws σ) n) :=
    fun σ => experimentLaw_probability (laws σ) n
  constructor
  simp only [signPriorExperiment, Measure.smul_apply, Measure.finsetSum_apply,
    MeasurableSet.univ, measure_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
    mul_one, smul_eq_mul, ENNReal.inv_mul_cancel (by positivity) (by finiteness)]

/-- The original-record mixture is itself a probability measure. [the stated conclusion](goal) holds. -/
-- @node: finiteSignMixture_probability
lemma finiteSignMixture_probability (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) :
    IsProbabilityMeasure (finiteSignMixture n k laws) := by
  have h := (signPriorExperiment_probability n k laws).measure_univ
  rw [signPriorExperiment_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    (show uniformLaw Set.univ = 1 from measure_univ), mul_one] at h
  exact ⟨h⟩

/-- Adding the same independent seed preserves total variation exactly. [the stated conclusion](goal) holds. -/
-- @node: signPriorExperiment_tv
lemma signPriorExperiment_tv (n k₀ k₁ : ℕ)
    (laws₀ : (Fin (k₀+1) → Bool) → ObservedLaw)
    (laws₁ : (Fin (k₁+1) → Bool) → ObservedLaw) :
    Causalean.Stat.tvDist (signPriorExperiment n k₀ laws₀)
      (signPriorExperiment n k₁ laws₁) =
    Causalean.Stat.tvDist (finiteSignMixture n k₀ laws₀)
      (finiteSignMixture n k₁ laws₁) := by
  letI := finiteSignMixture_probability n k₀ laws₀
  letI := finiteSignMixture_probability n k₁ laws₁
  rw [signPriorExperiment_eq_prod, signPriorExperiment_eq_prod,
    ← Measure.compProd_const, ← Measure.compProd_const,
    Causalean.Stat.tvDist_compProd_eq]

/-- Event probabilities are the finite average of the constituent experiments. Under the stated assumptions. [The stated hypotheses](hyp:hA) hold, and [the stated conclusion follows](goal). -/
-- @node: signPriorExperiment_real
lemma signPriorExperiment_real (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw)
    (A : Set (Experiment n)) (hA : MeasurableSet A) :
    (signPriorExperiment n k laws).real A =
      (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, (experimentLaw (laws σ) n).real A := by
  haveI : ∀ σ, IsProbabilityMeasure (experimentLaw (laws σ) n) :=
    fun σ => experimentLaw_probability (laws σ) n
  simp only [measureReal_def, signPriorExperiment, Measure.smul_apply,
    Measure.finsetSum_apply, hA, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹),
    ENNReal.toReal_sum (fun σ _ => measure_ne_top _ _)]

/-- [Integrals of an integrable observable are finite prior averages.](goal) Under [the stated assumptions](hyp:f). Under [the stated assumptions](hyp:hf). -/
-- @node: signPriorExperiment_integral
lemma signPriorExperiment_integral (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (f : Experiment n → ℝ)
    (hf : ∀ σ, Integrable f (experimentLaw (laws σ) n)) :
    (∫ ω, f ω ∂signPriorExperiment n k laws) =
      (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∫ ω, f ω ∂experimentLaw (laws σ) n := by
  rw [signPriorExperiment, integral_smul_measure,
    integral_finsetSum_measure (fun σ _ => hf σ)]
  simp only [ENNReal.toReal_ofReal (by positivity :
    0 ≤ (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹), smul_eq_mul]

/-- [Bounded measurable procedure length is integrable under the finite prior. [the stated conclusion](goal) holds. -/
-- @node: signPriorExperiment_length_integrable
lemma signPriorExperiment_length_integrable (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (I : Procedure n) :
    Integrable (fun ω => intervalLength (I.output ω)) (signPriorExperiment n k laws) := by
  apply Integrable.of_bound I.length_measurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalLength_nonneg _)]
    exact intervalLength_le_one _)

/-- If all prior draws lie in the evaluation slice, its average length is
bounded by the worst expected length on that slice. [the documented result](goal) Under [the stated assumptions](hyp:hP). -/
-- @node: signPriorExperiment_length_le_worst
lemma signPriorExperiment_length_le_worst (n k : ℕ) (α β r : ℝ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (I : Procedure n)
    (hP : ∀ σ, RadiusModel α β r (laws σ)) :
    (∫ ω, intervalLength (I.output ω) ∂signPriorExperiment n k laws) ≤
      worstLength n α β r I := by
  rw [signPriorExperiment_integral n k laws _
    (fun σ => procedure_length_integrable (laws σ) n I)]
  have h := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) =>
    expectedLength_le_worstLength (laws σ) n α β r I (hP σ))
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Global honesty transfers to a prior with a single common scalar effect. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hI,hP,hθ) hold, and [the stated conclusion follows](goal). -/
-- @node: signPriorExperiment_coverage
lemma signPriorExperiment_coverage (n k : ℕ) (α β t : ℝ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (I : Procedure n)
    (hI : HonestProcedure n α β I) (hP : ∀ σ, Model α β (laws σ))
    (hθ : ∀ σ, effect (laws σ) = t) :
    (9/10 : ℝ) ≤ (signPriorExperiment n k laws).real
      {ω | t ∈ intervalSet (I.output ω)} := by
  rw [signPriorExperiment_real n k laws _ (I.coverage_measurable t)]
  have hcover (σ : Fin (k+1) → Bool) :
      (9/10 : ℝ) ≤ (experimentLaw (laws σ) n).real
        {ω | t ∈ intervalSet (I.output ω)} := by
    letI := experimentLaw_probability (laws σ) n
    have h := hI.coverage (laws σ) (hP σ)
    rw [hθ σ] at h
    have := ENNReal.toReal_mono (measure_ne_top _ _) h
    norm_num [measureReal_def] at this ⊢
    exact this
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hcover σ))
    (by positivity : 0 ≤ (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (by positivity :
      (Fintype.card (Fin (k+1) → Bool) : ℝ) ≠ 0), one_mul] using h

/-- [Two common-effect finite priors give the roadmap's length bound. The
second prior needs ambient membership; only the first needs slice membership. [the documented result](goal) Under [the stated assumptions](hyp:hI,hP₀,hP₁,hθ₀,hθ₁,htv). -/
-- @node: finitePrior_testing_length_lower
lemma finitePrior_testing_length_lower (n k₀ k₁ : ℕ) (α β r a b tv : ℝ)
    (laws₀ : (Fin (k₀+1) → Bool) → ObservedLaw)
    (laws₁ : (Fin (k₁+1) → Bool) → ObservedLaw)
    (I : Procedure n) (hI : HonestProcedure n α β I)
    (hP₀ : ∀ σ, RadiusModel α β r (laws₀ σ))
    (hP₁ : ∀ σ, Model α β (laws₁ σ))
    (hθ₀ : ∀ σ, effect (laws₀ σ) = a)
    (hθ₁ : ∀ σ, effect (laws₁ σ) = b)
    (htv : Causalean.Stat.tvDist (signPriorExperiment n k₀ laws₀)
      (signPriorExperiment n k₁ laws₁) ≤ tv) :
    |b-a| *(4/5-tv) ≤ worstLength n α β r I := by
  classical
  let μ := signPriorExperiment n k₀ laws₀
  let ν := signPriorExperiment n k₁ laws₁
  let A := {ω | a ∈ intervalSet (I.output ω)}
  let B := {ω | b ∈ intervalSet (I.output ω)}
  have hA : MeasurableSet A := I.coverage_measurable a
  have hB : MeasurableSet B := I.coverage_measurable b
  have hcover₀ := signPriorExperiment_coverage n k₀ α β a laws₀ I hI
    (fun σ => (hP₀ σ).toModel) hθ₀
  have hcover₁ := signPriorExperiment_coverage n k₁ α β b laws₁ I hI hP₁ hθ₁
  have htransfer := Causalean.Stat.measureReal_sub_le_tvDist (μ := μ) (ν := ν) hB
  have hunion := measureReal_union_add_inter' (μ := μ) (t := B) hA
  have hmass : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  have hboth : 4/5-tv ≤ μ.real (A ∩ B) := by
    change (9/10 : ℝ) ≤ μ.real A at hcover₀
    change (9/10 : ℝ) ≤ ν.real B at hcover₁
    change Causalean.Stat.tvDist μ ν ≤ tv at htv
    linarith
  have hint : Integrable ((A ∩ B).indicator (fun _ => |b-a|)) μ :=
    (integrable_const |b-a|).indicator (hA.inter hB)
  calc
    _ ≤ |b-a| *μ.real (A ∩ B) :=
      mul_le_mul_of_nonneg_left hboth (abs_nonneg _)
    _ = ∫ ω, (A ∩ B).indicator (fun _ => |b-a|) ω ∂μ := by
      rw [integral_indicator (hA.inter hB), setIntegral_const]
      simp [measureReal_def, mul_comm]
    _ ≤ ∫ ω, intervalLength (I.output ω) ∂μ := by
      apply integral_mono hint (signPriorExperiment_length_integrable n k₀ laws₀ I)
      intro ω
      by_cases hω : ω ∈ A ∩ B
      · rw [Set.indicator_of_mem hω]
        apply abs_le.mpr
        constructor
        · have h := intervalLength_ge_separation _ _ _ hω.2 hω.1
          linarith
        · exact intervalLength_ge_separation _ _ _ hω.1 hω.2
      · rw [Set.indicator_of_notMem hω]
        exact intervalLength_nonneg _
    _ ≤ _ := signPriorExperiment_length_le_worst n k₀ α β r laws₀ I hP₀

end CausalSmith.Stat.LogoddsLowsmoothFrontier
