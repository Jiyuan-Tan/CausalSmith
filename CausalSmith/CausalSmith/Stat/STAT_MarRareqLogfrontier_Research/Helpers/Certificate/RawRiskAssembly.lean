module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.FullVarianceBudget
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RiskGeometry

/-! Square integrability, bias--variance decomposition, and clipping assemble
ideal squared risk from the actual raw-estimator variance and the proved bias
budget. Cross-cell independence is still needed to bound that variance. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonRawMixedValue
lemma memLp_poissonRawMixedValue (n d : ℕ) (q : ℝ) (P : FullLaw d) :
    MemLp (poissonRawMixedValue n d q) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hj (j : Cell d) :=
    (memLp_poissonMemberWeight_mul_selectedCellEstimate n d q P j).const_mul
      (armSign j.1)
  have hs := memLp_finsetSum (Finset.univ : Finset (Cell d)) (fun j _ ↦ hj j)
  change MemLp (fun s ↦ 2 * ∑ j : Cell d, armSign j.1 *
    poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s) 2 _
  simpa only [mul_assoc] using hs.const_mul (2 : ℝ)

/-- Given [the specified inputs and assumptions](hyp:Ω,μ,X,hX,θ), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_error_eq_variance_add_bias_sq
lemma integral_sq_error_eq_variance_add_bias_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (θ : ℝ) :
    (∫ s, (X s - θ) ^ 2 ∂μ) = variance X μ + ((∫ s, X s ∂μ) - θ) ^ 2 := by
  have hsub : MemLp (fun s ↦ X s - θ) 2 μ := hX.sub (memLp_const θ)
  have hv := variance_eq_sub hsub
  rw [variance_sub_const hX.aestronglyMeasurable θ] at hv
  have hm : (∫ s, X s - θ ∂μ) = (∫ s, X s ∂μ) - θ := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const θ)]
    simp
  simp only [Pi.pow_apply] at hv
  rw [hm] at hv
  linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,θ,P), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonRawMixedValue_error_eq
lemma integral_sq_poissonRawMixedValue_error_eq (n d : ℕ) (q θ : ℝ) (P : FullLaw d) :
    (∫ s, (poissonRawMixedValue n d q s - θ) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
    variance (poissonRawMixedValue n d q)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) +
    ((∫ s, poissonRawMixedValue n d q s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - θ) ^ 2 := by
  exact integral_sq_error_eq_variance_add_bias_sq _ (memLp_poissonRawMixedValue n d q P) θ

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonAuxiliaryMixedValue_le_raw
lemma integral_sq_poissonAuxiliaryMixedValue_le_raw (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hlarge : ¬ effectiveSize n q ≤ 1) :
    (∫ s, (poissonAuxiliaryMixedValue n d q s - cellFunctional P) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
    ∫ s, (poissonRawMixedValue n d q s - cellFunctional P) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2) := by
  have haux : MemLp (poissonAuxiliaryMixedValue n d q) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
    apply memLp_of_bounded (a := -1) (b := 1) _
      (measurable_poissonAuxiliaryMixedValue n d q).aestronglyMeasurable
    filter_upwards [] with s
    exact poissonAuxiliaryMixedValue_mem_Icc n d q s
  apply integral_mono
    (haux.sub (memLp_const (cellFunctional P))).integrable_sq
    ((memLp_poissonRawMixedValue n d q P).sub
      (memLp_const (cellFunctional P))).integrable_sq
  intro s
  change (poissonAuxiliaryMixedValue n d q s - cellFunctional P) ^ 2 ≤
    (poissonRawMixedValue n d q s - cellFunctional P) ^ 2
  simp only [poissonAuxiliaryMixedValue, if_neg hlarge]
  exact clip_sq_sub_le _ _ (cellFunctional_mem_Icc P hP)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonAuxiliaryMixedValue_le_variance_add_active_bias_sq
lemma integral_sq_poissonAuxiliaryMixedValue_le_variance_add_active_bias_sq
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q)
    (hlarge : ¬ effectiveSize n q ≤ 1) :
    (∫ s, (poissonAuxiliaryMixedValue n d q s - cellFunctional P) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
    variance (poissonRawMixedValue n d q)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) +
    (2 * (4 * d * needleRadius n q /
      (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) +
      3 * Real.exp (-16 * logScale n q))) ^ 2 := by
  have h := abs_integral_raw_poissonSelected_estimator_bias_le n d q P hP hb
  change |(∫ s, poissonRawMixedValue n d q s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellFunctional P| ≤ _ at h
  refine (integral_sq_poissonAuxiliaryMixedValue_le_raw n d q P hP hlarge).trans ?_
  rw [integral_sq_poissonRawMixedValue_error_eq]
  apply add_le_add_right
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← sq, sq_abs] using hs

end CausalSmith.Stat.MarRareqLogfrontier
