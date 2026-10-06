module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.FullBias
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.HeavyCorrection

/-! Full correction second-moment budget and weighted selected-cell variance
comparison for roadmap (21)--(24). Cross-cell independence is left to the
signed raw-estimator assembly. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_integral_sq_memberWeight_mul_selectedCorrection_le
lemma sum_integral_sq_memberWeight_mul_selectedCorrection_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q) :
    8 * (∑ j : Cell d, ∫ s, (poissonMemberWeight n j s *
      (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      64 * d * (Real.exp (logScale n q / 8) + 1) *
        (needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
          needleRadius n q / (streamSize n * streamEffectiveSize n q)) +
      32 * Real.exp (-32 * logScale n q) * (1 + 1 / streamSize n) := by
  classical
  let f : Cell d → ℝ := fun j ↦ ∫ s, (poissonMemberWeight n j s *
    (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)
  have hsplit : (∑ j : Cell d, f j) =
      (∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ streamSize n * arrivedCell P j ≤ needleRadius n q), f j) +
      (∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ needleRadius n q < streamSize n * arrivedCell P j), f j) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : streamSize n * arrivedCell P j ≤ needleRadius n q
    · simp [hj, not_lt.mpr hj]
    · simp [hj, lt_of_not_ge hj]
  change 8 * (∑ j : Cell d, f j) ≤ _
  rw [hsplit, mul_add]
  exact add_le_add
    (sum_light_integral_sq_poissonMemberWeight_mul_selectedCorrection_le n d q P hP hb)
    (sum_heavy_integral_sq_memberWeight_mul_selectedCorrection_le n d q P
      (lt_of_lt_of_le Nat.zero_lt_one hP.n_pos) hb)

/-- Given [the specified inputs and assumptions](hyp:Ω,μ,X,Y,hX,hY), [the stated mathematical conclusion holds](goal). -/
-- @node: selected_variance_add_le_twice
lemma selected_variance_add_le_twice {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun s ↦ X s + Y s) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  have hsub := variance_nonneg (X := X - Y) (μ := μ)
  rw [variance_sub hX hY] at hsub
  rw [variance_fun_add hX hY]
  linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: variance_memberWeight_mul_selectedCellEstimate_le
lemma variance_memberWeight_mul_selectedCellEstimate_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    variance (fun s ↦ poissonMemberWeight n j s *
      poissonSelectedCellEstimate n d q j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
    2 * variance (fun s ↦ poissonMemberWeight n j s * poissonRatioBranch j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) +
    2 * (∫ s, (poissonMemberWeight n j s *
      (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hD := memLp_poissonMemberWeight_mul_ratioBranch n d P j
  have hC := memLp_poissonMemberWeight_mul_selectedCorrection n d q P j
  have heq : (fun s ↦ poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s) =
      (fun s ↦ poissonMemberWeight n j s * poissonRatioBranch j s +
        poissonMemberWeight n j s *
          (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) := by
    funext s
    ring
  rw [heq]
  exact (selected_variance_add_le_twice _ hD hC).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (variance_le_expectation_sq hC.aestronglyMeasurable) (by norm_num : (0 : ℝ) ≤ 2)))

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: four_sum_variance_memberWeight_mul_selectedCellEstimate_le
lemma four_sum_variance_memberWeight_mul_selectedCellEstimate_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q) :
    4 * (∑ j : Cell d, variance (fun s ↦ poissonMemberWeight n j s *
      poissonSelectedCellEstimate n d q j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))) ≤
    8 * (4 / streamEffectiveSize n q + 1 / streamSize n) +
      64 * d * (Real.exp (logScale n q / 8) + 1) *
        (needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
          needleRadius n q / (streamSize n * streamEffectiveSize n q)) +
      32 * Real.exp (-32 * logScale n q) * (1 + 1 / streamSize n) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Cell d)))
    (fun j _ ↦ variance_memberWeight_mul_selectedCellEstimate_le n d q P j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
  have hratio := sum_variance_poissonMemberWeight_mul_ratioBranch_le n d q P hP
  have hcorr := sum_integral_sq_memberWeight_mul_selectedCorrection_le n d q P hP hb
  linarith

end CausalSmith.Stat.MarRareqLogfrontier
