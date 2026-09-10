import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Witness
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TExactPameVariance
import Causalean.Experimentation.FinitePopulationMoments
import Mathlib.Tactic.FinCases

/-!
# Exact moments of the eight-unit witness
-/

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation

-- @node: witness8_armTable_eq_sampleMean
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:A), [the stated equality holds](goal). -/
lemma witness8_armTable_eq_sampleMean (A : Omega 8 2) :
    armTable 8 2 witness8 true A = FinitePopulationMoments.sampleMean 2 a8 A := by
  unfold armTable witness8 witness8Bundle
  rw [Finset.sum_const, Finset.card_attach, A.2]
  simp [FinitePopulationMoments.sampleMean]

-- @node: witness8_sampleMean_eq_signSum
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:A), [the stated equality holds](goal). -/
lemma witness8_sampleMean_eq_signSum (A : Omega 8 2) :
    FinitePopulationMoments.sampleMean 2 a8 A =
      (∑ i ∈ A.1, if i.1 < 4 then (1 : ℝ) else -1) / 2 := by
  unfold FinitePopulationMoments.sampleMean a8
  rw [Finset.sum_ite]
  simp

-- @node: witness8_armTable_mean
/-- [the witness8 arm table mean result holds](goal). -/
lemma witness8_armTable_mean :
    (slice 8 2 (by omega)).E (armTable 8 2 witness8 true) = 0 := by
  rw [show armTable 8 2 witness8 true =
    FinitePopulationMoments.sampleMean 2 a8 by
      funext A
      exact witness8_armTable_eq_sampleMean A]
  unfold slice
  rw [FinitePopulationMoments.E_sampleMean 2 (by norm_num) (by norm_num) a8]
  norm_num [FinitePopulationMoments.popMean, a8, Fin.sum_univ_succ]

-- @node: witness8_armVar_treated
/-- [the stated variance result holds](goal). -/
lemma witness8_armVar_treated :
    armVar 8 2 (by omega) witness8 true = (3 : ℝ) / 7 := by
  rw [armVar, show armTable 8 2 witness8 true =
    FinitePopulationMoments.sampleMean 2 a8 by
      funext A
      exact witness8_armTable_eq_sampleMean A]
  unfold slice
  rw [FinitePopulationMoments.Var_sampleMean 2 (by norm_num) (by norm_num)
    (by norm_num) a8]
  norm_num [FinitePopulationMoments.popVar, FinitePopulationMoments.popMean, a8,
    Fin.sum_univ_succ]

-- @node: witness8_armTable_control
/-- [the witness8 arm table control result holds](goal). -/
lemma witness8_armTable_control : armTable 8 2 witness8 false = 0 := by
  funext A
  simp [armTable, witness8, witness8Bundle]

-- @node: witness8_armVar_control
/-- [the stated variance result holds](goal). -/
lemma witness8_armVar_control : armVar 8 2 (by omega) witness8 false = 0 := by
  unfold armVar
  rw [witness8_armTable_control, FiniteDesign.Var_eq]
  have hz : (slice 8 2 (by omega)).E (0 : Omega 8 2 → ℝ) = 0 := by
    change (slice 8 2 (by omega)).E (fun _ => 0) = 0
    apply FiniteDesign.E_const
  rw [hz]
  simp

-- @node: witness8_crossCov_control_right
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:a), [the witness8 cross cov control right result holds](goal). -/
lemma witness8_crossCov_control_right (a : Arm) :
    crossCov 8 2 (by omega) witness8 a false = 0 := by
  unfold crossCov armTableCentered
  rw [witness8_armTable_control]
  have hz : (slice 8 2 (by omega)).E (0 : Omega 8 2 → ℝ) = 0 := by
    change (slice 8 2 (by omega)).E (fun _ => 0) = 0
    apply FiniteDesign.E_const
  rw [hz]
  simp [sliceInner, kneserOp, kneserAdjacency]

-- @node: witness8_crossCov_control_left
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:b), [the witness8 cross cov control left result holds](goal). -/
lemma witness8_crossCov_control_left (b : Arm) :
    crossCov 8 2 (by omega) witness8 false b = 0 := by
  unfold crossCov armTableCentered
  rw [witness8_armTable_control]
  have hz : (slice 8 2 (by omega)).E (0 : Omega 8 2 → ℝ) = 0 := by
    change (slice 8 2 (by omega)).E (fun _ => 0) = 0
    apply FiniteDesign.E_const
  rw [hz]
  simp [sliceInner, kneserOp, kneserAdjacency]

-- @node: witness8_orderedDisjoint_signSum
/-- [the witness8 ordered disjoint sign sum result holds](goal). -/
lemma witness8_orderedDisjoint_signSum :
    (∑ P : OrderedDisjointPair 8 2,
      (∑ i ∈ P.1.1.1, if i.1 < 4 then (1 : ℤ) else -1) *
      (∑ i ∈ P.1.2.1, if i.1 < 4 then (1 : ℤ) else -1)) = -240 := by
  decide +kernel

-- @node: witness8_orderedDisjoint_signSum_real
/-- [the witness8 ordered disjoint sign sum real result holds](goal). -/
lemma witness8_orderedDisjoint_signSum_real :
    (∑ P : OrderedDisjointPair 8 2,
      (∑ i ∈ P.1.1.1, if i.1 < 4 then (1 : ℝ) else -1) *
      (∑ i ∈ P.1.2.1, if i.1 < 4 then (1 : ℝ) else -1)) = -240 := by
  exact_mod_cast witness8_orderedDisjoint_signSum

-- @node: witness8_crossCov_treated
/-- [the witness8 cross cov treated result holds](goal). -/
lemma witness8_crossCov_treated :
    crossCov 8 2 (by omega) witness8 true true = -(1 : ℝ) / 7 := by
  unfold crossCov
  rw [← orderedDisjointPair_E_eq 8 2 (by omega)]
  simp only [armTableCentered, witness8_armTable_mean, sub_zero]
  simp_rw [witness8_armTable_eq_sampleMean]
  change (∑ P : OrderedDisjointPair 8 2,
    (1 / (Fintype.card (OrderedDisjointPair 8 2) : ℝ)) *
      (FinitePopulationMoments.sampleMean 2 a8 P.1.1 *
       FinitePopulationMoments.sampleMean 2 a8 P.1.2)) = -(1 : ℝ) / 7
  rw [orderedDisjointPair_card 8 2 (by omega)]
  norm_num only [Nat.choose]
  simp_rw [witness8_sampleMean_eq_signSum]
  calc
    (∑ P : OrderedDisjointPair 8 2,
      (1 / (420 : ℝ)) *
       ((∑ i ∈ P.1.1.1, if i.1 < 4 then (1 : ℝ) else -1) / 2 *
        ((∑ i ∈ P.1.2.1, if i.1 < 4 then (1 : ℝ) else -1) / 2))) =
      (1 / 1680 : ℝ) * ∑ P : OrderedDisjointPair 8 2,
       (∑ i ∈ P.1.1.1, if i.1 < 4 then (1 : ℝ) else -1) *
       (∑ i ∈ P.1.2.1, if i.1 < 4 then (1 : ℝ) else -1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P _
        ring
    _ = -(1 / 7 : ℝ) := by
      rw [witness8_orderedDisjoint_signSum_real]
      norm_num

-- @node: sum_positive_fin_three
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:F), [the stated nonnegativity result holds](goal). -/
lemma sum_positive_fin_three (F : Fin 3 → ℝ) :
    (∑ k ∈ (Finset.univ.filter fun k : Fin 3 => 0 < k.1), F k) = F 1 + F 2 := by
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ]

-- @node: witness8_degreeOne_from_spectrum
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:J,hJohnson,f,hfmean,hvar,hcov), [the witness8 degree one from spectrum result holds](goal). -/
lemma witness8_degreeOne_from_spectrum (J : JohnsonProjections 8 2)
    (hJohnson : JohnsonOrthogonalDecomposition 8 2 J)
    (f : Omega 8 2 → ℝ) (hfmean : (slice 8 2 (by omega)).E f = 0)
    (hvar : (slice 8 2 (by omega)).Var f = (3 : ℝ) / 7)
    (hcov : (∑ k ∈ (Finset.univ.filter fun k : Fin 3 => 0 < k.1),
      kneserEigenvalue 8 2 k * sliceNorm 8 2 (by omega) (J.proj k f) ^ 2) =
        -(1 : ℝ) / 7) :
    sliceNorm 8 2 (by omega) (J.proj (1 : Fin 3) f) ^ 2 = (3 : ℝ) / 7 := by
  let p1 := J.proj (1 : Fin 3) f
  let p2 := J.proj (2 : Fin 3) f
  have hs : (Finset.univ.filter fun k : Fin 3 => 0 < k.1) = {1, 2} := by decide
  have hf (A : Omega 8 2) : p1 A + p2 A = f A := by
    have h := (hJohnson (by omega)).1 f A
    rw [hs] at h
    simpa [hfmean, p1, p2, add_comm] using h
  have horth : sliceInner 8 2 (by omega) p1 p2 = 0 :=
    (hJohnson (by omega)).2 (1 : Fin 3) (2 : Fin 3) f f (by decide)
  have hsum : sliceNorm 8 2 (by omega) p1 ^ 2 +
      sliceNorm 8 2 (by omega) p2 ^ 2 = (3 : ℝ) / 7 := by
    have hvinner : sliceInner 8 2 (by omega) f f = (3 : ℝ) / 7 := by
      rw [FiniteDesign.Var_eq] at hvar
      simpa [sliceInner, pow_two, hfmean] using hvar
    have hsq (g : Omega 8 2 → ℝ) :
        sliceNorm 8 2 (by omega) g ^ 2 = sliceInner 8 2 (by omega) g g := by
      unfold sliceNorm sliceNormSq
      exact Real.sq_sqrt (sliceInner_self_nonneg (by omega) g)
    rw [hsq, hsq, ← hvinner]
    unfold sliceInner
    rw [show (fun A => f A * f A) =
      (fun A => p1 A * p1 A + p2 A * p2 A + 2 * (p1 A * p2 A)) by
        funext A
        rw [← hf A]
        ring]
    rw [(slice 8 2 (by omega)).E_add, (slice 8 2 (by omega)).E_add,
      (slice 8 2 (by omega)).E_const_mul]
    change _ = _ + _ + 2 * sliceInner 8 2 (by omega) p1 p2
    rw [horth]
    ring
  have hcov' : -(1 : ℝ) / 3 * sliceNorm 8 2 (by omega) p1 ^ 2 +
      (1 : ℝ) / 15 * sliceNorm 8 2 (by omega) p2 ^ 2 = -(1 : ℝ) / 7 := by
    rw [sum_positive_fin_three] at hcov
    norm_num [p1, p2, kneserEigenvalue, Nat.descFactorial] at hcov ⊢
    exact hcov
  change sliceNorm 8 2 (by omega) p1 ^ 2 = _
  linarith

-- @node: prop:eight-unit-witness
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:J,hJohnsonOrthogonalDecomposition_of_gate,hKneserAdjacencySpectrum_of_gate), [the eight unit witness moments result holds](goal). -/
theorem eight_unit_witness_moments (J : JohnsonProjections 8 2)
    (hJohnsonOrthogonalDecomposition_of_gate : JohnsonOrthogonalDecomposition 8 2 J)
    (hKneserAdjacencySpectrum_of_gate : KneserAdjacencySpectrum 8 2) :
    armVar 8 2 (by omega) witness8 true = (3 : ℝ) / 7 ∧
    degreeOneEnergy 8 2 (by omega) (by omega) J witness8 = (3 : ℝ) / 7 ∧
    crossCov 8 2 (by omega) witness8 true true = -(1 : ℝ) / 7 ∧
    sigmaSq witness8 (by omega : 2 * 4 ≤ 8) (by omega : 0 < 2) (by omega : 2 < 4) =
      (1 : ℝ) / 7 ∧
    (randomPartitionDesign 8 2 4 2 (by omega) (by omega)).E
      (cr2Var witness8 (by omega) (by omega)) =
      (2 : ℝ) / 7 := by
  have hspectral :=
    (exact_kneser_identity 8 2 (by omega) (by omega) J witness8
      hJohnsonOrthogonalDecomposition_of_gate hKneserAdjacencySpectrum_of_gate).2.2
  have hcontrast : crossCovContrast 8 2 (by omega) witness8 = -(1 : ℝ) / 7 := by
    rw [crossCovContrast, witness8_crossCov_treated,
      witness8_crossCov_control_left, witness8_crossCov_control_right]
    ring
  rw [hcontrast] at hspectral
  let f : Omega 8 2 → ℝ := fun A =>
    armTable 8 2 witness8 true A - armTable 8 2 witness8 false A
  have hf : f = armTable 8 2 witness8 true := by
    funext A
    simp [f, witness8_armTable_control]
  have hfmean : (slice 8 2 (by omega)).E f = 0 := by
    rw [hf, witness8_armTable_mean]
  have hfvar : (slice 8 2 (by omega)).Var f = (3 : ℝ) / 7 := by
    rw [hf]
    exact witness8_armVar_treated
  have hdegree : degreeOneEnergy 8 2 (by omega) (by omega) J witness8 =
      (3 : ℝ) / 7 := by
    unfold degreeOneEnergy
    exact witness8_degreeOne_from_spectrum J hJohnsonOrthogonalDecomposition_of_gate
      f hfmean hfvar (by simpa [f] using hspectral.symm)
  have hexact := exact_pame_variance 8 2 4 2 (by omega) (by omega) (by omega)
    (by omega) witness8
  dsimp only at hexact
  refine ⟨witness8_armVar_treated, hdegree, witness8_crossCov_treated, ?_, ?_⟩
  · rw [hexact.2.1]
    unfold indepGroupVar
    rw [witness8_armVar_treated, witness8_crossCov_treated,
      witness8_armVar_control, witness8_crossCov_control_left, hcontrast]
    norm_num [indepGroupVar, pFrac, crossCovContrast]
  · rw [hexact.2.2.1, witness8_armVar_treated, witness8_crossCov_treated,
      witness8_armVar_control, witness8_crossCov_control_left]
    norm_num

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
