import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.ExactVariance

/-!
# Exact PAME variance and CR2 expectation
-/

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.TwoStageInterference

-- @node: thm:exact-pame-variance
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hMtwo,hG1two,hG0two,Y), [the stated variance result holds](goal). -/
theorem exact_pame_variance (n M G G1 : ℕ) (hMG : M * G ≤ n)
    (hMtwo : 2 ≤ M) (hG1two : 2 ≤ G1) (hG0two : 2 ≤ G - G1)
    (Y : PotentialOutcome n M) :
    let hG1pos : 0 < G1 := by omega
    let hG1lt : G1 < G := by omega
    let hG1le : G1 ≤ G := Nat.le_of_lt hG1lt
    let hM : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
    (randomPartitionDesign n M G G1 hMG hG1le).E (pameHat Y hG1pos hG1lt) = pame n M hM Y ∧
    sigmaSq Y hMG hG1pos hG1lt =
      indepGroupVar n M G G1 hM hG1pos hG1lt Y / (G : ℝ) +
        crossCovContrast n M hM Y -
        crossCov n M hM Y true true / (G1 : ℝ) -
        crossCov n M hM Y false false / ((G - G1 : ℕ) : ℝ) ∧
    (randomPartitionDesign n M G G1 hMG hG1le).E (cr2Var Y hG1two hG0two) =
      (armVar n M hM Y true - crossCov n M hM Y true true) / (G1 : ℝ) +
      (armVar n M hM Y false - crossCov n M hM Y false false) /
        ((G - G1 : ℕ) : ℝ) ∧
    (randomPartitionDesign n M G G1 hMG hG1le).E (cr2Var Y hG1two hG0two) -
      sigmaSq Y hMG hG1pos hG1lt =
      -crossCovContrast n M hM Y := by
  dsimp only
  let hG1pos : 0 < G1 := by omega
  let hG1lt : G1 < G := by omega
  let hG1le : G1 ≤ G := hG1lt.le
  let hG : 2 ≤ G := by omega
  let hM : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
  let h2M : 2 * M ≤ n := by
    exact le_trans (by nlinarith : 2 * M ≤ M * G) hMG
  let Dp := uniformPartitionTuple n M G hMG
  let Dt := completeRandomization (V := Fin G) G1 (by simpa using hG1le)
  let f1 := armTable n M Y true
  let f0 := armTable n M Y false
  let ft : Omega n M → ℝ := fun A => f1 A - f0 A
  have hcrossT : sliceInner n M hM
        (fun A => ft A - (slice n M hM).E ft)
        (kneserOp n M (fun A => ft A - (slice n M hM).E ft)) =
      crossCovContrast n M hM Y := by
    rw [show ft = fun A => f1 A - f0 A by rfl,
      disjointCov_sub_self n M h2M hM f1 f0]
    rfl
  have hES1 : Dp.E (fun T => S1 (fun g => f1 (T.1 g))) =
      armVar n M hM Y true - crossCov n M hM Y true true := by
    let hMc : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
    have hs := partition_expected_sample_variance n M G G1 hMG hG hG1le f1
    change Dp.E (fun T => S1 (fun g => f1 (T.1 g))) =
      (slice n M hMc).Var f1 - sliceInner n M hMc
        (fun A => f1 A - (slice n M hMc).E f1)
        (kneserOp n M (fun A => f1 A - (slice n M hMc).E f1)) at hs
    have hh : hMc = hM := Subsingleton.elim _ _
    subst hMc
    change Dp.E (fun T => S1 (fun g => f1 (T.1 g))) =
      (slice n M hM).Var f1 - sliceInner n M hM
        (fun A => f1 A - (slice n M hM).E f1)
        (kneserOp n M (fun A => f1 A - (slice n M hM).E f1))
    exact hs
  have hES0 : Dp.E (fun T => S0 (fun g => f0 (T.1 g))) =
      armVar n M hM Y false - crossCov n M hM Y false false := by
    change Dp.E (fun T => S1 (fun g => f0 (T.1 g))) = _
    let hMc : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
    have hs := partition_expected_sample_variance n M G G1 hMG hG hG1le f0
    change Dp.E (fun T => S1 (fun g => f0 (T.1 g))) =
      (slice n M hMc).Var f0 - sliceInner n M hMc
        (fun A => f0 A - (slice n M hMc).E f0)
        (kneserOp n M (fun A => f0 A - (slice n M hMc).E f0)) at hs
    have hh : hMc = hM := Subsingleton.elim _ _
    subst hMc
    change Dp.E (fun T => S1 (fun g => f0 (T.1 g))) =
      (slice n M hM).Var f0 - sliceInner n M hM
        (fun A => f0 A - (slice n M hM).E f0)
        (kneserOp n M (fun A => f0 A - (slice n M hM).E f0))
    exact hs
  have hESt : Dp.E (fun T => Stau (fun g => f1 (T.1 g))
      (fun g => f0 (T.1 g))) = (slice n M hM).Var ft - crossCovContrast n M hM Y := by
    simp_rw [Stau_eq_S1_sub]
    rw [show (fun T : PartitionTuple n M G => S1 (fun g => f1 (T.1 g) - f0 (T.1 g))) =
      (fun T => S1 (fun g => ft (T.1 g))) by rfl]
    rw [partition_expected_sample_variance n M G G1 hMG hG hG1le ft, hcrossT]
  have hVarMean : Dp.Var (fun T => (∑ g, ft (T.1 g)) / (G : ℝ)) =
      ((slice n M hM).Var ft + ((G : ℝ) - 1) * crossCovContrast n M hM Y) /
        (G : ℝ) := by
    rw [partition_mean_variance n M G G1 hMG hG hG1le ft, hcrossT]
  have hEmean : Dp.E (fun T => (∑ g, ft (T.1 g)) / (G : ℝ)) =
      (slice n M hM).E ft := partition_E_mean n M G G1 hMG (by omega) hG1le ft
  have hUnbiased : (randomPartitionDesign n M G G1 hMG hG1le).E
      (pameHat Y hG1pos hG1lt) = pame n M hM Y := by
    rw [randomPartitionDesign_eq_compoundCore n M G G1 hMG hG1le,
      finiteDesign_E_compoundCore_tower]
    simp_rw [conditional_E_pameHat Y hG1pos hG1lt]
    rw [hEmean]
    simp [ft, f1, f0, pame, FiniteDesign.E_sub]
  have hVar : sigmaSq Y hMG hG1pos hG1lt =
      (armVar n M hM Y true - crossCov n M hM Y true true) / (G1 : ℝ) +
      (armVar n M hM Y false - crossCov n M hM Y false false) /
        ((G - G1 : ℕ) : ℝ) + crossCovContrast n M hM Y := by
    rw [sigmaSq, randomPartitionDesign_eq_compoundCore n M G G1 hMG hG1le,
      finiteDesign_Var_compoundCore_tower]
    simp_rw [conditional_Var_pameHat Y hG1pos hG1lt]
    have hcondForm : (fun T : PartitionTuple n M G =>
        S1 (fun g => f1 (T.1 g)) / (G1 : ℝ) +
        S0 (fun g => f0 (T.1 g)) / ((G : ℝ) - G1) -
        Stau (fun g => f1 (T.1 g)) (fun g => f0 (T.1 g)) / (G : ℝ)) =
      (fun T => (G1 : ℝ)⁻¹ * S1 (fun g => f1 (T.1 g)) +
        ((G : ℝ) - G1)⁻¹ * S0 (fun g => f0 (T.1 g)) -
        (G : ℝ)⁻¹ * Stau (fun g => f1 (T.1 g)) (fun g => f0 (T.1 g))) := by
      funext T
      ring
    rw [hcondForm]
    rw [FiniteDesign.E_sub, FiniteDesign.E_add, FiniteDesign.E_const_mul,
      FiniteDesign.E_const_mul, FiniteDesign.E_const_mul, hES1, hES0, hESt]
    rw [show Dp.Var (fun T => Dt.E (fun S => pameHat Y hG1pos hG1lt (T, S))) =
      Dp.Var (fun T => (∑ g, ft (T.1 g)) / (G : ℝ)) by
        apply Dp.Var_congr
        intro T
        exact conditional_E_pameHat Y hG1pos hG1lt T]
    rw [hVarMean, Nat.cast_sub hG1le]
    have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast (by omega : G ≠ 0)
    ring_nf
    field_simp
    ring
  have hCR2 : (randomPartitionDesign n M G G1 hMG hG1le).E
      (cr2Var Y hG1two hG0two) =
      (armVar n M hM Y true - crossCov n M hM Y true true) / (G1 : ℝ) +
      (armVar n M hM Y false - crossCov n M hM Y false false) /
        ((G - G1 : ℕ) : ℝ) := by
    rw [randomPartitionDesign_eq_compoundCore n M G G1 hMG hG1le,
      finiteDesign_E_compoundCore_tower]
    simp_rw [conditional_E_cr2Var Y hG1two hG0two]
    have hcrForm : (fun T : PartitionTuple n M G =>
      S1 (fun g => f1 (T.1 g)) / (G1 : ℝ) +
      S0 (fun g => f0 (T.1 g)) / ((G - G1 : ℕ) : ℝ)) =
      (fun T => (G1 : ℝ)⁻¹ * S1 (fun g => f1 (T.1 g)) +
      ((G - G1 : ℕ) : ℝ)⁻¹ * S0 (fun g => f0 (T.1 g))) := by
      funext T
      ring
    rw [hcrForm]
    rw [FiniteDesign.E_add, FiniteDesign.E_const_mul,
      FiniteDesign.E_const_mul, hES1, hES0]
    ring
  refine ⟨hUnbiased, ?_, hCR2, ?_⟩
  · rw [hVar]
    unfold indepGroupVar pFrac
    rw [Nat.cast_sub hG1le]
    have hG1r : (G1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : G1 ≠ 0)
    have hG0r : (G : ℝ) - G1 ≠ 0 := by
      have : (G1 : ℝ) < G := by exact_mod_cast hG1lt
      linarith
    have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast (by omega : G ≠ 0)
    field_simp
    ring
  · rw [hCR2, hVar]
    ring

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
