import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionWitness
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.DeterminantEnvelope

/-!
# Pointwise quantitative contraction bridges

This module converts the paper's scale, equilibrium, and normalization assumptions into the
inputs of pairwise-affine local stability.  The separate compact-exclusion module is responsible
only for placing candidates in the required local chart.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator ENNReal

open Causalean.Discovery.LinearDisentanglement.Quantitative
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

/-- The paper's scale envelope bounds every honest shift coordinate. [Under the stated hypotheses](hyp:hscale,he) [this conclusion](goal) applies. -/
lemma abs_shift_le_of_matrixScaleBound {p m : ℕ}
    (H : Finset (Environment m)) (Omega : RealMatrix p)
    (Sigma : Environment m → RealMatrix p) (s : Environment m → Fin p → ℝ)
    {M : ℝ} (hscale : matrixScaleBound H Omega Sigma s ≤ M)
    {e : Environment m} (he : e ∈ H) (i : Fin p) :
    |s e i| ≤ M := by
  have hdiag : ‖Matrix.diagonal (s e)‖ ≤
      finsetMaxNorm H (fun e ↦ Matrix.diagonal (s e)) := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max (c := ‖Matrix.diagonal (s e)‖)).mpr
      (Or.inr ⟨e, he, le_rfl⟩)
  have hterm : finsetMaxNorm H (fun e ↦ Matrix.diagonal (s e)) ≤
      matrixScaleBound H Omega Sigma s := by
    unfold matrixScaleBound
    have hOmega : 0 ≤ ‖Omega‖ := norm_nonneg _
    have hSigma : 0 ≤ finsetMaxNorm H Sigma := by
      unfold finsetMaxNorm
      exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
    linarith
  calc
    |s e i| ≤ ‖s e‖ := by simpa using norm_le_pi_norm (s e) i
    _ = ‖Matrix.diagonal (s e)‖ := (Matrix.l2_opNorm_diagonal (s e)).symm
    _ ≤ finsetMaxNorm H (fun e ↦ Matrix.diagonal (s e)) := hdiag
    _ ≤ matrixScaleBound H Omega Sigma s := hterm
    _ ≤ M := hscale

/-- Centering a nonnegative honest shift family preserves the same scale envelope. [Under the stated hypotheses](hyp:hSH,hs,hscale,e0) [this conclusion](goal) applies. -/
lemma centered_shiftScaleBound_of_matrixScaleBound {p m : ℕ}
    (H S : Finset (Environment m)) (hSH : S ⊆ H)
    (Omega : RealMatrix p) (Sigma : Environment m → RealMatrix p)
    (s : Environment m → Fin p → ℝ) (hs : ∀ e ∈ H, ∀ i, 0 ≤ s e i)
    {M : ℝ} (hscale : matrixScaleBound H Omega Sigma s ≤ M)
    (e0 : {e // e ∈ S}) :
    ShiftScaleBound (fun e : {e // e ∈ S} ↦ fun i ↦ s e.1 i - s e0.1 i) M := by
  intro e i
  have heH := hSH e.property
  have he0H := hSH e0.property
  have heU := abs_shift_le_of_matrixScaleBound H Omega Sigma s hscale heH i
  have he0U := abs_shift_le_of_matrixScaleBound H Omega Sigma s hscale he0H i
  have heL := hs e.1 heH i
  have he0L := hs e0.1 he0H i
  rw [abs_le]
  constructor <;> nlinarith [le_trans (le_abs_self _) heU, le_trans (le_abs_self _) he0U]

/-- The equilibrium equation becomes exact diagonal congruence after centering at one retained
environment. [Under the stated hypotheses](hyp:hmodel,hSH,e0) [this conclusion](goal) applies. -/
lemma exactCongruence_centered_of_honestCovarianceModel {p m c : ℕ}
    (W : BackshiftSystem p m c) (hmodel : HonestCovarianceModel W)
    (S : Finset (Environment m)) (hSH : S ⊆ W.honest) (e0 : {e // e ∈ S}) :
    ExactCongruence
      (fun e : {e // e ∈ S} ↦ W.covariance e.1 - W.covariance e0.1)
      (fun e : {e // e ∈ S} ↦ fun i ↦ W.shifts e.1 i - W.shifts e0.1 i)
      W.structural := by
  intro e
  have transformed (a : Environment m) (ha : a ∈ W.honest) :
      W.structural * W.covariance a * W.structural.transpose =
        W.invariantNoise + Matrix.diagonal (W.shifts a) := by
    have hleft : W.structural * W.structural⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ W.structural_invertible
    have hright : W.structural⁻¹.transpose * W.structural.transpose = 1 := by
      rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
    rw [hmodel a ha]
    calc
      W.structural *
          (W.structural⁻¹ *
            (W.invariantNoise + Matrix.diagonal (W.shifts a)) *
              W.structural⁻¹.transpose) * W.structural.transpose =
          (W.structural * W.structural⁻¹) *
            (W.invariantNoise + Matrix.diagonal (W.shifts a)) *
              (W.structural⁻¹.transpose * W.structural.transpose) := by
            noncomm_ring
      _ = _ := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  have heH := hSH e.property
  have he0H := hSH e0.property
  rw [Matrix.mul_sub, Matrix.sub_mul, transformed e.1 heH, transformed e0.1 he0H]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Affine separation is unchanged when all retained shift vectors are centered at one retained
environment. [Under the stated hypotheses](hyp:hsep,e0) [this conclusion](goal) applies. -/
lemma pairwiseAffineSeparated_centered {p m : ℕ} (S : Finset (Environment m))
    (s : Environment m → Fin p → ℝ) {γ : ℝ}
    (hsep : PairwiseAffineSeparated (fun e : {e // e ∈ S} ↦ s e.1) γ)
    (e0 : {e // e ∈ S}) :
    PairwiseAffineSeparated
      (fun e : {e // e ∈ S} ↦ fun i ↦ s e.1 i - s e0.1 i) γ := by
  intro i j hij
  obtain ⟨a, b, d, habd⟩ := hsep i j hij
  refine ⟨a, b, d, ?_⟩
  convert habd using 1
  congr 1
  unfold pairAffineDet
  ring

/-- Paper admissibility and condition bounds give the reusable determinant/condition envelope. [Under the stated hypotheses](hyp:hD,hB,hDcond,hBcond) [this conclusion](goal) applies. -/
lemma pairDetConditionEnvelope_of_admissible {p : ℕ} {κ : ℝ}
    (D B : RealMatrix p) (hD : D ∈ admissibleSet p) (hB : B ∈ admissibleSet p)
    (hDcond : matrixConditionNumber D ≤ κ) (hBcond : matrixConditionNumber B ≤ κ) :
    PairDetConditionEnvelope κ D B := by
  exact ⟨⟨hD.1, abs_det_le_factorial_of_mem_admissibleSet hD, hDcond⟩,
    ⟨hB.1, abs_det_le_factorial_of_mem_admissibleSet hB, hBcond⟩⟩

/-- Two covariance perturbations around a common base produce at most twice the congruence error
on every off-diagonal entry. [Under the stated hypotheses](hyp:e0,hL,hr,hB,hGamma,herr) [this conclusion](goal) applies. -/
lemma offDiagonalApproximateCongruence_centered
    {p m : ℕ} (S : Finset (Environment m)) (Sigma Gamma : Environment m → RealMatrix p)
    (B Psi : RealMatrix p) (t : Environment m → Fin p → ℝ)
    (e0 : {e // e ∈ S}) {L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hB : ‖B‖ ≤ L)
    (hGamma : ∀ e ∈ S,
      B * Gamma e * B.transpose = Psi + Matrix.diagonal (t e))
    (herr : ∀ e ∈ S, ‖Gamma e - Sigma e‖ ≤ r) :
    OffDiagonalApproximateCongruence
      (fun e : {e // e ∈ S} ↦ Sigma e.1 - Sigma e0.1) B (2 * L ^ 2 * r) := by
  intro e i j hij
  have hzero :
      (B * (Gamma e.1 - Gamma e0.1) * B.transpose) i j = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hGamma e.1 e.property,
      hGamma e0.1 e0.property]
    simp [hij]
  have he : ‖Sigma e.1 - Gamma e.1‖ ≤ r := by
    rw [← neg_sub, norm_neg]
    exact herr e.1 e.property
  have he0 : ‖Sigma e0.1 - Gamma e0.1‖ ≤ r := by
    rw [← neg_sub, norm_neg]
    exact herr e0.1 e0.property
  have hid : Sigma e.1 - Sigma e0.1 =
      (Sigma e.1 - Gamma e.1) - (Sigma e0.1 - Gamma e0.1) +
        (Gamma e.1 - Gamma e0.1) := by abel
  change |(B * (Sigma e.1 - Sigma e0.1) * B.transpose) i j| ≤ _
  rw [hid, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hzero, add_zero]
  calc
    |(B * ((Sigma e.1 - Gamma e.1) - (Sigma e0.1 - Gamma e0.1)) *
        B.transpose) i j| ≤
        ‖B * ((Sigma e.1 - Gamma e.1) - (Sigma e0.1 - Gamma e0.1)) *
          B.transpose‖ := abs_entry_le_opNorm _ _ _
    _ ≤ ‖B‖ *
        ‖(Sigma e.1 - Gamma e.1) - (Sigma e0.1 - Gamma e0.1)‖ * ‖B.transpose‖ := by
      calc
        _ ≤ ‖B * ((Sigma e.1 - Gamma e.1) - (Sigma e0.1 - Gamma e0.1))‖ *
            ‖B.transpose‖ := norm_mul_le _ _
        _ ≤ (‖B‖ * ‖(Sigma e.1 - Gamma e.1) -
            (Sigma e0.1 - Gamma e0.1)‖) * ‖B.transpose‖ := by
              gcongr
              exact norm_mul_le _ _
    _ ≤ L * (2 * r) * L := by
      have htrans : ‖B.transpose‖ = ‖B‖ := by
        change ‖star B‖ = ‖B‖
        exact norm_star B
      rw [htrans]
      have hmid : ‖(Sigma e.1 - Gamma e.1) -
          (Sigma e0.1 - Gamma e0.1)‖ ≤ 2 * r :=
        (norm_sub_le _ _).trans (by linarith)
      exact mul_le_mul
        (mul_le_mul hB hmid (norm_nonneg _) hL) hB
        (norm_nonneg _) (mul_nonneg hL (by positivity))
    _ = 2 * L ^ 2 * r := by ring

/-- An invertible congruence equation can be returned to covariance form. [Under the stated hypotheses](hyp:hunit,htransformed) [this conclusion](goal) applies. -/
lemma covariance_eq_of_transformed {p : ℕ} (B Sigma Psi : RealMatrix p)
    (s : Fin p → ℝ) (hunit : IsUnit B.det)
    (htransformed : B * Sigma * B.transpose = Psi + Matrix.diagonal s) :
    Sigma = B⁻¹ * (Psi + Matrix.diagonal s) * B⁻¹.transpose := by
  have hleft : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hunit
  have hright : B.transpose * B⁻¹.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  rw [← htransformed]
  calc
    Sigma = (B⁻¹ * B) * Sigma * (B.transpose * B⁻¹.transpose) := by
      rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
    _ = B⁻¹ * (B * Sigma * B.transpose) * B⁻¹.transpose := by noncomm_ring

end CausalSmith.ExactID.RobustBackshiftUniformDistance
