import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.RealDiagonalizationBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TObservedVMWMarginInclusion
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ConditionalMomentAdapters
import CausalSmith.Substrate.CollisionSafeSpectralLaw.MoorePenrose

/-!
Uniformly conditioned ambient real diagonalizations built from a model's thin target-feature
singular-value decomposition and an orthonormal kernel complement.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped Matrix.Norms.L2Operator
open CausalSmith.Substrate.CollisionSafeSpectralLaw
open Causalean.Mathlib.Probability

-- @node: modelRealDiagonalization_thinSignalFactorization
structure ThinSignalFactorization {dx k : ℕ} (B : RectMatrix dx k) where
  V : SignalBasis dx k
  coord : RectMatrix k k
  coordInv : RectMatrix k k
  factor : B = V.V * coord
  coord_mul_inv : coord * coordInv = 1
  inv_mul_coord : coordInv * coord = 1

-- @node: modelRealDiagonalization_thinSignalFactorization_construct
noncomputable def thinSignalFactorization {dx k : ℕ} (B : RectMatrix dx k)
    (hpos : ∀ r : Fin k, 0 < (singularSystem B).sigma r) : ThinSignalFactorization B := by
  let S := singularSystem B
  let V : SignalBasis dx k := {
    V := fun i r => S.left r i
    orthonormal := fun r s => S.left_orthonormal_of_pos r s (hpos r) (hpos s) }
  let C : RectMatrix k k := fun r j => S.sigma r * S.right r j
  let Cinv : RectMatrix k k := fun j r => S.right r j * (S.sigma r)⁻¹
  have hfactor : B = V.V * C := by
    ext i j
    simp only [V, C, Matrix.mul_apply]
    rw [S.expansion]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hmul : C * Cinv = 1 := by
    ext r s
    simp only [C, Cinv, Matrix.mul_apply, Matrix.one_apply]
    by_cases hrs : r = s
    · subst s
      rw [if_pos rfl]
      calc
        (∑ x, S.sigma r * S.right r x * (S.right r x * (S.sigma r)⁻¹)) =
            (S.sigma r * (S.sigma r)⁻¹) * ∑ x, S.right r x * S.right r x := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = 1 := by rw [mul_inv_cancel₀ (ne_of_gt (hpos r)), S.right_orthonormal r r]; simp
    · rw [if_neg hrs]
      calc
        (∑ x, S.sigma r * S.right r x * (S.right s x * (S.sigma s)⁻¹)) =
            (S.sigma r * (S.sigma s)⁻¹) * ∑ x, S.right r x * S.right s x := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = 0 := by rw [S.right_orthonormal r s, if_neg hrs]; ring
  exact ⟨V, C, Cinv, hfactor, hmul, (mul_eq_one_comm.mp hmul)⟩


-- @node: modelRealDiagonalization_signalBasis_transpose_mul_self
lemma SignalBasis.transpose_mul_self {dx k : ℕ} (V : SignalBasis dx k) :
    V.V.transpose * V.V = (1 : RectMatrix k k) := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply] using V.orthonormal i j

-- @node: modelRealDiagonalization_forward
noncomputable def ThinSignalFactorization.forward {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) : RectMatrix dx dx :=
  F.V.V * F.coordInv.transpose * F.V.V.transpose +
    (1 - F.V.V * F.V.V.transpose)

-- @node: modelRealDiagonalization_backward
noncomputable def ThinSignalFactorization.backward {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) : RectMatrix dx dx :=
  F.V.V * F.coord.transpose * F.V.V.transpose +
    (1 - F.V.V * F.V.V.transpose)

-- @node: modelRealDiagonalization_forward_mul_backward
lemma ThinSignalFactorization.forward_mul_backward {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) : F.forward * F.backward = 1 := by
  let V := F.V.V
  let K : RectMatrix dx dx := 1 - V * V.transpose
  have hgram : V.transpose * V = (1 : RectMatrix k k) := F.V.transpose_mul_self
  have hci : F.coordInv.transpose * F.coord.transpose = (1 : RectMatrix k k) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose F.coord_mul_inv
  have hVK : V.transpose * K = 0 := by
    calc
      V.transpose * K = V.transpose - (V.transpose * V) * V.transpose := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hgram, Matrix.one_mul, sub_self]
  have hKV : K * V = 0 := by
    calc
      K * V = V - V * (V.transpose * V) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hgram, Matrix.mul_one, sub_self]
  have hKK : K * K = K := by
    calc
      K * K = (1 - V * V.transpose) * K := by rfl
      _ = K - V * (V.transpose * K) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = K := by rw [hVK, Matrix.mul_zero, sub_zero]
  let A := V * F.coordInv.transpose * V.transpose
  let D := V * F.coord.transpose * V.transpose
  have hAD : A * D = V * V.transpose := by
    simp only [A, D, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V.transpose V, hgram, Matrix.one_mul,
      ← Matrix.mul_assoc F.coordInv.transpose F.coord.transpose, hci,
      Matrix.one_mul]
  have hAK : A * K = 0 := by simp [A, Matrix.mul_assoc, hVK]
  have hKD : K * D = 0 := by simp [D, ← Matrix.mul_assoc, hKV]
  change (A + K) * (D + K) = 1
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAD, hAK, hKD, hKK]
  simp [K]

-- @node: modelRealDiagonalization_backward_mul_forward
lemma ThinSignalFactorization.backward_mul_forward {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) : F.backward * F.forward = 1 := by
  let V := F.V.V
  let K : RectMatrix dx dx := 1 - V * V.transpose
  have hgram : V.transpose * V = (1 : RectMatrix k k) := F.V.transpose_mul_self
  have hci : F.coord.transpose * F.coordInv.transpose = (1 : RectMatrix k k) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose F.inv_mul_coord
  have hVK : V.transpose * K = 0 := by
    calc
      V.transpose * K = V.transpose - (V.transpose * V) * V.transpose := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hgram, Matrix.one_mul, sub_self]
  have hKV : K * V = 0 := by
    calc
      K * V = V - V * (V.transpose * V) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hgram, Matrix.mul_one, sub_self]
  have hKK : K * K = K := by
    calc
      K * K = (1 - V * V.transpose) * K := by rfl
      _ = K - V * (V.transpose * K) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = K := by rw [hVK, Matrix.mul_zero, sub_zero]
  let A := V * F.coord.transpose * V.transpose
  let D := V * F.coordInv.transpose * V.transpose
  have hAD : A * D = V * V.transpose := by
    simp only [A, D, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V.transpose V, hgram, Matrix.one_mul,
      ← Matrix.mul_assoc F.coord.transpose F.coordInv.transpose, hci,
      Matrix.one_mul]
  have hAK : A * K = 0 := by simp [A, Matrix.mul_assoc, hVK]
  have hKD : K * D = 0 := by simp [D, ← Matrix.mul_assoc, hKV]
  change (A + K) * (D + K) = 1
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAD, hAK, hKD, hKK]
  simp [K]

-- @node: modelRealDiagonalization_linearEquiv
noncomputable def ThinSignalFactorization.linearEquiv {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) : Euc dx ≃ₗ[ℝ] Euc dx := by
  apply LinearEquiv.ofLinear (Matrix.toEuclideanLin F.forward)
    (Matrix.toEuclideanLin F.backward)
  · apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    simpa [LinearMap.comp_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (fun M : RectMatrix dx dx => Matrix.mulVec M x.ofLp i)
        F.forward_mul_backward
  · apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    simpa [LinearMap.comp_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (fun M : RectMatrix dx dx => Matrix.mulVec M x.ofLp i)
        F.backward_mul_forward


end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
