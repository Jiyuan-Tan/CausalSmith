import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Basic.Occupancy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.EMetricSpace.Diam

/-!
# Operator-norm margins and set radii

Conditioning, normalization slack, scale, and the extended-valued outer-radius functional used by
the contraction theorem.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator MatrixOrder ENNReal BigOperators

/-- Operator-norm condition number.

@realizes kappa(kappa_D = ‖D‖op ‖D⁻¹‖op)
-/
noncomputable def matrixConditionNumber {p : ℕ} (D : RealMatrix p) : ℝ :=
  ‖D‖ * ‖D⁻¹‖

/-- Cycle-product normalization slack.

@realizes zeta(zeta_D = 1 - CP(I-D))
-/
noncomputable def normalizationSlack {p : ℕ} (D : RealMatrix p) : ℝ :=
  1 - cycleProduct (1 - D)

/-- Maximum operator norm over an indexed finite family. -/
noncomputable def finsetMaxNorm {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (f : ι → RealMatrix p) : ℝ :=
  Finset.fold max 0 (fun i ↦ ‖f i‖) I

/-- True-instance scale bound.

@realizes Mbound(1 + noise norm + honest covariance and shift-diagonal maxima)
-/
noncomputable def matrixScaleBound {p m : ℕ} (H : Finset (Environment m))
    (Omega : RealMatrix p) (covarianceFamily : Environment m → RealMatrix p)
    (s : Environment m → Fin p → ℝ) : ℝ :=
  1 + ‖Omega‖ + finsetMaxNorm H covarianceFamily +
    finsetMaxNorm H (fun e ↦ Matrix.diagonal (s e))

/-- Mathlib's extended metric diameter in the operator-norm matrix metric realizes the paper's
operator diameter.

@realizes diamOp(Metric.ediam in operator-norm metric)
-/
-- @node: def:operator-diameter
noncomputable example {p : ℕ} (A : Set (RealMatrix p)) : ℝ≥0∞ := Metric.ediam A

-- The planned `def:operator-diameter` node reuses the imported declaration `Metric.ediam`.

-- @node: def:operator-outer-radius
/-- Extended-valued supremum of operator distance from a set to one structural matrix.

@realizes outerOp(supremum of operator distances to D)
-/
noncomputable def opOuterRadius {p : ℕ} (A : Set (RealMatrix p))
    (_hA : A.Nonempty) (D : RealMatrix p) : ℝ≥0∞ :=
  ⨆ A1 ∈ A, edist A1 D

/-- Diameter is at most twice the outer radius about any center. [Under the stated hypotheses](hyp:hA) [this conclusion](goal) applies. -/
lemma ediam_le_two_mul_opOuterRadius {p : ℕ} (A : Set (RealMatrix p))
    (hA : A.Nonempty) (D : RealMatrix p) :
    Metric.ediam A ≤ 2 * opOuterRadius A hA D := by
  refine Metric.ediam_le fun x hx y hy ↦ ?_
  calc
    edist x y ≤ edist x D + edist y D := edist_triangle_right _ _ _
    _ ≤ 2 * opOuterRadius A hA D := by
      rw [two_mul]
      exact add_le_add
        (le_iSup_of_le x (le_iSup_of_le hx le_rfl))
        (le_iSup_of_le y (le_iSup_of_le hy le_rfl))

/-- Positive-semidefinite summands are monotone in operator norm. [Under the stated hypotheses](hyp:hP,hQ) [this conclusion](goal) applies. -/
lemma opNorm_le_opNorm_add_of_posSemidef {p : ℕ} {P Q : RealMatrix p}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : ‖P‖ ≤ ‖P + Q‖ := by
  let TP := Matrix.toEuclideanCLM (𝕜 := ℝ) P
  let TQ := Matrix.toEuclideanCLM (𝕜 := ℝ) Q
  have hTPsymm : TP.IsSymmetric := by
    simpa [TP, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.1
  rw [Matrix.l2_opNorm_def]
  change ‖TP‖ ≤ ‖P + Q‖
  rw [TP.norm_eq_iSup_rayleighQuotient hTPsymm]
  refine ciSup_le fun x ↦ ?_
  have hTPnonneg : 0 ≤ TP.rayleighQuotient x := by
    by_cases hx : x = 0
    · simp [hx]
    · dsimp [ContinuousLinearMap.rayleighQuotient]
      apply div_nonneg
      · rw [ContinuousLinearMap.reApplyInnerSelf_apply,
          EuclideanSpace.inner_eq_star_dotProduct]
        change 0 ≤ dotProduct (star (WithLp.ofLp x))
          (Matrix.mulVec P (WithLp.ofLp x))
        exact hP.dotProduct_mulVec_nonneg (WithLp.ofLp x)
      · positivity
  rw [abs_of_nonneg hTPnonneg]
  calc
    TP.rayleighQuotient x ≤ (TP + TQ).rayleighQuotient x := by
      rw [ContinuousLinearMap.rayleighQuotient_add]
      exact le_add_of_nonneg_right (by
        by_cases hx : x = 0
        · simp [hx]
        · dsimp [ContinuousLinearMap.rayleighQuotient]
          apply div_nonneg
          · rw [ContinuousLinearMap.reApplyInnerSelf_apply,
              EuclideanSpace.inner_eq_star_dotProduct]
            change 0 ≤ dotProduct (star (WithLp.ofLp x))
              (Matrix.mulVec Q (WithLp.ofLp x))
            exact hQ.dotProduct_mulVec_nonneg (WithLp.ofLp x)
          · positivity)
    _ ≤ |(TP + TQ).rayleighQuotient x| := le_abs_self _
    _ ≤ ‖TP + TQ‖ := (TP + TQ).rayleighQuotient_le_norm x
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (P + Q)‖ := by simp [TP, TQ]
    _ = ‖P + Q‖ := Matrix.l2_opNorm_toEuclideanCLM _

end CausalSmith.ExactID.RobustBackshiftUniformDistance
