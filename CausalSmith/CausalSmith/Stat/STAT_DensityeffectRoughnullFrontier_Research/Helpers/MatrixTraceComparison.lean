module
public import Mathlib.Analysis.Matrix.Order
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.OperatorCovariance

/-! Positive semidefinite trace comparison for the covariance certificate (19).
Cyclicity of trace removes the commutator; no simultaneous diagonalization is used. -/

public section

noncomputable section
open scoped MatrixOrder
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
-- @node: trace_mul_nonneg_of_posSemidef
lemma trace_mul_nonneg_of_posSemidef {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  classical
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hS, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same S).trace_nonneg

/-- The square trace is monotone along positive semidefinite domination. -/
-- @node: trace_square_le_of_posSemidef_sub
lemma trace_square_le_of_posSemidef_sub {n : Type*} [Fintype n]
    (A D : Matrix n n ℝ) (hA : A.PosSemidef) (hDA : (D - A).PosSemidef) :
    (A * A).trace ≤ (D * D).trace := by
  classical
  have hD : D.PosSemidef := by simpa using hDA.add hA
  have h := trace_mul_nonneg_of_posSemidef (D - A) (D + A) hDA (hD.add hA)
  simp only [sub_mul, mul_add, Matrix.trace_sub, Matrix.trace_add] at h
  have hc := Matrix.trace_mul_comm D A
  linarith

/-- The paper's concrete covariance trace is the usual matrix square trace. -/
-- @node: covarianceSquareTrace_eq_trace
lemma covarianceSquareTrace_eq_trace {J : ℕ} (sigma : Matrix (Fin J) (Fin J) ℝ) :
    covarianceSquareTrace sigma = (sigma * sigma).trace := by
  simp only [covarianceSquareTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- Quadratic-form positivity in histogram coordinates gives matrix positivity. -/
-- @node: posSemidef_of_covarianceForm_nonneg
lemma posSemidef_of_covarianceForm_nonneg {J : ℕ}
    (sigma : Matrix (Fin J) (Fin J) ℝ) (hsym : sigma.IsHermitian)
    (hform : ∀ f : Hj J, 0 ≤ covarianceForm sigma f) : sigma.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym
  intro x
  simpa only [covarianceForm, PiLp.toLp_apply, dotProduct, Matrix.mulVec,
    star_trivial, Finset.mul_sum, mul_assoc] using hform (WithLp.toLp 2 x)

/-- The observable chain covariance is symmetric. -/
-- @node: contrastCovariance_isHermitian
lemma contrastCovariance_isHermitian (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    (contrastCovariance P train mx my L T J q kt).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose, Matrix.transpose, contrastCovariance, mul_comm]

/-- The observable chain covariance is positive semidefinite. -/
-- @node: contrastCovariance_posSemidef
lemma contrastCovariance_posSemidef (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    (contrastCovariance P train mx my L T J q kt).PosSemidef :=
  posSemidef_of_covarianceForm_nonneg _
    (contrastCovariance_isHermitian P train mx my L T J q kt)
    (contrastCovariance_form_nonneg P train mx my L T J q kt)

end CausalSmith.Stat.DensityEffectRoughNull
