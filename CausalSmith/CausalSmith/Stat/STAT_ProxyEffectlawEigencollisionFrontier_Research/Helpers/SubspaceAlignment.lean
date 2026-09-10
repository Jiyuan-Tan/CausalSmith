import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Basic

/-!
# Alignment of orthonormal signal frames

This module isolates the exact algebraic core of Procrustes alignment.  Two orthonormal
rectangular frames with the same column space differ by an explicitly constructed square
orthogonal matrix.  The result is stated in the matrix operator norm used by the surrounding
proxy-effect-law development.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators Matrix.Norms.L2Operator

/-- The Gram matrix of [an orthonormal signal frame](hyp:V) [is the identity](goal). -/
-- @node: subspace_alignment_signalBasis_gram
lemma SignalBasis.gram_eq_one {dx k : ℕ} (V : SignalBasis dx k) :
    V.V.transpose * V.V = (1 : RectMatrix k k) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  exact V.orthonormal i j

/-- If [two orthonormal signal frames](hyp:V,W) [have the same column space](hyp:hrange),
then projecting either frame through the other [recovers it exactly](goal). -/
-- @node: subspace_alignment_cross_projection
lemma SignalBasis.mul_transpose_mul_eq_of_range_eq {dx k : ℕ}
    (V W : SignalBasis dx k)
    (hrange : LinearMap.range (Matrix.toEuclideanLin V.V) =
      LinearMap.range (Matrix.toEuclideanLin W.V)) :
    W.V * W.V.transpose * V.V = V.V := by
  have hW := W.gram_eq_one
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hx : Matrix.toEuclideanLin V.V x ∈
      LinearMap.range (Matrix.toEuclideanLin W.V) := by
    rw [← hrange]
    exact LinearMap.mem_range_self _ x
  rcases hx with ⟨y, hy⟩
  have hleft : Matrix.toEuclideanLin W.V.transpose
      (Matrix.toEuclideanLin W.V y) = y := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hW]
  have hmul : Matrix.toEuclideanLin (W.V * W.V.transpose * V.V) x =
      Matrix.toEuclideanLin W.V
        (Matrix.toEuclideanLin W.V.transpose (Matrix.toEuclideanLin V.V x)) := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmul, ← hy, hleft, hy]

/-- If [two orthonormal signal frames](hyp:V,W) [span the same subspace](hyp:hrange),
there is [a square matrix orthogonal on both sides](goal) that aligns the second frame with the
first exactly.  The alignment is the cross-Gram matrix `WᵀV`. -/
-- @node: subspace_alignment_exact_procrustes
theorem SignalBasis.exists_orthogonal_alignment_of_range_eq {dx k : ℕ}
    (V W : SignalBasis dx k)
    (hrange : LinearMap.range (Matrix.toEuclideanLin V.V) =
      LinearMap.range (Matrix.toEuclideanLin W.V)) :
    ∃ O : RectMatrix k k,
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧ W.V * O = V.V := by
  refine ⟨W.V.transpose * V.V, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      V.V.transpose * W.V * (W.V.transpose * V.V) =
          V.V.transpose * (W.V * W.V.transpose * V.V) := by
            simp only [Matrix.mul_assoc]
      _ = V.V.transpose * V.V := by
        rw [V.mul_transpose_mul_eq_of_range_eq W hrange]
      _ = 1 := V.gram_eq_one
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      W.V.transpose * V.V * (V.V.transpose * W.V) =
          W.V.transpose * (V.V * V.V.transpose * W.V) := by
            simp only [Matrix.mul_assoc]
      _ = W.V.transpose * W.V := by
        rw [W.mul_transpose_mul_eq_of_range_eq V hrange.symm]
      _ = 1 := W.gram_eq_one
  · rw [← Matrix.mul_assoc]
    exact V.mul_transpose_mul_eq_of_range_eq W hrange

/-- Under [a common signal row space](hyp:hrange), [positive margin](hyp:hs₀), and [arbitrary
matrix perturbation data](hyp:A,B), the exactly aligned orthonormal frames have [zero operator
distance, hence obey the requested inverse-margin perturbation bound](goal). -/
-- @node: subspace_alignment_exact_bound
theorem SignalBasis.exists_orthogonal_alignment_bound_of_range_eq
    {rows dx k : ℕ} {s₀ : ℝ} (A B : RectMatrix rows dx)
    (V W : SignalBasis dx k)
    (hrange : LinearMap.range (Matrix.toEuclideanLin V.V) =
      LinearMap.range (Matrix.toEuclideanLin W.V))
    (hs₀ : 0 < s₀) :
    ∃ O : RectMatrix k k,
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
        ‖V.V - W.V * O‖ ≤ 8 * s₀⁻¹ * ‖A - B‖ := by
  obtain ⟨O, hOtO, hOOt, hO⟩ := V.exists_orthogonal_alignment_of_range_eq W hrange
  refine ⟨O, hOtO, hOOt, ?_⟩
  rw [hO, sub_self, norm_zero]
  positivity

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
