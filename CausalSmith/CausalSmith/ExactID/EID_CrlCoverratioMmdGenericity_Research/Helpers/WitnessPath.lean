import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Witnesses

/-!
# Explicit cancellation-to-sparse witness path

This file records the elementary one-dimensional facts about the child-mechanism
coefficient along the path from the cancellation witness to the sparse witness.
-/

open Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: cancellationSparsePathPrimitive
/-- The child-mechanism coefficient on the affine path from the cancellation
witness (`t = 0`) to the sparse witness (`t = 1`). -/
def cancellationSparsePathPrimitive (t x : ℝ) : ℝ :=
  (1 - t) * cancellationPrimitive x + t * centeredCoordinate x

-- @node: cancellationSparsePathPrimitive_mem_unitInterval
/-- Convex interpolation preserves the coefficient bound on the unit interval.  Given [the stated inputs and conditions](hyp:ht,hx), [the stated conclusion](goal) follows. -/
lemma cancellationSparsePathPrimitive_mem_unitInterval
    {t x : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    cancellationSparsePathPrimitive t x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hH := cancellationPrimitive_mem_unitInterval_sub hx
  have hh := abs_centeredCoordinate_le_one hx
  rw [abs_le] at hh
  unfold cancellationSparsePathPrimitive
  constructor <;> nlinarith [ht.1, ht.2, hH.1, hH.2, hh.1, hh.2]

-- @node: cancellationSparsePathPrimitive_nonconstant
/-- Every coefficient on the closed cancellation-to-sparse segment is nonconstant.  Given [the stated inputs and conditions](hyp:ht), [the stated conclusion](goal) follows. -/
lemma cancellationSparsePathPrimitive_nonconstant
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x, cancellationSparsePathPrimitive t x ≠
      cancellationSparsePathPrimitive t 0 := by
  by_cases ht0 : t = 0
  · subst t
    simpa [cancellationSparsePathPrimitive] using cancellationPrimitive_nonconstant
  · refine ⟨1, ?_⟩
    have hH := cancellationPrimitive_zero
    simp only [cancellationSparsePathPrimitive, hH.1, hH.2, centeredCoordinate]
    intro heq
    apply ht0
    linarith

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
