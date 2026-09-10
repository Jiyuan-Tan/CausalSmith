import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Cycle-product normalization

Finite directed simple cycles and the maximum absolute matrix-entry product used by the
BACKSHIFT normalization.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open scoped BigOperators

noncomputable section

/-- The absolute entry product associated with a permutation that is one nontrivial cycle. -/
def simpleCycleWeight {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (σ : Equiv.Perm (Fin p)) : ℝ := by
  classical
  exact if σ.IsCycle ∧ 2 ≤ σ.support.card then
      ∏ i ∈ σ.support, |A i (σ i)|
    else 0

/-- Maximum absolute product along a directed simple cycle of length at least two.

@realizes CP(maximum absolute directed-simple-cycle entry product)
-/
def cycleProduct {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) : ℝ := by
  classical
  exact Finset.fold max 0 (simpleCycleWeight A)
    (Finset.univ : Finset (Equiv.Perm (Fin p)))

/-- The cycle-product functional is continuous in the matrix entries. [This is the asserted conclusion](goal). -/
lemma continuous_cycleProduct {p : ℕ} :
    Continuous (cycleProduct : Matrix (Fin p) (Fin p) ℝ → ℝ) := by
  classical
  let f : Equiv.Perm (Fin p) → Matrix (Fin p) (Fin p) ℝ → ℝ :=
    fun σ A ↦ simpleCycleWeight A σ
  have hf (σ : Equiv.Perm (Fin p)) : Continuous (f σ) := by
    dsimp [f]
    unfold simpleCycleWeight
    split_ifs <;> fun_prop
  have hs (s : Finset (Equiv.Perm (Fin p))) :
      Continuous (fun A ↦ Finset.fold max 0 (fun σ ↦ f σ A) s) := by
    induction s using Finset.induction with
    | empty => simp only [Finset.fold_empty]; fun_prop
    | @insert σ s hσ ih =>
        simp only [Finset.fold_insert hσ]
        exact (hf σ).max ih
  change Continuous (fun A : Matrix (Fin p) (Fin p) ℝ ↦
    Finset.fold max 0 (simpleCycleWeight A)
      (Finset.univ : Finset (Equiv.Perm (Fin p))))
  simpa only [f] using
    hs (Finset.univ : Finset (Equiv.Perm (Fin p)))

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
