module
public import Mathlib.Data.Fin.Basic

/-!
# Consecutive coarse-cell pair classes

A pair class groups two adjacent coarse cells. These definitions are independent
of counting and component proofs, allowing those proof layers to share a stable
interface. Divisibility and evenness are imposed by the counting theorems.
-/

@[expose] public section

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- [The index of the consecutive coarse-cell pair](goal) containing [a fine
cell](hyp:a), for [fine and coarse cell counts K and M](hyp:K,M), is the cell's
position divided by twice the coarse-cell width K/M, both quotients rounded down
(and equal to zero when the width K/M rounds down to zero). -/
def pairClass (K M : ℕ) (a : Fin K) : ℕ := a.val / (2 * (K / M))

/-- [Two labelled assignments](hyp:x,y) have [all their cells in one common
consecutive coarse-cell pair](goal), with pair index below half the coarse count,
for [the given cell counts](hyp:K,M). -/
def SamePair {ι κ : Type*} (K M : ℕ) (x : ι → Fin K) (y : κ → Fin K) : Prop :=
  ∃ p < M / 2, (∀ i, pairClass K M (x i) = p) ∧
    (∀ j, pairClass K M (y j) = p)

end Causalean.Stat.RandomGraph.PathOccupancy
