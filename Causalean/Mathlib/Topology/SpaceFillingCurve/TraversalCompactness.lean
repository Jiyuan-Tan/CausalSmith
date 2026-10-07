module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.FiniteTraversal

/-!
# Compactness for finite dyadic traversals

Finite traversals can be restricted to a shorter depth. Their finite sets of
possible cell orders form an inverse system; a coherent sequence of finite
orders is the input for the infinite traversal construction.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a finite dyadic traversal](hyp:T) and [a shorter depth](hyp:hmn), [its truncation](goal) is [the restricted traversal at that depth](step:1). -/
def FiniteDyadicTraversal.truncate {d m n : ℕ} (T : FiniteDyadicTraversal d n)
    (hmn : m ≤ n) : FiniteDyadicTraversal d m where
  cell k hk := T.cell k (hk.trans hmn)
  bijective k hk := T.bijective k (hk.trans hmn)
  adjacent k hk a b hab := T.adjacent k (hk.trans hmn) a b hab
  nested k hk a b hab := T.nested k (hk.trans hmn) a b hab

/-- Restricting a traversal twice gives the same finite traversal as a single
restriction to the final depth. -/
theorem FiniteDyadicTraversal.truncate_trans {d l m n : ℕ}
    (T : FiniteDyadicTraversal d n) (hlm : l ≤ m) (hmn : m ≤ n) :
    (T.truncate hmn).truncate hlm = T.truncate (hlm.trans hmn) := by
  rfl

/-- At every finite depth there are only finitely many coherent dyadic cell
orders in a fixed dimension. -/
theorem finite_finiteDyadicTraversal (d n : ℕ) :
    Finite (FiniteDyadicTraversal d n) := by
  classical
  let encode : FiniteDyadicTraversal d n →
      (k : Fin (n + 1)) → Fin (2 ^ (d * k.val)) → Fin d → Fin (2 ^ k.val) :=
    fun T k => T.cell k.val (by omega)
  apply Finite.of_injective encode
  intro T U h
  cases T with
  | mk cellT bijT adjT nestT =>
    cases U with
    | mk cellU bijU adjU nestU =>
      have hc : cellT = cellU := by
        funext m hm k i
        exact congrArg (fun f => f ⟨m, by omega⟩ k i) h
      cases hc
      rfl

/-- Given [a cube dimension](hyp:d) and [nonempty finite traversals at every depth](hyp:hfinite),
[there is a sequence of finite traversals, one for each depth, in which every traversal is the truncation of the next one](goal). -/
theorem exists_coherent_finiteDyadicTraversals (d : ℕ)
    (hfinite : ∀ n, Nonempty (FiniteDyadicTraversal d n)) :
    ∃ T : ∀ n, FiniteDyadicTraversal d n,
      ∀ n, (T (n + 1)).truncate (Nat.le_succ n) = T n := by
  letI (n : ℕ) : Nonempty (FiniteDyadicTraversal d n) := hfinite n
  letI (n : ℕ) : Finite (FiniteDyadicTraversal d n) :=
    finite_finiteDyadicTraversal d n
  obtain ⟨T, hT⟩ := exists_seq_forall_proj_of_forall_finite
    (fun {i j} hij (U : FiniteDyadicTraversal d j) => U.truncate hij)
    (by intro i U; rfl)
    (by intro i j k hij hjk U; rfl)
    (by intro i U; exact Set.toFinite _)
  exact ⟨T, fun n => hT (Nat.le_succ n)⟩

end Causalean.Mathlib.Topology.SpaceFillingCurve
