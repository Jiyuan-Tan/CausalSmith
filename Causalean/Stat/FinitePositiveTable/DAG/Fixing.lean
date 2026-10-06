module
public import Causalean.Stat.FinitePositiveTable.DAG.Elimination

/-!
# Sequential fixing removes local DAG factors

This module proves the graph-independent fixing expansion requested by downstream consumers:
for any list of distinct vertices, sequential `FinitePositiveTable` fixing conditional on the
original DAG parent sets equals the product of precisely the local factors whose vertices have
not been fixed.  Hence the result is a normalized kernel over the remaining coordinates with
the fixed coordinates acting as arguments.
-/

public section

open Finset

noncomputable section

namespace Causalean.Stat.FinitePositiveTable.DAG

open Causalean.Graph
open Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}
variable {G : DAG V} {p : PositiveTable r}

namespace PositiveDAGTableFactorization

/-- A [factorized table](hyp:fac), [vertex list](hyp:vertices), and [proof that its vertices are
distinct](hyp:hvertices) give [the sequential-fixing expansion as the truncated local-factor
product](goal). -/
theorem fixSequence_eq_remainingFactorKernel
    (fac : PositiveDAGTableFactorization G p) (vertices : List V)
    (hvertices : vertices.Nodup) :
    fixSequence p (parentFixingSteps G vertices) =
      fac.remainingFactorKernel vertices.toFinset := by
  /-
  Induct on `vertices`.  At the empty list, use `fac.mass_eq_jointMass` and identify the
  `univ \ ∅` product with `jointMass`.  At `v :: vs`, rewrite the first kernel by the
  induction invariant for the already fixed set and apply
  `fixKernelCoordinate_remainingFactorKernel`; `List.Nodup` supplies `v ∉ vs.toFinset`.
  The recursion direction of `fixKernelSequence` may make it cleaner to strengthen the
  induction statement to start from an arbitrary already-fixed set.
  -/
  have hstart : p.mass = fac.remainingFactorKernel ∅ := by
    funext x
    rw [fac.mass_eq_jointMass]
    unfold Causalean.Graph.FiniteDensity.PositiveFiniteDAGMechanism.jointMass
      remainingFactorKernel
    simp
  have haux : ∀ (done : Finset V) (vs : List V),
      vs.Nodup → Disjoint done vs.toFinset →
      fixKernelSequence (fac.remainingFactorKernel done) (parentFixingSteps G vs) =
        fac.remainingFactorKernel (done ∪ vs.toFinset) := by
    intro done vs hnodup hdisj
    induction vs generalizing done with
    | nil =>
        simp [parentFixingSteps, fixKernelSequence]
    | cons v vs ih =>
        simp only [List.nodup_cons] at hnodup
        simp only [List.toFinset_cons, Finset.disjoint_insert_right] at hdisj
        rw [show parentFixingSteps G (v :: vs) =
          { coordinate := v, conditioning := G.parents v } :: parentFixingSteps G vs by rfl]
        rw [fixKernelSequence]
        rw [fac.fixKernelCoordinate_remainingFactorKernel done hdisj.1]
        rw [ih (insert v done) hnodup.2]
        · congr 1
          ext w
          simp
        · rw [Finset.disjoint_insert_left]
          exact ⟨by simpa using hnodup.1, hdisj.2⟩
  unfold fixSequence
  rw [hstart]
  simpa using haux ∅ vertices hvertices (by simp)

/-- A [factorized table](hyp:fac), [distinct vertex list](hyp:vertices,hvertices), and [profile](hyp:x)
give [unit mass for the sequentially fixed kernel in that fixed-coordinate row](goal). -/
theorem fixSequence_row_normalized
    (fac : PositiveDAGTableFactorization G p) (vertices : List V)
    (hvertices : vertices.Nodup) (x : ProfileSpace r) :
    kernelMarginalMass (fixSequence p (parentFixingSteps G vertices))
      vertices.toFinset x = 1 := by
  rw [fixSequence_eq_remainingFactorKernel fac vertices hvertices]
  exact fac.remainingFactorKernel_row_normalized vertices.toFinset x

/-- A [factorized table](hyp:fac), [vertex list](hyp:vertices), and [proof that its vertices are
distinct](hyp:hvertices) give [a pointwise strictly positive sequentially fixed kernel](goal). -/
theorem fixSequence_strictlyPositive
    (fac : PositiveDAGTableFactorization G p) (vertices : List V)
    (hvertices : vertices.Nodup) :
    (fixSequence p (parentFixingSteps G vertices)).IsStrictlyPositive := by
  rw [fixSequence_eq_remainingFactorKernel fac vertices hvertices]
  exact fac.remainingFactorKernel_pos vertices.toFinset

end PositiveDAGTableFactorization

end Causalean.Stat.FinitePositiveTable.DAG
