/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.IDAlgorithm
public import Causalean.SCM.ID.Density.CountingReference
public import Causalean.SCM.ID.DiscreteID.Positive

/-! # On-contract discrete soundness of the graphical ID assembly

`GraphicalThms.IDAlgorithm.id_sound` concludes over the model class
`fun M => DominatedObs M ref ∧ DiscretePositive M` on a standard graph,
parameterised by an arbitrary faithful reference family.  Instantiating that reference at the
counting measure and using that the counting reference dominates every model
(`dominatedObs_countingRef`), the model class collapses to the frozen
discrete-positive class `StandardDiscretePositive`.  The explicit standard-graph
guard excludes nonstandard graphs, while the explicit inhabitation premise in
the soundness theorem rules out an empty compatible model class.
-/

public section

open Causalean.Graph


namespace Causalean.SCM.ID

open Causalean.SCM Causalean.SCM.ID.DiscreteID
open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Discrete soundness of the ID assembly for the no-additional-fixing
(full-district) fragment (on-contract).** For [treatments](hyp:X), [outcomes](hyp:Y),
[a standard graph](hyp:G,hG), [an inhabited compatible positive class](hyp:hNonempty), and
[a successful no-fixing certificate](hyp:h),
[the query is identifiable from the observational law within that class](goal).

This is a *sound sufficient fragment* of Tian–Shpitser ID soundness, not
the recursive acceptance certificate: `idSucceeds` only certifies the case where every
post-intervention ancestral district is already a full c-component of the original
graph (no fixing sequence needed); the recursive case is `id_sound_rec`.  The
standard-graph guard, intervention-validity certificate, and condition `Y ⊆ G.observed`
put the query on its meaningful `doKernelY` branch. The inhabitation premise is needed to
exclude vacuous identification over an empty compatible class. Obtained from `id_sound` at the
counting reference by collapsing `DominatedObs · countingRef` (which holds for every model)
down to `StandardDiscretePositive` via `identifiableUnder_mono`. -/
theorem id_sound_discrete
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (hG : G.isStandard)
    (hNonempty : ∃ M : Causalean.SCM N Ω,
      M.toSWIGGraph = G ∧ StandardDiscretePositive M)
    (h : idSucceeds X Y G) :
    IdentifiableUnder G (fun _ => True) StandardDiscretePositive
      (interventionalQuery (Ω := Ω) X Y) := by
  have hdom :=
    id_sound X Y G (countingRef (Ω := Ω)) referenceFaithful_countingRef hG
      (by
        rcases hNonempty with ⟨M, hMG, hM⟩
        exact ⟨M, hMG, dominatedObs_countingRef M, hM.2⟩)
      h
  exact identifiableUnder_mono G (fun _ => True) (fun _ => True)
    (fun M => DominatedObs M (countingRef (Ω := Ω)) ∧ DiscretePositive M)
    StandardDiscretePositive (interventionalQuery (Ω := Ω) X Y)
    (fun _ h => h) (fun M hM => ⟨dominatedObs_countingRef M, hM.2⟩) hdom

end Causalean.SCM.ID
