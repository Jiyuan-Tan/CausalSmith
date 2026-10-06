/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Identification overlap predicate

The kernel-level absolute-continuity (overlap) predicate used as an explicit
support assumption by backdoor / frontdoor identification theorems.

## Main definition

* `Rule2JointOverlap M' Z hZ_obs hZ_fixed W hZrW s'` — the do-intervened
  model's `(Z.random ∪ W)`-marginal is absolutely continuous w.r.t. the base
  model's `(Z.random ∪ W)`-marginal.  Continuous-friendly: no pointwise
  singleton positivity is required.

-/

module
public import Causalean.SCM.Model.SCM
public import Causalean.SCM.Model.Kernel
public import Causalean.SCM.Model.InterventionSet
public import Causalean.SCM.Do.Rule2Kernel.Helpers

/-! # Overlap

This file defines a kernel-level support condition used by identification
rules. The predicate `Rule2JointOverlap` requires the
post-intervention marginal on `Z.random ∪ W` to be absolutely continuous with
respect to the corresponding observational marginal. This continuous-friendly
condition is an explicit assumption of backdoor/frontdoor interfaces; it is not
implied merely by discreteness, measurability of structural functions, or an
unchanged latent law. -/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory
open Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For [a finite node-label set](hyp:N), [measurable node-value spaces](hyp:Ω),
    [a structural causal model](hyp:M'), [an intervention target set](hyp:Z),
    [proof that each target is an observed random node not already fixed](hyp:hZ_obs,hZ_fixed),
    [an additional observed-node set](hyp:W), [proof that the random copies of
    the targets together with that set are observed](hyp:hZrW), and [a fixed-value
    assignment after intervention](hyp:s'), [Rule 2 joint overlap](goal) means
    that the post-intervention observational marginal on those nodes is absolutely
    continuous with respect to the corresponding pre-intervention observational
    marginal at the projected fixed-value assignment.

    This is an explicit support assumption with no pointwise singleton
    positivity requirement. Discreteness alone does not imply it, and neither
    do measurability of the structural functions and equality of latent laws.
    It is used by backdoor / frontdoor identification interfaces. -/
def Rule2JointOverlap (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    Prop :=
  ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s'
      |>.map (valuesProjection
        ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW)))
    ≪
  (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')
      |>.map (valuesProjection hZrW))

end Causalean.SCM.ID
