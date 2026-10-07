/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Restricted do-calculus interfaces (SCM skeleton, single-intervention form)

This file gives Rule 1 together with restricted sufficient forms of Rule 2
and Rule 3*.  The results operate directly on an SCM `M'`; an existing outer
intervention may be represented by taking `M' := M.fixSet X …`.  The Rule 2
interface additionally requires non-descendancy in both relevant graphs and
product absolute continuity, while the Rule 3* interface assumes that every
target fixed copy is non-ancestral to the entire outcome/conditioning block.
They therefore do not state Pearl's Rules 2 and 3 at their full graphical
generality.

## Main declarations

* `do_rule1` — Insertion/deletion of observations (CI under the mutilated model)
* `do_rule2_kernel_of_nondescendant_product_ae` — restricted action/observation exchange
  under non-descendancy and product absolute continuity
* `do_rule3_star` — Rule 3* insertion/deletion of actions under a non-ancestor premise

## References

* Basic Concepts.tex, Proposition (do-Calculus), for the split-language outline.
* Pearl (2009), Causality, Chapter 3, for the full rules used as comparison points.
* Malinsky, Shpitser & Richardson (2019), for Rule 3*.
-/

module
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.Do.Rule2
public import Causalean.SCM.Do.Rule2AE
public import Causalean.SCM.Do.Rule3
public import Causalean.SCM.Model.InterventionSet
public import Causalean.SCM.Model.Induced
public import Causalean.SCM.Do.Overlap

/-! # Do-Calculus for Structural Causal Models

This file states Rule 1 and restricted sufficient forms of Rule 2 and Rule 3*
for structural causal models in a single-intervention form. The Rule 2 result
also assumes non-descendancy and product absolute continuity; the Rule 3* result
uses the stronger non-ancestor premise on the whole outcome/conditioning block.
These are sound interfaces used by the identification layer, not the full Pearl
rules at their stated graphical generality. -/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Restricted do-calculus interfaces — single-intervention SCM form
-- ============================================================

/-- **Rule 1: Insertion/deletion of observations (single-SCM form).** On any structural causal
    model `M'`, suppose [`Y`, `Z`, and `W` are all observed nodes of `M'`](hyp:hY,hZ,hW), and
    that [`Y` is d-separated from `Z` given `W` together with the fixed nodes `M'.fixed`, in the
    split graph `M'.dag`](hyp:hdSep). Then, at any fixed-value point [`s`](hyp:s), [`Y` and `Z`
    are conditionally independent given `W` under the observational kernel
    `M'.obsKernel s`](goal).

    The d-sep conditioning set is `W ∪ M'.fixed` — the split's fixed
    nodes are constants (kernel parameters) under `obsKernel s`, so
    extending the conditioning set by `M'.fixed` is free at the kernel
    level.

    **Pearl correspondence.**  Taking `M' := M.fixSet X …` recovers
    Pearl's two-layer Rule 1 `(Y ⊥ Z | W, X)_{G_{\overline X}}` —
    the outer `do(X)` is absorbed into the choice of `M'`.

    **Proof.**  Delegates to `SCM.globalMarkov_with_fixed` on `M'`,
    splitting the condition into the observed part `W` and the fixed
    part `M'.fixed`. -/
theorem do_rule1 (M' : Causalean.SCM N Ω)
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    (Y Z W : Finset (SWIGNode N))
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))] [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Z (swigΩ Ω))] [Nonempty (ValuesOn Z (swigΩ Ω))]
    (hY : Y ⊆ M'.observed)
    (hZ : Z ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hdSep : M'.dag.dSep Y Z (W ∪ M'.fixed))
    (s : M'.FixedValues) :
    ObsCondIndep M' Y Z W hY hZ hW (M'.obsKernel s) := by
  have hDisj_YZ : Disjoint Y Z := hdSep.1
  have hDisj_YW : Disjoint Y W :=
    Disjoint.mono_right Finset.subset_union_left hdSep.2.1
  have hDisj_ZW : Disjoint Z W :=
    Disjoint.mono_right Finset.subset_union_left hdSep.2.2.1
  exact M'.globalMarkov_with_fixed Y Z W M'.fixed hY hZ hW (Finset.Subset.refl _)
    hdSep s

/-- **Rule 3*: insertion/deletion of actions (simplified joint-marginal form).** Fix a structural
    causal model `M'` and a treatment set `Z` for which [each member's random copy is already
    observed in `M'`](hyp:hZ_obs) and [each member's fixed copy is not yet among `M'`'s fixed
    nodes](hyp:hZ_fixed), together with outcome and conditioning sets [`Y`](hyp:hY) and
    [`W`](hyp:hW), both observed in `M'`. Suppose [no node of `Y ∪ W` is, in the model
    intervened on `Z`, a descendant of the fixed copy of any variable in `Z`](hyp:hNoDesc).
    For [any post-intervention fixed value](hyp:s'), [the joint law of `(Y, W)` under the intervened model
    equals the joint law of `(Y, W)` under the base model `M'` at the corresponding
    pre-intervention fixed value](goal).

    This is the node-splitting version of Pearl's Rule 3\* from
    Malinsky–Shpitser–Richardson (2019), in single-SCM form:

        (Y(z) ⊥⊥ z)_{M'.fixSet Z}   ⟹   p( Y(z) ) = p( Y )   on `M'`.

    We instantiate with outcome set `T := Y ∪ W`, so the conclusion is
    the *joint* marginal equality of `(Y, W)` under `do(Z)` on `M'`
    vs. under the base `M'`:

        p( Y(z), W(z) )_{M'.fixSet Z} = p( Y, W )_{M'}    if
        ( Y ∪ W  ⊥⊥  z )_{M'.fixSet Z}.

    Dividing by the (equal) `W`-marginals recovers conditional Rule 3*.
    A single hypothesis/conclusion pair here covers both the
    marginal and conditional forms.

    Hypothesis `hNoDesc`. It states `z_d ∉ An_{M'.fixSet Z}(v)` for
    every `d ∈ Z`, `v ∈ Y ∪ W`.  Because every `SWIGNode.fixed d` is a
    source in a SWIG graph, its only ancestor is itself, so d-connection
    from `z_d` to `v` given ∅ coincides with
    `z_d ∈ An_{M'.fixSet Z}(v)`.  Hence `hNoDesc` is equivalent to
    `(Y ∪ W ⊥⊥ z)_{M'.fixSet Z}`.

    Taking `M' := M.fixSet X …` gives this Rule 3* statement after an outer
    intervention. It does not by itself recover Pearl's full Rule 3.

    Relation to the full Rule 3. The unsimplified rule partitions
    `Z = Z₁ ⊔ Z₂` with `Z₁ = Z \ An_{M'}(W)` and a weaker two-part
    d-sep premise. Deriving that rule requires combining the partition with
    other do-calculus steps; it is not the statement proved here. Rule 3\* on
    the joint `Y ∪ W` is used because its kernel-level statement is a single
    clean marginal equality. The
    conditional form `p(Y | do(z), W) = p(Y | W)` is derived from this joint
    equality in `Rule3Conditional.lean` (`do_rule3_star_conditional`), in the honest
    a.e. `obsCondKernel` form — no positivity/ratio hypotheses are needed, since
    `condDistrib` depends only on the (Rule-3*-equal) joint law.

    Proof idea. Delegates to `SCM.condDistrib_intervention_ancestral_eq`
    with `T := Y ∪ W`, repackaging `hNoDesc` into the per-node form
    expected by that lemma. -/
theorem do_rule3_star (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor
        (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s').map
        (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm
            ▸ Finset.union_subset hY hW))
      =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
        (valuesProjection (Finset.union_subset hY hW)) :=
  SCM.condDistrib_intervention_ancestral_eq M' Z
    hZ_obs hZ_fixed (Y ∪ W)
    (Finset.union_subset hY hW)
    (fun z hz v hv => hNoDesc v hv z hz) s'

end SCM

end Causalean
