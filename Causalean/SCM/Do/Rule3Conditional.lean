/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.Mathlib.Probability.Kernel.CondDistrib
public import Causalean.SCM.Do.Rule3
public import Causalean.SCM.Do.ValuesProjectionCI

/-! # Conditional Rule 3* (a.e. `obsCondKernel` form)

The joint-marginal Rule 3\* (`do_rule3_star` / `condDistrib_intervention_ancestral_eq`)
transports the *joint* law of an ancestrally-blocked outcome block across an
intervention. This file derives its **conditional Rule 3\*** consequence,
`p(Y | do(z), W) = p(Y | W)`, under the same strong non-ancestor premise, in an
almost-everywhere form. It does not formalize Pearl's full Rule 3 premise.

The mathematical content is a single disintegration fact: `condDistrib` depends
only on the joint pushforward `μ.map (X, Y)`, and Rule 3\* makes the two joint
pushforwards (under `do(Z)` and under the base model) literally equal on the
target/conditioning block.  No positivity or ratio infrastructure is required
because there is no do-side pinning here (unlike Rule 2); the intervention only
transports a marginal.

## Main declarations

* `condDistrib_eq_of_map_prod_eq` — generic: equal joint pushforwards ⇒ equal `condDistrib`.
* `obsKernel_map_prodWY_eq` — Rule 3\* specialized to the `(W, Y)` joint pushforward.
* `obsKernel_map_W_eq` — Rule 3\* specialized to the `W`-marginal.
* `do_rule3_star_conditional_condDistrib` — conditional Rule 3*, literal `condDistrib` form.
* `do_rule3_star_conditional` — conditional Rule 3*, headline a.e. `obsCondKernel` form.

## References

* Basic Concepts.tex, Proposition (do-Calculus), Rule 3*.
* Malinsky, Shpitser & Richardson (2019), for Rule 3*.
* Pearl (2009), Causality, Chapter 3, for comparison with the full Rule 3.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

open Causalean.Mathlib.Probability.Kernel

namespace Causalean

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 0. Disintegration uniqueness (the whole mathematical core)
-- ============================================================

-- ============================================================
-- § 1. Rule 3* pushforward specializations
-- ============================================================

/-- Rule 3\* on the `(W, Y)` joint pushforward.

    Under the ancestral no-descendant premise `hNoDesc`, the joint law of the
    conditioning block `W` paired with the target block `Y` is the same after
    intervening on `Z` as under the base model with the induced fixed values.
    This is `condDistrib_intervention_ancestral_eq` at outcome block `T := Y ∪ W`,
    read through the sub-projections `W ⊆ Y ∪ W` and `Y ⊆ Y ∪ W`. -/
theorem obsKernel_map_prodWY_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s').map
        (fun ω =>
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) ω,
           valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY) ω))
      =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
        (fun ω => (valuesProjection hW ω, valuesProjection hY ω)) := by
  -- Factor both pair-maps through the single `Y ∪ W` projection, then apply
  -- Rule 3* (`condDistrib_intervention_ancestral_eq`) on that union block.
  classical
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let U := Y ∪ W
  have hU : U ⊆ M'.observed := Finset.union_subset hY hW
  have hU_do : U ⊆ M2.observed := by
    simpa [M2, SCM.fixSet_observed] using hU
  have hW_U : W ⊆ U := Finset.subset_union_right
  have hY_U : Y ⊆ U := Finset.subset_union_left
  let pairU : ValuesOn U (swigΩ Ω) →
      ValuesOn W (swigΩ Ω) × ValuesOn Y (swigΩ Ω) :=
    fun ω => (valuesProjection hW_U ω, valuesProjection hY_U ω)
  have hpairU_meas : Measurable pairU := by
    exact (measurable_valuesProjection hW_U).prodMk (measurable_valuesProjection hY_U)
  have hPair_do_comp :
      pairU ∘ valuesProjection hU_do =
        (fun ω : M2.ObservedValues =>
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) ω,
           valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY) ω)) := by
    funext ω
    apply Prod.ext
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hW_U hU_do).symm ω
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hY_U hU_do).symm ω
  have hPair_base_comp :
      pairU ∘ valuesProjection hU =
        (fun ω : M'.ObservedValues => (valuesProjection hW ω, valuesProjection hY ω)) := by
    funext ω
    apply Prod.ext
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hW_U hU).symm ω
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hY_U hU).symm ω
  have hR3 :
      (M2.obsKernel s').map (valuesProjection hU_do) =
        (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
          (valuesProjection hU) := by
    simpa [M2, U] using
      condDistrib_intervention_ancestral_eq M' Z hZ_obs hZ_fixed U hU
        (fun z hz v hv => hNoDesc v (by simpa [U] using hv) z hz) s'
  change (M2.obsKernel s').map
      (fun ω =>
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) ω,
         valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY) ω))
    =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
      (fun ω => (valuesProjection hW ω, valuesProjection hY ω))
  rw [← hPair_do_comp, ← hPair_base_comp]
  rw [← MeasureTheory.Measure.map_map hpairU_meas (measurable_valuesProjection hU_do)]
  rw [← MeasureTheory.Measure.map_map hpairU_meas (measurable_valuesProjection hU)]
  exact congrArg (MeasureTheory.Measure.map pairU) hR3

/-- Rule 3\* on the `W`-marginal.

    Under the ancestral no-descendant premise, the marginal law of the
    conditioning block `W` is unchanged by intervening on `Z`.  This is
    `condDistrib_intervention_ancestral_eq` at outcome block `T := W`. -/
theorem obsKernel_map_W_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hW : W ⊆ M'.observed)
    (hNoDesc : ∀ v ∈ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s').map
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
      =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
        (valuesProjection hW) :=
  condDistrib_intervention_ancestral_eq M' Z hZ_obs hZ_fixed W hW
    (fun z hz v hv => hNoDesc v hv z hz) s'

-- ============================================================
-- § 2. Conditional Rule 3*
-- ============================================================

/-- **Conditional Rule 3* (literal `condDistrib` form).** Fix [a do-set whose random copies are
    observed and whose fixed copies have not already been intervened on](hyp:hZ_obs,hZ_fixed),
    [an observed target block](hyp:hY), and [an observed conditioning block](hyp:hW). If [no fixed
    copy of an intervened node is an ancestor of the target or conditioning block](hyp:hNoDesc),
    then at [each post-intervention fixed assignment](hyp:s'), [the conditional distribution of
    the target given the conditioning block is the same after intervention as under the base
    model at the corresponding fixed assignment](goal).

    In probability notation:

        p( Y(z) | W(z) )_{M'.fixSet Z} = p( Y | W )_{M'}.

    Because Rule 3\* makes the two `(W, Y)` joint laws literally equal
    (`obsKernel_map_prodWY_eq`) and `condDistrib` depends only on the joint law
    (`condDistrib_eq_of_map_prod_eq`), the two conditional distributions are
    literally equal — no almost-everywhere qualifier is needed here. -/
theorem do_rule3_star_conditional_condDistrib
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ProbabilityTheory.condDistrib
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY))
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
        ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s')
      =
    ProbabilityTheory.condDistrib (valuesProjection hY) (valuesProjection hW)
        (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')) :=
  condDistrib_eq_of_map_prod_eq
    (obsKernel_map_prodWY_eq M' Z hZ_obs hZ_fixed Y W hY hW hNoDesc s')

/-- **Conditional Rule 3* (headline, a.e. `obsCondKernel` form).** The non-ancestor
    specialization of deletion of actions, stated against the project's jointly-measurable
    conditional kernel. Fix [a do-set `Z` of nodes whose random copies are observed
    in the base model and whose fixed nodes have not already been intervened
    on](hyp:hZ_obs,hZ_fixed), [an outcome block `Y`](hyp:hY) and [a conditioning
    block `W`](hyp:hW) of observed variables. If [none of the fixed copies of `Z`'s
    nodes is an ancestor, in the intervention SWIG graph, of any node in
    `Y ∪ W`](hyp:hNoDesc), then at [a post-intervention fixed assignment](hyp:s'),
    [for almost every value `w` of `W` under the
    base model's `W`-marginal, the `Y`-given-`W` conditional kernel of the
    model intervened at `do(Z)` equals the `Y`-given-`W` conditional kernel of the
    base model, both evaluated at the corresponding fixed values](goal).

    This is the conditional analogue of the joint Rule 3\* `do_rule3_star`.
    Its non-ancestor premise on all of `Y ∪ W` is stronger than the premise of
    Pearl's full Rule 3.

    The a.e. qualifier is intrinsic to `obsCondKernel` (a disintegration
    representative), not to the intervention: the underlying conditional
    distributions are literally equal by `do_rule3_star_conditional_condDistrib`; the
    common base measure is the (Rule-3\*-equal) `W`-marginal. -/
theorem do_rule3_star_conditional
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    (fun w => (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (s', w))
      =ᵐ[(M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
            (valuesProjection hW)]
    (fun w => M'.obsCondKernel Y W hY hW
          (M'.fixSetProj Z hZ_obs hZ_fixed s', w)) := by
  -- Bridge both `obsCondKernel`s to `condDistrib`, rewrite the do-side base to the
  -- common `W`-marginal (`obsKernel_map_W_eq`) and the do-side conditional to the
  -- base conditional (`do_rule3_star_conditional_condDistrib`), then chain a.e. equalities.
  have h1 := (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel_ae_eq_condDistrib Y W
    ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
    ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) s'
  have h2 := M'.obsCondKernel_ae_eq_condDistrib Y W hY hW
    (M'.fixSetProj Z hZ_obs hZ_fixed s')
  have hbase := obsKernel_map_W_eq M' Z hZ_obs hZ_fixed W hW
    (fun v hv d hd => hNoDesc v (Finset.mem_union_right _ hv) d hd) s'
  have hcd := do_rule3_star_conditional_condDistrib M' Z hZ_obs hZ_fixed Y W hY hW hNoDesc s'
  rw [hbase] at h1
  rw [hcd] at h1
  exact h1.trans h2.symm

end SCM

end Causalean
