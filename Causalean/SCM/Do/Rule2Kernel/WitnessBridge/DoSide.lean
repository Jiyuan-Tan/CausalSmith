/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.MeasurableSpace.MeasureEquality
public import Causalean.Mathlib.Probability.Kernel.CondDistrib
public import Causalean.Mathlib.Probability.Kernel.CondDistribWitness
public import Causalean.SCM.Do.CutsetDSep
public import Causalean.SCM.Do.GlobalMarkov
public import Causalean.SCM.Do.Rule2
public import Causalean.SCM.Do.Rule2Kernel.DiscreteZHelpers
public import Causalean.SCM.Do.Rule2Kernel.Helpers
public import Causalean.SCM.Do.Rule2Kernel.Structural.StructCrossSCM
public import Causalean.SCM.Do.Rule2Kernel.WitnessBridge.Cutset
public import Causalean.SCM.Do.Rule2Kernel.WitnessBridge.ObsSide
public import Causalean.SCM.Do.Rule3
public import Causalean.SCM.Model.CutsetLatent
public import Causalean.SCM.Model.Kernel

/-!
# Cross-SCM `obsCondKernel` identity via the posterior witness kernel

This file isolates the genuinely-hard analytic step of the continuous-`Z`
Rule 2 (backdoor) argument and assembles the cross-SCM bridge
`obsCondKernel_fixSet_M1_eq_ae_product` around it.

## Posterior witness kernel

Both the obs-side and the do-side equal the **posterior** witness kernel

    `(condDistrib C_W (πW ∘ E) μ_lat).map (h t w)`

where `μ_lat = M.latentProduct`, `E = M.evalMap s`, `C_W = M.cutsetLatent Y (Zr∪W)`
is the latent cut-set, and `h` is the cut-set override map.  This is the law of
`Y | W` under the *posterior* of the cut-set given `W`, which — crucially —
respects the W–Y confounding allowed by the backdoor criterion.  (The old
`obsCondKernel_struct` route pushed the *prior* latent law forward, giving
`Y | do(C)`, which is wrong under confounding; that route is deleted.)

The spine is:

* `condDistrib_map_comp` (Mathlib helper): transport the obs-level
  `condDistrib π_Y π_{Zr∪W} (obsKernel s)` onto the latent space
  `latentProduct`, where `π ∘ E` are the pulled-back coordinate maps.
* `condDistrib_map_of_condDistrib_fst_eq` (witness lemma, `CondDistribWitness.lean`):
  given the pointwise factorization `Y = h X Z C` and the conditional
  independence `C ⊥ X | Z` (in `condDistrib`-equality form), it yields the
  posterior witness-kernel form of `condDistrib Y (X,Z)`.
* the do-side under `M2 := M'.fixSet Z` mirrors the obs-side (random `Zr` has no
  children in `M2`), and the two witness kernels are identified via
  `fixSet_latentProduct_compat` plus the `fillZrW` override agreement; positivity
  (Rule 3*) transports onto the product `νZ ⊗ₘ μW`.

## Analytic cores

The construction is assembled from the following named lemmas:

* `cutset_factor_pointwise` — the pointwise factorization
  `π_Y ∘ E = h (π_Zr∘E) (π_W∘E) C_W`, together with the OFF-diagonal override
  characterization `h zr w' (π_{C_W} ℓ) = evalMap_overrideC … (valuesUnionMk zr w') ℓ`
  (needed do-side, where the treatment is pinned at `t` off the M1 diagonal).
* `cutset_condIndep_condDistrib` — the CI `C_W ⊥ (π_Zr∘E) | (π_W∘E)` under
  `latentProduct`, in the `condDistrib`-pair form the witness lemma consumes,
  from `cutsetLatent_dSep_of_dSep` + `full_globalMarkov_with_fixed`.
* `obsSide_eq_witness`, `doSide_eq_witness` — the two witness-kernel identities.
* `doSide_M2_pullback_eq_M1_witness` — the `fillZrW` cross-SCM identification of the
  `M2`-pullback `W`-conditional with the M1 witness kernel.  Closed via the no-X
  witness corollary `condDistrib_map_of_funext` (`Mathlib/CondDistribWitness.lean`)
  plus the override chain `evalMap_overrideC_at_self`@M2 →
  `evalMap_overrideC_dropZr_on_fillZrW` → `evalMap_overrideC_fixSet_compat_on_fillZrW`
  → the override characterization of `h`.
* `obsCondKernel_fixSet_M1_eq_ae_product` — the product-form connect + positivity
  transport (consumed by `condDistrib_fixSet_cross_SCM_bridge` in `Rule2AE`).
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

open Causalean.Mathlib.MeasureTheory.MeasurableSpace

open Causalean.Mathlib.Probability.Kernel

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1000000 in
-- The cross-SCM override-compat unfolding (`evalMap_overrideC_fixSet_compat_on_fillZrW`
-- transported through `evalMap_overrideC_eq` at each `Y`-node) is `whnf`-heavy, so the
-- default heartbeat budget is raised for this single filled-assignment identification lemma.
/-- **Do-side cross-SCM core: the M2-pullback `W`-conditional on
    `M2.latentProduct` equals the M1 posterior witness kernel.**

    This is the genuinely-new analytic content of the do-side bridge, isolated
    *after* the mechanical Step-A transport (`condDistrib_map_comp`@M2).  The LHS
    is the conditional law of `π_Y ∘ E2` given `π_W ∘ E2` under `M2.latentProduct`
    (`E2 := M2.randomToObserved ∘ M2.evalMap s'`, `s' := fixSetExtend s0 t`);
    the RHS is `M1`'s posterior witness kernel `(condDistrib C_W (π_W∘E1)
    M1.latentProduct w).map (h t w)` (`C_W := M'.cutsetLatent Y (Zr∪W)`,
    `E1 := randomToObserved ∘ M'.evalMap s0`).

    **Content (M2 witness chain + cross-SCM identification).**  At `M2`, random
    `Zr` is childless (`fixSet_random_not_isAncestor`), so `Y` factors through
    `(W, C_W@M2)` with no treatment coordinate; the witness lemma
    `condDistrib_map_of_condDistrib_fst_eq` (with the `M2` cut-set factorization
    `cutset_factor_pointwise`@M2 and the `M2` cut-set CI
    `cutset_condIndep_condDistrib`@M2) yields the `M2` posterior witness kernel.
    The two witness kernels are then identified along the `fillZrW` assignment via
    `fixSet_latentProduct_compat` (`M2.latentProduct.map reindex = M1.latentProduct`)
    and `evalMap_overrideC_fixSet_compat_on_fillZrW` (override maps agree on
    observed nodes), with the `W`-coordinate aligned by `fixSet_evalMap_nonAnc_compat`
    (`W` non-descendant via `hWNonDesc`) — needing the cross-SCM cut-set identity
    `M2.cutsetLatent Y (Zr∪W) = M'.cutsetLatent Y (Zr∪W)` (Zr-avoidance automatic
    at M2 since `Zr` is childless).

    This uses the posterior witness-kernel construction and does not rely on
    the retired rectangle identity `obsKernel_fixSet_rect_eq`.

    The theorem isolates the M2-side witness chain plus the cross-SCM
    identification of the M2 witness kernel with the M1 witness kernel, so the
    surrounding Step-A reduction can use it as a named bridge. -/
theorem doSide_M2_pullback_eq_M1_witness
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    [StandardBorelSpace M'.RandomValues]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s0 : M'.FixedValues)
    (t : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
    (h : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) → ValuesOn W (swigΩ Ω)
            → ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω)
            → ValuesOn Y (swigΩ Ω))
    (hh : Measurable (fun p :
        (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
          × ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
        h p.1.1 p.1.2 p.2))
    (hoverride : ∀ (zr : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
          (w' : ValuesOn W (swigΩ Ω)) (ℓ : M'.LatentValues),
        h zr w'
            (valuesProjection (M'.cutsetLatent_subset Y
              (Z.image SWIGNode.random ∪ W)) ℓ)
          = M'.evalMap_overrideC hY hZrW s0 (valuesUnionMk zr w') ℓ) :
    (fun w => ProbabilityTheory.condDistrib
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
            ∘ fun ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues =>
              (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
                ((M'.fixSet Z hZ_obs hZ_fixed).evalMap
                  (M'.fixSetExtend Z hZ_obs hZ_fixed s0 t) ℓ))
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸
            (fun _ hw => hZrW (Finset.mem_union_right _ hw)))
            ∘ fun ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues =>
              (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
                ((M'.fixSet Z hZ_obs hZ_fixed).evalMap
                  (M'.fixSetExtend Z hZ_obs hZ_fixed s0 t) ℓ))
          (M'.fixSet Z hZ_obs hZ_fixed).latentProduct w)
      =ᵐ[(M'.obsKernel s0).map
        (valuesProjection (fun _ hw => hZrW (Finset.mem_union_right _ hw)))]
        (fun w => ((ProbabilityTheory.condDistrib
              (valuesProjection
                (M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
              (fun ℓ : M'.LatentValues =>
                valuesProjection (fun _ hw => hZrW (Finset.mem_union_right _ hw))
                  (M'.randomToObserved (M'.evalMap s0 ℓ)))
              M'.latentProduct) w).map (h t w)) := by
  classical
  have hW : W ⊆ M'.observed := fun _ hw => hZrW (Finset.mem_union_right _ hw)
  set M2 := M'.fixSet Z hZ_obs hZ_fixed with hM2
  set s' := M'.fixSetExtend Z hZ_obs hZ_fixed s0 t with hs'
  haveI : MeasureTheory.IsProbabilityMeasure M'.latentProduct := inferInstance
  haveI : MeasureTheory.IsFiniteMeasure M'.latentProduct := inferInstance
  set hY_M2 : Y ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY with hhY_M2
  set hW_M2 : W ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW with hhW_M2
  set hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW with hhZrW_M2
  -- The M2 / M1 observed-eval pullbacks.  Both act on `M'.LatentValues = M2.LatentValues`.
  set E2 : M2.LatentValues → M2.ObservedValues :=
    fun ℓ => M2.randomToObserved (M2.evalMap s' ℓ) with hE2_def
  set E1 : M'.LatentValues → M'.ObservedValues :=
    fun ℓ => M'.randomToObserved (M'.evalMap s0 ℓ) with hE1_def
  -- Cut-set subset (the SAME finset on the M1 side; latent index spaces agree by `rfl`).
  have hCWsub : M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W) ⊆ M'.unobserved :=
    M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)
  -- (P2): the `W`-projection of `E2` equals that of `E1` (W non-descendant of the do-targets).
  have hP2 : ∀ ℓ : M2.LatentValues,
      valuesProjection hW_M2 (E2 ℓ) = valuesProjection hW (E1 ℓ) := by
    intro ℓ; funext v
    have hvW : v.val ∈ W := v.property
    have hvObs : v.val ∈ M'.observed := hW v.property
    have hkey := fixSet_evalMap_nonAnc_compat M' Z hZ_obs hZ_fixed s' ℓ (v := v.val) hvObs
      (fun z hz => hWNonDesc z hz v.val hvW)
    rw [M'.fixSetProj_fixSetExtend Z hZ_obs hZ_fixed s0 t] at hkey
    change M2.evalMap s' ℓ _ = M'.evalMap s0 _ _
    rw [hkey]; rfl
  -- (P1): the `Y`-projection of `E2` is the M1 witness map at treatment `t`.
  -- Proof: M2's override at `Y` reduces — via `evalMap_overrideC_dropZr_on_fillZrW` and the
  -- cross-SCM compat `evalMap_overrideC_fixSet_compat_on_fillZrW` — to M1's override at the
  -- block value `valuesUnionMk t (π_W (E2 ℓ))`, which `hoverride` identifies with `h t ·`.
  have hP1 : ∀ ℓ : M2.LatentValues,
      valuesProjection hY_M2 (E2 ℓ)
        = h t (valuesProjection hW_M2 (E2 ℓ)) (valuesProjection hCWsub ℓ) := by
    intro ℓ
    -- Abbreviate the realized `W`-value of `E2 ℓ`.
    set w := valuesProjection hW_M2 (E2 ℓ) with hw_def
    -- (a) M2.evalMap_overrideC over `W` at its self-value equals `π_Y (E2 ℓ)`.
    have hself_W : (w : ValuesOn W (swigΩ Ω))
        = (fun v' : {v // v ∈ W} =>
            (M2.observedAt_observedIndex ⟨v'.val, hW_M2 v'.property⟩) ▸
              evalObservedAux M2 s' ℓ
                (M2.observedIndex ⟨v'.val, hW_M2 v'.property⟩).val
                (M2.observedIndex ⟨v'.val, hW_M2 v'.property⟩).isLt) := by
      funext v'
      change (E2 ℓ) ⟨v'.val, hW_M2 v'.property⟩ = _
      change M2.evalMap s' ℓ ⟨v'.val, _⟩ = _
      rw [M2.evalMap_observed s' ℓ _ (hW_M2 v'.property)]
    have hcW : M2.evalMap_overrideC hY_M2 hW_M2 s' w ℓ
            = valuesProjection hY_M2 (E2 ℓ) := by
      rw [hself_W, M2.evalMap_overrideC_at_self hY_M2 hW_M2 s' ℓ]
      funext v
      change _ = (E2 ℓ) ⟨v.val, hY_M2 v.property⟩
      change _ = M2.evalMap s' ℓ ⟨v.val, _⟩
      rw [M2.evalMap_observed s' ℓ _ (hY_M2 v.property)]
    -- (b) override over `W` = override over `Zr∪W` at the `fillZrW`-filled block (`dropZr`).
    have hdrop : M2.evalMap_overrideC hY_M2 hZrW_M2 s'
            (M'.fillZrW Z hZ_obs hZ_fixed W s' w) ℓ
          = M2.evalMap_overrideC hY_M2 hW_M2 s' w ℓ :=
      evalMap_overrideC_dropZr_on_fillZrW M' Z hZ_obs hZ_fixed Y W
        hY_M2 hZrW_M2 hDisj_YZr s' ℓ w
    -- (c) cross-SCM compat: M2 override over `Zr∪W` at `fillZrW` = M1 override over `Zr∪W`
    --     at `fillZrW`, base `fixSetProj s' = s0`, latent reindex = identity.
    have hcompat : M2.evalMap_overrideC hY_M2 hZrW_M2 s'
            (M'.fillZrW Z hZ_obs hZ_fixed W s' w) ℓ
          = M'.evalMap_overrideC hY hZrW s0 (valuesUnionMk t w) ℓ := by
      -- Rewrite the `M2`-side fill block to `valuesUnionMk t w` (`s' = fixSetExtend s0 t`).
      rw [hs', fillZrW_fixSetExtend M' Z hZ_obs hZ_fixed W s0 t w, ← hs']
      funext v
      -- unfold both overrides to `evalObservedAuxOverride` at the SAME node `v.val`.
      rw [evalMap_overrideC_eq M2 hY_M2 hZrW_M2 s' _ ℓ v,
          evalMap_overrideC_eq M' hY hZrW s0 _ ℓ v]
      -- the compat lemma compares the full-observed-output overrides at node `v.val`;
      -- both unfold to the same `evalObservedAuxOverride` value, so transport via it.
      have hcv := evalMap_overrideC_fixSet_compat_on_fillZrW M' Z hZ_obs hZ_fixed W
        hZrW_M2 s' w ℓ (v := v.val) (hY_M2 v.property)
      -- `hcv` (read right→left) equates M2 and M1 full-output overrides at `⟨v.val, _⟩`.
      rw [evalMap_overrideC_eq M2 (Finset.Subset.refl _) hZrW_M2 s' _ ℓ
            ⟨v.val, hY_M2 v.property⟩,
          evalMap_overrideC_eq M' (Finset.Subset.refl _) hZrW
            (M'.fixSetProj Z hZ_obs hZ_fixed s')
            _ _ ⟨v.val, hY v.property⟩] at hcv
      -- `s0 = fixSetProj s'`, `valuesUnionMk t w = fillZrW W s' w`, reindex ℓ = ℓ.
      rw [M'.fixSetProj_fixSetExtend Z hZ_obs hZ_fixed s0 t,
          fillZrW_fixSetExtend M' Z hZ_obs hZ_fixed W s0 t w] at hcv
      exact hcv.symm
    -- (d) `hoverride` identifies the M1 override at `(t, w)` with `h t w (π_{C_W} ℓ)`.
    rw [← hcW, ← hdrop, hcompat]
    exact (hoverride t w ℓ).symm
  -- Measurability of the M1 conditioning / cut-set maps (reuse the SCM helper).
  have hZmeas : Measurable (fun ℓ : M'.LatentValues => valuesProjection hW (E1 ℓ)) := by fun_prop
  have hCmeas : Measurable
      (valuesProjection (Ω := swigΩ Ω) hCWsub) := by fun_prop
  -- `H := fun w c => h t w c` packages the witness map at the fixed treatment `t`.
  have hH : Measurable (fun p : ValuesOn W (swigΩ Ω)
        × ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
        h t p.1 p.2) :=
    hh.comp (((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
  -- The no-treatment witness corollary on `M'.latentProduct`, conditioning on `π_W ∘ E1`.
  have hwit := ProbabilityTheory.condDistrib_map_of_funext (Ω := M'.LatentValues)
    (𝒵 := ValuesOn W (swigΩ Ω))
    (𝒞 := ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))
    (𝒴 := ValuesOn Y (swigΩ Ω))
    M'.latentProduct
    (Z := fun ℓ : M'.LatentValues => valuesProjection hW (E1 ℓ))
    (C := valuesProjection hCWsub) (H := fun w c => h t w c)
    hZmeas hCmeas hH
  -- The corollary's LHS factorized map `fun ℓ => h t (π_W (E1 ℓ)) (π_{C_W} ℓ)` equals `π_Y ∘ E2`.
  have hYeq : (fun ℓ : M'.LatentValues =>
        h t (valuesProjection hW (E1 ℓ)) (valuesProjection hCWsub ℓ))
      = fun ℓ : M2.LatentValues => valuesProjection hY_M2 (E2 ℓ) := by
    funext ℓ; rw [hP1 ℓ, hP2 ℓ]
  rw [hYeq] at hwit
  -- The base `M'.latentProduct.map (π_W ∘ E1)` equals `μW = (obsKernel s0).map π_W`.
  have hE1meas : Measurable (fun ℓ : M'.LatentValues =>
      M'.randomToObserved (M'.evalMap s0 ℓ)) := by fun_prop
  have hbaseμW : M'.latentProduct.map (fun ℓ : M'.LatentValues => valuesProjection hW (E1 ℓ))
      = (M'.obsKernel s0).map (valuesProjection hW) := by
    rw [M'.obsKernel_eq_latentProduct_map s0,
      MeasureTheory.Measure.map_map (measurable_valuesProjection hW) hE1meas]
    rfl
  rw [hbaseμW] at hwit
  -- The goal's LHS conditioning map `π_W ∘ E2` equals `π_W ∘ E1` (by (P2)); rewrite `hwit`'s
  -- conditioning back to the `E2`-form so its LHS matches the goal's LHS (defeq otherwise).
  have hWmapeq : (fun ℓ : M2.LatentValues => valuesProjection hW_M2 (E2 ℓ))
      = fun ℓ : M'.LatentValues => valuesProjection hW (E1 ℓ) := funext hP2
  convert hwit using 3
  congr 1

/-- **Do-side analytic core: the M2 `W`-conditional equals the M1 witness kernel.** Let
    `M'` be a structural causal model and `Z` a set of treatment names with [each
    treatment's pre-intervention node observed](hyp:hZ_obs) and [each treatment's
    post-intervention node not already fixed in `M'`](hyp:hZ_fixed), so that intervening on
    `Z` is well-formed; let `Y`, `W` be node sets with [`Y`, `W`, the treatments'
    pre-intervention nodes, and their union with `W` all observed](hyp:hY,hW,hZr,hZrW) and
    [`Y` disjoint from the treatments' pre-intervention nodes](hyp:hDisj_YZr). Suppose
    [no node of `W` is a descendant, in the intervened model's graph, of any treatment's
    post-intervention node](hyp:hWNonDesc), and let `h` be [a jointly measurable
    map](hyp:hh) that, at a baseline assignment `s0` to the original model's fixed nodes,
    [factors the realized outcome as `h` applied to the realized treatment value, the
    realized `W` value, and the latent cut-set's value](hyp:hfac) and additionally,
    [for every candidate treatment/`W` pair, agrees there with the outcome obtained by
    instead overriding the baseline assignment `s0` to that pair](hyp:hoverride). Then, at
    the intervened model's slice fixing the treatments to a value `t` and the remaining
    fixed nodes to `s0`, [the measure-level conditional law of `Y` given `W` equals, for
    almost every `w` under the `W`-marginal of the original model's observational kernel at
    `s0`, the pushforward under `h t w` of the original model's posterior conditional law of
    the latent cut-set given `W`](goal).

    Explicitly: at the extended base slice `s' := fixSetExtend s0 t`,

      `condDistrib π_Y π_W (M2.obsKernel s') w
         = (condDistrib C_W (π_W∘E1) M1.latentProduct w).map (h t w)`,

    `μW`-a.e. in `w`, where `μW = (M'.obsKernel s0).map π_W` and `M2 := M'.fixSet Z`.

    This is the genuinely-new analytic content of the do-side bridge.  It bundles
    the `M2`-side witness chain (transport the `M2` obs-level conditional onto
    `M2.latentProduct` via `condDistrib_map_comp`, then apply the witness lemma
    with the `M2` cut-set factorization — where random `Zr` is childless, so it
    contributes no treatment coordinate) together with the cross-SCM
    identification of the resulting `M2` witness kernel with the `M1` witness
    kernel (`fixSet_latentProduct_compat` + `evalMap_overrideC_fixSet_compat_on_fillZrW`),
    all transported onto the common `μW` base by Rule 3*'s `W`-marginal equality
    `obsKernel_fixSet_W_marginal_eq_M1_marginal` (with `fixSetProj_fixSetExtend`).

    This uses the posterior witness-kernel construction and does not rely on
    the retired rectangle identity `obsKernel_fixSet_rect_eq`.

    This is the full `M2`-witness mirror of `obsSide_eq_witness` plus the
    `fillZrW` cross-SCM kernel identification. It is isolated as a named bridge
    used by the surrounding `doSide_eq_witness` assembly for base alignment,
    the obsCondKernel/condDistrib bridge, and a.e. plumbing. -/
theorem doSide_M2_condDistrib_eq_M1_witness
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    (hZr : Z.image SWIGNode.random ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    [StandardBorelSpace M'.RandomValues]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s0 : M'.FixedValues)
    (t : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
    (h : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) → ValuesOn W (swigΩ Ω)
            → ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω)
            → ValuesOn Y (swigΩ Ω))
    (hh : Measurable (fun p :
        (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
          × ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
        h p.1.1 p.1.2 p.2))
    (hfac : ∀ ℓ : M'.LatentValues,
        valuesProjection hY (M'.randomToObserved (M'.evalMap s0 ℓ))
          = h (valuesProjection hZr (M'.randomToObserved (M'.evalMap s0 ℓ)))
              (valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
              (valuesProjection (M'.cutsetLatent_subset Y
                (Z.image SWIGNode.random ∪ W)) ℓ))
    (hoverride : ∀ (zr : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
          (w' : ValuesOn W (swigΩ Ω)) (ℓ : M'.LatentValues),
        h zr w'
            (valuesProjection (M'.cutsetLatent_subset Y
              (Z.image SWIGNode.random ∪ W)) ℓ)
          = M'.evalMap_overrideC hY hZrW s0 (valuesUnionMk zr w') ℓ) :
    (fun w => ProbabilityTheory.condDistrib
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY))
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
          ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel
            (M'.fixSetExtend Z hZ_obs hZ_fixed s0 t)) w)
      =ᵐ[(M'.obsKernel s0).map (valuesProjection hW)]
        (fun w => ((ProbabilityTheory.condDistrib
              (valuesProjection
                (M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
              (fun ℓ : M'.LatentValues =>
                valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
              M'.latentProduct) w).map (h t w)) := by
  classical
  set M2 := M'.fixSet Z hZ_obs hZ_fixed with hM2
  set s' := M'.fixSetExtend Z hZ_obs hZ_fixed s0 t with hs'
  set hY_M2 : Y ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY with hhY_M2
  set hW_M2 : W ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW with hhW_M2
  set μW := (M'.obsKernel s0).map (valuesProjection hW) with hμW
  -- Abbreviation: the M2 observed-eval pullback `E2`.
  set E2 : M2.LatentValues → M2.ObservedValues :=
    fun ℓ => M2.randomToObserved (M2.evalMap s' ℓ) with hE2_def
  have hE2meas : Measurable E2 := by
    have hev : Measurable (fun ℓ : M2.LatentValues => M2.evalMap s' ℓ) := by fun_prop
    exact M2.measurable_randomToObserved.comp hev
  have hπY : Measurable (valuesProjection (Ω := swigΩ Ω) hY_M2) := by fun_prop
  have hπW : Measurable (valuesProjection (Ω := swigΩ Ω) hW_M2) := by fun_prop
  -- Base alignment: the M2 `W`-marginal at the slice `s'` equals `μW` (Rule 3*).
  have hbase : (M2.obsKernel s').map (valuesProjection hW_M2) = μW := by
    have hRule3 := obsKernel_fixSet_W_marginal_eq_M1_marginal M' Z hZ_obs hZ_fixed W hW
      hWNonDesc s'
    rw [hμW]
    rw [show (M2.obsKernel s').map (valuesProjection hW_M2)
        = (M2.obsKernel s').map
            (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
        from rfl, hRule3,
      M'.fixSetProj_fixSetExtend Z hZ_obs hZ_fixed s0 t]
  -- Step A: transport the M2 LHS `condDistrib π_Y π_W (M2.obsKernel s')` onto
  -- `M2.latentProduct` via `obsKernel_eq_latentProduct_map` + `condDistrib_map_comp`.
  have hobs : M2.obsKernel s' = M2.latentProduct.map E2 :=
    M2.obsKernel_eq_latentProduct_map s'
  have hstepA := condDistrib_map_comp (𝒴 := ValuesOn Y (swigΩ Ω))
    M2.latentProduct (φ := E2) (g := valuesProjection hY_M2) (f := valuesProjection hW_M2)
    hE2meas hπY hπW
  -- `hstepA : condDistrib π_Y π_W (latentProduct.map E2)
  --            =ᵐ[(latentProduct.map E2).map π_W] condDistrib (π_Y∘E2) (π_W∘E2) latentProduct`.
  -- Align the base of `hstepA` to `μW`.
  have hbase' : (M2.latentProduct.map E2).map (valuesProjection hW_M2) = μW := by
    rw [← hobs]; exact hbase
  rw [hbase'] at hstepA
  -- Step B+C (isolated TRUE core): the M2-pullback condDistrib equals the M1 witness kernel.
  have hcore := doSide_M2_pullback_eq_M1_witness M' Z hZ_obs hZ_fixed Y W hY hZrW
    hDisj_YZr hWNonDesc s0 t h hh hoverride
  -- Align the goal's LHS (over `M2.obsKernel s'`) to `hstepA`'s LHS (over `latentProduct.map E2`)
  -- via `hobs`, handling the dependent `IsFiniteMeasure` instance with `subst`.
  refine Filter.EventuallyEq.trans ?_ (hstepA.trans hcore)
  have hcongr : (ProbabilityTheory.condDistrib (valuesProjection hY_M2)
        (valuesProjection hW_M2) (M2.obsKernel s'))
      = ProbabilityTheory.condDistrib (valuesProjection hY_M2)
        (valuesProjection hW_M2) (M2.latentProduct.map E2) := by
    congr 1
  rw [hcongr]

/-- **Do-side per-slice witness identity (M1-witness-kernel form).** Let `M'` be a
    structural causal model and `Z` a set of treatment names with [each treatment's
    pre-intervention node observed](hyp:hZ_obs) and [each treatment's post-intervention
    node not already fixed in `M'`](hyp:hZ_fixed); let `Y`, `W` be node sets with [`Y`,
    `W`, the treatments' pre-intervention nodes, and their union with `W` all
    observed](hyp:hY,hW,hZr,hZrW), [`Y` disjoint from the treatments' pre-intervention
    nodes](hyp:hDisj_YZr), and [those pre-intervention nodes disjoint from
    `W`](hyp:hDisj_ZrW). Suppose [no node of `W` is a descendant, in the intervened
    model's graph, of any treatment's post-intervention node](hyp:hWNonDesc), and let `h`
    be [a jointly measurable map](hyp:hh) that, at a baseline assignment `s0` to the
    original model's fixed nodes, [factors the realized outcome as `h` applied to the
    realized treatment value, the realized `W` value, and the latent cut-set's
    value](hyp:hfac), and additionally [for every candidate treatment/`W` pair agrees there
    with the outcome obtained by instead overriding the baseline assignment `s0` to that
    pair](hyp:hoverride). Then, at the intervened model's slice fixing the treatments to a
    value `t` and the remaining fixed nodes to `s0`, [for almost every `w` under the
    `W`-marginal of the original model's observational kernel at `s0`, the intervened
    model's conditional-probability kernel for `Y` given `W` at `(s', w)` equals the
    pushforward under `h t w` of the original model's posterior conditional law of the
    latent cut-set given `W`](goal).

    Explicitly, the do-model's `W`-conditional intervened at `t` equals

      `(condDistrib C_W (π_W∘E1) M1.latentProduct w).map (h t w)`,

    the SAME witness kernel `obsCondKernel_union_eq_witness`@M1 produces (so the
    export can connect the two by transitivity without any positivity assumption in
    *this* lemma).  The `h`/`hh`/`hfac` arguments are the M1 cut-set factorization
    data (obtained by the export from `cutset_factor_pointwise M' Y W Z … s0`,
    exactly as `obsSide_eq_witness` consumes them).

    This gives the per-slice comparison directly through posterior witness
    kernels, without using the retired rectangle identity `obsCondKernel_fixSet_eq`.

    * **LHS = M2 witness, then = M1 witness.**  Mirroring
      `obsCondKernel_union_eq_witness` at `M2` conditioned on `W` *alone* (random
      `Zr` has no children in `M2` — `fixSet_random_not_isAncestor` — so `Zr`
      contributes no treatment coordinate and `M2.cutsetLatent Y W` coincides with
      `M1.cutsetLatent Y (Zr∪W)`).  The two witness kernels are then identified on
      the `fillZrW` assignment via `fixSet_latentProduct_compat`
      (`M2.latentProduct.map (reindex) = M1.latentProduct`) and
      `evalMap_overrideC_fixSet_compat_on_fillZrW` (the override maps agree on
      observed nodes), with the `W`-marginals aligned by
      `obsKernel_fixSet_W_marginal_eq_M1_marginal` (Rule 3*).

    The theorem combines the `M2`-side mirror of the obs-side witness chain
    (`obsCondKernel_ae_eq_condDistrib`@M2 → `condDistrib_map_comp`@M2 → the
    `M2` cut-set factorization → the `M2` witness identity) with the cross-SCM
    identification of the `M2` witness kernel and the `M1` witness kernel,
    transported onto the common `μW` base via Rule 3*'s `W`-marginal equality. -/
theorem doSide_eq_witness
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    (hZr : Z.image SWIGNode.random ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    [StandardBorelSpace M'.RandomValues]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s0 : M'.FixedValues)
    (t : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
    (h : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) → ValuesOn W (swigΩ Ω)
            → ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω)
            → ValuesOn Y (swigΩ Ω))
    (hh : Measurable (fun p :
        (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
          × ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
        h p.1.1 p.1.2 p.2))
    (hfac : ∀ ℓ : M'.LatentValues,
        valuesProjection hY (M'.randomToObserved (M'.evalMap s0 ℓ))
          = h (valuesProjection hZr (M'.randomToObserved (M'.evalMap s0 ℓ)))
              (valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
              (valuesProjection (M'.cutsetLatent_subset Y
                (Z.image SWIGNode.random ∪ W)) ℓ))
    (hoverride : ∀ (zr : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
          (w' : ValuesOn W (swigΩ Ω)) (ℓ : M'.LatentValues),
        h zr w'
            (valuesProjection (M'.cutsetLatent_subset Y
              (Z.image SWIGNode.random ∪ W)) ℓ)
          = M'.evalMap_overrideC hY hZrW s0 (valuesUnionMk zr w') ℓ) :
    ∀ᵐ w ∂((M'.obsKernel s0).map (valuesProjection hW)),
      (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (M'.fixSetExtend Z hZ_obs hZ_fixed s0 t, w)
        = ((ProbabilityTheory.condDistrib
              (valuesProjection
                (M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
              (fun ℓ : M'.LatentValues =>
                valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
              M'.latentProduct) w).map (h t w) := by
  -- Witness-route per-slice identity, **M1-witness-kernel form**.  The LHS (the M2
  -- `W`-conditional intervened at `t`) equals the M1 posterior witness kernel at
  -- `(t, w)`. The M2 witness chain (`obsCondKernel_ae_eq_condDistrib`@M2 →
  -- `condDistrib_map_comp`@M2 → the M2 cut-set factorization with trivial `Zr`
  -- coordinate → the M2 witness identity) and the cross-SCM identification of the M2
  -- witness kernel with the M1 witness kernel via `fixSet_latentProduct_compat` +
  -- `evalMap_overrideC_fixSet_compat_on_fillZrW`, transported onto the common `μW`
  -- base by Rule 3* (`obsKernel_fixSet_W_marginal_eq_M1_marginal`).  The analytic
  -- core is isolated as `doSide_M2_condDistrib_eq_M1_witness`; here we discharge
  -- the assembly (obsCondKernel ↔ condDistrib bridge at M2 + base alignment).
  classical
  set M2 := M'.fixSet Z hZ_obs hZ_fixed with hM2
  set s' := M'.fixSetExtend Z hZ_obs hZ_fixed s0 t with hs'
  set hY_M2 : Y ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY with hhY_M2
  set hW_M2 : W ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW with hhW_M2
  set μW := (M'.obsKernel s0).map (valuesProjection hW) with hμW
  -- Base alignment: the M2 `W`-marginal at the slice `s'` equals `μW` (Rule 3* +
  -- `fixSetProj (fixSetExtend s0 t) = s0`).
  have hbase : (M2.obsKernel s').map (valuesProjection hW_M2) = μW := by
    have hRule3 := obsKernel_fixSet_W_marginal_eq_M1_marginal M' Z hZ_obs hZ_fixed W hW
      hWNonDesc s'
    rw [hμW]
    rw [show (M2.obsKernel s').map (valuesProjection hW_M2)
        = (M2.obsKernel s').map
            (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
        from rfl, hRule3,
      M'.fixSetProj_fixSetExtend Z hZ_obs hZ_fixed s0 t]
  -- Step 1: at M2, `obsCondKernel Y W (s', ·) =ᵐ condDistrib π_Y π_W (M2.obsKernel s')`,
  -- with base `(M2.obsKernel s').map π_W`.
  have h1 := M2.obsCondKernel_ae_eq_condDistrib Y W hY_M2 hW_M2 s'
  rw [hbase] at h1
  -- Step 2: the analytic core — that condDistrib equals the M1 witness kernel.
  have h2 := doSide_M2_condDistrib_eq_M1_witness M' Z hZ_obs hZ_fixed Y W hY hW hZr
    hZrW hDisj_YZr hWNonDesc s0 t h hh hfac hoverride
  -- Both `h1` and `h2` are stated over the base `μW`; chain.
  filter_upwards [h1, h2] with w hw1 hw2
  -- `hw1 : M2.obsCondKernel Y W (s', w) = condDistrib π_Y π_W (M2.obsKernel s') w`
  -- `hw2 : condDistrib π_Y π_W (M2.obsKernel s') w = witness`
  rw [hw1, hw2]

/-- **Product-form cross-SCM bridge for the do-side conditional kernel.** Let `M'` be a
    structural causal model and `Z` a set of treatment names with [each treatment's
    pre-intervention node observed](hyp:hZ_obs) and [each treatment's post-intervention
    node not already fixed in `M'`](hyp:hZ_fixed); let `Y`, `W` be node sets with [`Y`,
    `W`, the treatments' pre-intervention nodes, and their union with `W` all
    observed](hyp:hY,hW,hZr,hZrW), [`Y` disjoint from the treatments' pre-intervention
    nodes](hyp:hDisj_YZr), and [those pre-intervention nodes disjoint from
    `W`](hyp:hDisj_ZrW). Suppose that, in the intervened model's graph, [no node of `W`
    is a descendant of any treatment's post-intervention node](hyp:hWNonDesc), that, in
    the original model's graph, [no node of `W` is a descendant of any treatment's
    pre-intervention node](hyp:hWNonDescM1), and that [in the intervened model's graph,
    `Y` is d-separated from the treatments' pre-intervention nodes given `W` together with
    the intervened model's fixed nodes](hyp:hdSep). Assume also, at a baseline assignment
    `s0` to the original model's fixed nodes, [an overlap condition: the pushforward, under
    combining a treatment value with a `W` value, of the product of the treatments'
    pre-intervention marginal law and the `W`-marginal law (both taken from the original
    model's observational kernel at `s0`) is absolutely continuous with respect to the
    original model's marginal law on the treatments' pre-intervention nodes together with
    `W`, again at `s0`](hyp:_hPositivity_ae). Then [for almost every pair `(t, w)` drawn
    from that product law, the intervened model's conditional-probability kernel for `Y`
    given `W`, evaluated at treatment value `t` and conditioning value `w`, equals the
    original model's conditional-probability kernel for `Y` given the union of the
    treatments' pre-intervention nodes and `W`, evaluated at the combined value `(t,
    w)`](goal).

    Explicitly, for `(νZ ⊗ₘ const μW)`-a.e. `(t, w)`, the do-model `W`-conditional intervened
    at `t` equals the original model's `(Zr∪W)`-conditional at the filled point
    `valuesUnionMk t w`.  Consumed by `condDistrib_fixSet_cross_SCM_bridge`
    (`Rule2AE.lean`).

    **Witness-route assembly** (replacing the deleted, mis-routed
    `obsCondKernel_struct` chain):

    * Obs side: `obsCondKernel_ae_eq_condDistrib` pins
      `M1.obsCondKernel Y (Zr∪W) (s0, ·) =ᵐ condDistrib π_Y π_{Zr∪W} (obsKernel s0)`;
      `condDistrib_map_comp` (with `φ = randomToObserved ∘ evalMap s0`) transports
      this onto `latentProduct`; reparametrizing the `(Zr∪W)`-conditioning by the
      disjoint-union iso `valuesUnionEquiv` (via
      `condDistrib_comp_right_measurableEquiv`) lands it on the pair
      `(π_Zr∘E, π_W∘E)`, where `obsSide_eq_witness` rewrites it as the posterior
      witness kernel `(condDistrib C_W (π_W∘E) latentProduct).map (h t w)`.
    * Do side: the same chain under `M2 := M'.fixSet Z` (random `Zr` has no
      children, `fixSet_random_not_isAncestor`), giving the M2 witness kernel; the
      two witness kernels coincide along the `fillZrW` assignment via `fixSet_latentProduct_compat`
      + `evalMap_overrideC_fixSet_compat_on_fillZrW`.
    * Positivity: `obsKernel_fixSet_W_marginal_eq_M1_marginal` (Rule 3*) +
      `hPositivity_ae` transport the obs-side a.e. statement onto the product
      `νZ ⊗ₘ μW`, where the do-side is natively pinned (Fubini via
      `ae_compProd_of_ae_ae`).

    The theorem assembles the iso reparametrization (`valuesUnionEquiv` ↔ pair
    conditioning), the do-side `M2` mirror of `obsSide_eq_witness`, the `fillZrW`
    identification of the two witness kernels, and the product/positivity Fubini
    lift, using `cutset_factor_pointwise` and `cutset_condIndep_condDistrib` as
    the cut-set cores. -/
theorem obsCondKernel_fixSet_M1_eq_ae_product
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    (hZr : Z.image SWIGNode.random ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W,
      ¬ M'.dag.isAncestor (SWIGNode.random D) w)
    (hdSep : (M'.fixSet Z hZ_obs hZ_fixed).dag.dSep
      Y (Z.image SWIGNode.random)
      (W ∪ (M'.fixSet Z hZ_obs hZ_fixed).fixed))
    [StandardBorelSpace M'.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.jointKernel s)]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s0 : M'.FixedValues)
    (_hPositivity_ae :
      (((M'.obsKernel s0).map (valuesProjection hZr) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((M'.obsKernel s0).map (valuesProjection hW))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((M'.obsKernel s0).map (valuesProjection hZrW))) :
    ∀ᵐ p ∂((M'.obsKernel s0).map (valuesProjection hZr) ⊗ₘ
            ProbabilityTheory.Kernel.const _
              ((M'.obsKernel s0).map (valuesProjection hW))),
      (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (M'.fixSetExtend Z hZ_obs hZ_fixed s0 p.1, p.2)
        = M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
            (s0, valuesUnionMk p.1 p.2) := by
  -- **Per-slice posterior-witness construction.**  `doSide_eq_witness` gives,
  -- for each treatment value `t`, the equality of LHS and RHS at the slice
  -- `s' := fixSetExtend s0 t`, a.e. in `w` under `μW = (M'.obsKernel s0).map π_W`
  -- (the M2 `W`-marginal at the slice equals `μW` literally by Rule 3*,
  -- `obsKernel_fixSet_W_marginal_eq_M1_marginal`).  Both sides of that per-slice
  -- identity are pinned to the posterior witness kernel
  -- `(condDistrib C_W (π_W∘E1) M1.latentProduct w).map (h t w)` — RHS via
  -- `obsCondKernel_union_eq_witness`@M1, LHS via the M2 witness chain + cross-SCM
  -- connect. This proof does not rely on the retired rectangle identity
  -- `obsKernel_fixSet_rect_eq`. Finally `ae_compProd_of_ae_ae` lifts the iterated
  -- `∀ᵐ t, ∀ᵐ w` statement to the product `νZ ⊗ₘ const μW`.
  classical
  set M2 := M'.fixSet Z hZ_obs hZ_fixed with hM2
  set hY_M2 : Y ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY with hhY_M2
  set hW_M2 : W ⊆ M2.observed := (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW with hhW_M2
  set νZ := (M'.obsKernel s0).map (valuesProjection hZr) with hνZ
  set μW := (M'.obsKernel s0).map (valuesProjection hW) with hμW
  set lam := νZ ⊗ₘ ProbabilityTheory.Kernel.const _ μW with hlam
  -- The fill map and the cut-set factorization data, shared by both witness lemmas.
  set G : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω)
      → ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) :=
    fun p => valuesUnionMk p.1 p.2 with hG
  have hG_meas : Measurable G := by fun_prop
  haveI hΩne : ∀ n, Nonempty (Ω n) := fun n =>
    (inferInstance : Nonempty (swigΩ Ω (SWIGNode.random n)))
  obtain ⟨h, hh, hfac, hoverride⟩ := cutset_factor_pointwise M' Y W Z hY hZrW s0
  -- The shared posterior witness kernel, as a function of the conditioning pair.
  set wk : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω)
      → MeasureTheory.Measure (ValuesOn Y (swigΩ Ω)) :=
    fun p =>
      ((ProbabilityTheory.condDistrib
          (valuesProjection
            (M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
          (fun ℓ : M'.LatentValues =>
            valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
          M'.latentProduct) p.2).map (h p.1 p.2) with hwk
  -- The projection facts: under `G = valuesUnionMk`, the union iso recovers `(t, w)`.
  have hproj_left : ∀ (t : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
      (w : ValuesOn W (swigΩ Ω)),
      valuesProjection (Finset.subset_union_left) (valuesUnionMk t w) = t := by
    intro t w; funext v
    exact valuesUnionMk_apply_left t w v.property
  have hproj_right : ∀ (t : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
      (w : ValuesOn W (swigΩ Ω)),
      valuesProjection (Finset.subset_union_right) (valuesUnionMk t w) = w := by
    intro t w; funext v
    have hnotleft : v.val ∉ Z.image SWIGNode.random := fun hv =>
      (Finset.disjoint_left.mp hDisj_ZrW) hv v.property
    exact valuesUnionMk_apply_right t w (Finset.subset_union_right v.property) hnotleft
  haveI hM2Markov : ProbabilityTheory.IsMarkovKernel
      (M2.obsCondKernel Y W hY_M2 hW_M2) := by
    unfold SCM.obsCondKernel; infer_instance
  haveI hM1Markov : ProbabilityTheory.IsMarkovKernel
      (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW) := by
    unfold SCM.obsCondKernel; infer_instance
  -- **RHS = witness** (transport `obsCondKernel_union_eq_witness`@M1 from `μ_C` onto
  -- `lam` via the product positivity `hPositivity_ae`).  This is where positivity is
  -- consumed.
  have h_rhs_witness :
      ∀ᵐ p ∂lam,
        M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, G p) = wk p := by
    -- Cutset d-sep at M1, derived from the do-graph d-sep `hdSep`@M2 + criterion (i)
    -- (`hWNonDescM1`) via the cross-model graph lemma.  This REPLACES the deleted
    -- false hypothesis `hdSepM1 : M'.dag.dSep Y Zr (W∪M'.fixed)`.
    have hdSepCW : M'.dag.dSep (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W))
        (Z.image SWIGNode.random) (W ∪ M'.fixed) :=
      M'.cutsetLatent_dSep_of_fixSet_dSep Z hZ_obs hZ_fixed Y W hW hWNonDescM1 hdSep
    have hunion := obsCondKernel_union_eq_witness M' Y W Z hY hZrW
      hDisj_ZrW hdSepCW s0 h hh hfac
    -- `lam.map G ≪ μ_C` (the positivity assumption) transports the `μ_C`-a.e. identity.
    have hAC : MeasureTheory.Measure.map G lam
        ≪ (M'.obsKernel s0).map (valuesProjection hZrW) := _hPositivity_ae
    have h_mapG :
        (fun c => M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, c))
          =ᵐ[lam.map G]
          (fun c =>
            ((ProbabilityTheory.condDistrib
                (valuesProjection
                  (M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
                (fun ℓ : M'.LatentValues =>
                  valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
                M'.latentProduct)
              (valuesProjection (Finset.subset_union_right) c)).map
              (h (valuesProjection (Finset.subset_union_left) c)
                 (valuesProjection (Finset.subset_union_right) c))) :=
      hAC.ae_eq hunion
    have h_prod := MeasureTheory.ae_of_ae_map hG_meas.aemeasurable h_mapG
    filter_upwards [h_prod] with p hp
    rw [hp, hwk]
    -- Rewrite the projections of `G p = valuesUnionMk p.1 p.2` to `p.1`, `p.2`.
    simp only [hG, hproj_left, hproj_right]
  -- **LHS = witness** (the do-side per-slice identity, lifted to `lam`).
  have h_lhs_witness :
      ∀ᵐ p ∂lam,
        M2.obsCondKernel Y W hY_M2 hW_M2
            (M'.fixSetExtend Z hZ_obs hZ_fixed s0 p.1, p.2) = wk p := by
    refine MeasureTheory.Measure.ae_compProd_of_ae_ae ?_ ?_
    · -- Measurability of the agreement set.
      have hfst : Measurable (fun p :
          ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω) =>
          M2.obsCondKernel Y W hY_M2 hW_M2
            (M'.fixSetExtend Z hZ_obs hZ_fixed s0 p.1, p.2)) := by fun_prop
      have hwk_meas : Measurable wk := by
        rw [hwk]
        exact ProbabilityTheory.Kernel.measurable
          (ProbabilityTheory.witnessKernel M'.latentProduct
            (Z := fun ℓ => valuesProjection hW (M'.randomToObserved (M'.evalMap s0 ℓ)))
            (C := valuesProjection
              (M'.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W))) hh)
      exact measurableSet_measure_eq hfst hwk_meas (fun _ => inferInstance)
    · -- The per-slice posterior witness-kernel identity at `s' := fixSetExtend s0 t`.
      refine MeasureTheory.ae_of_all _ (fun t => ?_)
      rw [ProbabilityTheory.Kernel.const_apply]
      exact SCM.doSide_eq_witness M' Z hZ_obs hZ_fixed Y W hY hW hZr hZrW
        hDisj_ZrW hDisj_YZr hWNonDesc s0 t h hh hfac hoverride
  -- Combine: LHS = witness = RHS.
  filter_upwards [h_lhs_witness, h_rhs_witness] with p hL hR
  rw [hL, ← hR]

end SCM

end Causalean
