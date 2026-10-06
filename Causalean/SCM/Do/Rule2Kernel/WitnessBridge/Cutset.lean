/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Probability.Kernel.CondDistrib
public import Causalean.Mathlib.Probability.Kernel.CondDistribWitness
public import Causalean.SCM.Do.CutsetDSep
public import Causalean.SCM.Do.GlobalMarkov
public import Causalean.SCM.Do.Rule2
public import Causalean.SCM.Do.Rule2Kernel.DiscreteZHelpers
public import Causalean.SCM.Do.Rule2Kernel.Helpers
public import Causalean.SCM.Do.Rule2Kernel.Structural.StructCrossSCM
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

open Causalean.Mathlib.Probability.Kernel

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § Plumbing: measurability of a measure-valued agreement set
-- ============================================================


-- ============================================================
-- § Plumbing: `obsKernel s` as a latent pushforward
-- ============================================================

/-- **`obsKernel s` is the latent product pushed through `randomToObserved ∘ evalMap s`.**

    Folds `obsKernel = jointKernel.map randomToObserved` (`Kernel.obsKernel`) and
    `jointKernel s = latentProduct.map (evalMap s)` (`jointKernel_apply_eq`) into a
    single pushforward of `latentProduct`.  This is the form consumed by
    `condDistrib_map_comp` to move the obs-level conditional onto the latent
    space. -/
theorem obsKernel_eq_latentProduct_map (M : Causalean.SCM N Ω) (s : M.FixedValues) :
    M.obsKernel s
      = M.latentProduct.map (fun ℓ => M.randomToObserved (M.evalMap s ℓ)) := by
  have hev : Measurable (fun ℓ : M.LatentValues => M.evalMap s ℓ) := by fun_prop
  rw [obsKernel, ProbabilityTheory.Kernel.map_apply _ M.measurable_randomToObserved,
    jointKernel_apply_eq, MeasureTheory.Measure.map_map M.measurable_randomToObserved hev]
  rfl

/-- The pulled-back observed-coordinate projection through `randomToObserved ∘ evalMap s`
    is the latent projection of the evaluation, `valuesProjection hY ∘ randomToObserved ∘ E`.
    This is definitional unfolding, exposed so downstream `condDistrib_map_comp`
    rewrites can name the composite. -/
@[fun_prop]
theorem valuesProjection_randomToObserved_evalMap_meas
    (M : Causalean.SCM N Ω) {Y : Finset (SWIGNode N)} (hY : Y ⊆ M.observed)
    (s : M.FixedValues) :
    Measurable (fun ℓ : M.LatentValues =>
        valuesProjection hY (M.randomToObserved (M.evalMap s ℓ))) := by
  have hev : Measurable (fun ℓ : M.LatentValues => M.evalMap s ℓ) := by fun_prop
  exact (measurable_valuesProjection hY).comp (M.measurable_randomToObserved.comp hev)

-- ============================================================
-- § The witness factorization map `h` and pointwise identity
-- ============================================================

/-- **Cut-set factorization, pointwise, at the realized override.**

    The evaluation projected to `Y` factors through the cut-set projection and the
    realized conditioning value: there is a measurable `h` (taking the
    `(Zr, W)`-conditioning value as its `(x, z)` arguments and the cut-set value as
    its `c` argument) with

      `π_Y (E ℓ) = h (π_Zr (E ℓ)) (π_W (E ℓ)) (π_{C_W} ℓ)`   for every `ℓ`.

    Combine `exists_evalMap_overrideC_factors_cutset` (for each fixed override `c`,
    a cut-set map `h_c` with `evalMap_overrideC … c = h_c ∘ π_{C_W}`) with
    `evalMap_overrideC_at_self` (at `c = π_C (E ℓ)`, the override equals the real
    `E`), so `h (x, z) cw := h_{fill(x,z)} cw`.

    The canonical `h` is the override map `h x z c := evalMap_overrideC … s
    (valuesUnionMk x z) (extendCutset c)`; its joint measurability comes from
    `measurable_evalMap_overrideC`.  Besides the realized-`s` factorization, `h`
    satisfies an OFF-diagonal override characterization (`hoverride`): for any
    override block `(zr, w')` and any latent `ℓ`, `h zr w' (π_{C_W} ℓ) =
    evalMap_overrideC … s (valuesUnionMk zr w') ℓ`.  This pins `h` off the
    realized-`s` diagonal, which the do-side bridge needs (its treatment
    coordinate is held at `t`, off the M1 diagonal). -/
theorem cutset_factor_pointwise (M : Causalean.SCM N Ω)
    [∀ n, Nonempty (Ω n)]
    (Y W : Finset (SWIGNode N)) (Z : Finset N)
    (hY : Y ⊆ M.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M.observed)
    (s : M.FixedValues) :
    ∃ h : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) → ValuesOn W (swigΩ Ω)
            → ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω)
            → ValuesOn Y (swigΩ Ω),
      Measurable (fun p :
          (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
            × ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
          h p.1.1 p.1.2 p.2) ∧
      (∀ ℓ : M.LatentValues,
        valuesProjection hY (M.randomToObserved (M.evalMap s ℓ))
          = h (valuesProjection (fun _ hz => hZrW (Finset.mem_union_left _ hz))
                (M.randomToObserved (M.evalMap s ℓ)))
              (valuesProjection (fun _ hw => hZrW (Finset.mem_union_right _ hw))
                (M.randomToObserved (M.evalMap s ℓ)))
              (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)) ℓ)) ∧
      -- Override-form characterization: `h` evaluated at the cut-set projection of
      -- *any* latent `ℓ` equals the override map at that `ℓ` with override block
      -- `(zr, w')`.  This pins `h` OFF the realized-`s` diagonal — needed do-side,
      -- where the treatment coordinate is fixed at `t` (off the M1 diagonal).
      (∀ (zr : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω)) (w' : ValuesOn W (swigΩ Ω))
          (ℓ : M.LatentValues),
        h zr w'
            (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)) ℓ)
          = M.evalMap_overrideC hY hZrW s (valuesUnionMk zr w') ℓ) := by
  classical
  have hZr : Z.image SWIGNode.random ⊆ M.observed :=
    fun _ hz => hZrW (Finset.mem_union_left _ hz)
  have hW : W ⊆ M.observed :=
    fun _ hw => hZrW (Finset.mem_union_right _ hw)
  set C := Z.image SWIGNode.random ∪ W with hC_def
  set CW := M.cutsetLatent Y C with hCW_def
  have hCWsub : CW ⊆ M.unobserved := M.cutsetLatent_subset Y C
  -- Default latent vector for filling non-cutset coords.
  have hNEΩ : ∀ w : SWIGNode N, Nonempty (swigΩ Ω w) := by
    intro w; cases w <;> exact inferInstance
  let ℓ₀ : M.LatentValues := fun u => (hNEΩ u.val).some
  -- The measurable section restoring the cutset coordinates.
  let extendCutset : ValuesOn CW (swigΩ Ω) → M.LatentValues :=
    fun cwProj u => if h : u.val ∈ CW then cwProj ⟨u.val, h⟩ else ℓ₀ u
  have hext_meas : Measurable extendCutset := by
    refine measurable_pi_lambda _ (fun u => ?_)
    by_cases h : u.val ∈ CW
    · have : (fun cwProj : ValuesOn CW (swigΩ Ω) => extendCutset cwProj u)
          = fun cwProj => cwProj ⟨u.val, h⟩ := by funext cwProj; simp [extendCutset, h]
      rw [this]; exact measurable_pi_apply _
    · have : (fun cwProj : ValuesOn CW (swigΩ Ω) => extendCutset cwProj u)
          = fun _ => ℓ₀ u := by funext cwProj; simp [extendCutset, h]
      rw [this]; exact measurable_const
  -- The section restores cutset coordinates.
  have hext_restore : ∀ cwProj : ValuesOn CW (swigΩ Ω),
      valuesProjection hCWsub (extendCutset cwProj) = cwProj := by
    intro cwProj; funext u
    simp only [valuesProjection, extendCutset, dif_pos u.property]
  refine ⟨fun zr w c => M.evalMap_overrideC hY hZrW s (valuesUnionMk zr w) (extendCutset c),
    ?_, ?_, ?_⟩
  · -- Joint measurability via `measurable_evalMap_overrideC`.
    have hcomp :
        (fun p :
            (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
              × ValuesOn CW (swigΩ Ω) =>
            M.evalMap_overrideC hY hZrW s (valuesUnionMk p.1.1 p.1.2) (extendCutset p.2))
          =
        (fun q : (M.FixedValues × ValuesOn C (swigΩ Ω)) × M.LatentValues =>
            M.evalMap_overrideC hY hZrW q.1.1 q.1.2 q.2)
          ∘ (fun p => ((s, valuesUnionMk p.1.1 p.1.2), extendCutset p.2)) := by
      funext p; rfl
    rw [hcomp]
    refine (measurable_evalMap_overrideC M hY hZrW).comp ?_
    refine Measurable.prodMk ?_ (hext_meas.comp measurable_snd)
    refine measurable_const.prodMk ?_
    exact measurable_valuesUnionMk.comp measurable_fst
  · -- Factorization at the realized point.
    intro ℓ
    set E := M.randomToObserved (M.evalMap s ℓ) with hE_def
    -- (a) valuesUnionMk of the two projections of E equals the (Zr∪W)-projection of E.
    have ha : valuesUnionMk (valuesProjection hZr E) (valuesProjection hW E)
        = valuesProjection hZrW E := by
      funext ⟨v, hv⟩
      by_cases hvZr : v ∈ Z.image SWIGNode.random
      · rw [valuesUnionMk_apply_left _ _ hvZr]; rfl
      · have hvW : v ∈ W := (Finset.mem_union.mp hv).resolve_left hvZr
        rw [valuesUnionMk_apply_right _ _ hv hvZr]; rfl
    -- (b) override agrees with `ℓ` after the cutset section, by cutset agreement.
    have hb : M.evalMap_overrideC hY hZrW s (valuesProjection hZrW E)
                (extendCutset (valuesProjection hCWsub ℓ))
            = M.evalMap_overrideC hY hZrW s (valuesProjection hZrW E) ℓ := by
      refine evalMap_overrideC_agree_cutset M hY hZrW s _ _ _ ?_
      rw [hext_restore]
    -- (c) the override at its "self" C-value equals the real eval on Y.
    have hc : M.evalMap_overrideC hY hZrW s (valuesProjection hZrW E) ℓ
            = valuesProjection hY E := by
      -- Both sides are the (cast-transported) `evalObservedAux` at observed nodes.
      have hself : valuesProjection hZrW E
          = (fun v' : {v // v ∈ C} =>
              (M.observedAt_observedIndex ⟨v'.val, hZrW v'.property⟩) ▸
                evalObservedAux M s ℓ
                  (M.observedIndex ⟨v'.val, hZrW v'.property⟩).val
                  (M.observedIndex ⟨v'.val, hZrW v'.property⟩).isLt) := by
        funext v'
        change E ⟨v'.val, hZrW v'.property⟩ = _
        change M.evalMap s ℓ ⟨v'.val, _⟩ = _
        rw [M.evalMap_observed s ℓ _ (hZrW v'.property)]
      rw [hself, M.evalMap_overrideC_at_self hY hZrW s ℓ]
      funext v
      change _ = E ⟨v.val, hY v.property⟩
      change _ = M.evalMap s ℓ ⟨v.val, _⟩
      rw [M.evalMap_observed s ℓ _ (hY v.property)]
    -- Assemble.
    calc valuesProjection hY E
        = M.evalMap_overrideC hY hZrW s (valuesProjection hZrW E) ℓ := hc.symm
      _ = M.evalMap_overrideC hY hZrW s (valuesProjection hZrW E)
            (extendCutset (valuesProjection hCWsub ℓ)) := hb.symm
      _ = M.evalMap_overrideC hY hZrW s
            (valuesUnionMk (valuesProjection hZr E) (valuesProjection hW E))
            (extendCutset (valuesProjection hCWsub ℓ)) := by rw [ha]
  · -- Override-form characterization (off-diagonal pinning of `h`).
    -- `h zr w' (π_{C_W} ℓ) = override (valuesUnionMk zr w') (extendCutset (π_{C_W} ℓ))`,
    -- and the override depends on the latent only through the cut-set projection,
    -- so we may replace `extendCutset (π_{C_W} ℓ)` by `ℓ` itself.
    intro zr w' ℓ
    change M.evalMap_overrideC hY hZrW s (valuesUnionMk zr w')
        (extendCutset (valuesProjection hCWsub ℓ))
      = M.evalMap_overrideC hY hZrW s (valuesUnionMk zr w') ℓ
    refine evalMap_overrideC_agree_cutset M hY hZrW s _ _ _ ?_
    rw [hext_restore]

-- ============================================================
-- § Conditional independence of the cut-set, condDistrib form
-- ============================================================

/-- For [a finite structural causal model with measurable node-value spaces](hyp:N,Ω,M),
[outcome and conditioning node sets and a treatment-variable set](hyp:Y,W,Z), if [the random
treatment copies are observed](hyp:hZr), [the conditioning nodes are observed](hyp:hW), and
[the relevant cut-set is d-separated from treatment given the conditioning nodes](hyp:hdSepCW),
then at [any fixed-node assignment](hyp:s), [the cut-set's conditional distribution given
treatment and conditioning agrees almost surely with its conditional distribution given the
conditioning variables alone](goal).

**Cut-set conditional independence, in `condDistrib`-pair form.**

    Under `latentProduct`, the cut-set `C_W = cutsetLatent Y (Zr∪W)` is
    conditionally independent of the (pulled-back) treatment coordinate
    `X = π_Zr ∘ E` given the conditioning coordinate `Z = π_W ∘ E`:

      `condDistrib C_W (X, Z) latentProduct =ᵐ condDistrib C_W Z latentProduct ∘ snd`.

    This is the form `condDistrib_map_of_condDistrib_fst_eq` consumes.  Derivation:
    `cutsetLatent_dSep_of_dSep` gives the graph d-sep `C_W ⊥ Zr | (W ∪ fixed)`;
    `full_globalMarkov_with_fixed` turns it into `FullCondIndep` (= `CondIndepFun`
    under `jointKernel s`); since `jointKernel s = latentProduct.map (evalMap s)`,
    `CondIndepFun` transfers to `latentProduct` for the pulled-back coordinates;
    finally `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` rewrites
    `CondIndepFun` into the `condDistrib`-pair equality.

    The proof packages the chain
    `FullCondIndep(jointKernel) → CondIndepFun(latentProduct, pulled-back coords)
    → condDistrib-pair form`, including the coordinate-order rewrite from
    `prodMkRight`/`prodMkLeft` to the witness lemma's `(X, Z) → Z` shape. -/
theorem cutset_condIndep_condDistrib (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (Y W : Finset (SWIGNode N)) (Z : Finset N)
    [StandardBorelSpace (ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty (ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    (hZr : Z.image SWIGNode.random ⊆ M.observed)
    (hW : W ⊆ M.observed)
    (hdSepCW : M.dag.dSep (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W))
      (Z.image SWIGNode.random) (W ∪ M.fixed))
    (s : M.FixedValues) :
    (fun p : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω) =>
        ProbabilityTheory.condDistrib
          (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
          (fun ℓ : M.LatentValues =>
            (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)),
             valuesProjection hW (M.randomToObserved (M.evalMap s ℓ))))
          M.latentProduct p)
      =ᵐ[M.latentProduct.map (fun ℓ : M.LatentValues =>
          (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)),
           valuesProjection hW (M.randomToObserved (M.evalMap s ℓ))))]
        (fun p =>
          ProbabilityTheory.condDistrib
            (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
            (fun ℓ : M.LatentValues =>
              valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
            M.latentProduct p.2) := by
  classical
  set Zr := Z.image SWIGNode.random with hZr_def
  set CW := M.cutsetLatent Y (Zr ∪ W) with hCW_def
  have hCWsub : CW ⊆ M.unobserved := M.cutsetLatent_subset Y (Zr ∪ W)
  -- Subset facts into `randomVars`.
  have hobs_rv : M.observed ⊆ M.randomVars := by
    intro v hv; exact Finset.mem_union_left _ hv
  have hunobs_rv : M.unobserved ⊆ M.randomVars := by
    intro v hv; exact Finset.mem_union_right _ hv
  have hZr_rv : Zr ⊆ M.randomVars := hZr.trans hobs_rv
  have hW_rv : W ⊆ M.randomVars := hW.trans hobs_rv
  have hCW_rv : CW ⊆ M.randomVars := hCWsub.trans hunobs_rv
  -- Bridge: for an observed set `D`, projecting `randomToObserved (evalMap s ℓ)`
  -- equals projecting `evalMap s ℓ` directly (same underlying values).
  have hbridge_obs : ∀ {D : Finset (SWIGNode N)} (hD : D ⊆ M.observed)
      (hD_rv : D ⊆ M.randomVars) (ℓ : M.LatentValues),
      valuesProjection hD (M.randomToObserved (M.evalMap s ℓ))
        = valuesProjection hD_rv (M.evalMap s ℓ) := by
    intro D hD hD_rv ℓ; funext v; rfl
  -- Bridge: for the latent cutset, projecting `evalMap s ℓ` equals projecting `ℓ`.
  have hbridge_lat : ∀ ℓ : M.LatentValues,
      valuesProjection hCW_rv (M.evalMap s ℓ) = valuesProjection hCWsub ℓ := by
    intro ℓ; funext v
    change M.evalMap s ℓ ⟨v.val, hCW_rv v.property⟩ = ℓ ⟨v.val, hCWsub v.property⟩
    rw [M.evalMap_unobserved s ℓ _ (hCWsub v.property)]
  -- Measurability of the pulled-back coordinate maps (as compositions with evalMap s).
  have hev : Measurable (fun ℓ : M.LatentValues => M.evalMap s ℓ) := by fun_prop
  -- Abbreviations for the pulled-back coordinate maps.
  set Xmap : M.LatentValues → ValuesOn Zr (swigΩ Ω) :=
    fun ℓ => valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)) with hX_def
  set Zmap : M.LatentValues → ValuesOn W (swigΩ Ω) :=
    fun ℓ => valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)) with hZmap_def
  set Cmap : M.LatentValues → ValuesOn CW (swigΩ Ω) :=
    valuesProjection hCWsub with hC_def
  have hXmeas : Measurable Xmap := by fun_prop
  have hZmeas : Measurable Zmap := by fun_prop
  have hCmeas : Measurable Cmap := by fun_prop
  -- Step 1: cutset graph d-sep is now a direct hypothesis; global Markov
  -- (FullCondIndep under jointKernel) follows.  (Previously derived internally
  -- via `cutsetLatent_dSep_of_dSep` from `dSep Y Zr`, which is FALSE at M1; the
  -- cutset d-sep `dSep C_W Zr` is the satisfiable input and is threaded directly.)
  have hdSepCW : M.dag.dSep CW Zr (W ∪ M.fixed) := hdSepCW
  have hDisj_CWZr : Disjoint CW Zr := by
    rw [Finset.disjoint_left]; intro a haCW haZr
    exact not_obs_of_unobs M.toSWIGGraph (hCWsub haCW) (hZr haZr)
  have hDisj_CWW : Disjoint CW W := by
    rw [Finset.disjoint_left]; intro a haCW haW
    exact not_obs_of_unobs M.toSWIGGraph (hCWsub haCW) (hW haW)
  have hFCI : FullCondIndep M CW Zr W hCW_rv hZr_rv hW_rv (M.jointKernel s) :=
    full_globalMarkov_with_fixed M CW Zr W M.fixed hCW_rv hZr_rv hW_rv (Finset.Subset.refl _)
      hdSepCW s
  -- `Zr ⟂ CW | W` form (swap X↔Y), which the Mathlib iff consumes as `g ⟂ᵢ[k] f`.
  have hFCI_symm : FullCondIndep M Zr CW W hZr_rv hCW_rv hW_rv (M.jointKernel s) :=
    fullCondIndep_symm M hCW_rv hZr_rv hW_rv hFCI
  haveI : MeasureTheory.IsProbabilityMeasure M.latentProduct := inferInstance
  -- Measurability of the `valuesProjection` maps on `RandomValues`.
  have hCW_proj_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hCW_rv) := by fun_prop
  have hZr_proj_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hZr_rv) := by fun_prop
  have hW_proj_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hW_rv) := by fun_prop
  -- Step 2: Mathlib iff turns `FullCondIndep` into a condDistrib-pair equality
  -- under `jointKernel s`, conditioning on the pair `(W, Zr)`.
  have hCI_joint :
      (fun p => ProbabilityTheory.condDistrib (valuesProjection hCW_rv)
          (fun ξ => (valuesProjection hW_rv ξ, valuesProjection hZr_rv ξ)) (M.jointKernel s) p)
        =ᵐ[(M.jointKernel s).map
            (fun ξ => (valuesProjection hW_rv ξ, valuesProjection hZr_rv ξ))]
          (fun p => ((ProbabilityTheory.condDistrib (valuesProjection hCW_rv)
              (valuesProjection hW_rv) (M.jointKernel s)).prodMkRight _) p) := by
    have := (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (μ := M.jointKernel s) (f := valuesProjection hCW_rv) (g := valuesProjection hZr_rv)
      (k := valuesProjection hW_rv) hCW_proj_meas hZr_proj_meas hW_proj_meas).mp hFCI_symm
    exact this
  -- The two coordinate maps on `RandomValues`, and their compositions with `evalMap s`.
  set Wmap_rv : M.RandomValues → ValuesOn W (swigΩ Ω) := valuesProjection hW_rv with hWmap_rv
  set Zrmap_rv : M.RandomValues → ValuesOn Zr (swigΩ Ω) := valuesProjection hZr_rv with hZrmap_rv
  set CWmap_rv : M.RandomValues → ValuesOn CW (swigΩ Ω) := valuesProjection hCW_rv with hCWmap_rv
  set pairWZr : M.RandomValues → ValuesOn W (swigΩ Ω) × ValuesOn Zr (swigΩ Ω) :=
    fun ξ => (Wmap_rv ξ, Zrmap_rv ξ) with hpairWZr
  have hpairWZr_meas : Measurable pairWZr := by fun_prop
  -- Rewrite `jointKernel s` as the pushforward of `latentProduct`.
  have hjk : M.jointKernel s = M.latentProduct.map (fun ℓ => M.evalMap s ℓ) :=
    jointKernel_apply_eq M s
  simp only [hjk] at hCI_joint
  -- Compositions with `evalMap s` reduce to `Zmap`, `Xmap`, `Cmap`.
  have hcomp_pair : pairWZr ∘ (fun ℓ => M.evalMap s ℓ) = fun ℓ => (Zmap ℓ, Xmap ℓ) := by
    funext ℓ
    simp only [hpairWZr, hWmap_rv, hZrmap_rv, Function.comp_apply, hZmap_def, hX_def]
    rw [hbridge_obs hW hW_rv ℓ, hbridge_obs hZr hZr_rv ℓ]
  have hcomp_W : Wmap_rv ∘ (fun ℓ => M.evalMap s ℓ) = Zmap := by
    funext ℓ; simp only [hWmap_rv, Function.comp_apply, hZmap_def]
    rw [hbridge_obs hW hW_rv ℓ]
  have hcomp_CW : CWmap_rv ∘ (fun ℓ => M.evalMap s ℓ) = Cmap := by
    funext ℓ
    change CWmap_rv (M.evalMap s ℓ) = Cmap ℓ
    rw [hbridge_lat ℓ]
  -- Transfer the pair-conditioned `condDistrib` onto `latentProduct`.
  have htr_pair := condDistrib_map_comp (𝒴 := ValuesOn CW (swigΩ Ω)) M.latentProduct
    (φ := fun ℓ => M.evalMap s ℓ) (g := CWmap_rv) (f := pairWZr)
    hev hCW_proj_meas hpairWZr_meas
  have htr_W := condDistrib_map_comp (𝒴 := ValuesOn CW (swigΩ Ω)) M.latentProduct
    (φ := fun ℓ => M.evalMap s ℓ) (g := CWmap_rv) (f := Wmap_rv)
    hev hCW_proj_meas hW_proj_meas
  -- The `(W, Zr)`-ordered latent pair map and its marginal measure facts.
  set pairWZr_lat : M.LatentValues → ValuesOn W (swigΩ Ω) × ValuesOn Zr (swigΩ Ω) :=
    fun ℓ => (Zmap ℓ, Xmap ℓ) with hpairWZr_lat
  have hpairWZr_lat_meas : Measurable pairWZr_lat := by fun_prop
  -- Push `htr_pair`/`htr_W`/`hCI_joint` filters into `LP.map (·∘E)` form.
  rw [MeasureTheory.Measure.map_map hpairWZr_meas hev, hcomp_pair, hcomp_CW]
    at htr_pair
  rw [MeasureTheory.Measure.map_map hpairWZr_meas hev, hcomp_pair] at hCI_joint
  rw [MeasureTheory.Measure.map_map hW_proj_meas hev, hcomp_W, hcomp_CW] at htr_W
  -- `htr_pair` now: condDistrib CWmap_rv pairWZr (LP.map E) =ᵐ[LP.map pairWZr_lat]
  --                condDistrib Cmap pairWZr_lat LP
  -- `hCI_joint` now RHS uses prodMkRight of condDistrib CWmap_rv Wmap_rv (LP.map E).
  -- Reduce prodMkRight to evaluation at `.1`.
  have hCI_joint' :
      (fun p => ProbabilityTheory.condDistrib CWmap_rv pairWZr
          (M.latentProduct.map (fun ℓ => M.evalMap s ℓ)) p)
        =ᵐ[M.latentProduct.map pairWZr_lat]
          (fun p => ProbabilityTheory.condDistrib CWmap_rv Wmap_rv
            (M.latentProduct.map (fun ℓ => M.evalMap s ℓ)) p.1) := by
    filter_upwards [hCI_joint] with p hp
    rw [hp, ProbabilityTheory.Kernel.prodMkRight_apply]
  -- Lift `htr_W` from the `W`-marginal to the pair-marginal along `Prod.fst`.
  have htr_W_fst :
      (fun p => ProbabilityTheory.condDistrib CWmap_rv Wmap_rv
          (M.latentProduct.map (fun ℓ => M.evalMap s ℓ)) p.1)
        =ᵐ[M.latentProduct.map pairWZr_lat]
          (fun p : ValuesOn W (swigΩ Ω) × ValuesOn Zr (swigΩ Ω) =>
            ProbabilityTheory.condDistrib Cmap Zmap M.latentProduct p.1) := by
    have hfst_marg : (M.latentProduct.map pairWZr_lat).map Prod.fst
        = M.latentProduct.map Zmap := by
      rw [MeasureTheory.Measure.map_map measurable_fst hpairWZr_lat_meas]; rfl
    have := MeasureTheory.ae_eq_comp (μ := M.latentProduct.map pairWZr_lat)
      (f := Prod.fst) (g := fun q => ProbabilityTheory.condDistrib CWmap_rv Wmap_rv
        (M.latentProduct.map (fun ℓ => M.evalMap s ℓ)) q)
      (g' := fun q => ProbabilityTheory.condDistrib Cmap Zmap M.latentProduct q)
      measurable_fst.aemeasurable (by rw [hfst_marg]; exact htr_W)
    exact this
  -- Assemble the `(W, Zr)`-ordered equality on `LP.map pairWZr_lat`.
  have keyWZr :
      (fun p => ProbabilityTheory.condDistrib Cmap pairWZr_lat M.latentProduct p)
        =ᵐ[M.latentProduct.map pairWZr_lat]
          (fun p : ValuesOn W (swigΩ Ω) × ValuesOn Zr (swigΩ Ω) =>
            ProbabilityTheory.condDistrib Cmap Zmap M.latentProduct p.1) :=
    (htr_pair.symm.trans hCI_joint').trans htr_W_fst
  -- Swap `(W, Zr)` to `(Zr, W)` via the product-comm measurable equivalence.
  set e : (ValuesOn W (swigΩ Ω) × ValuesOn Zr (swigΩ Ω)) ≃ᵐ
      (ValuesOn Zr (swigΩ Ω) × ValuesOn W (swigΩ Ω)) := MeasurableEquiv.prodComm with he_def
  have hpair_swap : (fun ℓ => (Xmap ℓ, Zmap ℓ)) = e ∘ pairWZr_lat := by
    funext ℓ; rfl
  -- `condDistrib Cmap (e ∘ pairWZr_lat) LP (e p) = condDistrib Cmap pairWZr_lat LP p`, a.e.
  have hreparam := condDistrib_comp_right_measurableEquiv (μ := M.latentProduct)
    (Y := Cmap) (X := pairWZr_lat) e hCmeas hpairWZr_lat_meas
  -- Transport the goal (over `LP.map (Xmap, Zmap) = (LP.map pairWZr_lat).map e`) to `keyWZr`.
  have hmap_e : M.latentProduct.map (fun ℓ => (Xmap ℓ, Zmap ℓ))
      = (M.latentProduct.map pairWZr_lat).map e := by
    rw [hpair_swap, ← MeasureTheory.Measure.map_map e.measurable hpairWZr_lat_meas]
  -- Final: rewrite the goal's conditioning into `Xmap`/`Zmap`, then chain.
  change (fun p => ProbabilityTheory.condDistrib Cmap (fun ℓ => (Xmap ℓ, Zmap ℓ))
        M.latentProduct p)
      =ᵐ[M.latentProduct.map (fun ℓ => (Xmap ℓ, Zmap ℓ))]
        (fun p => ProbabilityTheory.condDistrib Cmap Zmap M.latentProduct p.2)
  rw [hmap_e]
  -- On `(LP.map pairWZr_lat).map e`, pull back along the measurable embedding `e`.
  rw [Filter.EventuallyEq, e.measurableEmbedding.ae_map_iff]
  filter_upwards [keyWZr, hreparam] with p hkey hrep
  -- LHS at `e p`: condDistrib Cmap (Xmap,Zmap) LP (e p) = condDistrib Cmap pairWZr_lat LP p.
  have hLHS : ProbabilityTheory.condDistrib Cmap (fun ℓ => (Xmap ℓ, Zmap ℓ))
        M.latentProduct (e p)
      = ProbabilityTheory.condDistrib Cmap pairWZr_lat M.latentProduct p := by
    rw [hpair_swap]; exact hrep
  change ProbabilityTheory.condDistrib Cmap (fun ℓ => (Xmap ℓ, Zmap ℓ)) M.latentProduct (e p)
      = ProbabilityTheory.condDistrib Cmap Zmap M.latentProduct (e p).2
  rw [hLHS, hkey]
  -- RHS: `condDistrib Cmap Zmap LP p.1 = condDistrib Cmap Zmap LP (e p).2`.
  rfl

end SCM

end Causalean
