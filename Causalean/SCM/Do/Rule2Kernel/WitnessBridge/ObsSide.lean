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

-- ============================================================
-- § Obs-side: `condDistrib π_Y (π_Zr, π_W) (latentProduct)` = witness kernel
-- ============================================================

/-- **Obs-side witness-kernel identity (pair-conditioned, on the latent space).** Let `M`
    be a structural causal model with node sets `Y`, `W` and a set of treatment names `Z`,
    where [`Y` is observed](hyp:hY), [the pre-intervention nodes of `Z` are
    observed](hyp:hZr), and [`W` is observed](hyp:hW). Suppose [the latent cut-set for `Y`
    relative to `Z`'s pre-intervention nodes together with `W` is d-separated, in `M`'s
    causal graph, from `Z`'s pre-intervention nodes given `W` and the fixed
    nodes](hyp:hdSepCW), and let `h` be [a jointly measurable map](hyp:hh) such that, at a
    fixed baseline assignment `s`, [the realized value of `Y` factors pointwise as `h`
    applied to the realized pre-intervention-`Z` value, the realized `W` value, and the
    cut-set's latent value](hyp:hfac). Then, under `M`'s latent product measure, [the
    conditional law of `Y` given the pair of realized pre-intervention-`Z` and `W` values
    equals, for almost every such pair, the pushforward under `h` applied to that pair of
    the conditional law of the latent cut-set given the realized `W` value](goal).

    This is a direct application of the witness lemma `condDistrib_map_of_condDistrib_fst_eq`
    with the cut-set factorization `cutset_factor_pointwise` and the conditional independence
    `cutset_condIndep_condDistrib`. -/
theorem obsSide_eq_witness (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (Y W : Finset (SWIGNode N)) (Z : Finset N)
    [StandardBorelSpace (ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty (ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))] [Nonempty (ValuesOn Y (swigΩ Ω))]
    (hY : Y ⊆ M.observed)
    (hZr : Z.image SWIGNode.random ⊆ M.observed)
    (hW : W ⊆ M.observed)
    (hdSepCW : M.dag.dSep (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W))
      (Z.image SWIGNode.random) (W ∪ M.fixed))
    (s : M.FixedValues)
    (h : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) → ValuesOn W (swigΩ Ω)
            → ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω)
            → ValuesOn Y (swigΩ Ω))
    (hh : Measurable (fun p :
        (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
          × ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
        h p.1.1 p.1.2 p.2))
    (hfac : ∀ ℓ : M.LatentValues,
        valuesProjection hY (M.randomToObserved (M.evalMap s ℓ))
          = h (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)))
              (valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
              (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)) ℓ)) :
    (fun p : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω) =>
        ProbabilityTheory.condDistrib
          (fun ℓ : M.LatentValues =>
            valuesProjection hY (M.randomToObserved (M.evalMap s ℓ)))
          (fun ℓ : M.LatentValues =>
            (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)),
             valuesProjection hW (M.randomToObserved (M.evalMap s ℓ))))
          M.latentProduct p)
      =ᵐ[M.latentProduct.map (fun ℓ : M.LatentValues =>
          (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)),
           valuesProjection hW (M.randomToObserved (M.evalMap s ℓ))))]
        (fun p =>
          (ProbabilityTheory.condDistrib
            (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
            (fun ℓ : M.LatentValues =>
              valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
            M.latentProduct p.2).map (h p.1 p.2)) := by
  haveI : MeasureTheory.IsProbabilityMeasure M.latentProduct := inferInstance
  have hX : Measurable (fun ℓ : M.LatentValues =>
      valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ))) := by fun_prop
  have hZmeas : Measurable (fun ℓ : M.LatentValues =>
      valuesProjection hW (M.randomToObserved (M.evalMap s ℓ))) := by fun_prop
  have hCmeas : Measurable
      (valuesProjection (Ω := swigΩ Ω)
        (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W))) := by fun_prop
  -- The witness lemma's `Y = h X Z C` pointwise (from `hfac`).
  have hY_eq : (fun ℓ : M.LatentValues =>
        valuesProjection hY (M.randomToObserved (M.evalMap s ℓ)))
      = fun ℓ => h
          (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)))
          (valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
          (valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)) ℓ) :=
    funext hfac
  have hwit := ProbabilityTheory.condDistrib_map_of_condDistrib_fst_eq
    (Ω := M.LatentValues)
    (𝒳 := ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))
    (𝒵 := ValuesOn W (swigΩ Ω))
    (𝒞 := ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))
    (𝒴 := ValuesOn Y (swigΩ Ω))
    (μ := M.latentProduct)
    (X := fun ℓ => valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)))
    (Z := fun ℓ => valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
    (C := valuesProjection (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
    (h := h)
    hX hZmeas hCmeas hh
    (cutset_condIndep_condDistrib M Y W Z hZr hW hdSepCW s)
  -- `hwit` conditions `condDistrib (fun ℓ => h (X ℓ)(Z ℓ)(C ℓ)) ...`; rewrite via `hY_eq`.
  rw [hY_eq]
  exact hwit

/-- **The `(Zr∪W)`-conditional packaged as the witness kernel.**

    For any model `M`, the observational conditional of `Y` given the union block
    `Zr∪W` is, `μ_C`-a.e. (μ_C the `(Zr∪W)`-marginal of `obsKernel s`), the posterior
    witness kernel evaluated at the `(Zr, W)`-split of the conditioning value.
    Assembled from `obsCondKernel_ae_eq_condDistrib` (obsCondKernel ↔ condDistrib),
    `condDistrib_map_comp` (transport onto `latentProduct`),
    `condDistrib_comp_right_measurableEquiv` with `valuesUnionEquiv` (re-split the
    union conditioning into the pair), and `obsSide_eq_witness` (the witness
    identity). -/
theorem obsCondKernel_union_eq_witness (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (Y W : Finset (SWIGNode N)) (Z : Finset N)
    [StandardBorelSpace
      (ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty (ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))] [Nonempty (ValuesOn Y (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated M.FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (hY : Y ⊆ M.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hdSepCW : M.dag.dSep (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W))
      (Z.image SWIGNode.random) (W ∪ M.fixed))
    (s : M.FixedValues)
    (h : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) → ValuesOn W (swigΩ Ω)
            → ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω)
            → ValuesOn Y (swigΩ Ω))
    (hh : Measurable (fun p :
        (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω))
          × ValuesOn (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω) =>
        h p.1.1 p.1.2 p.2))
    (hfac : ∀ ℓ : M.LatentValues,
        valuesProjection hY (M.randomToObserved (M.evalMap s ℓ))
          = h (valuesProjection
                ((Finset.subset_union_left
                  (s₁ := Z.image SWIGNode.random) (s₂ := W)).trans hZrW)
                (M.randomToObserved (M.evalMap s ℓ)))
              (valuesProjection
                ((Finset.subset_union_right
                  (s₁ := Z.image SWIGNode.random) (s₂ := W)).trans hZrW)
                (M.randomToObserved (M.evalMap s ℓ)))
              (valuesProjection (M.cutsetLatent_subset Y
                (Z.image SWIGNode.random ∪ W)) ℓ)) :
    (fun c => M.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s, c))
      =ᵐ[(M.obsKernel s).map (valuesProjection hZrW)]
        (fun c =>
          ((ProbabilityTheory.condDistrib
              (valuesProjection
                (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
              (fun ℓ : M.LatentValues =>
                valuesProjection (Finset.subset_union_right.trans hZrW)
                  (M.randomToObserved (M.evalMap s ℓ)))
              M.latentProduct)
            (valuesProjection (Finset.subset_union_right
              (s₁ := Z.image SWIGNode.random) (s₂ := W)) c)).map
            (h (valuesProjection (Finset.subset_union_left
              (s₁ := Z.image SWIGNode.random) (s₂ := W)) c)
                 (valuesProjection (Finset.subset_union_right
                   (s₁ := Z.image SWIGNode.random) (s₂ := W)) c))) := by
  classical
  have hZr : Z.image SWIGNode.random ⊆ M.observed :=
    Finset.subset_union_left.trans hZrW
  have hW : W ⊆ M.observed := Finset.subset_union_right.trans hZrW
  -- Abbreviations: the observed-eval pullback `E` and the conditioning maps.
  set E : M.LatentValues → M.ObservedValues :=
    fun ℓ => M.randomToObserved (M.evalMap s ℓ) with hE_def
  have hEmeas : Measurable E := by fun_prop
  have hπY : Measurable (valuesProjection (Ω := swigΩ Ω) hY) := by fun_prop
  have hπZrW : Measurable (valuesProjection (Ω := swigΩ Ω) hZrW) := by fun_prop
  -- Step 1: obsCondKernel ↔ condDistrib.
  have h1 := M.obsCondKernel_ae_eq_condDistrib Y (Z.image SWIGNode.random ∪ W) hY hZrW s
  -- Step 2: transport the condDistrib onto `latentProduct` along `E`.
  have hobs : M.obsKernel s = M.latentProduct.map E := M.obsKernel_eq_latentProduct_map s
  have h2 := condDistrib_map_comp (𝒴 := ValuesOn Y (swigΩ Ω))
    M.latentProduct (φ := E) (g := valuesProjection hY) (f := valuesProjection hZrW)
    hEmeas hπY hπZrW
  -- Step 3: reparametrize the `πZrW∘E` conditioning by the union iso.
  have h3 := condDistrib_comp_right_measurableEquiv (Ω := ValuesOn Y (swigΩ Ω))
    M.latentProduct (Y := valuesProjection hY ∘ E) (X := valuesProjection hZrW ∘ E)
    (valuesUnionEquiv hDisj_ZrW) (hπY.comp hEmeas) (hπZrW.comp hEmeas)
  -- Step 4: the witness identity (pair-conditioned).
  have h4 := obsSide_eq_witness M Y W Z hY hZr hW hdSepCW s h hh hfac
  -- The pair map equals `e ∘ (π_{Zr∪W} ∘ E)` (both pick the `Zr`- and `W`-coords).
  have hpair : (fun ℓ : M.LatentValues =>
        (valuesProjection hZr (E ℓ), valuesProjection hW (E ℓ)))
      = (⇑(valuesUnionEquiv hDisj_ZrW)) ∘ (valuesProjection hZrW ∘ E) := by
    funext ℓ; rfl
  -- Common base measure `ν` and the base alignments.
  have hbase1 : MeasureTheory.Measure.map (valuesProjection hZrW) (M.obsKernel s)
      = MeasureTheory.Measure.map (valuesProjection hZrW ∘ E) M.latentProduct := by
    rw [hobs, MeasureTheory.Measure.map_map hπZrW hEmeas]
  simp only [← hobs] at h2
  -- Chain h1, h2: obsCondKernel = condDistrib of the pulled-back coords.
  have h12 := h1.trans h2
  -- Transport h4 from base `map pair lat` to `ν` via the iso `e`.
  have hh4base : MeasureTheory.Measure.map
        (fun ℓ : M.LatentValues =>
          (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)),
           valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))) M.latentProduct
      = MeasureTheory.Measure.map (valuesUnionEquiv hDisj_ZrW)
          (MeasureTheory.Measure.map (valuesProjection hZrW ∘ E) M.latentProduct) := by
    rw [show (fun ℓ : M.LatentValues =>
        (valuesProjection hZr (M.randomToObserved (M.evalMap s ℓ)),
         valuesProjection hW (M.randomToObserved (M.evalMap s ℓ))))
        = (⇑(valuesUnionEquiv hDisj_ZrW)) ∘ (valuesProjection hZrW ∘ E) from hpair,
      ← MeasureTheory.Measure.map_map (valuesUnionEquiv hDisj_ZrW).measurable
        (hπZrW.comp hEmeas)]
  rw [hh4base] at h4
  -- The witness kernel (its coe is defeq to `h4`'s RHS), used for measurability.
  have hwk_meas : Measurable (fun p :
        ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω) =>
        (ProbabilityTheory.condDistrib
            (valuesProjection
              (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W)))
            (fun ℓ => valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
            M.latentProduct p.2).map (h p.1 p.2)) :=
    ProbabilityTheory.Kernel.measurable
      (ProbabilityTheory.witnessKernel M.latentProduct
        (Z := fun ℓ => valuesProjection hW (M.randomToObserved (M.evalMap s ℓ)))
        (C := valuesProjection
          (M.cutsetLatent_subset Y (Z.image SWIGNode.random ∪ W))) hh)
  have h4' := (MeasureTheory.ae_map_iff
      (valuesUnionEquiv hDisj_ZrW).measurable.aemeasurable
      (measurableSet_measure_eq (ProbabilityTheory.Kernel.measurable _) hwk_meas
        (fun _ => inferInstance))).mp h4
  -- Final assembly (all a.e. statements share base `ν = map (πZrW ∘ E) latentProduct`).
  rw [hbase1] at h12 ⊢
  filter_upwards [h12, h3, h4'] with c hc12 hc3 hc4
  rw [hc12, ← hc3]
  exact hc4

end SCM

end Causalean
