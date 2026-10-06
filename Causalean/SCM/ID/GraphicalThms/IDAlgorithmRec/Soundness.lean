/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.IDSoundDiscrete
public import Causalean.SCM.ID.GraphicalThms.DoGFormulaRec
public import Causalean.SCM.ID.GraphicalThms.IDAlgorithmRec.Core

/-! # Soundness for recursive IDENTIFY acceptance certificates

`id_sound` (in `GraphicalThms.IDAlgorithm`) proves soundness for the *no-fixing*
certificate `idSucceeds`, where every post-intervention ancestral district is
already a full c-component of the original graph.  This file lifts soundness to
the **recursive acceptance certificate** `idSucceedsRec`: each district need only be
*recursively reachable* (`CFactorReachableRec`) from its containing district via
Tian's IDENTIFY fixing sequence.  These results are one-sided soundness
statements for inhabited compatible model classes; they do not prove acceptance
completeness or produce a hedge on failure.

Since `idSucceeds → idSucceedsRec` (`idSucceeds_toRec`), `id_sound_rec` subsumes
`id_sound`, and `id_sound_rec_discrete` subsumes the frozen `id_sound_discrete`.

## Proof architecture for `id_sound_rec`

The assembly mirrors `id_sound`: the do-law `Y`-marginal factorizes over the
c-components of the post-intervention ancestral graph `H`, and it suffices to
show each district factor `tianDistrictDensity H D (do-law marginal) ref S` is a
functional of the observational kernel.  The ONLY change from `id_sound` is the
per-district recovery step (`id_sound` uses
`doAncestralDistrictDensity_recovered_from_obs`, which needs `S` to be a full
c-component).  The recursive version is:

* **M4a (per-step Lemma 12).**  For `W` ancestrally closed inside a district `T`,
  the `W`-marginal of the `Q[T]`-density equals the `Q[W]`-density.  At the
  measure level this is `q_factor_marginal_fixing` applied inside
  `M_T := M.fixSet (observed ∖ T)`; transport to densities via the
  DoLawMarginal / FiniteReference bridges used by `id_sound`'s base recovery.
* **M4b (recursive recovery).**  By induction on the `CFactorReachableRec C S`
  derivation: the base case (`inducedAncestral G C S = S`) is a marginalization
  of the *full-district* obs-side factor `cComponentDensityFactor ref C` (whose
  recovery is the existing `doAncestralDistrictDensity_recovered_from_obs` at the
  containing full c-component `C`); each `step` composes one M4a fixing step.  The
  recovered value is a functional of `obsKernel`, so equal observational kernels
  give equal district factors — exactly as in `id_sound`'s
  `cComponentDensityFactor_heq_of_obsKernel_heq` step.
* **M4c (assembly).**  Feed the recursive per-district equality into the same
  `Finset.prod` induction as `id_sound`.

Everything downstream of the per-district recovery is verbatim `id_sound`.
-/

public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM.ID

open Causalean.SCM Causalean.SCM.ID.DiscreteID
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

-- Match the finite-reference ID API in `IDAlgorithm.lean`: these statements keep
-- `Fintype` assumptions even when Lean can elaborate a particular wrapper
-- without using them syntactically.
set_option linter.unusedFintypeInType false


/-- Recursive Tian–Shpitser density core for the observed-ancestral do-law.

This is the new mathematical layer beyond `id_sound`: it replaces the no-fixing
per-district recovery step in `doObsKernelAncestralMarginal_heq_of_obsDensity_heq`
with recovery by induction on `CFactorReachableRec`. -/
theorem doObsKernelAncestralMarginal_heq_of_obsDensity_heq_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (_hsg₁ : M₁.toSWIGGraph = G) (_hsg₂ : M₂.toSWIGGraph = G)
    (_hdom₁ : DominatedObs M₁ ref) (_hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (_hden : HEq (M₁.obsDensity ref) (M₂.obsDensity ref))
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    HEq (doObsKernelAncestralMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y)
        (doObsKernelAncestralMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y) := by
  classical
  have hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y := by
    rcases _hID with ⟨_hX, hIDrest⟩
    exact hIDrest.2.1
  have hobs : HEq M₁.obsKernel M₂.obsKernel :=
    obsKernel_heq_of_obsDensity_heq M₁ M₂ ref (_hsg₁.trans _hsg₂.symm)
      _hdom₁ _hdom₂ _hden
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  haveI hfin1 : ∀ s, MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y) s) :=
    fun s => inferInstance
  haveI hfin2 : ∀ s, MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y) s) :=
    fun s => inferInstance
  haveI hobsfin1 : ∀ s, MeasureTheory.IsFiniteMeasure (M₁.obsKernel s) :=
    fun s => inferInstance
  haveI hobsfin2 : ∀ s, MeasureTheory.IsFiniteMeasure (M₂.obsKernel s) :=
    fun s => inferInstance
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  have hfio : fio₂ = fio₁ := Subsingleton.elim _ _
  subst fio₂
  have hoi : oi₂ = oi₁ := Subsingleton.elim _ _
  subst oi₂
  have hod : od₂ = od₁ := Subsingleton.elim _ _
  subst od₂
  have hoou : oou₂ = oou₁ := Subsingleton.elim _ _
  subst oou₂
  have hfoi : foi₂ = foi₁ := Subsingleton.elim _ _
  subst foi₂
  have hfou : fou₂ = fou₁ := Subsingleton.elim _ _
  subst fou₂
  have haic : aic₂ = aic₁ := Subsingleton.elim _ _
  subst aic₂
  have hdc : dc₂ = dc₁ := Subsingleton.elim _ _
  subst dc₂
  have hfoff : foff₂ = foff₁ := Subsingleton.elim _ _
  subst foff₂
  have haco : aco₂ = aco₁ := Subsingleton.elim _ _
  subst aco₂
  apply heq_of_eq
  refine ProbabilityTheory.Kernel.ext (fun s => ?_)
  -- `s` is typed against the *first* model's fixed-value space, so the `∀ s`
  -- instances above are only usable after one application at default
  -- transparency; instance synthesis alone cannot bridge the two (definitionally
  -- equal) fixed-value types.  Specialize them here so the shapes match
  -- syntactically at every later call site.
  haveI hfin1s := hfin1 s
  haveI hfin2s := hfin2 s
  refine MeasureTheory.Measure.eq_of_rnDeriv_eq
    (doObsKernelAncestralMarginal_dominated _ X hvalid₁.1 hvalid₁.2.1 Y ref href s)
    (doObsKernelAncestralMarginal_dominated _ X hvalid₂.1 hvalid₂.2.1 Y ref href s) ?_
  have w1 := doObsKernelAncestralMarginal_tian_cfactorization_density _ X hvalid₁.1 hvalid₁.2.1
    Y ref s
    (doObsKernelAncestralMarginal_dominated _ X hvalid₁.1 hvalid₁.2.1 Y ref href s)
  have w2 := doObsKernelAncestralMarginal_tian_cfactorization_density _ X hvalid₂.1 hvalid₂.2.1
    Y ref s
    (doObsKernelAncestralMarginal_dominated _ X hvalid₂.1 hvalid₂.2.1 Y ref href s)
  refine w1.trans (Filter.EventuallyEq.trans ?_ w2.symm)
  let M₁' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁, unobserved := unobserved₁,
      fixed_is_fixed := fio₁, observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁, unobs_are_roots := dc₁,
      fixed_outside_fixed_isolated := foff₁, all_children_in_observed := aco₁,
      edgeTypes := eT₁, iota_valueSpace := iota₁, structFun := sf₁,
      structFun_measurable := mf₁, latentDist := lD₁, isProbability_latent := pL₁ }
  let M₂' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁, unobserved := unobserved₁,
      fixed_is_fixed := fio₁, observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁, unobs_are_roots := dc₁,
      fixed_outside_fixed_isolated := foff₁, all_children_in_observed := aco₁,
      edgeTypes := eT₂, iota_valueSpace := iota₂, structFun := sf₂,
      structFun_measurable := mf₂, latentDist := lD₂, isProbability_latent := pL₂ }
  let D := fixObservedAncestralSet M₁' X hvalid₁.1 hvalid₁.2.1 Y
  let H := (M₁'.fixSet X hvalid₁.1 hvalid₁.2.1).toSWIGGraph.induce
    (fixAncestralSet M₁' X hvalid₁.1 hvalid₁.2.1 Y)
  haveI hν₁ : MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) :=
    hfin1 s
  haveI hν₂ : MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) :=
    hfin2 s
  haveI hν₂D : MeasureTheory.IsFiniteMeasure
      (show MeasureTheory.Measure (ValuesOn D (swigΩ Ω)) from
        ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s)) := by
    change MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s)
    exact hfin2 s
  change (fun x => ∏ S ∈ H.cComponentSet,
      tianDistrictDensity H D
        ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S x)
      =ᵐ[jointRef ref D]
    (fun x => ∏ S ∈ H.cComponentSet,
      tianDistrictDensity H D
        ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S x)
  have hfac : ∀ S ∈ H.cComponentSet,
      tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S
        =ᵐ[jointRef ref D]
      tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S := by
    intro S hS
    have hIDM : idSucceedsRec X Y M₁'.toSWIGGraph := by
      rw [_hsg₁]
      exact _hID
    rcases hIDM with ⟨hX, hIDrest⟩
    have hSreach : S ∈ ((M₁'.toSWIGGraph.splitMono X hX.1 hX.2).induce
        ((M₁'.toSWIGGraph.splitMono X hX.1 hX.2).dag.ancestralSet Y)).cComponentSet := by
      exact hS
    let C := containingCComponent M₁'.toSWIGGraph S
    have hReach : CFactorReachableRec M₁'.toSWIGGraph C S := by
      simpa [C] using hIDrest.2.2 S hSreach
    have hSne : S.Nonempty := by
      simp only [SWIGGraph.cComponentSet] at hS
      rcases Finset.mem_image.mp hS with ⟨v, hv, rfl⟩
      exact ⟨v, H.mem_cComponentOf_self hv⟩
    have hSobs : S ⊆ M₁'.toSWIGGraph.observed := by
      have hSobsH : S ⊆ H.observed :=
        H.cComponentSet_subset_observed S hS
      intro v hv
      have hvD : v ∈ D := by
        simpa [H, D, fixObservedAncestralSet, SCM.fixSet_observed, SWIGGraph.induce]
          using hSobsH hv
      exact (Finset.mem_inter.mp hvD).2
    have hCmem : C ∈ M₁'.toSWIGGraph.cComponentSet := by
      have hchoose : hSne.choose ∈ M₁'.toSWIGGraph.observed :=
        hSobs hSne.choose_spec
      simp only [C, containingCComponent, dif_pos hSne, SWIGGraph.cComponentSet]
      exact Finset.mem_image.mpr ⟨hSne.choose, hchoose, rfl⟩
    let extend : ValuesOn D (swigΩ Ω) → ValuesOn M₁'.observed (swigΩ Ω) :=
      pinnedExtend M₁' X hvalid₁.1 hvalid₁.2.1 Y s
    have hExtend : ∀ xD, valuesProjection
        (show D ⊆ M₁'.observed from Finset.inter_subset_right) (extend xD) = xD :=
      pinnedExtend_projection_eq M₁' X hvalid₁.1 hvalid₁.2.1 Y s hYX
    have hExtendX : ∀ xD (D : N) (hD : D ∈ X),
        extend xD ⟨SWIGNode.random D, hvalid₁.1 D hD⟩ =
          s ⟨SWIGNode.fixed D,
            Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩ :=
      pinnedExtend_pin_eq M₁' X hvalid₁.1 hvalid₁.2.1 Y s
    have hpos₁' : ∀ s' : M₁'.FixedValues,
        DiscreteID.PositiveMass (M₁'.obsKernel s') :=
      hpos₁
    have hpos₂' : ∀ s' : M₂'.FixedValues,
        DiscreteID.PositiveMass (M₂'.obsKernel s') :=
      hpos₂
    haveI hobsfin₁ : ∀ s' : M₁'.FixedValues,
        MeasureTheory.IsFiniteMeasure (M₁'.obsKernel s') :=
      hobsfin1
    haveI hobsfin₂ : ∀ s' : M₂'.FixedValues,
        MeasureTheory.IsFiniteMeasure (M₂'.obsKernel s') :=
      hobsfin2
    have t1 := doAncestralDistrictDensity_recovered_from_obs_rec M₁'
      X hvalid₁.2.2.2 hvalid₁.1 hvalid₁.2.1 Y ref href s S C
      (by simpa [H, fixTruncCComponentSet] using hS) hReach hCmem hpos₁' hYX extend hExtend
      hExtendX
    have t2 := doAncestralDistrictDensity_recovered_from_obs_rec M₂'
      X hvalid₂.2.2.2 hvalid₂.1 hvalid₂.2.1 Y ref href s S C
      (by exact hS)
      (by simpa [M₁', M₂'] using hReach) (by simpa [M₁', M₂'] using hCmem)
      hpos₂' hYX extend (by exact hExtend)
      (by exact hExtendX)
    have hrec := recoveredFactorRec_heq_of_obsKernel_heq M₁' M₂' ref C S rfl hobs
    have hrec_fun : (fun s' => recoveredFactorRec M₁' ref s' C S) =
        (fun s' => recoveredFactorRec M₂' ref s' C S) :=
      eq_of_heq hrec
    have hrec_s := congrFun hrec_fun (M₁'.fixSetProj X hvalid₁.1 hvalid₁.2.1 s)
    refine t1.trans ?_
    filter_upwards [t2.symm] with x hx
    exact hrec_s ▸ hx
  clear w1 w2
  have hprod : ∀ I : Finset (Finset (SWIGNode N)),
      (∀ S ∈ I,
        tianDistrictDensity H D
            ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S
          =ᵐ[jointRef ref D]
        tianDistrictDensity H D
            ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S) →
      (fun x => ∏ S ∈ I,
        tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S x)
        =ᵐ[jointRef ref D]
      (fun x => ∏ S ∈ I,
        tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S x) := by
    intro I hIall
    induction I using Finset.induction_on with
    | empty =>
        simp
    | insert S I hSnot ih =>
        have hS : tianDistrictDensity H D
              ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S
            =ᵐ[jointRef ref D]
            tianDistrictDensity H D
              ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S :=
          hIall S (Finset.mem_insert_self S I)
        have hI : (fun x => ∏ T ∈ I,
              tianDistrictDensity H D
                ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref T x)
            =ᵐ[jointRef ref D]
          (fun x => ∏ T ∈ I,
            tianDistrictDensity H D
              ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref T x) :=
          ih (by
            intro T hT
            exact hIall T (Finset.mem_insert_of_mem hT))
        filter_upwards [hS, hI] with x hxS hxI
        simp [Finset.prod_insert hSnot, hxS, hxI]
  exact hprod H.cComponentSet hfac

/-- Recursive density-to-`Y`-marginal wrapper.  The projection from the
observed-ancestral marginal to the query coordinates is identical to the
no-fixing proof; only the ancestral density core changes. -/
theorem doObsKernelYMarginal_heq_of_obsDensity_heq_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (_hsg₁ : M₁.toSWIGGraph = G) (_hsg₂ : M₂.toSWIGGraph = G)
    (_hdom₁ : DominatedObs M₁ ref) (_hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (_hden : HEq (M₁.obsDensity ref) (M₂.obsDensity ref))
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    HEq (doObsKernelYMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y hvalid₁.2.2.1)
        (doObsKernelYMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y hvalid₂.2.2.1) := by
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  exact doObsKernelYMarginal_heq_of_ancestralMarginal_heq X Y M₁ M₂ hsg
    hvalid₁.1 hvalid₁.2.1 hvalid₂.1 hvalid₂.2.1 hvalid₁.2.2.1 hvalid₂.2.2.1
    (doObsKernelAncestralMarginal_heq_of_obsDensity_heq_rec X Y G ref href _hID M₁ M₂
      _hsg₁ _hsg₂ _hdom₁ _hdom₂ hpos₁ hpos₂ _hden hvalid₁ hvalid₂)

/-- Recursive observational-kernel wrapper.  Equal observational kernels give
equal observational densities, which feed the recursive density core. -/
theorem doObsKernelYMarginal_heq_of_obsKernel_heq_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (hsg₁ : M₁.toSWIGGraph = G) (hsg₂ : M₂.toSWIGGraph = G)
    (hdom₁ : DominatedObs M₁ ref) (hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (hobs : HEq M₁.obsKernel M₂.obsKernel)
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    HEq (doObsKernelYMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y hvalid₁.2.2.1)
        (doObsKernelYMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y hvalid₂.2.2.1) :=
  doObsKernelYMarginal_heq_of_obsDensity_heq_rec X Y G ref href hID M₁ M₂ hsg₁ hsg₂
    hdom₁ hdom₂ hpos₁ hpos₂
    (obsDensity_heq_of_obsKernel_heq M₁ M₂ ref (hsg₁.trans hsg₂.symm) hobs)
    hvalid₁ hvalid₂

/-- **Recursive valid-branch kernel equality.** For two finite structural causal models `M₁`,
`M₂` that share [the same SWIG graph `G`](hyp:_hsg₁,_hsg₂), are each [dominated by a
reference-measure family `ref` that is faithful to the graph](hyp:href,_hdom₁,_hdom₂), [satisfy
discrete positivity of their observational kernels](hyp:hpos₁,hpos₂), and [have
heterogeneously equal observational kernels](hyp:_hobs), if [the total interventional query on
outcome set `Y` under intervention `X` is well formed in both models](hyp:hvalid₁,hvalid₂) and
`X`, `Y` have a successful recursive ID soundness certificate on `G`, then [the two models'
post-intervention outcome kernels for `Y` are equal at their chosen default fixed-value assignments](goal). This is the same
transport as `doKernelY_eq_cfactor_decomposition`, with the recursive `Y`-marginal wrapper in
place of the no-fixing one. -/
theorem doKernelY_eq_cfactor_decomposition_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (_hsg₁ : M₁.toSWIGGraph = G) (_hsg₂ : M₂.toSWIGGraph = G)
    (_hdom₁ : DominatedObs M₁ ref) (_hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (_hobs : HEq M₁.obsKernel M₂.obsKernel)
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    M₁.doKernelY X hvalid₁.1 hvalid₁.2.1 Y hvalid₁.2.2.1
        (standardFixedValues M₁ hvalid₁.2.2.2)
      =
    M₂.doKernelY X hvalid₂.1 hvalid₂.2.1 Y hvalid₂.2.2.1
        (standardFixedValues M₂ hvalid₂.2.2.2) := by
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  exact doKernelY_eq_of_doObsKernel_heq X Y M₁ M₂ hsg
    hvalid₁.1 hvalid₁.2.1 hvalid₂.1 hvalid₂.2.1 hvalid₁.2.2.1 hvalid₂.2.2.1
    (standardFixedValues M₁ hvalid₁.2.2.2) (standardFixedValues M₂ hvalid₂.2.2.2)
    (standardFixedValues_heq M₁ M₂ (congrArg SWIGGraph.fixed hsg) hvalid₁.2.2.2)
    (doObsKernelYMarginal_heq_of_obsKernel_heq_rec X Y G ref href _hID M₁ M₂ _hsg₁ _hsg₂
      _hdom₁ _hdom₂ hpos₁ hpos₂ _hobs hvalid₁ hvalid₂)

/-- **Soundness of the recursive ID acceptance certificate for finite discrete-positive
models.** Fix [targets](hyp:X), [outcomes](hyp:Y), [a standard graph](hyp:G,hG), and
[a faithful reference family](hyp:ref,href), and assume
[an inhabited compatible dominated-positive class](hyp:hNonempty). Then
[recursive certificate success guarantees query identification within that class](goal).
The standard-graph premise keeps the query on its meaningful branch. The
inhabitation premise prevents a vacuous conclusion over an empty compatible class.
This generalizes `id_sound` from the no-fixing fragment to the full
Tian-Shpitser IDENTIFY recursion; see the module docstring for the proof
architecture. -/
theorem id_sound_rec [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref) (hG : G.isStandard)
    (hNonempty : ∃ M : Causalean.SCM N Ω,
      M.toSWIGGraph = G ∧ DominatedObs M ref ∧ DiscreteID.DiscretePositive M) :
    idSucceedsRec X Y G →
      IdentifiableUnder (Ω := Ω) G (fun _ => True)
        (fun M => DominatedObs M ref ∧ DiscreteID.DiscretePositive M)
        (interventionalQuery (Ω := Ω) X Y) := by
  classical
  intro hID M₁ M₂ hsg₁ hsg₂ _ _ hM₁ hM₂ hobs
  have hvalid_iff :
      interventionalQueryValid X Y M₁ ↔ interventionalQueryValid X Y M₂ :=
    interventionalQueryValid_iff_of_toSWIGGraph_eq
      (Ω := Ω) X Y M₁ M₂ (hsg₁.trans hsg₂.symm)
  by_cases hvalid₁ : interventionalQueryValid X Y M₁
  · have hvalid₂ : interventionalQueryValid X Y M₂ := hvalid_iff.mp hvalid₁
    rw [interventionalQuery_eq_doKernelY_of_valid (Ω := Ω) X Y M₁ hvalid₁,
      interventionalQuery_eq_doKernelY_of_valid (Ω := Ω) X Y M₂ hvalid₂]
    exact doKernelY_eq_cfactor_decomposition_rec
      (Ω := Ω) X Y G ref href hID M₁ M₂ hsg₁ hsg₂ hM₁.1 hM₂.1 hM₁.2 hM₂.2
      hobs hvalid₁ hvalid₂
  · have hvalid₂ : ¬ interventionalQueryValid X Y M₂ := by
      intro h
      exact hvalid₁ (hvalid_iff.mpr h)
    rw [interventionalQuery_eq_default_of_not_valid (Ω := Ω) X Y M₁ hvalid₁,
      interventionalQuery_eq_default_of_not_valid (Ω := Ω) X Y M₂ hvalid₂]

/-- **Discrete soundness of the recursive ID acceptance certificate (on-contract).** For
[targets](hyp:X), [outcomes](hyp:Y), [a standard graph](hyp:G,hG),
[an inhabited compatible positive class](hyp:hNonempty), and
[a successful recursive certificate](hyp:h),
[the corresponding query is identifiable within that class](goal). The standard-graph premise
prevents a dummy-query conclusion, while inhabitation prevents vacuous identification. Obtained from
`id_sound_rec` at the counting reference by collapsing `DominatedObs · countingRef` to
`StandardDiscretePositive`, exactly as
`id_sound_discrete` is obtained from `id_sound`.  This subsumes
`id_sound_discrete` (via `idSucceeds_toRec`). -/
theorem id_sound_rec_discrete
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (hG : G.isStandard)
    (hNonempty : ∃ M : Causalean.SCM N Ω,
      M.toSWIGGraph = G ∧ StandardDiscretePositive M)
    (h : idSucceedsRec X Y G) :
    IdentifiableUnder G (fun _ => True) StandardDiscretePositive
      (interventionalQuery (Ω := Ω) X Y) := by
  have hdom :=
    id_sound_rec X Y G (countingRef (Ω := Ω)) referenceFaithful_countingRef hG
      (by
        rcases hNonempty with ⟨M, hMG, hM⟩
        exact ⟨M, hMG, dominatedObs_countingRef M, hM.2⟩)
      h
  exact identifiableUnder_mono G (fun _ => True) (fun _ => True)
    (fun M => DominatedObs M (countingRef (Ω := Ω)) ∧ DiscretePositive M)
    StandardDiscretePositive (interventionalQuery (Ω := Ω) X Y)
    (fun _ h => h) (fun M hM => ⟨dominatedObs_countingRef M, hM.2⟩) hdom

end Causalean.SCM.ID
