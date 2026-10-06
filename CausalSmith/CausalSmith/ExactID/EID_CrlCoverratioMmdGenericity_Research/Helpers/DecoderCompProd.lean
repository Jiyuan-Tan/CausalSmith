module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderConditionalKernel

/-!
# Product-law assembly for decoder coordinates

This file separates one distinguished coordinate from a finite product-density measure.
It supplies the measure-product step needed to assemble the equation-(11) conditional kernel.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: map_withDensity_measurableEquiv
/-- Transporting a weighted measure through a measurable equivalence transports its density
by the inverse equivalence.  Given [the stated inputs and conditions](hyp:f), [the stated conclusion](goal) follows. -/
lemma map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ : Measure α} {ν : Measure β}
    (h : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) :
    Measure.map e (μ.withDensity f) = ν.withDensity (f ∘ e.symm) := by
  classical
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  rw [h.lintegral_map_equiv]
  apply lintegral_congr
  intro a
  change (if e a ∈ s then f a else 0) =
    if e a ∈ s then f (e.symm (e a)) else 0
  rw [e.symm_apply_apply]

-- @node: weightedCoordinate_independence
/-- If a finite product density factors into a normalized density at one coordinate and a
factor depending only on a disjoint coordinate set, that coordinate is independent of the
projected set under the weighted measure.  Given [the stated inputs and conditions](hyp:hjS,hq,hg,hgS,q,g), [the stated conclusion](goal) follows. -/
lemma weightedCoordinate_independence
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ : V → Measure ℝ) [∀ k, SigmaFinite (μ k)] [∀ k, IsProbabilityMeasure (μ k)]
    (j : V) (S : Finset V) (hjS : j ∉ S)
    (q : ℝ → ℝ≥0∞) (hq : Measurable q)
    (g : (V → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hgS : Causalean.Mathlib.MeasureTheory.FiniteCoordinate.DependsOn S g)
    [IsProbabilityMeasure ((μ j).withDensity q)] :
    Measure.map (fun x =>
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S x, x j))
        ((Measure.pi μ).withDensity (fun x => q (x j) * g x)) =
      (Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S)
        ((Measure.pi μ).withDensity (fun x => q (x j) * g x))).prod
        ((μ j).withDensity q) := by
  classical
  let p : V → Prop := fun k => k = j
  let E0 := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => ℝ) p
  let μone : Measure ((k : {k // p k}) → ℝ) :=
    @Measure.pi (Subtype p) (fun _ => ℝ) (Subtype.fintype p) (fun _ => inferInstance)
      (fun k => μ k)
  let μrest : Measure ((k : {k // ¬ p k}) → ℝ) :=
    @Measure.pi (Subtype fun k => ¬ p k) (fun _ => ℝ)
      (Subtype.fintype fun k => ¬ p k) (fun _ => inferInstance) (fun k => μ k)
  let qone : ((k : {k // p k}) → ℝ) → ℝ≥0∞ := fun z => q (z ⟨j, rfl⟩)
  let zeroOne : (k : {k // p k}) → ℝ := fun _ => 0
  let grest : ((k : {k // ¬ p k}) → ℝ) → ℝ≥0∞ :=
    fun z => g (E0.symm (zeroOne, z))
  have hsplit : MeasurePreserving E0 (Measure.pi μ) (μone.prod μrest) := by
    simpa [E0, μone, μrest] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd μ p)
  have hqone : Measurable qone := by
    exact hq.comp (measurable_pi_apply (⟨j, rfl⟩ : {k // p k}))
  have hgrest : Measurable grest :=
    hg.comp (E0.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hdensity : (fun z => q (E0.symm z j) * g (E0.symm z)) =
      fun z => qone z.1 * grest z.2 := by
    funext z
    congr 1
    · change q (E0.symm z j) = q (z.1 ⟨j, rfl⟩)
      congr 1
      simp [E0, p]
    · apply hgS
      intro k hk
      have hkj : k ≠ j := fun h => hjS (h ▸ hk)
      change E0.symm z k = E0.symm (zeroOne, z.2) k
      simp [E0, p, hkj]
  have hweighted : Measure.map E0
      ((Measure.pi μ).withDensity (fun x => q (x j) * g x)) =
      (μone.withDensity qone).prod (μrest.withDensity grest) := by
    rw [map_withDensity_measurableEquiv E0 hsplit]
    rw [MeasureTheory.prod_withDensity hqone hgrest]
    congr 1
  let evalOne : ((k : {k // p k}) → ℝ) → ℝ := fun z => z ⟨j, rfl⟩
  let projectRest : ((k : {k // ¬ p k}) → ℝ) → ((k : S) → ℝ) :=
    fun z k => z ⟨k, by
      intro hkj
      apply hjS
      rw [← hkj]
      exact k.property⟩
  have heval : Measurable evalOne :=
    measurable_pi_apply (⟨j, rfl⟩ : {k // p k})
  have hproject : Measurable projectRest := by
    apply measurable_pi_lambda
    intro k
    exact measurable_pi_apply _
  have htarget : Measure.map evalOne (μone.withDensity qone) =
      (μ j).withDensity q := by
    let Eone := MeasurableEquiv.piUnique (fun _ : {k // p k} => ℝ)
    have hone : MeasurePreserving Eone μone (μ j) := by
      have hraw := @MeasureTheory.measurePreserving_piUnique
        (Subtype p) (Subtype.fintype p) (fun _ => ℝ) inferInstance
        (fun _ => inferInstance) (fun k => μ k)
      have hdef : (default : {k // p k}).1 = j := (default : {k // p k}).2
      simpa [Eone, μone, p, hdef] using hraw
    rw [show evalOne = Eone by rfl]
    rw [map_withDensity_measurableEquiv Eone hone]
    congr 1
  have hdown : Measurable (fun z : ((k : {k // p k}) → ℝ) ×
      ((k : {k // ¬ p k}) → ℝ) => (projectRest z.2, evalOne z.1)) :=
    (hproject.comp measurable_snd).prodMk (heval.comp measurable_fst)
  have hpair : (fun x : V → ℝ =>
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S x, x j)) =
      (fun z => (projectRest z.2, evalOne z.1)) ∘ E0 := by
    funext x
    apply Prod.ext
    · funext k
      simp [projectRest, E0, p, Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection]
    · simp [evalOne, E0, p]
  have hjoint : Measure.map (fun x : V → ℝ =>
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S x, x j))
        ((Measure.pi μ).withDensity (fun x => q (x j) * g x)) =
      (Measure.map projectRest (μrest.withDensity grest)).prod
        (Measure.map evalOne (μone.withDensity qone)) := by
    rw [hpair, ← Measure.map_map hdown E0.measurable, hweighted]
    calc
      Measure.map (fun z => (projectRest z.2, evalOne z.1))
          ((μone.withDensity qone).prod (μrest.withDensity grest)) =
          Measure.map Prod.swap
            (Measure.map (Prod.map evalOne projectRest)
              ((μone.withDensity qone).prod (μrest.withDensity grest))) := by
              rw [Measure.map_map measurable_swap (heval.prodMap hproject)]
              rfl
      _ = Measure.map Prod.swap
          ((Measure.map evalOne (μone.withDensity qone)).prod
            (Measure.map projectRest (μrest.withDensity grest))) := by
              rw [← Measure.map_prod_map _ _ heval hproject]
      _ = _ := Measure.prod_swap
  have hpred : Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S)
      ((Measure.pi μ).withDensity (fun x => q (x j) * g x)) =
      Measure.map projectRest (μrest.withDensity grest) := by
    calc
      Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S)
          ((Measure.pi μ).withDensity (fun x => q (x j) * g x)) =
          Measure.map Prod.fst
            (Measure.map (fun x : V → ℝ =>
              (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S x, x j))
              ((Measure.pi μ).withDensity (fun x => q (x j) * g x))) := by
                rw [Measure.map_map measurable_fst (by fun_prop)]
                rfl
      _ = Measure.map Prod.fst
          ((Measure.map projectRest (μrest.withDensity grest)).prod
            ((μ j).withDensity q)) := by rw [hjoint, htarget]
      _ = Measure.map projectRest (μrest.withDensity grest) := by
        rw [Measure.map_fst_prod]
        simp
  rw [hjoint, htarget, hpred]

-- @node: equationTen_predecessorCoordinates_independent_target
/-- Equation (10) as a product law: under intervention `i`, the target coordinate has its
replacement-density law and is independent of all latent coordinates preceding `i`.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationTen_predecessorCoordinates_independent_target
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    let A := decoderRetainedLatentSet W order i
    let S := A.erase (W.targetPerm i)
    let pred := Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
      (X := fun _ : Fin n => ℝ) S
    Measure.map (fun v => (pred v, v (W.targetPerm i)))
        (interventionalLaw θ (W.targetPerm i)) =
      (Measure.map pred (interventionalLaw θ (W.targetPerm i))).prod
        (decoderInterventionCoordinateMeasure W hpos i) := by
  dsimp only
  let B := mechanismUnitCubeFactorization hpos
  let q := mechanismInterventionDensity W hpos i
  let A := decoderRetainedLatentSet W order i
  let S := A.erase (W.targetPerm i)
  let μ : Fin n → Measure ℝ := fun _ =>
    Causalean.Graph.FiniteDensity.unitIntervalReference
  let ν := (Measure.pi μ).withDensity
    (fun v => q.density (v (W.targetPerm i)) * B.partialDensity S v)
  have hσ : ∀ k, SigmaFinite (μ k) := fun _ => by
    dsimp only [μ]
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  letI : ∀ k, SigmaFinite (μ k) := hσ
  have hprob : ∀ k, IsProbabilityMeasure (μ k) := fun _ => by
    constructor
    dsimp only [μ]
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    simp [Real.volume_Icc]
  letI : ∀ k, IsProbabilityMeasure (μ k) := hprob
  have htargetNotMem : W.targetPerm i ∉ S := Finset.notMem_erase _ _
  have hg : Measurable (B.partialDensity S) :=
    B.measurable_partialDensity S
  have hgS : Causalean.Mathlib.MeasureTheory.FiniteCoordinate.DependsOn S (B.partialDensity S) := by
    intro x y hxy
    unfold Causalean.Graph.FiniteDensity.Factorization.partialDensity
    apply Finset.prod_congr rfl
    intro k hk
    apply B.local_factor k
    intro a ha
    apply hxy a
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hk
    have hkA : k ∈ A := (Finset.mem_erase.mp hk).2
    have haA : a ∈ A :=
      decoderRetainedLatentSet_parentClosed W horder hgraphOrder i hkA ha
    have hane : a ≠ W.targetPerm i := by
      intro hat
      subst a
      change k ∈ decoderRetainedLatentSet W order i at hkA
      rw [decoderRetainedLatentSet, Finset.mem_insert] at hkA
      rcases hkA with hkt | hkpred
      · exact (Finset.mem_erase.mp hk).1 hkt
      · rcases Finset.mem_map.mp hkpred with ⟨b, hb, rfl⟩
        exact target_not_parent_of_mem_predecessorSet W horder hgraphOrder hb ha
    exact Finset.mem_erase.mpr ⟨hane, haA⟩
  have hνprod := @weightedCoordinate_independence (Fin n) inferInstance inferInstance
    μ hσ hprob (W.targetPerm i) S htargetNotMem q.density q.measurable_density
      (B.partialDensity S) hg hgS (by
        simpa [μ, q, decoderInterventionCoordinateMeasure] using
          decoderInterventionCoordinateMeasure_isProbability W hpos i)
  have hAeq : A = decoderRetainedLatentSet W order i := rfl
  have hretained := equationTen_retainedMarginalMeasure W hpos horder hgraphOrder i
  change Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection A)
      (interventionalLaw θ (W.targetPerm i)) =
    Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection A) ν at hretained
  have hpairMeas : Measurable (fun v : LatentState n =>
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S v, v (W.targetPerm i))) :=
    (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection S).prodMk
      (measurable_pi_apply _)
  have hpairDepends : Causalean.Mathlib.MeasureTheory.FiniteCoordinate.DependsOn A
      (fun v : LatentState n =>
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S v, v (W.targetPerm i))) := by
    intro x y hxy
    apply Prod.ext
    · funext k
      exact hxy k (Finset.mem_of_mem_erase k.property)
    · exact hxy _ (by simp [A, decoderRetainedLatentSet])
  have hpredMeas : Measurable (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
      (X := fun _ : Fin n => ℝ) S) :=
    Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection S
  have hpredDepends : Causalean.Mathlib.MeasureTheory.FiniteCoordinate.DependsOn A
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n => ℝ) S) := by
    intro x y hxy
    funext k
    exact hxy k (Finset.mem_of_mem_erase k.property)
  have hpairMap := Causalean.Mathlib.MeasureTheory.FiniteCoordinate.map_eq_of_map_coordinateProjection_eq
    (fun _ : Fin n => (0 : ℝ)) hpairMeas hpairDepends hretained
  have hpredMap := Causalean.Mathlib.MeasureTheory.FiniteCoordinate.map_eq_of_map_coordinateProjection_eq
    (fun _ : Fin n => (0 : ℝ)) hpredMeas hpredDepends hretained
  calc
    Measure.map (fun v : LatentState n =>
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S v, v (W.targetPerm i)))
        (interventionalLaw θ (W.targetPerm i)) =
      Measure.map (fun v : LatentState n =>
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S v, v (W.targetPerm i))) ν :=
          hpairMap
    _ = (Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S) ν).prod
        (decoderInterventionCoordinateMeasure W hpos i) := by
          simpa [μ, q, decoderInterventionCoordinateMeasure] using hνprod
    _ = (Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection S)
        (interventionalLaw θ (W.targetPerm i))).prod
        (decoderInterventionCoordinateMeasure W hpos i) := by rw [hpredMap]

-- @node: map_prod_compProd_of_fiber
/-- Mapping a product measure through a measurable fiber map gives a compositional product
whenever the supplied kernel is the fiberwise pushforward of the second marginal.  Given [the stated inputs and conditions](hyp:hg,hf,hκ), [the stated conclusion](goal) follows. -/
lemma map_prod_compProd_of_fiber
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (g : α → δ) (hg : Measurable g) (f : α × β → γ) (hf : Measurable f)
    (κ : Kernel δ γ) [IsSFiniteKernel κ]
    (hκ : ∀ a, κ (g a) = Measure.map (fun b => f (a, b)) ν) :
    Measure.map (fun z : α × β => (g z.1, f z)) (μ.prod ν) =
      Measure.map g μ ⊗ₘ κ := by
  have hpair : Measurable (fun z : α × β => (g z.1, f z)) := by
    fun_prop
  ext s hs
  rw [Measure.map_apply hpair hs,
    Measure.prod_apply (hs.preimage hpair),
    Measure.compProd_apply hs]
  rw [MeasureTheory.lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  apply lintegral_congr
  intro a
  rw [hκ a, Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop))]
  rfl

-- @node: retainedProjectionToPredecessorCube
/-- Reindex and clamp retained latent predecessor coordinates into the compact decoder cube. -/
def retainedProjectionToPredecessorCube
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (y : (k : (decoderRetainedLatentSet W order i).erase (W.targetPerm i)) → ℝ) :
    PredecessorLatentCube order i := fun j =>
  ⟨max 0 (min 1 (y ⟨W.targetPerm j, by
    apply Finset.mem_erase.mpr
    constructor
    · intro h
      have hji : j.1 = i := W.targetPerm.injective h
      have hjlt : order j < order i := by simpa [predecessorSet] using j.2
      exact (hji ▸ hjlt).false
    · rw [decoderRetainedLatentSet]
      exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨j, j.2, rfl⟩)⟩)),
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

-- @node: measurable_retainedProjectionToPredecessorCube
/-- [Reindexing and clamping the retained predecessor projection is measurable](goal). -/
@[fun_prop] lemma measurable_retainedProjectionToPredecessorCube
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n) :
    Measurable (retainedProjectionToPredecessorCube W order i) := by
  apply measurable_pi_lambda
  intro j
  apply Measurable.subtype_mk
  fun_prop

-- @node: retainedProjectionToPredecessorCube_coordinateProjection
/-- On the latent cube, the clamped retained projection is the actual predecessor restriction.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma retainedProjectionToPredecessorCube_coordinateProjection
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (v : LatentState n) (hv : v ∈ latentCube n) :
    retainedProjectionToPredecessorCube W order i
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        ((decoderRetainedLatentSet W order i).erase (W.targetPerm i)) v) =
      predecessorLatentCubeOfState W order i v hv := by
  funext j
  apply Subtype.ext
  simp only [retainedProjectionToPredecessorCube,
    Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection,
    predecessorLatentCubeOfState]
  have hj := hv (W.targetPerm j) (Set.mem_univ _)
  rw [min_eq_right hj.2, max_eq_right hj.1]

-- @node: clampedPredecessorCoordinates
/-- The globally measurable clamped predecessor restriction of an ambient latent state. -/
def clampedPredecessorCoordinates
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n) (v : LatentState n) :
    PredecessorLatentCube order i :=
  retainedProjectionToPredecessorCube W order i
    (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
      ((decoderRetainedLatentSet W order i).erase (W.targetPerm i)) v)

-- @node: measurable_clampedPredecessorCoordinates
/-- The [clamped predecessor-coordinate restriction is measurable](goal). -/
@[fun_prop] lemma measurable_clampedPredecessorCoordinates
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n) :
    Measurable (clampedPredecessorCoordinates W order i) := by
  exact (measurable_retainedProjectionToPredecessorCube W order i).comp
    (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection _)

-- @node: clampedPredecessorCoordinates_of_mem
/-- On the latent cube, clamped predecessor coordinates equal the genuine restriction.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma clampedPredecessorCoordinates_of_mem
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (v : LatentState n) (hv : v ∈ latentCube n) :
    clampedPredecessorCoordinates W order i v =
      predecessorLatentCubeOfState W order i v hv :=
  retainedProjectionToPredecessorCube_coordinateProjection W order i v hv

-- @node: predecessorCoordinates_independent_target
/-- Equation (10) transported to the compact predecessor cube: under intervention `i`,
clamped predecessor coordinates and the target coordinate have a product law.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma predecessorCoordinates_independent_target
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    Measure.map (fun v => (clampedPredecessorCoordinates W order i v,
        v (W.targetPerm i))) (interventionalLaw θ (W.targetPerm i)) =
      (Measure.map (clampedPredecessorCoordinates W order i)
        (interventionalLaw θ (W.targetPerm i))).prod
        (decoderInterventionCoordinateMeasure W hpos i) := by
  let A := decoderRetainedLatentSet W order i
  let S := A.erase (W.targetPerm i)
  let pred := Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
    (X := fun _ : Fin n => ℝ) S
  let F := retainedProjectionToPredecessorCube W order i
  let μ := interventionalLaw θ (W.targetPerm i)
  let ν := decoderInterventionCoordinateMeasure W hpos i
  letI : IsProbabilityMeasure μ := interventionalLaw_isProbabilityMeasure W hpos i
  have hprod := equationTen_predecessorCoordinates_independent_target
    W hpos horder hgraphOrder i
  change Measure.map (fun v => (pred v, v (W.targetPerm i))) μ =
    (Measure.map pred μ).prod ν at hprod
  have hF : Measurable F := measurable_retainedProjectionToPredecessorCube W order i
  have hpair : Measurable (fun v : LatentState n => (pred v, v (W.targetPerm i))) := by
    fun_prop
  have hmap := congrArg (Measure.map (Prod.map F id)) hprod
  calc
    Measure.map (fun v => (clampedPredecessorCoordinates W order i v,
        v (W.targetPerm i))) μ =
      Measure.map (Prod.map F id)
        (Measure.map (fun v => (pred v, v (W.targetPerm i))) μ) := by
          rw [Measure.map_map (hF.prodMap measurable_id) hpair]
          rfl
    _ = Measure.map (Prod.map F id) ((Measure.map pred μ).prod ν) := hmap
    _ = (Measure.map F (Measure.map pred μ)).prod ν := by
      rw [← Measure.map_prod_map _ _ hF measurable_id]
      simp
    _ = (Measure.map (clampedPredecessorCoordinates W order i) μ).prod ν := by
      rw [Measure.map_map hF (by fun_prop)]
      rfl

-- @node: equationElevenAmbientKernel_apply_scoreMap
/-- On a triangular predecessor score, the ambient equation-(11) kernel is precisely the
pushforward of the replacement coordinate law along the corresponding own-score fiber.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationElevenAmbientKernel_apply_scoreMap
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n)
    (z : PredecessorLatentCube order i) :
    (equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i)
        (predecessorScoreMap W order i z) =
      Measure.map (fun w => equationElevenClampedScore W order i (z, w))
        (decoderInterventionCoordinateMeasure W hpos i) := by
  let e := predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i
  have hrange : predecessorScoreMap W order i z ∈
      Set.range (predecessorScoreMap W order i) := ⟨z, rfl⟩
  have hretract : predecessorScoreRangeRetraction W order i
      (predecessorScoreMap W order i z) =
        ⟨predecessorScoreMap W order i z, hrange⟩ := by
    simp [predecessorScoreRangeRetraction, hrange]
  have hinv : e.symm ⟨predecessorScoreMap W order i z, hrange⟩ = z := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  rw [equationElevenAmbientKernel, Kernel.comap_apply,
    equationElevenScoreImageKernel, Kernel.comap_apply, hretract, hinv,
    equationElevenPredecessorKernel]
  ext u hu
  rw [Kernel.map_apply' _ (measurable_equationElevenClampedScore W hpos order i) _ hu,
    Kernel.comap_apply, Kernel.parallelComp_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_apply (by fun_prop)
    (hu.preimage (measurable_equationElevenClampedScore W hpos order i))]
  rw [Measure.map_apply (by fun_prop) hu]
  rfl

-- @node: equationElevenClampedScore_of_latentState
/-- On a latent cube point, the clamped equation-(11) fiber score equals the observed target
log-ratio, because every target parent occurs among the reconstructed predecessors.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,horder,hgraphOrder,hv), [the stated conclusion](goal) follows. -/
lemma equationElevenClampedScore_of_latentState
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n)
    (v : LatentState n) (hv : v ∈ latentCube n) :
    equationElevenClampedScore W order i
        (clampedPredecessorCoordinates W order i v, v (W.targetPerm i)) =
      observedLawLogRatio W.law i (W.mix v) := by
  rw [clampedPredecessorCoordinates_of_mem W order i v hv]
  rw [observedLawLogRatio_comp_mix_eq W hpos hmix hone i v hv]
  unfold equationElevenClampedScore
  have hvi := hv (W.targetPerm i) (Set.mem_univ _)
  rw [min_eq_right hvi.2, max_eq_right hvi.1]
  dsimp only
  have hp : θ.p (W.targetPerm i)
      (Function.update (predecessorCubeLatentState W order i
        (predecessorLatentCubeOfState W order i v hv))
        (W.targetPerm i) (v (W.targetPerm i))) = θ.p (W.targetPerm i) v := by
    apply θ.parent_local (W.targetPerm i)
    · simp
    · intro a ha
      let j := W.targetPerm.symm a
      have hjparent : j ∈ environmentParentSet W i := by
        simpa [j, environmentParentSet, DAG.parents] using ha
      have hjpred := environmentParentSet_subset_predecessorSet_of_transitiveClosure
        W horder hgraphOrder i hjparent
      have hbase := predecessorCubeLatentState_ofState_apply W order i v hv j hjpred
      have hat : a ≠ W.targetPerm i := by
        intro h
        have hji : j = i := W.targetPerm.injective (by simpa [j] using h)
        have hjlt : order j < order i := by simpa [predecessorSet] using hjpred
        exact (hji ▸ hjlt).false
      simpa [Function.update, hat, j] using hbase
  rw [hp]

-- @node: observedRatioPredecessor_compProd
/-- Under intervention `i`, the observed predecessor-score and target-score law is the
predecessor marginal composed with the ambient equation-(11) Markov kernel.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma observedRatioPredecessor_compProd
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    Measure.map
        (fun x ↦
          (familyProjection (observedLawLogRatio W.law) (predecessorSet order i) x,
            observedLawLogRatio W.law i x)) (W.law i.succ) =
      Measure.map
          (familyProjection (observedLawLogRatio W.law) (predecessorSet order i))
          (W.law i.succ) ⊗ₘ
        equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i := by
  let μ := interventionalLaw θ (W.targetPerm i)
  let ν := decoderInterventionCoordinateMeasure W hpos i
  let z := clampedPredecessorCoordinates W order i
  let g := predecessorScoreMap W order i
  let f := equationElevenClampedScore W order i
  let κ := equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i
  let latentJoint : LatentState n → PredecessorLogRatios order i × ℝ := fun v =>
    (g (z v), f (z v, v (W.targetPerm i)))
  let observedJoint : LatentState n → PredecessorLogRatios order i × ℝ := fun x =>
    (familyProjection (observedLawLogRatio W.law) (predecessorSet order i) x,
      observedLawLogRatio W.law i x)
  have hμ : IsProbabilityMeasure μ := interventionalLaw_isProbabilityMeasure W hpos i
  letI : IsProbabilityMeasure μ := hμ
  have hν : IsProbabilityMeasure ν := decoderInterventionCoordinateMeasure_isProbability W hpos i
  letI : IsProbabilityMeasure ν := hν
  have hz : Measurable z := measurable_clampedPredecessorCoordinates W order i
  have hg : Measurable g := (continuous_predecessorScoreMap W hpos order i).measurable
  have hf : Measurable f := measurable_equationElevenClampedScore W hpos order i
  have hκ : ∀ a, κ (g a) = Measure.map (fun b => f (a, b)) ν :=
    equationElevenAmbientKernel_apply_scoreMap
      s W hpos hmix hone hsign horder hgraphOrder i
  have hbase := predecessorCoordinates_independent_target W hpos horder hgraphOrder i
  change Measure.map (fun v => (z v, v (W.targetPerm i))) μ =
    (Measure.map z μ).prod ν at hbase
  have hpair : Measurable (fun v : LatentState n => (z v, v (W.targetPerm i))) := by
    fun_prop
  have hgf : Measurable (fun p : PredecessorLatentCube order i × ℝ =>
      (g p.1, f p)) := by fun_prop
  have hmap := congrArg (Measure.map (fun p : PredecessorLatentCube order i × ℝ =>
    (g p.1, f p))) hbase
  have hlatent : Measure.map latentJoint μ = Measure.map g (Measure.map z μ) ⊗ₘ κ := by
    calc
      Measure.map latentJoint μ = Measure.map (fun p : PredecessorLatentCube order i × ℝ =>
          (g p.1, f p)) (Measure.map (fun v => (z v, v (W.targetPerm i))) μ) := by
        rw [Measure.map_map hgf hpair]
        rfl
      _ = Measure.map (fun p : PredecessorLatentCube order i × ℝ =>
          (g p.1, f p)) ((Measure.map z μ).prod ν) := hmap
      _ = Measure.map g (Measure.map z μ) ⊗ₘ κ :=
        map_prod_compProd_of_fiber (Measure.map z μ) ν g hg f hf κ hκ
  have hcube : ∀ᵐ v ∂μ, v ∈ latentCube n := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with v hv
    simpa [μ, interventionalLaw_support_eq_latentCube W hpos i] using hv
  have hlatent_obs : latentJoint =ᵐ[μ] observedJoint ∘ W.mix := by
    filter_upwards [hcube] with v hv
    apply Prod.ext
    · dsimp only [latentJoint, observedJoint, g, z]
      rw [clampedPredecessorCoordinates_of_mem W order i v hv]
      exact predecessorScoreMap_of_latentState W hpos hmix hone horder hgraphOrder i v hv
    · exact equationElevenClampedScore_of_latentState
        W hpos hmix hone horder hgraphOrder i v hv
  have hmixAE : AEMeasurable W.mix μ := by
    apply Causalean.Mathlib.MeasureTheory.aemeasurable_of_supportMeasurableOn (by
      rw [latentCube]
      exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc))
      hcube hmix.1.continuousOn.domRestrict.measurable
  have hobsJoint : Measurable observedJoint := by
    dsimp only [observedJoint]
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro j
      exact measurable_observedLawLogRatio W.law j
    · exact measurable_observedLawLogRatio W.law i
  have hpushed : Measure.map observedJoint (W.law i.succ) = Measure.map latentJoint μ := by
    rw [hone.2.1 i]
    rw [AEMeasurable.map_map_of_aemeasurable hobsJoint.aemeasurable hmixAE]
    exact Measure.map_congr hlatent_obs.symm
  have hpredAE : (g ∘ z) =ᵐ[μ]
      (familyProjection (observedLawLogRatio W.law) (predecessorSet order i)) ∘ W.mix := by
    filter_upwards [hcube] with v hv
    dsimp only [g, z, Function.comp_apply]
    rw [clampedPredecessorCoordinates_of_mem W order i v hv]
    exact predecessorScoreMap_of_latentState W hpos hmix hone horder hgraphOrder i v hv
  have hpredMeas : Measurable
      (familyProjection (observedLawLogRatio W.law) (predecessorSet order i)) := by
    apply measurable_pi_lambda
    intro j
    exact measurable_observedLawLogRatio W.law j
  have hpredPushed : Measure.map
      (familyProjection (observedLawLogRatio W.law) (predecessorSet order i))
        (W.law i.succ) = Measure.map g (Measure.map z μ) := by
    rw [hone.2.1 i]
    rw [AEMeasurable.map_map_of_aemeasurable hpredMeas.aemeasurable hmixAE]
    rw [Measure.map_map hg hz]
    exact Measure.map_congr hpredAE.symm
  rw [hpushed, hlatent, hpredPushed]

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
