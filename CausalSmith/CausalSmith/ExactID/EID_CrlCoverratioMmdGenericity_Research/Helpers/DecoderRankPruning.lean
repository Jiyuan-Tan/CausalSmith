module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderOrderedLocalMarkov
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRankCondIndep

/-!
# Rank-coordinate parent-pruning assembly

This module transports conditional independence between law-selected signed-CDF ranks and
measurable support-restricted latent coordinates, then combines ordered local Markov and
positive-density intersection to characterize the admissible parent sets exactly.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: observedLatentUnitCoordinate
/-- The support-restricted observed latent coordinate, bundled with its unit-interval range. -/
def observedLatentUnitCoordinate
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hmix : SharedDiffeomorphicMixing G θ W) (e : Fin n) :
    LatentState n → Set.Icc (0 : ℝ) 1 := fun x =>
  ⟨observedLatentCoordinate W e x, by
    classical
    by_cases hx : x ∈ observedSupport G W
    · rcases hx with ⟨v, hv, rfl⟩
      rw [observedLatentCoordinate_mix W hmix e v hv]
      exact hv _ (Set.mem_univ _)
    · simp [observedLatentCoordinate, hx]⟩

-- @node: measurable_observedLatentUnitCoordinate
/-- The unit-interval-valued observed latent coordinate is measurable.  Given [the stated inputs and conditions](hyp:hmix), [the stated conclusion](goal) follows. -/
lemma measurable_observedLatentUnitCoordinate
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hmix : SharedDiffeomorphicMixing G θ W) (e : Fin n) :
    Measurable (observedLatentUnitCoordinate W hmix e) :=
  (measurable_observedLatentCoordinate W hmix e).subtype_mk

-- @node: signedInterventionCDFFamilyChart
/-- Coordinatewise signed-CDF chart on a finite family of environment labels. -/
def signedInterventionCDFFamilyChart
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (W : ObservedWorld G θ) (A : Finset (Fin n)) :
    ((e : {e // e ∈ A}) → Set.Icc (0 : ℝ) 1) →
      ((e : {e // e ∈ A}) → Set.Icc (0 : ℝ) 1) :=
  fun z e => signedInterventionCDFChart s θ hpos (W.targetPerm e) (z e)

-- @node: signedInterventionCDFFamilyChart_measurableEmbedding
/-- Applying the signed intervention CDF separately in finitely many coordinates is a
measurable embedding.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma signedInterventionCDFFamilyChart_measurableEmbedding
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (W : ObservedWorld G θ) (A : Finset (Fin n)) :
    MeasurableEmbedding (signedInterventionCDFFamilyChart s θ hpos W A) := by
  apply Continuous.measurableEmbedding
  · apply continuous_pi
    intro e
    exact (continuous_signedInterventionCDFChart s θ hpos (W.targetPerm e)).comp
      (continuous_apply e)
  · intro x y hxy
    funext e
    exact (signedInterventionCDFChart_measurableEmbedding s θ hpos (W.targetPerm e)).injective
      (congrFun hxy e)

-- @node: unitFamilyVal
/-- Coordinatewise coercion from unit-interval-valued families to real-valued families. -/
def unitFamilyVal (A : Finset (Fin n)) :
    ((e : {e // e ∈ A}) → Set.Icc (0 : ℝ) 1) → ((e : {e // e ∈ A}) → ℝ) :=
  fun z e => z e

-- @node: unitFamilyVal_measurableEmbedding
/-- Coordinatewise coercion from a finite product of unit intervals is a measurable embedding.  [the stated conclusion](goal) follows. -/
lemma unitFamilyVal_measurableEmbedding (A : Finset (Fin n)) :
    MeasurableEmbedding (unitFamilyVal A) := by
  apply Continuous.measurableEmbedding
  · exact continuous_pi fun e => continuous_subtype_val.comp (continuous_apply e)
  · intro x y hxy
    funext e
    exact Subtype.ext (congrFun hxy e)

-- @node: rankCoordinate_condIndep_iff_observedLatent
/-- Pointwise identification of every selected rank with its signed intervention CDF transports
the decoder's conditional-independence test exactly to the support-restricted latent coordinates.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hrank), [the stated conclusion](goal) follows. -/
lemma rankCoordinate_condIndep_iff_observedLatent
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ)
    (hrank : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W.mix v) : ℝ) =
        signedInterventionCDF s θ (W.targetPerm e) (v (W.targetPerm e)))
    (i : Fin n) (Y Z : Finset (Fin n)) :
    CondIndepGiven (W.law 0) (observedLawRankCoordinate laws order i)
        (familyProjection (observedLawRankCoordinate laws order) Y)
        (familyProjection (observedLawRankCoordinate laws order) Z) ↔
      CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
        (familyProjection (observedLatentCoordinate W) Y)
        (familyProjection (observedLatentCoordinate W) Z) := by
  classical
  let U := fun e => observedLatentUnitCoordinate W hmix e
  let phi := fun e => signedInterventionCDFChart s θ hpos (W.targetPerm e)
  have hsupp : ∀ᵐ x ∂W.law 0, x ∈ observedSupport G W := by
    filter_upwards [Measure.support_mem_ae (μ := W.law 0)] with x hx
    rwa [observedLaw_support_eq_observedSupport W hpos hmix hone] at hx
  have hi : observedLawRankCoordinate laws order i =ᵐ[W.law 0] phi i ∘ U i := by
    filter_upwards [hsupp] with x hx
    rcases hx with ⟨v, hv, rfl⟩
    apply Subtype.ext
    simpa [phi, U, signedInterventionCDFChart, observedLatentUnitCoordinate,
      observedLatentCoordinate_mix W hmix i v hv] using hrank i v hv
  have hY : familyProjection (observedLawRankCoordinate laws order) Y =ᵐ[W.law 0]
      signedInterventionCDFFamilyChart s θ hpos W Y ∘ familyProjection U Y := by
    filter_upwards [hsupp] with x hx
    rcases hx with ⟨v, hv, rfl⟩
    funext e
    apply Subtype.ext
    simpa [signedInterventionCDFFamilyChart, familyProjection, U,
      signedInterventionCDFChart, observedLatentUnitCoordinate,
      observedLatentCoordinate_mix W hmix e v hv] using hrank e v hv
  have hZ : familyProjection (observedLawRankCoordinate laws order) Z =ᵐ[W.law 0]
      signedInterventionCDFFamilyChart s θ hpos W Z ∘ familyProjection U Z := by
    filter_upwards [hsupp] with x hx
    rcases hx with ⟨v, hv, rfl⟩
    funext e
    apply Subtype.ext
    simpa [signedInterventionCDFFamilyChart, familyProjection, U,
      signedInterventionCDFChart, observedLatentUnitCoordinate,
      observedLatentCoordinate_mix W hmix e v hv] using hrank e v hv
  have hU (e : Fin n) : Measurable (U e) :=
    measurable_observedLatentUnitCoordinate W hmix e
  have hUY (A : Finset (Fin n)) : Measurable (familyProjection U A) :=
    measurable_pi_lambda _ fun e => hU e
  have hcongr := condIndepGiven_congr_ae
    (measurable_observedLawRankCoordinate laws order i)
    ((signedInterventionCDFChart_measurableEmbedding s θ hpos (W.targetPerm i)).measurable.comp
      (hU i))
    (measurable_rankFamilyProjection laws order Y)
    ((signedInterventionCDFFamilyChart_measurableEmbedding s θ hpos W Y).measurable.comp (hUY Y))
    (measurable_rankFamilyProjection laws order Z)
    ((signedInterventionCDFFamilyChart_measurableEmbedding s θ hpos W Z).measurable.comp (hUY Z))
    hi hY hZ
  have hchart := condIndepGiven_measurableEmbedding_comp
    (μ := W.law 0)
    (U i) (familyProjection U Y) (familyProjection U Z)
    (signedInterventionCDFChart_measurableEmbedding s θ hpos (W.targetPerm i))
    (signedInterventionCDFFamilyChart_measurableEmbedding s θ hpos W Y)
    (signedInterventionCDFFamilyChart_measurableEmbedding s θ hpos W Z)
  have hval := condIndepGiven_measurableEmbedding_comp
    (μ := W.law 0)
    (U i) (familyProjection U Y) (familyProjection U Z)
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)
    (unitFamilyVal_measurableEmbedding Y) (unitFamilyVal_measurableEmbedding Z)
  have hvalI : ((fun z : Set.Icc (0 : ℝ) 1 => (z : ℝ)) ∘ U i) =
      observedLatentCoordinate W i := by
    funext x
    rfl
  have hvalY : unitFamilyVal Y ∘ familyProjection U Y =
      familyProjection (observedLatentCoordinate W) Y := by
    funext x e
    rfl
  have hvalZ : unitFamilyVal Z ∘ familyProjection U Z =
      familyProjection (observedLatentCoordinate W) Z := by
    funext x e
    rfl
  have hc : CondIndepGiven (W.law 0) (phi i ∘ U i)
        (signedInterventionCDFFamilyChart s θ hpos W Y ∘ familyProjection U Y)
        (signedInterventionCDFFamilyChart s θ hpos W Z ∘ familyProjection U Z) ↔
      CondIndepGiven (W.law 0) (U i) (familyProjection U Y) (familyProjection U Z) := by
    simpa [phi] using hchart
  have hv : CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
        (familyProjection (observedLatentCoordinate W) Y)
        (familyProjection (observedLatentCoordinate W) Z) ↔
      CondIndepGiven (W.law 0) (U i) (familyProjection U Y) (familyProjection U Z) := by
    rw [hvalI, hvalY, hvalZ] at hval
    exact hval
  exact hcongr.trans (hc.trans hv.symm)

-- @node: measurableMixVersion
/-- A globally measurable version of the mixing map, equal to it on the latent cube. -/
def measurableMixVersion
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) : LatentState n → LatentState n := by
  classical
  exact (latentCube n).piecewise W.mix (fun _ => 0)

-- @node: measurable_measurableMixVersion
/-- The support-restricted mixing-map version is measurable.  Given [the stated inputs and conditions](hyp:hmix), [the stated conclusion](goal) follows. -/
lemma measurable_measurableMixVersion
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hmix : SharedDiffeomorphicMixing G θ W) :
    Measurable (measurableMixVersion W) := by
  classical
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    measurability
  unfold measurableMixVersion
  exact hmix.1.continuousOn.measurable_piecewise continuous_const.continuousOn hcube

-- @node: observedLatent_condIndep_iff_latent
/-- Conditional independence of support-restricted observed latent coordinates is equivalent
to conditional independence of the target-permuted coordinates under the latent observational law.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedLatent_condIndep_iff_latent
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (i : Fin n) (Y Z : Finset (Fin n)) :
    CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
        (familyProjection (observedLatentCoordinate W) Y)
        (familyProjection (observedLatentCoordinate W) Z) ↔
      CondIndepGiven (observationalLaw θ) (fun v => v (W.targetPerm i))
        (familyProjection (fun e v => v (W.targetPerm e)) Y)
        (familyProjection (fun e v => v (W.targetPerm e)) Z) := by
  classical
  let mix' := measurableMixVersion W
  let V := fun e : Fin n => observedLatentCoordinate W e
  let X := fun e : Fin n => fun v : LatentState n => v (W.targetPerm e)
  have hmix' : Measurable mix' := measurable_measurableMixVersion W hmix
  have hV (e : Fin n) : Measurable (V e) := measurable_observedLatentCoordinate W hmix e
  have hVproj (A : Finset (Fin n)) : Measurable (familyProjection V A) :=
    measurable_pi_lambda _ fun e => hV e
  have hcube : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n :=
    observationalLaw_ae_mem_latentCube hpos
  have hmix_eq : W.mix =ᵐ[observationalLaw θ] mix' := by
    filter_upwards [hcube] with v hv
    simp [mix', measurableMixVersion, hv]
  have hlaw : W.law 0 = Measure.map mix' (observationalLaw θ) := by
    rw [hone.1]
    exact Measure.map_congr hmix_eq
  have hi : V i ∘ mix' =ᵐ[observationalLaw θ] X i := by
    filter_upwards [hcube, hmix_eq] with v hv hmv
    change V i (mix' v) = X i v
    rw [← hmv]
    exact observedLatentCoordinate_mix W hmix i v hv
  have hY : familyProjection V Y ∘ mix' =ᵐ[observationalLaw θ]
      familyProjection X Y := by
    filter_upwards [hcube, hmix_eq] with v hv hmv
    change familyProjection V Y (mix' v) = familyProjection X Y v
    rw [← hmv]
    funext e
    exact observedLatentCoordinate_mix W hmix e v hv
  have hZ : familyProjection V Z ∘ mix' =ᵐ[observationalLaw θ]
      familyProjection X Z := by
    filter_upwards [hcube, hmix_eq] with v hv hmv
    change familyProjection V Z (mix' v) = familyProjection X Z v
    rw [← hmv]
    funext e
    exact observedLatentCoordinate_mix W hmix e v hv
  letI : IsProbabilityMeasure (observationalLaw θ) :=
    observationalLaw_isProbabilityMeasure hpos
  have hmap := condIndepGiven_map_iff (mu := observationalLaw θ)
    hmix' (hV i) (hVproj Y) (hVproj Z)
  rw [← hlaw] at hmap
  have hcongr := condIndepGiven_congr_ae
    ((hV i).comp hmix') (measurable_pi_apply (W.targetPerm i))
    ((hVproj Y).comp hmix')
    (measurable_pi_lambda _ fun e => measurable_pi_apply (W.targetPerm e))
    ((hVproj Z).comp hmix')
    (measurable_pi_lambda _ fun e => measurable_pi_apply (W.targetPerm e))
    hi hY hZ
  exact hmap.symm.trans hcongr

-- @node: permutedValuesEquiv
/-- Reindexing a finite coordinate family along the world's target permutation. -/
def permutedValuesEquiv
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (A : Finset (Fin n)) :
    ((k : {k // k ∈ A.map W.targetPerm.toEmbedding}) → ℝ) ≃ᵐ
      ((e : {e // e ∈ A}) → ℝ) where
  toFun x e := x ⟨W.targetPerm e,
    Finset.mem_map.mpr ⟨e, e.2, rfl⟩⟩
  invFun y k := y ⟨W.targetPerm.symm k, by
    rcases Finset.mem_map.mp k.2 with ⟨e, he, hek⟩
    have heq : e = W.targetPerm.symm k := by
      apply W.targetPerm.injective
      simpa using hek
    simpa only [← heq] using he⟩
  left_inv x := by
    funext k
    apply congrArg x
    apply Subtype.ext
    simp
  right_inv y := by
    funext e
    apply congrArg y
    apply Subtype.ext
    simp
  measurable_toFun := measurable_pi_lambda _ fun e => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun k => measurable_pi_apply _

-- @node: singletonFamilyEquiv
/-- A one-coordinate finite family is measurably equivalent to its scalar coordinate. -/
def singletonFamilyEquiv (b : Fin n) :
    ((e : {e // e ∈ ({b} : Finset (Fin n))}) → ℝ) ≃ᵐ ℝ where
  toFun x := x ⟨b, Finset.mem_singleton_self b⟩
  invFun r _ := r
  left_inv x := by
    funext e
    apply congrArg x
    apply Subtype.ext
    exact (Finset.mem_singleton.mp e.2).symm
  right_inv _ := rfl
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_id

-- @node: mechanism_condIndepGiven_permutedOrderedLocalMarkov_env
/-- Ordered local Markov in environment-label coordinates, reindexing the latent projection
along the intervention-target permutation.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder,hA,hpa), [the stated conclusion](goal) follows. -/
lemma mechanism_condIndepGiven_permutedOrderedLocalMarkov_env
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) (A : Finset (Fin n))
    (hA : A ⊆ predecessorSet order i)
    (hpa : environmentParentSet W i ⊆ A) :
    CondIndepGiven (observationalLaw θ) (fun v => v (W.targetPerm i))
      (familyProjection (fun e v => v (W.targetPerm e))
        (predecessorSet order i \ A))
      (familyProjection (fun e v => v (W.targetPerm e)) A) := by
  classical
  let S := predecessorSet order i
  have hraw := mechanism_condIndepGiven_permutedOrderedLocalMarkov
    W hpos order horder hgraphOrder i A hA hpa
  have hmapdiff : S.map W.targetPerm.toEmbedding \ A.map W.targetPerm.toEmbedding =
      (S \ A).map W.targetPerm.toEmbedding := by
    ext k
    simp [S]
  rw [hmapdiff] at hraw
  have htransport := (condIndepGiven_measurableEquiv_comp
    (μ := observationalLaw θ)
    (fun v : LatentState n => v (W.targetPerm i))
    (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
      (X := fun _ : Fin n => ℝ) ((S \ A).map W.targetPerm.toEmbedding))
    (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
      (X := fun _ : Fin n => ℝ) (A.map W.targetPerm.toEmbedding))
    (MeasurableEquiv.refl ℝ) (permutedValuesEquiv W (S \ A))
    (permutedValuesEquiv W A)).2 hraw
  convert htransport using 1
  · rfl
  · funext x e
    rfl
  · funext x e
    rfl

-- @node: exactRankCondIndepCharacterization_of_order
/-- For every valid ratio-graph ordering, rank-coordinate conditional independence holds
exactly when the conditioning set contains all environment-label parents.  Given [the stated inputs and conditions](hyp:hpos,hminimal,hmix,hone,horder,hgraphOrder,hrank), [the stated conclusion](goal) follows. -/
lemma exactRankCondIndepCharacterization_of_order
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hminimal : CausalMinimality G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (hrank : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W.mix v) : ℝ) =
        signedInterventionCDF s θ (W.targetPerm e) (v (W.targetPerm e))) :
    ∀ i A, A ⊆ predecessorSet order i →
      (CondIndepGiven (W.law 0) (observedLawRankCoordinate laws order i)
        (familyProjection (observedLawRankCoordinate laws order)
          (predecessorSet order i \ A))
        (familyProjection (observedLawRankCoordinate laws order) A) ↔
      environmentParentSet W i ⊆ A) := by
  classical
  intro i A hAS
  let S := predecessorSet order i
  let P := environmentParentSet W i
  have hPS : P ⊆ S :=
    environmentParentSet_subset_predecessorSet_of_transitiveClosure W horder
      hgraphOrder i
  have hrankObs := rankCoordinate_condIndep_iff_observedLatent
    s W hpos hmix hone laws order hrank i (S \ A) A
  constructor
  · intro hCIrank
    have hCIobs : CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
        (familyProjection (observedLatentCoordinate W) (S \ A))
        (familyProjection (observedLatentCoordinate W) A) := hrankObs.1 hCIrank
    by_contra hnsub
    rw [Finset.not_subset] at hnsub
    rcases hnsub with ⟨b, hbP, hbA⟩
    have hmarkLat := mechanism_condIndepGiven_permutedOrderedLocalMarkov_env
      W hpos order horder hgraphOrder i P hPS (Finset.Subset.rfl)
    have hmarkObs := (observedLatent_condIndep_iff_latent
      W hpos hmix hone i (S \ P) P).2 hmarkLat
    have hiS : i ∉ S := by simp [S, predecessorSet]
    have hscalarObs := parentOmission_intersection_core W hpos hmix hone
      i b S P A (fun c => measurable_observedLatentCoordinate W hmix c)
      hPS hAS hiS hbP hbA hCIobs hmarkObs
    have hsingleObs : CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
        (familyProjection (observedLatentCoordinate W) {b})
        (familyProjection (observedLatentCoordinate W) (P.erase b)) := by
      have h := (condIndepGiven_measurableEquiv_comp
        (μ := W.law 0) (observedLatentCoordinate W i)
        (familyProjection (observedLatentCoordinate W) {b})
        (familyProjection (observedLatentCoordinate W) (P.erase b))
        (MeasurableEquiv.refl ℝ) (singletonFamilyEquiv b)
        (MeasurableEquiv.refl _)).1
      apply h
      simpa [singletonFamilyEquiv, familyProjection, Function.comp_def] using hscalarObs
    have hsingleLat := (observedLatent_condIndep_iff_latent
      W hpos hmix hone i {b} (P.erase b)).1 hsingleObs
    have hscalarLat : CondIndepGiven (observationalLaw θ)
        (fun v => v (W.targetPerm i)) (fun v => v (W.targetPerm b))
        (familyProjection (fun e v => v (W.targetPerm e)) (P.erase b)) := by
      have h := (condIndepGiven_measurableEquiv_comp
        (μ := observationalLaw θ) (fun v : LatentState n => v (W.targetPerm i))
        (familyProjection (fun (e : Fin n) (v : LatentState n) => v (W.targetPerm e)) {b})
        (familyProjection (fun (e : Fin n) (v : LatentState n) => v (W.targetPerm e)) (P.erase b))
        (MeasurableEquiv.refl ℝ) (singletonFamilyEquiv b)
        (MeasurableEquiv.refl _)).2 hsingleLat
      simpa [singletonFamilyEquiv, familyProjection, Function.comp_def] using h
    have hmapP : P.map W.targetPerm.toEmbedding = G.parents (W.targetPerm i) := by
      ext k
      simp [P, environmentParentSet, DAG.parents]
    have hmapErase : (P.erase b).map W.targetPerm.toEmbedding =
        (G.parents (W.targetPerm i)).erase (W.targetPerm b) := by
      rw [Finset.map_erase, hmapP]
      rfl
    have hactual : CondIndepGiven (observationalLaw θ)
        (fun v => v (W.targetPerm i)) (fun v => v (W.targetPerm b))
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
          (X := fun _ : Fin n => ℝ) ((G.parents (W.targetPerm i)).erase (W.targetPerm b))) := by
      have h := (condIndepGiven_measurableEquiv_comp
        (μ := observationalLaw θ) (fun v : LatentState n => v (W.targetPerm i))
        (fun v : LatentState n => v (W.targetPerm b))
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
          (X := fun _ : Fin n => ℝ) ((P.erase b).map W.targetPerm.toEmbedding))
        (MeasurableEquiv.refl ℝ) (MeasurableEquiv.refl ℝ)
        (permutedValuesEquiv W (P.erase b))).1 hscalarLat
      rw [← hmapErase]
      exact h
    have hedge : G.edge (W.targetPerm b) (W.targetPerm i) := by
      simpa [P, environmentParentSet, DAG.parents] using hbP
    exact hminimal hedge
      ((condIndepCoordinates_singletons_iff_condIndepGiven
        (W.targetPerm i) (W.targetPerm b)
        ((G.parents (W.targetPerm i)).erase (W.targetPerm b))).2 hactual)
  · intro hpa
    have hlat := mechanism_condIndepGiven_permutedOrderedLocalMarkov_env
      W hpos order horder hgraphOrder i A hAS hpa
    have hobs := (observedLatent_condIndep_iff_latent
      W hpos hmix hone i (S \ A) A).2 hlat
    exact hrankObs.2 hobs

-- @node: exactRankCondIndepCharacterization
/-- Transitive-closure recovery specializes the ordered characterization to every ratio order.  Given [the stated inputs and conditions](hyp:hpos,hminimal,hmix,hone,htc,horder,hrank), [the stated conclusion](goal) follows. -/
lemma exactRankCondIndepCharacterization
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hminimal : CausalMinimality G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (laws : ObservedProbabilityLawFamily n)
    (htc : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W))
    (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hrank : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W.mix v) : ℝ) =
        signedInterventionCDF s θ (W.targetPerm e) (v (W.targetPerm e))) :
    ∀ i A, A ⊆ predecessorSet order i →
      (CondIndepGiven (W.law 0) (observedLawRankCoordinate laws order i)
        (familyProjection (observedLawRankCoordinate laws order)
          (predecessorSet order i \ A))
        (familyProjection (observedLawRankCoordinate laws order) A) ↔
      environmentParentSet W i ⊆ A) :=
  exactRankCondIndepCharacterization_of_order s W hpos hminimal hmix hone laws
    order horder (permutedGraphOrdered_of_transitiveClosure W order horder htc) hrank

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
