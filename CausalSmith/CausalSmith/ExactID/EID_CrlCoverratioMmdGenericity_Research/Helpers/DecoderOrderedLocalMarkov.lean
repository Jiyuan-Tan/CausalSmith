module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderGraph
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.FiniteDensityBridge
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CondIndepIntersection

/-!
# Ordered local Markov bridge for decoder pruning

This module packages the finite-density ordered local Markov theorem in the
paper's `CondIndepGiven` interface under its observational law.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory

noncomputable section

open Causalean.Mathlib.MeasureTheory

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: permutedGraph_edge_lt_of_transitiveClosure
/-- A numeric topological order for the ratio graph also orders every latent edge once their
transitive closures agree.  Given [the stated inputs and conditions](hyp:horder,htc), [the stated conclusion](goal) follows. -/
lemma permutedGraph_edge_lt_of_transitiveClosure
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (htc : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W)) :
    ∀ ⦃j i⦄, permutedGraph G W j i → order j < order i := by
  intro j i hji
  have hpath : Relation.TransGen
      (observedLawRatioGraph gaussianFeatureMap W.law) j i := by
    rw [htc]
    exact Relation.TransGen.single hji
  have path_lt : ∀ {a b : Fin n},
      Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) a b →
        order a < order b := by
    intro a b hab
    induction hab with
    | single h => exact horder.2 h
    | tail hab h ih => exact lt_trans ih (horder.2 h)
  exact path_lt hpath

-- @node: latentTopologicalRankingOfPermutedOrder
/-- A topological order of the environment-label graph pulls back along the target permutation
to a topological ranking of the latent graph. -/
def latentTopologicalRankingOfPermutedOrder
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ)
    (hinj : Function.Injective order)
    (hedge : ∀ ⦃j i⦄, permutedGraph G W j i → order j < order i) :
    Causalean.Graph.FiniteDensity.TopologicalRanking G where
  rank := fun k ↦ order (W.targetPerm.symm k)
  injective_rank := hinj.comp W.targetPerm.symm.injective
  edge_lt := by
    intro j i hji
    apply hedge
    simpa [permutedGraph] using hji

-- @node: latentTopologicalRankingOfPermutedOrder_predecessors
/-- Predecessors in the pulled-back latent ranking are exactly target-permutation images of
the environment-label predecessors.  Given [the stated inputs and conditions](hyp:hinj,hedge), [the stated conclusion](goal) follows. -/
lemma latentTopologicalRankingOfPermutedOrder_predecessors
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ)
    (hinj : Function.Injective order)
    (hedge : ∀ ⦃j i⦄, permutedGraph G W j i → order j < order i)
    (k i : Fin n) :
    k ∈ Causalean.Graph.FiniteDensity.predecessors
        (latentTopologicalRankingOfPermutedOrder W order hinj hedge) (W.targetPerm i) ↔
      W.targetPerm.symm k ∈ predecessorSet order i := by
  simp [Causalean.Graph.FiniteDensity.predecessors, predecessorSet,
    latentTopologicalRankingOfPermutedOrder]

-- @node: mechanism_condIndepGiven_orderedLocalMarkov
/-- A positive normalized paper mechanism makes a latent coordinate conditionally independent
of the nonconditioned predecessors whenever the conditioning set contains all latent parents.  Given [the stated inputs and conditions](hyp:hpos,hA,hpa), [the stated conclusion](goal) follows. -/
lemma mechanism_condIndepGiven_orderedLocalMarkov
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (τ : Causalean.Graph.FiniteDensity.TopologicalRanking G)
    (i : Fin n) (A : Finset (Fin n))
    (hA : A ⊆ Causalean.Graph.FiniteDensity.predecessors τ i)
    (hpa : G.parents i ⊆ A) :
    CondIndepGiven (observationalLaw θ) (fun v : LatentState n ↦ v i)
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n ↦ ℝ)
        (Causalean.Graph.FiniteDensity.predecessors τ i \ A))
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n ↦ ℝ) A) := by
  rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
  rcases mechanism_orderedLocalMarkov hpos τ i A hA hpa with ⟨hfinite, hci⟩
  exact ⟨hfinite, measurable_pi_apply i,
    Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection _,
    Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection _, hci⟩

-- @node: mechanism_condIndepGiven_permutedOrderedLocalMarkov
/-- The ordered local-Markov property pulled back to environment labels: whenever an
environment conditioning set contains the target's environment-label parents, the target
latent coordinate is independent of all remaining predecessors.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder,hA,hpa), [the stated conclusion](goal) follows. -/
lemma mechanism_condIndepGiven_permutedOrderedLocalMarkov
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
    CondIndepGiven (observationalLaw θ)
      (fun v : LatentState n ↦ v (W.targetPerm i))
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n ↦ ℝ)
        ((predecessorSet order i).map W.targetPerm.toEmbedding \
          A.map W.targetPerm.toEmbedding))
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n ↦ ℝ) (A.map W.targetPerm.toEmbedding)) := by
  let τ := latentTopologicalRankingOfPermutedOrder W order horder.1 hgraphOrder
  have hpred : Causalean.Graph.FiniteDensity.predecessors τ (W.targetPerm i) =
      (predecessorSet order i).map W.targetPerm.toEmbedding := by
    ext k
    rw [latentTopologicalRankingOfPermutedOrder_predecessors
      W order horder.1 hgraphOrder k i]
    simp
  rw [← hpred]
  apply mechanism_condIndepGiven_orderedLocalMarkov hpos τ (W.targetPerm i)
      (A.map W.targetPerm.toEmbedding)
  · rw [hpred]
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨e, he, rfl⟩
    exact Finset.mem_map.mpr ⟨e, hA he, rfl⟩
  · intro k hk
    have hkEnv : W.targetPerm.symm k ∈ environmentParentSet W i := by
      simpa [environmentParentSet, DAG.parents] using hk
    exact Finset.mem_map.mpr ⟨W.targetPerm.symm k, hpa hkEnv,
      W.targetPerm.apply_symm_apply k⟩

-- @node: condIndepCoordinates_singletons_iff_condIndepGiven
/-- Singleton-block conditional independence is equivalent to its scalar-coordinate
presentation, with the same finite conditioning projection.  [the stated conclusion](goal) follows. -/
lemma condIndepCoordinates_singletons_iff_condIndepGiven
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (i b : Fin n) (Z : Finset (Fin n)) :
    CondIndepCoordinates θ {i} {b} Z ↔
      CondIndepGiven (observationalLaw θ)
        (fun v : LatentState n ↦ v i) (fun v : LatentState n ↦ v b)
        (coordinateProjection Z) := by
  constructor
  · rintro ⟨hfinite, hXi, hXb, hZ, hCI⟩
    letI := hfinite
    let evalI : ((j : {j // j ∈ ({i} : Finset (Fin n))}) → ℝ) → ℝ :=
      fun x ↦ x ⟨i, Finset.mem_singleton_self i⟩
    let evalB : ((j : {j // j ∈ ({b} : Finset (Fin n))}) → ℝ) → ℝ :=
      fun x ↦ x ⟨b, Finset.mem_singleton_self b⟩
    have hevalI : Measurable evalI := measurable_pi_apply _
    have hevalB : Measurable evalB := measurable_pi_apply _
    refine ⟨hfinite, measurable_pi_apply i, measurable_pi_apply b, hZ, ?_⟩
    simpa [evalI, evalB, coordinateProjection, Function.comp_def] using
      hCI.comp hevalI hevalB
  · rintro ⟨hfinite, hi, hb, hZ, hCI⟩
    letI := hfinite
    let singletonI : ℝ → ((j : {j // j ∈ ({i} : Finset (Fin n))}) → ℝ) :=
      fun r _ ↦ r
    let singletonB : ℝ → ((j : {j // j ∈ ({b} : Finset (Fin n))}) → ℝ) :=
      fun r _ ↦ r
    have hsingletonI : Measurable singletonI :=
      measurable_pi_lambda _ fun _ ↦ measurable_id
    have hsingletonB : Measurable singletonB :=
      measurable_pi_lambda _ fun _ ↦ measurable_id
    refine ⟨hfinite,
      Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection _,
      Causalean.Mathlib.MeasureTheory.FiniteCoordinate.measurable_coordinateProjection _, hZ, ?_⟩
    have hraw := hCI.comp hsingletonI hsingletonB
    convert hraw using 1
    · funext v j
      have hj : (j : Fin n) = i := Finset.mem_singleton.mp j.2
      change v j = v i
      exact congrArg v hj
    · funext v j
      have hj : (j : Fin n) = b := Finset.mem_singleton.mp j.2
      change v j = v b
      exact congrArg v hj

-- @node: parentOmission_intersection_core
/-- The decoder's weak-union independence and the ordered local-Markov independence combine,
by strict-positive-density intersection, to remove every nonparent predecessor from the
conditioning set of a putatively omitted parent.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hU,hPS,hAS,hiS,hbP,hbA,hCI,hMarkov), [the stated conclusion](goal) follows. -/
lemma parentOmission_intersection_core
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (i b : Fin n) (S P A : Finset (Fin n))
    (hU : ∀ c, Measurable (observedLatentCoordinate W c))
    (hPS : P ⊆ S) (hAS : A ⊆ S) (hiS : i ∉ S)
    (hbP : b ∈ P) (hbA : b ∉ A)
    (hCI : CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
      (familyProjection (observedLatentCoordinate W) (S \ A))
      (familyProjection (observedLatentCoordinate W) A))
    (hMarkov : CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
      (familyProjection (observedLatentCoordinate W) (S \ P))
      (familyProjection (observedLatentCoordinate W) P)) :
    CondIndepGiven (W.law 0) (observedLatentCoordinate W i)
      (observedLatentCoordinate W b)
      (familyProjection (observedLatentCoordinate W) (P.erase b)) := by
  classical
  let U := observedLatentCoordinate W
  have hU' : ∀ c, Measurable (U c) := hU
  letI : IsFiniteMeasure (W.law 0) := hCI.choose
  have hbS : b ∈ S := hPS hbP
  have hweak : CondIndepGiven (W.law 0) (U i) (U b)
      (familyProjection U (S.erase b)) :=
    (condIndep_coordSplit_prodMk U i b A S hU' hAS hbS hbA hCI).2
  let Z := P.erase b
  let C := S \ P
  have hib : i ≠ b := by
    intro h
    subst b
    exact hiS (hPS hbP)
  have hiZ : i ∉ Z := by
    intro hi
    exact hiS (hPS (Finset.mem_of_mem_erase hi))
  have hiC : i ∉ C := by
    intro hi
    exact hiS (Finset.mem_sdiff.mp hi).1
  have hbZ : b ∉ Z := by simp [Z]
  have hbC : b ∉ C := by
    intro hb
    exact (Finset.mem_sdiff.mp hb).2 hbP
  have hZC : Disjoint Z C := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxZ hxC
    exact (Finset.mem_sdiff.mp hxC).2 (Finset.mem_of_mem_erase hxZ)
  have hZCeq : Z ∪ C = S.erase b := by
    ext x
    simp only [Z, C, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff]
    constructor
    · rintro (⟨hxb, hxP⟩ | ⟨hxS, hxnotP⟩)
      · exact ⟨hxb, hPS hxP⟩
      · exact ⟨by intro h; subst x; exact hxnotP hbP, hxS⟩
    · rintro ⟨hxb, hxS⟩
      by_cases hxP : x ∈ P
      · exact Or.inl ⟨hxb, hxP⟩
      · exact Or.inr ⟨hxS, hxP⟩
  let eZC : ((j : {j // j ∈ S.erase b}) → ℝ) ≃ᵐ
      (((j : {j // j ∈ Z}) → ℝ) × ((j : {j // j ∈ C}) → ℝ)) :=
    (valuesEquivOfEq (Ω := fun _ : Fin n ↦ ℝ) hZCeq.symm).trans
      (MeasurableEquiv.piFinsetUnion (fun _ : Fin n ↦ ℝ) hZC).symm
  have heZC : eZC ∘ familyProjection U (S.erase b) =
      fun x => (familyProjection U Z x, familyProjection U C x) := by
    funext x
    ext j <;> rfl
  have h₁ : CondIndepGiven (W.law 0) (U i) (U b)
      (fun x => (familyProjection U Z x, familyProjection U C x)) := by
    rw [← heZC]
    exact (condIndepGiven_measurableEquiv_comp (U i) (U b)
      (familyProjection U (S.erase b)) (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.refl ℝ) eZC).2 hweak
  let singletonB : ((j : {j // j ∈ ({b} : Finset (Fin n))}) → ℝ) ≃ᵐ ℝ := {
    toFun x := x ⟨b, Finset.mem_singleton_self b⟩
    invFun r _ := r
    left_inv x := by
      funext j
      have hj : j = ⟨b, Finset.mem_singleton_self b⟩ :=
        Subtype.ext (Finset.mem_singleton.mp j.2)
      subst j
      rfl
    right_inv _ := rfl
    measurable_toFun := measurable_pi_apply _
    measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_id }
  have hZb : Disjoint Z ({b} : Finset (Fin n)) := by
    simpa [Finset.disjoint_singleton_right]
  have hZbeq : Z ∪ {b} = P := by
    rw [Finset.union_comm]
    exact Finset.insert_erase hbP
  let eZb : ((j : {j // j ∈ P}) → ℝ) ≃ᵐ
      (((j : {j // j ∈ Z}) → ℝ) × ℝ) :=
    (valuesEquivOfEq (Ω := fun _ : Fin n ↦ ℝ) hZbeq.symm).trans
      ((MeasurableEquiv.piFinsetUnion (fun _ : Fin n ↦ ℝ) hZb).symm.trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) singletonB))
  have heZb : eZb ∘ familyProjection U P =
      fun x => (familyProjection U Z x, U b x) := by
    funext x
    ext j <;> rfl
  have h₂ : CondIndepGiven (W.law 0) (U i) (familyProjection U C)
      (fun x => (familyProjection U Z x, U b x)) := by
    rw [← heZb]
    exact (condIndepGiven_measurableEquiv_comp (U i) (familyProjection U C)
      (familyProjection U P) (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.refl _) eZb).2 hMarkov
  exact (condIndep_intersection_of_pos W hpos hmix hone i b C Z hib hiC hiZ
    hbC hbZ hZC.symm h₁ h₂).1

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
