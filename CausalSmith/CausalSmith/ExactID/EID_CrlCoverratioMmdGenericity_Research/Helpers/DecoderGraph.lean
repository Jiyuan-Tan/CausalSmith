module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCore
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRank
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Ratio-graph reconstruction for the exact decoder

This file proves equations (4)--(6): nonancestor interventions cannot create ratio-law
edges, ancestral covers generate the latent transitive closure, and every ratio-graph
topological ordering places latent parents before their children.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Environment-label parents obtained by pulling back the latent parent set. -/
def environmentParentSet {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => G.edge (W.targetPerm j) (W.targetPerm i))

-- @node: PermutedGraphOrdered
/-- A numeric order respects every latent edge after intervention-label relabeling. -/
def PermutedGraphOrdered
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) : Prop :=
  ∀ ⦃j i⦄, permutedGraph G W j i → order j < order i

-- @node: permutedGraphOrdered_of_transitiveClosure
/-- Transitive-closure recovery makes every ratio-graph topological order respect latent edges.  Given [the stated inputs and conditions](hyp:horder,htc), [the stated conclusion](goal) follows. -/
lemma permutedGraphOrdered_of_transitiveClosure
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (htc : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W)) :
    PermutedGraphOrdered W order := by
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

/-- The observational canonical-ratio law is invariant under the supplied support
diffeomorphism.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma canonical_observationalRatioLaw_eq_supplied
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (i : Fin n) :
    observationalRatioLaw (canonicalObservedWorld G θ W.targetPerm) i =
      observationalRatioLaw W i := by
  have hcanonical : observedLawRatio (canonicalObservedWorld G θ W.targetPerm).law i =
      fun v => ((interventionalLaw θ (W.targetPerm i)).rnDeriv
        (observationalLaw θ) v).toReal := by
    rfl
  rw [observationalRatioLaw, observationalRatioLaw, hcanonical, hone.1]
  exact canonicalRatio_map_eq_observedLawRatio_map_mix W hpos hmix hone i
    (observationalLaw θ) Measure.AbsolutelyContinuous.rfl

/-- Every intervention-base canonical-ratio law is likewise invariant under the supplied
support diffeomorphism.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma canonical_interventionalRatioLaw_eq_supplied
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (j i : Fin n) :
    interventionalRatioLaw (canonicalObservedWorld G θ W.targetPerm) j i =
      interventionalRatioLaw W j i := by
  have hcanonical : observedLawRatio (canonicalObservedWorld G θ W.targetPerm).law i =
      fun v => ((interventionalLaw θ (W.targetPerm i)).rnDeriv
        (observationalLaw θ) v).toReal := by
    rfl
  rw [interventionalRatioLaw, interventionalRatioLaw, hcanonical, hone.2.1 j]
  exact canonicalRatio_map_eq_observedLawRatio_map_mix W hpos hmix hone i
    (interventionalLaw θ (W.targetPerm j))
    (interventionalLaw_absolutelyContinuous_observational W hpos j)

/-- Hence the canonical-world discrepancy used by cover separation is exactly the observable
discrepancy of the supplied law family.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma canonical_populationDiscrepancy_eq_observedLawDiscrepancy
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (j i : Fin n) :
    populationDiscrepancy U (canonicalObservedWorld G θ W.targetPerm) j i =
      observedLawDiscrepancy U W.law j i := by
  unfold populationDiscrepancy observedLawDiscrepancy
  rw [canonical_observationalRatioLaw_eq_supplied W hpos hmix hone i,
    canonical_interventionalRatioLaw_eq_supplied W hpos hmix hone j i]
  rfl

/-- Cover separation stated for the identity-mixing canonical world supplies exactly the cover
edges required for the observed world.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hcover), [the stated conclusion](goal) follows. -/
lemma canonical_coverDiscrepancy_to_supplied
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hcover : ∀ ⦃a b : Fin n⦄, ancestralCover G a b →
      0 < populationDiscrepancy U (canonicalObservedWorld G θ W.targetPerm)
        (W.targetPerm.symm a) (W.targetPerm.symm b)) :
    ∀ ⦃a b : Fin n⦄, ancestralCover G a b →
      0 < populationDiscrepancy U W
        (W.targetPerm.symm a) (W.targetPerm.symm b) := by
  intro a b hab
  have hc := hcover hab
  rw [canonical_populationDiscrepancy_eq_observedLawDiscrepancy
    U W hpos hmix hone] at hc
  exact hc

-- @node: ratio_nonancestor_zero
/-- A non-ancestor intervention leaves the corresponding ratio law unchanged, hence has zero MMD.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hne,hna), [the stated conclusion](goal) follows. -/
lemma ratio_nonancestor_zero
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {j i : Fin n} (hne : j ≠ i)
    (hna : ¬ G.isAncestor (W.targetPerm j) (W.targetPerm i)) :
    populationDiscrepancy gaussianFeatureMap W j i = 0 := by
  apply populationDiscrepancy_eq_zero_of_ratioLaw_eq
  exact FiniteDensityObservedWorldBridge.ratioLaw_eq_of_nonancestor
    (finiteDensityObservedWorldBridge_of_assumptions W hpos hmix hone) hne hna

-- @node: isAncestor_transGen_ancestralCover
/-- Every strict ancestor relation in a finite DAG factors through ancestral covers.  Given [the stated inputs and conditions](hyp:h), [the stated conclusion](goal) follows. -/
lemma isAncestor_transGen_ancestralCover
    {n : ℕ} (G : DAG (Fin n)) {a b : Fin n}
    (h : G.isAncestor a b) : Relation.TransGen (ancestralCover G) a b := by
  letI : LE (Fin n) := ⟨fun x y => x = y ∨ G.isAncestor x y⟩
  letI : LT (Fin n) := ⟨G.isAncestor⟩
  letI : PartialOrder (Fin n) := {
    le_refl x := Or.inl rfl
    le_trans x y z hxy hyz := by
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (G.isAncestor_trans hxy hyz)
    le_antisymm x y hxy hyx := by
      rcases hxy with rfl | hxy
      · rfl
      rcases hyx with rfl | hyx
      · rfl
      exact False.elim (G.isAncestor_irrefl x (G.isAncestor_trans hxy hyx))
    lt_iff_le_not_ge x y := by
      constructor
      · intro hxy
        exact ⟨Or.inr hxy, fun hyx => by
          rcases hyx with rfl | hyx
          · exact G.isAncestor_irrefl _ hxy
          · exact G.isAncestor_irrefl _ (G.isAncestor_trans hxy hyx)⟩
      · rintro ⟨hxy, hnxy⟩
        rcases hxy with rfl | hxy
        · exact False.elim (hnxy (Or.inl rfl))
        · exact hxy }
  letI : DecidableLE (Fin n) := Classical.decRel _
  letI : DecidableLT (Fin n) := Classical.decRel _
  letI : LocallyFiniteOrder (Fin n) := Fintype.toLocallyFiniteOrder
  exact transGen_covBy_of_lt h

-- @node: observedLawRatioGraph_edge_isAncestor
/-- Every observable ratio-graph edge points along the latent ancestral order.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hji), [the stated conclusion](goal) follows. -/
lemma observedLawRatioGraph_edge_isAncestor
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {j i : Fin n}
    (hji : observedLawRatioGraph gaussianFeatureMap W.law j i) :
    G.isAncestor (W.targetPerm j) (W.targetPerm i) := by
  by_contra hna
  have hz := ratio_nonancestor_zero (s := s) W hpos hmix hone hji.1 hna
  have hz' : observedLawDiscrepancy gaussianFeatureMap W.law j i = 0 := by
    exact hz
  exact (not_lt_of_ge hz'.le) hji.2

-- @node: ratioGraph_transitiveClosure_eq_of_cover
/-- Sound ratio edges plus all ancestral covers recover exactly the permuted latent
transitive closure.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hcover), [the stated conclusion](goal) follows. -/
lemma ratioGraph_transitiveClosure_eq_of_cover
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hcover : ∀ ⦃a b : Fin n⦄, ancestralCover G a b →
      0 < populationDiscrepancy gaussianFeatureMap W
        (W.targetPerm.symm a) (W.targetPerm.symm b)) :
    Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W) := by
  have hliftAncestor : ∀ {a b}, G.isAncestor a b →
      Relation.TransGen (permutedGraph G W) (W.targetPerm.symm a) (W.targetPerm.symm b) := by
    intro a b hji
    induction hji with
    | edge h => exact Relation.TransGen.single (by simpa [permutedGraph] using h)
    | trans hab hbc ih =>
        exact Relation.TransGen.tail ih (by simpa [permutedGraph] using hbc)
  have hancestorPath : ∀ {j i}, G.isAncestor (W.targetPerm j) (W.targetPerm i) →
      Relation.TransGen (permutedGraph G W) j i := by
    intro j i hji
    simpa using hliftAncestor hji
  have hforward : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) ≤
      Relation.TransGen (permutedGraph G W) := by
    apply Relation.TransGen.closed
    intro j i hji
    exact hancestorPath
      (observedLawRatioGraph_edge_isAncestor (s := s) W hpos hmix hone hji)
  have hcoverEdge : ∀ {a b : Fin n}, ancestralCover G a b →
      observedLawRatioGraph gaussianFeatureMap W.law
        (W.targetPerm.symm a) (W.targetPerm.symm b) := by
    intro a b hab
    have hne : W.targetPerm.symm a ≠ W.targetPerm.symm b := by
      intro heq
      have : a = b := W.targetPerm.symm.injective heq
      subst b
      exact G.isAncestor_irrefl a (@CovBy.lt (Fin n) ⟨G.isAncestor⟩ a a hab)
    refine ⟨hne, ?_⟩
    exact hcover hab
  have hmapCoverPath : ∀ {a b}, Relation.TransGen (ancestralCover G) a b →
      Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law)
        (W.targetPerm.symm a) (W.targetPerm.symm b) := by
    intro a b hc
    exact hc.lift W.targetPerm.symm (fun _ _ h => hcoverEdge h)
  have hpermEdge : ∀ {j i}, permutedGraph G W j i →
      Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) j i := by
    intro j i hji
    have hc := isAncestor_transGen_ancestralCover G (DAG.isAncestor.edge hji)
    simpa using hmapCoverPath hc
  exact le_antisymm hforward (Relation.TransGen.closed (fun _ _ h => hpermEdge h))

-- @node: environmentParentSet_subset_predecessorSet_of_transitiveClosure
/-- Once the ratio graph has the latent transitive closure, every topological ordering puts
all environment-label parents before their child.  Given [the stated inputs and conditions](hyp:horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma environmentParentSet_subset_predecessorSet_of_transitiveClosure
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    environmentParentSet W i ⊆ predecessorSet order i := by
  intro j hj
  have hedge : permutedGraph G W j i := by
    simpa [environmentParentSet, permutedGraph] using hj
  have hlt : order j < order i := hgraphOrder hedge
  simpa [predecessorSet] using hlt

-- @node: finTwo_edge_ancestralCover
/-- In a two-vertex DAG every directed edge is automatically a cover of the ancestral
order, since there is no third vertex that can lie strictly between its endpoints.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma finTwo_edge_ancestralCover (G : DAG (Fin 2)) {j i : Fin 2}
    (hji : G.edge j i) : ancestralCover G j i := by
  refine ⟨DAG.isAncestor.edge hji, ?_⟩
  intro c hjc hci
  have hj_ne_i : j ≠ i := by
    intro h
    subst i
    exact G.acyclic j (Relation.TransGen.single hji)
  have hj_ne_c : j ≠ c := by
    intro h
    subst c
    exact G.acyclic j ((G.isAncestor_iff_transGen).mp hjc)
  have hc_ne_i : c ≠ i := by
    intro h
    subst c
    exact G.acyclic i ((G.isAncestor_iff_transGen).mp hci)
  fin_cases j <;> fin_cases i <;> fin_cases c <;> simp_all

-- @node: bivariate_edge_discrepancy_pos_of_coverSeparated
/-- Cover separation supplies the bivariate Gaussian-MMD edge witness because every edge of a
two-vertex DAG is an ancestral cover.  Given [the stated inputs and conditions](hyp:hcover), [the stated conclusion](goal) follows. -/
lemma bivariate_edge_discrepancy_pos_of_coverSeparated
    {G : DAG (Fin 2)} {theta : Mechanism 2 G}
    (W : ObservedWorld G theta)
    (hcover : ∀ ⦃a b : Fin 2⦄, ancestralCover G a b →
      0 < populationDiscrepancy gaussianFeatureMap W
        (W.targetPerm.symm a) (W.targetPerm.symm b)) :
    ∀ ⦃j i⦄, G.edge j i →
      0 < observedLawDiscrepancy gaussianFeatureMap W.law
        (W.targetPerm.symm j) (W.targetPerm.symm i) := by
  intro j i hji
  simpa [observedLawDiscrepancy, populationDiscrepancy,
    observationalRatioLaw, interventionalRatioLaw] using
      hcover (finTwo_edge_ancestralCover G hji)

/-- The intervention target of a node cannot be a parent of any earlier node in a valid
ratio-graph topological ordering.  Given [the stated inputs and conditions](hyp:horder,hgraphOrder,hj), [the stated conclusion](goal) follows. -/
lemma target_not_parent_of_mem_predecessorSet
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    {j i : Fin n} (hj : j ∈ predecessorSet order i) :
    W.targetPerm i ∉ G.parents (W.targetPerm j) := by
  intro hparent
  have hi_env : i ∈ environmentParentSet W j := by
    simpa [environmentParentSet, DAG.parents] using hparent
  have hi_pred := environmentParentSet_subset_predecessorSet_of_transitiveClosure
    W horder hgraphOrder j hi_env
  have hji : order j < order i := by simpa [predecessorSet] using hj
  have hij : order i < order j := by simpa [predecessorSet] using hi_pred
  exact lt_asymm hji hij

/-- The triangular predecessor-score map recovers every predecessor's latent coordinate.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder,hv,hw,heq), [the stated conclusion](goal) follows. -/
lemma predecessorLogRatioProjection_injective_on_predecessors
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) {v w : LatentState n} (hv : v ∈ latentCube n) (hw : w ∈ latentCube n)
    (heq : familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v) =
      familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix w)) :
    ∀ j ∈ predecessorSet order i, v (W.targetPerm j) = w (W.targetPerm j) := by
  have hind : ∀ m : ℕ, ∀ j : Fin n, order j = m → j ∈ predecessorSet order i →
      v (W.targetPerm j) = w (W.targetPerm j) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hjorder hjpred
      have hparents : ∀ a ∈ G.parents (W.targetPerm j), v a = w a := by
        intro a ha
        let k := W.targetPerm.symm a
        have hk_env : k ∈ environmentParentSet W j := by
          simpa [k, environmentParentSet, DAG.parents] using ha
        have hk_pred_j := environmentParentSet_subset_predecessorSet_of_transitiveClosure
          W horder hgraphOrder j hk_env
        have hkj : order k < order j := by
          simpa [predecessorSet] using hk_pred_j
        have hji : order j < order i := by simpa [predecessorSet] using hjpred
        have hk_pred_i : k ∈ predecessorSet order i := by
          simpa [predecessorSet] using hkj.trans hji
        have hk := ih (order k) (by simpa [hjorder] using hkj) k rfl hk_pred_i
        simpa [k] using hk
      have hscore :
          Real.log (θ.q (W.targetPerm j) (v (W.targetPerm j)) /
              θ.p (W.targetPerm j) v) =
            Real.log (θ.q (W.targetPerm j) (w (W.targetPerm j)) /
              θ.p (W.targetPerm j) w) := by
        have hjscore := congrFun heq ⟨j, hjpred⟩
        simpa only [familyProjection,
          observedLawLogRatio_comp_mix_eq W hpos hmix hone j v hv,
          observedLawLogRatio_comp_mix_eq W hpos hmix hone j w hw] using hjscore
      exact (mechanismLogRatio_eq_iff_own_eq_of_parents_eq s θ hpos hsign
        (W.targetPerm j) hv hw hparents).mp hscore
  intro j hj
  exact hind (order j) j rfl hj

-- @node: observedLawRatioGraph_hasTopologicalOrdering
/-- Positivity and the shared perfect-intervention representation make the observed ratio graph
acyclic, witnessed by the latent DAG's topological order transported to environment labels.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedLawRatioGraph_hasTopologicalOrdering
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) :
    ∃ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order := by
  let order : Fin n → ℕ := fun i => G.topoOrder (W.targetPerm i)
  refine ⟨order, ?_, ?_⟩
  · exact G.topoOrder_injective.comp W.targetPerm.injective
  · intro j i hji
    exact G.isAncestor_topoOrder_lt
      (observedLawRatioGraph_edge_isAncestor (s := s) W hpos hmix hone hji)

-- @node: selectedTopologicalOrder_valid_of_assumptions
/-- Under the model assumptions, the decoder's internally selected ordering is a valid
topological ordering of the observed ratio graph.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma selectedTopologicalOrder_valid_of_assumptions
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) :
    IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law)
      (selectedTopologicalOrder (observedProbabilityLawFamily W.law)) := by
  classical
  let laws := observedProbabilityLawFamily W.law
  have hprob : ∀ e, IsProbabilityMeasure (W.law e) :=
    observedWorld_laws_isProbabilityMeasure W hpos hmix hone
  have hlaws : laws.1 = W.law := by
    simp [laws, observedProbabilityLawFamily, hprob]
  have hex : ∃ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order := by
    rw [hlaws]
    exact observedLawRatioGraph_hasTopologicalOrdering (s := s) W hpos hmix hone
  simpa only [hlaws] using selectedTopologicalOrder_isTopologicalOrdering laws hex

-- @node: ratioGraph_reconstruction_order_and_predecessors
/-- Equations (4)--(6) assemble into transitive-closure recovery, validity of the decoder's
selected order, and containment of every true parent among every valid order's predecessors.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hcover), [the stated conclusion](goal) follows. -/
lemma ratioGraph_reconstruction_order_and_predecessors
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hcover : ∀ ⦃a b : Fin n⦄, ancestralCover G a b →
      0 < populationDiscrepancy gaussianFeatureMap W
        (W.targetPerm.symm a) (W.targetPerm.symm b)) :
    Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
        Relation.TransGen (permutedGraph G W) ∧
    IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law)
      (selectedTopologicalOrder (observedProbabilityLawFamily W.law)) ∧
    ∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
      ∀ i, environmentParentSet W i ⊆ predecessorSet order i := by
  have htc := ratioGraph_transitiveClosure_eq_of_cover (s := s) W hpos hmix hone hcover
  refine ⟨htc, selectedTopologicalOrder_valid_of_assumptions (s := s) W hpos hmix hone, ?_⟩
  intro order horder i
  exact environmentParentSet_subset_predecessorSet_of_transitiveClosure W horder
    (permutedGraphOrdered_of_transitiveClosure W order horder htc) i

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
