import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.RkhsEmpiricalMean
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.TExactRatioDecoder
import Mathlib.Order.Interval.Finset.Basic

/-!
# Simultaneous confidence edges

This file states the conditional and unconditional simultaneous MMD bounds,
soundness of selected edges, and transitive-closure recovery under a cover margin.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Every strict ancestor relation in a finite DAG factors through ancestral covers. -/
lemma isAncestor_transGen_ancestralCover
    {n : ℕ} (G : Causalean.DAG (Fin n)) {a b : Fin n}
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

/-- The event that every empirical MMD is within the simultaneous confidence radius. -/
def simultaneousMmdEvent
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    {W : ObservedWorld G θ} {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : SampleSplitWorld W Ω) (U : UnitNormFeatureMap H) : Set Ω :=
  {ω | ∀ j i : Fin n, j ≠ i →
    |empiricalDiscrepancy S U j i ω - populationDiscrepancy U W j i| ≤
      confidenceRadius S}

set_option maxHeartbeats 2000000 in
-- @node: thm:simultaneous-confidence-edges
/-- Under the simultaneous first-stage event, sample splitting yields familywise MMD confidence
bounds. Selected arrows are ancestral, and a two-radius cover margin recovers the true transitive
closure. -/
theorem simultaneous_confidence_edges
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    {Ω : Type*} [MeasurableSpace Ω] (S : SampleSplitWorld W Ω)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hSampling : IndependentEnvironmentSampling S)
    (hn : 1 ≤ n) (hN : ∀ e, 1 ≤ S.sampleSize e)
    (hα : S.alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hη : S.eta ∈ Set.Ioo (0 : ℝ) 1)
    (hfirst : 1 - S.eta ≤ S.probability.real (firstStageL1Event S)) :
    ConditionalProbabilityAtLeast S.probability
      (MeasurableSpace.comap (trainingFold S) inferInstance)
      (simultaneousMmdEvent S gaussianFeatureMap) (firstStageL1Event S)
      (1 - S.alpha) ∧
    1 - S.alpha - S.eta ≤
      S.probability.real (simultaneousMmdEvent S gaussianFeatureMap) ∧
    (∀ ω ∈ simultaneousMmdEvent S gaussianFeatureMap, ∀ j i,
      sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω j i →
      G.isAncestor (W.targetPerm j) (W.targetPerm i)) ∧
    ((∀ j i, ancestralCover G (W.targetPerm j) (W.targetPerm i) →
        2 * confidenceRadius S < populationDiscrepancy gaussianFeatureMap W j i) →
      ∀ ω ∈ simultaneousMmdEvent S gaussianFeatureMap,
        Relation.TransGen (sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω) =
          Relation.TransGen (permutedGraph G W)) := by
  classical
  letI : IsProbabilityMeasure S.probability := hSampling.1
  letI : MeasurableSpace (lp (fun _ : ℕ => ℝ) 2) := borel _
  letI : BorelSpace (lp (fun _ : ℕ => ℝ) 2) := ⟨rfl⟩
  let R : ℝ := (1 + Real.sqrt (2 * Real.log
      ((n : ℝ) * (n + 1 : ℝ) / S.alpha))) /
      Real.sqrt (minimumSampleSize S)
  let Good : Set Ω := {ω | ∀ i : Fin n, ∀ e : Fin (n + 1),
    ‖empiricalMeanEmbedding S gaussianFeatureMap e i ω -
      fittedMeanEmbedding S gaussianFeatureMap e i ω‖ ≤ R}
  have hcondSampling := hSampling.toConditionalEvaluationSampling
  have hgood : ConditionalProbabilityAtLeast S.probability
      (MeasurableSpace.comap (trainingFold S) inferInstance)
      Good Set.univ (1 - S.alpha) := by
    simpa only [Good, R] using
      bounded_rkhs_empirical_mean S gaussianFeatureMap hcondSampling hn hN hα
  have hlaw : ∀ e, IsProbabilityMeasure (W.law e) := hSampling.2.1
  have hbridge (ω : Ω) (hω : ω ∈ firstStageL1Event S)
      (i : Fin n) (e : Fin (n + 1)) :
      ‖fittedMeanEmbedding S gaussianFeatureMap e i ω -
        meanEmbedding gaussianFeatureMap
          (Measure.map (observedLawRatio W.law i) (W.law e))‖ ≤
          Real.sqrt 2 * S.firstStageRadius S.eta := by
    letI : IsProbabilityMeasure (W.law e) := hlaw e
    exact (meanEmbedding_map_sub_le_l1 gaussianFeatureMap (W.law e)
      (S.ratioEstimate ω i) (observedLawRatio W.law i)
      (S.ratioFit_measurable (trainingFold S ω) i)
      (measurable_observedLawRatio W.law i) (hω i e).1).trans
        (mul_le_mul_of_nonneg_left (hω i e).2 (Real.sqrt_nonneg _))
  have hGoodEvent : Good ∩ firstStageL1Event S ⊆
      simultaneousMmdEvent S gaussianFeatureMap := by
    intro ω hω
    intro j i hji
    have hjEval := hω.1 i j.succ
    have h0Eval := hω.1 i 0
    have hjFit := hbridge ω hω.2 i j.succ
    have h0Fit := hbridge ω hω.2 i 0
    let Ej := empiricalMeanEmbedding S gaussianFeatureMap j.succ i ω
    let E0 := empiricalMeanEmbedding S gaussianFeatureMap 0 i ω
    let Fj := fittedMeanEmbedding S gaussianFeatureMap j.succ i ω
    let F0 := fittedMeanEmbedding S gaussianFeatureMap 0 i ω
    let Pj := meanEmbedding gaussianFeatureMap
      (Measure.map (observedLawRatio W.law i) (W.law j.succ))
    let P0 := meanEmbedding gaussianFeatureMap
      (Measure.map (observedLawRatio W.law i) (W.law 0))
    have hvec : ‖(Ej - E0) - (Pj - P0)‖ ≤
        2 * R + 2 * (Real.sqrt 2 * S.firstStageRadius S.eta) := by
      calc
        ‖(Ej - E0) - (Pj - P0)‖ = ‖(Ej - Fj) + (Fj - Pj) -
            ((E0 - F0) + (F0 - P0))‖ := by congr 1 <;> abel
        _ ≤ ‖Ej - Fj‖ + ‖Fj - Pj‖ + (‖E0 - F0‖ + ‖F0 - P0‖) := by
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ ≤ R + (Real.sqrt 2 * S.firstStageRadius S.eta) +
            (R + (Real.sqrt 2 * S.firstStageRadius S.eta)) := by
          gcongr
        _ = 2 * R + 2 * (Real.sqrt 2 * S.firstStageRadius S.eta) := by ring
    have hnorm : |‖Ej - E0‖ - ‖Pj - P0‖| ≤
        2 * R + 2 * (Real.sqrt 2 * S.firstStageRadius S.eta) :=
      (abs_norm_sub_norm_le (Ej - E0) (Pj - P0)).trans hvec
    have hrev : ‖Pj - P0‖ = ‖P0 - Pj‖ := norm_sub_rev _ _
    rw [hrev] at hnorm
    have hfinal : |‖Ej - E0‖ - ‖P0 - Pj‖| ≤ confidenceRadius S := by
      convert hnorm using 1 <;> simp only [confidenceRadius, R] <;> ring
    simpa only [empiricalDiscrepancy, populationDiscrepancy,
      observationalRatioLaw, interventionalRatioLaw, Ej, E0, Pj, P0] using hfinal
  have hconditional : ConditionalProbabilityAtLeast S.probability
      (MeasurableSpace.comap (trainingFold S) inferInstance)
      (simultaneousMmdEvent S gaussianFeatureMap) (firstStageL1Event S)
      (1 - S.alpha) := by
    intro B hB
    have hA : @MeasurableSet Ω (MeasurableSpace.comap (trainingFold S) inferInstance)
        (firstStageL1Event S) := hSampling.2.2.2.2.2.2.2.2.2.2.2
    have hg := hgood (firstStageL1Event S ∩ B) (hA.inter hB)
    simp only [Set.univ_inter, Set.inter_assoc] at hg
    exact hg.trans (measureReal_mono
      (by
        intro ω hω
        exact ⟨⟨hGoodEvent ⟨hω.1, hω.2.1⟩, hω.2.1⟩, hω.2.2⟩)
      (measure_ne_top _ _))
  refine ⟨hconditional, ?_, ?_, ?_⟩
  · have hc := hconditional Set.univ MeasurableSet.univ
    simp only [Set.inter_univ] at hc
    have hEA : S.probability.real
        (simultaneousMmdEvent S gaussianFeatureMap ∩ firstStageL1Event S) ≤
        S.probability.real (simultaneousMmdEvent S gaussianFeatureMap) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have hnonneg : 0 ≤ 1 - S.alpha := by linarith [hα.2]
    have hmul := mul_le_mul_of_nonneg_left hfirst hnonneg
    nlinarith [hη.1, hα.1]
  · intro ω hω j i hedge
    by_contra hna
    have hz := ratio_nonancestor_zero (s := s) W hpos hmix hone hedge.1 hna
    have herr := hω j i hedge.1
    rw [hz, sub_zero] at herr
    have hem : 0 ≤ empiricalDiscrepancy S gaussianFeatureMap j i ω := by
      exact norm_nonneg _
    rw [abs_of_nonneg hem] at herr
    unfold sampleSplitConfidenceGraph at hedge
    linarith
  · intro hmargin ω hω
    have hedge : ∀ {j i},
        sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω j i →
        G.isAncestor (W.targetPerm j) (W.targetPerm i) := by
      intro j i hji
      apply Classical.byContradiction
      intro hna
      have hz := ratio_nonancestor_zero (s := s) W hpos hmix hone hji.1 hna
      have herr := hω j i hji.1
      rw [hz, sub_zero] at herr
      have hem : 0 ≤ empiricalDiscrepancy S gaussianFeatureMap j i ω := by
        exact norm_nonneg _
      rw [abs_of_nonneg hem] at herr
      unfold sampleSplitConfidenceGraph at hji
      linarith
    have hliftAncestor : ∀ {a b}, G.isAncestor a b →
        Relation.TransGen (permutedGraph G W)
          (W.targetPerm.symm a) (W.targetPerm.symm b) := by
      intro a b hji
      induction hji with
      | edge h =>
          apply Relation.TransGen.single
          simpa [permutedGraph] using h
      | trans hab hbc ih =>
          apply Relation.TransGen.tail ih
          simpa [permutedGraph] using hbc
    have hancestorPath : ∀ {j i}, G.isAncestor (W.targetPerm j) (W.targetPerm i) →
        Relation.TransGen (permutedGraph G W) j i := by
      intro j i hji
      simpa using hliftAncestor hji
    have hforward : Relation.TransGen
        (sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω) ≤
        Relation.TransGen (permutedGraph G W) := by
      intro j i hji
      induction hji with
      | single h => exact hancestorPath (hedge h)
      | tail hab hbc ih => exact ih.trans (hancestorPath (hedge hbc))
    have hcoverEdge : ∀ {a b : Fin n}, ancestralCover G a b →
        sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω
          (W.targetPerm.symm a) (W.targetPerm.symm b) := by
      intro a b hab
      have hne : W.targetPerm.symm a ≠ W.targetPerm.symm b := by
        intro heq
        have : a = b := W.targetPerm.symm.injective heq
        subst b
        have hab' : G.isAncestor a a := by
          exact (@CovBy.lt (Fin n) ⟨G.isAncestor⟩ a a hab)
        exact G.isAncestor_irrefl a hab'
      have hD := hmargin (W.targetPerm.symm a) (W.targetPerm.symm b) (by simpa)
      have herr := hω (W.targetPerm.symm a) (W.targetPerm.symm b) hne
      unfold sampleSplitConfidenceGraph
      refine ⟨hne, ?_⟩
      have hlow := (abs_le.mp herr).1
      linarith
    have hmapCoverPath : ∀ {a b}, Relation.TransGen (ancestralCover G) a b →
        Relation.TransGen
          (sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω)
          (W.targetPerm.symm a) (W.targetPerm.symm b) := by
      intro a b hc
      induction hc with
      | single h => exact Relation.TransGen.single (hcoverEdge h)
      | tail hab hbc ih => exact Relation.TransGen.tail ih (hcoverEdge hbc)
    have hpermEdge : ∀ {j i}, permutedGraph G W j i →
        Relation.TransGen
          (sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω) j i := by
      intro j i hji
      have ha : G.isAncestor (W.targetPerm j) (W.targetPerm i) :=
        Causalean.DAG.isAncestor.edge hji
      have hc := isAncestor_transGen_ancestralCover G ha
      have mapped := hmapCoverPath hc
      simpa using mapped
    have hbackward : Relation.TransGen (permutedGraph G W) ≤
        Relation.TransGen
          (sampleSplitConfidenceGraph S gaussianFeatureMap hSampling ω) := by
      intro j i hji
      induction hji with
      | single h => exact hpermEdge h
      | tail hab hbc ih => exact ih.trans (hpermEdge hbc)
    apply le_antisymm
    · exact hforward
    · exact hbackward

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
