module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingPosterior

/-!
# Finite Bayes identities for the full planted graph

Singleton masses identify the declared graph likelihood and posterior denominator
with the actual acquired-graph law, including reports of zero marginal mass.
-/

public section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable

/-- [Each recorded Bernoulli bit has the declared atom probability.](goal) -/
-- @node: graphBayes_bernoulli_singleton
lemma graphBayes_bernoulli_singleton (p : ℝ) (b : Bool) :
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p {b} =
      ENNReal.ofReal (if b then p else 1 - p) := by
  cases b <;> simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw]

/-- Given [the stated assumptions](hyp:hfit,hqr), [The product likelihood is the atom mass of the full labeled acquisition law.](goal) -/
-- @node: acquisitionLaw_matching_singleton
lemma acquisitionLaw_matching_singleton (n m : ℕ) (hfit : 2 * m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) (M : Matching m) :
    acquisitionLaw (matchingGraphSchedule n m hfit M) q r {H} =
      ENNReal.ofReal (graphLikelihood n m hfit q r H M) := by
  have hq : q ∈ Set.Icc 0 1 := ⟨hqr.1.trans hqr.2.1, hqr.2.2⟩
  have hr : r ∈ Set.Icc 0 1 := ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩
  let : ∀ e : OffDiag (Fin n), IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
        (if (matchingGraphSchedule n m hfit M).edge e.1.1 e.1.2 then q else r)) := fun e => by
    split <;>
      exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
        _ (by assumption)
  unfold acquisitionLaw
  rw [Measure.pi_singleton]
  simp only [graphBayes_bernoulli_singleton, matchingGraphSchedule]
  unfold graphLikelihood
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro e _
    by_cases he : matchingEdge n m hfit M e.1.1 e.1.2
    all_goals cases H e <;> simp [he]
  · intro e _
    split_ifs <;> linarith [hq.1, hq.2, hr.1, hr.2]

/-- Given [the stated assumptions](hyp:hfit,hqr), [The actual planted graph atom is the finite Bayes denominator.](goal) -/
-- @node: plantedGraphLaw_singleton
lemma plantedGraphLaw_singleton (n m : ℕ) (hfit : 2 * m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) :
    plantedGraphLaw n m hfit q r {H} =
      ENNReal.ofReal (∑ M : Matching m, posteriorWeight n m hfit q r H M) := by
  unfold plantedGraphLaw
  rw [Measure.bind_apply (measurableSet_singleton H) Measurable.of_discrete.aemeasurable]
  unfold matchingPrior
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul,
    lintegral_dirac' _ Measurable.of_discrete,
    acquisitionLaw_matching_singleton n m hfit q r hqr H]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun M _ => posteriorWeight_nonneg n m hfit q r hqr H M)]
  apply Finset.sum_congr rfl
  intro M _
  exact (ENNReal.ofReal_mul (matchingPriorMass_nonneg m M)).symm

/-- Given [the stated assumptions](hyp:hfit,hqr), [Multiplying the posterior by its marginal mass recovers every joint weight,
even at reports where the marginal mass vanishes.](goal) -/
-- @node: matchingPosterior_mul_denominator
lemma matchingPosterior_mul_denominator (n m : ℕ) (hfit : 2 * m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) (M : Matching m) :
    matchingPosterior n m hfit q r H M *
        (∑ M' : Matching m, posteriorWeight n m hfit q r H M') =
      posteriorWeight n m hfit q r H M := by
  unfold matchingPosterior
  split_ifs with hz
  · have hle := Finset.single_le_sum
      (fun M' _ => posteriorWeight_nonneg n m hfit q r hqr H M') (Finset.mem_univ M)
    rw [hz] at hle
    have hw := le_antisymm hle (posteriorWeight_nonneg n m hfit q r hqr H M)
    rw [hz, mul_zero, hw]
  · exact div_mul_cancel₀ _ hz

/-- Given [the stated assumptions](hyp:hfit,hqr), [Bayes' formula relates the declared posterior to the actual full-report atoms.](goal) -/
-- @node: matchingPosterior_graphBayes
lemma matchingPosterior_graphBayes (n m : ℕ) (hfit : 2 * m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) (M : Matching m) :
    ENNReal.ofReal (matchingPosterior n m hfit q r H M) *
        plantedGraphLaw n m hfit q r {H} =
      ENNReal.ofReal (matchingPriorMass m M) *
        acquisitionLaw (matchingGraphSchedule n m hfit M) q r {H} := by
  rw [plantedGraphLaw_singleton n m hfit q r hqr H,
    acquisitionLaw_matching_singleton n m hfit q r hqr H,
    ← ENNReal.ofReal_mul (matchingPosterior_nonneg n m hfit q r hqr H M),
    matchingPosterior_mul_denominator n m hfit q r hqr H M,
    posteriorWeight, ENNReal.ofReal_mul (matchingPriorMass_nonneg m M)]

/-- Given [the stated assumptions](hyp:hfit,hqr), [The posterior denominator is positive at almost every actual report.](goal) -/
-- @node: posterior_denominator_pos_ae
lemma posterior_denominator_pos_ae (n m : ℕ) (hfit : 2 * m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) :
    ∀ᵐ H ∂plantedGraphLaw n m hfit q r,
      0 < ∑ M : Matching m, posteriorWeight n m hfit q r H M := by
  apply ae_iff_of_countable.mpr
  intro H hH
  rw [plantedGraphLaw_singleton n m hfit q r hqr H] at hH
  exact lt_of_not_ge (fun h => hH (ENNReal.ofReal_eq_zero.mpr h))

/-- Given [the stated assumptions](hyp:hfit,hqr), [Tilting the actual graph marginal by one posterior mass recovers the
prior-weighted conditional acquisition measure.](goal) -/
-- @node: matchingPosterior_withDensity_plantedGraphLaw
lemma matchingPosterior_withDensity_plantedGraphLaw (n m : ℕ) (hfit : 2 * m ≤ n)
    (q r : ℝ) (hqr : ChannelDomain q r) (M : Matching m) :
    (plantedGraphLaw n m hfit q r).withDensity
        (fun H => ENNReal.ofReal (matchingPosterior n m hfit q r H M)) =
      ENNReal.ofReal (matchingPriorMass m M) •
        acquisitionLaw (matchingGraphSchedule n m hfit M) q r := by
  apply Measure.ext_of_singleton
  intro H
  rw [withDensity_apply _ (measurableSet_singleton H), lintegral_singleton,
    Measure.smul_apply, smul_eq_mul]
  exact matchingPosterior_graphBayes n m hfit q r hqr H M

end CausalSmith.Experimentation.NoisygraphTtePrecision
