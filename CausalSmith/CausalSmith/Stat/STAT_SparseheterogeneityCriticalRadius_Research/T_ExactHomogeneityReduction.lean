module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.ExactEndpointLower
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.ExactEndpointDesign
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.RateAlgebra
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Pilot
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Risk
public import Causalean.Stat.Minimax.MinimaxValue

/-! A direct exact-homogeneity estimator and same-class endpoint proposition. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable def exactClassRisk (n : ℕ) (M : ℝ) : ℝ :=
  ⨅ est : DiscreteAteHeterogeneityFrontier.Estimator n n M,
    ⨆ P : ExactClass n M, DiscreteAteHeterogeneityFrontier.mse P.1.law est.1

noncomputable def exactRegressionH (n : ℕ)
    (sample : Fin n → SampleObs n) : ℝ :=
  ∑ i : Fin n,
    ((if (sample i).a then (1 : ℝ) else 0) -
      exactTreatmentMean n sample (sample i).x) * (sample i).y

noncomputable def withinCellRegressionEstimator (n : ℕ) (M : ℝ)
    (sample : Fin n → SampleObs n) : ℝ :=
  clipM M (if 0 < exactRegressionD n sample then
    exactRegressionH n sample / exactRegressionD n sample else 0)

-- @node: exactRegressionH_measurable
lemma exactRegressionH_measurable (n : ℕ) :
    Measurable (exactRegressionH n) := by
  unfold exactRegressionH
  apply Finset.measurable_sum
  intro i hi
  have ha : Measurable (fun sample : Fin n → SampleObs n =>
      if (sample i).a then (1 : ℝ) else 0) := by
    apply Measurable.ite
    · exact (measurableSet_singleton true).preimage
        ((sampleObsA_measurable n).comp (measurable_pi_apply i))
    · exact measurable_const
    · exact measurable_const
  have hm : Measurable (fun sample : Fin n → SampleObs n =>
      exactTreatmentMean n sample (sample i).x) :=
    measurable_finite_lookup (n := n)
      (fun k sample => exactTreatmentMean n sample k)
      (fun sample => (sample i).x)
      (exactTreatmentMean_measurable n)
      ((sampleObsX_measurable n).comp (measurable_pi_apply i))
  exact (ha.sub hm).mul
    ((sampleObsY_measurable n).comp (measurable_pi_apply i))

-- @node: withinCellRegressionEstimator_measurable
lemma withinCellRegressionEstimator_measurable (n : ℕ) (M : ℝ) :
    Measurable (withinCellRegressionEstimator n M) := by
  unfold withinCellRegressionEstimator clipM
  have h : Measurable (fun sample : Fin n → SampleObs n =>
      if 0 < exactRegressionD n sample then
        exactRegressionH n sample / exactRegressionD n sample else 0) := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (exactRegressionD_measurable n)
    · exact (exactRegressionH_measurable n).div (exactRegressionD_measurable n)
    · exact measurable_const
  exact measurable_const.max (measurable_const.min h)

-- @node: withinCellRegressionEstimator_range
lemma withinCellRegressionEstimator_range (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∀ sample, withinCellRegressionEstimator n M sample ∈ Icc (-M) M := by
  intro sample
  simp only [withinCellRegressionEstimator, clipM, mem_Icc]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

-- @node: exactClass_to_radiusZero
lemma exactClass_to_radiusZero {n : ℕ} {M : ℝ} (P : ExactClass n M) :
    ∃ Q : KnownRadiusClass n M 0, Q.law = P.1.law := by
  let Q : KnownRadiusClass n M 0 :=
    { P.1 with
      radius := by
        refine ⟨⟨le_refl 0, by norm_num⟩, ?_⟩
        intro k hk
        have heq := P.2 k hk
        simp only [DiscreteAteHeterogeneityFrontier.cellDeviation]
        rw [heq]
        simp }
  exact ⟨Q, rfl⟩

-- @node: radiusZero_to_exactClass
lemma radiusZero_to_exactClass {n : ℕ} {M : ℝ}
    (Q : KnownRadiusClass n M 0) :
    ∃ P : ExactClass n M, P.1.law = Q.law := by
  let P : CriticalClass n M :=
    { Q with
      radius := by
        refine ⟨criticalRadius_range n Q.n_ge_three, ?_⟩
        intro k hk
        have hz := Q.radius.2 k hk
        have hzero : DiscreteAteHeterogeneityFrontier.cellDeviation Q.law k = 0 := by
          have : |DiscreteAteHeterogeneityFrontier.cellDeviation Q.law k| ≤ 0 := by
            simpa using hz
          exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
        rw [hzero, abs_zero]
        exact mul_nonneg (criticalRadius_range n Q.n_ge_three).1
          (by linarith [Q.M_ge_one]) }
  refine ⟨⟨P, ?_⟩, rfl⟩
  intro k hk
  have hz := Q.radius.2 k hk
  have : |DiscreteAteHeterogeneityFrontier.cellDeviation Q.law k| ≤ 0 := by
    simpa using hz
  have heq := abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  exact sub_eq_zero.mp heq

/-- Class equality in roadmap (2) preserves every observed-sample risk. -/
-- @node: exactClass_worstRisk_eq_radiusZero
lemma exactClass_worstRisk_eq_radiusZero (n : ℕ) (M : ℝ)
    (T : (Fin n → SampleObs n) → ℝ) :
    (⨆ P : ExactClass n M, DiscreteAteHeterogeneityFrontier.mse P.1.law T) =
      worstRisk n M 0 T := by
  unfold worstRisk
  change sSup (Set.range (fun P : ExactClass n M =>
    DiscreteAteHeterogeneityFrontier.mse P.1.law T)) =
    sSup (Set.range (fun Q : KnownRadiusClass n M 0 =>
      DiscreteAteHeterogeneityFrontier.mse Q.law T))
  congr 1
  ext r
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, hQ⟩ := exactClass_to_radiusZero P
    exact ⟨Q, congrArg (fun L : Law n => DiscreteAteHeterogeneityFrontier.mse L T) hQ⟩
  · rintro ⟨Q, rfl⟩
    obtain ⟨P, hP⟩ := radiusZero_to_exactClass Q
    exact ⟨P, congrArg (fun L : Law n => DiscreteAteHeterogeneityFrontier.mse L T) hP⟩

/-- The exact-homogeneity and supplied-radius-zero minimax problems coincide. -/
-- @node: exactClassRisk_eq_radiusZeroMinimaxRisk
lemma exactClassRisk_eq_radiusZeroMinimaxRisk (n : ℕ) (M : ℝ) :
    exactClassRisk n M = knownRadiusMinimaxRisk n M 0 := by
  unfold exactClassRisk knownRadiusMinimaxRisk
  simp_rw [exactClass_worstRisk_eq_radiusZero]

/-- The observable regression rule is an admissible estimator, so its worst-case risk
bounds the exact-class minimax value (proof roadmap, following (24)). -/
-- @node: exactClassRisk_le_regressionRisk
lemma exactClassRisk_le_regressionRisk (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    exactClassRisk n M ≤
      ⨆ P : ExactClass n M,
        DiscreteAteHeterogeneityFrontier.mse P.1.law
          (withinCellRegressionEstimator n M) := by
  let est : DiscreteAteHeterogeneityFrontier.Estimator n n M :=
    ⟨withinCellRegressionEstimator n M,
      withinCellRegressionEstimator_measurable n M,
      withinCellRegressionEstimator_range n M hM⟩
  exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (e : DiscreteAteHeterogeneityFrontier.Estimator n n M)
      (P : ExactClass n M) => DiscreteAteHeterogeneityFrontier.mse P.1.law e.1)
    (fun e P => integral_nonneg (fun _ => sq_nonneg _)) est

/-- The paper regression rule is precisely the library's guarded, clipped rule. -/
-- @node: withinCellRegressionEstimator_eq_library
lemma withinCellRegressionEstimator_eq_library (n : ℕ) (M : ℝ) :
    withinCellRegressionEstimator n M =
      Causalean.Stat.Sample.Stratified.TreatmentRegression.clippedEstimator
        (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y) M := by
  rfl

/-- The observed categorical design has the cell probabilities of the full law. -/
-- @node: exactDesign_cellProbability
lemma exactDesign_cellProbability {n : ℕ} (P : Law n) (k : Fin n) :
    Causalean.Stat.Sample.Stratified.TreatmentRegression.cellProbability
      (P.observedLaw.map (fun o : SampleObs n => (o.x, o.a))) k = P.cellMass k := by
  have hm : Measurable (fun o : SampleObs n => (o.x, o.a)) :=
    (sampleObsX_measurable n).prodMk (sampleObsA_measurable n)
  unfold Causalean.Stat.Sample.Stratified.TreatmentRegression.cellProbability
  rw [Measure.map_apply hm (show MeasurableSet {v : Fin n × Bool | v.1 = k} from
    measurableSet_eq_fun measurable_fst measurable_const)]
  exact (P.cellMass_eq k).symm

/-- Occupied design cells preserve the propensity of the original law. -/
-- @node: exactDesign_propensity
lemma exactDesign_propensity {n : ℕ} (P : Law n) (k : Fin n)
    (hk : 0 < P.cellMass k) :
    Causalean.Stat.Sample.Stratified.TreatmentRegression.propensity
      (P.observedLaw.map (fun o : SampleObs n => (o.x, o.a))) k = P.propensity k := by
  have hm : Measurable (fun o : SampleObs n => (o.x, o.a)) :=
    (sampleObsX_measurable n).prodMk (sampleObsA_measurable n)
  unfold Causalean.Stat.Sample.Stratified.TreatmentRegression.propensity
  rw [exactDesign_cellProbability, if_neg (ne_of_gt hk),
    Measure.map_apply hm (measurableSet_singleton (k, true))]
  have hs : (fun o : SampleObs n => (o.x, o.a)) ⁻¹' {(k, true)} =
      {o | o.x = k ∧ o.a = true} := by ext o; simp
  rw [hs]
  change Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.armCellMass
    P.observedLaw (fun o : SampleObs n => o.x) (fun o => o.a) true k /
      P.cellMass k = _
  rw [observedArmMass_eq]
  simp [ne_of_gt hk]

/-- The clipped regression rule attains the exact-class upper bound, using only
conditional second moments and occupied-cell overlap. -/
-- @node: exactRegressionRisk_bound
lemma exactRegressionRisk_bound (n : ℕ) (M : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M) :
    (⨆ P : ExactClass n M,
      DiscreteAteHeterogeneityFrontier.mse P.1.law
        (withinCellRegressionEstimator n M)) ≤
      (72 + 4 * (1296 + 729 / 64) : ℝ) * M ^ 2 / n := by
  refine Real.iSup_le (fun P => ?_) (by positivity)
  have hobs := knownObservedAssumptions P.1
  have hres : Causalean.Stat.Sample.Stratified.TreatmentRegression.ResidualAssumptions
      P.1.law.observedLaw (fun o : SampleObs n => o.x) (fun o => o.a)
      (fun o => o.y) (observedCenter P.1.law) M :=
    { X_measurable := hobs.X_measurable
      A_measurable := hobs.A_measurable
      Y_measurable := hobs.Y_measurable
      residual_L2 := hobs.residual_L2
      residual_centered := hobs.residual_centered
      residual_second_moment := hobs.residual_second_moment }
  have hb := Causalean.Stat.Sample.Stratified.TreatmentRegression.clipped_regression_mse_le_quarter
    n P.1.law.observedLaw (fun o : SampleObs n => o.x) (fun o => o.a)
    (fun o => o.y) (observedCenter P.1.law) M
    (DiscreteAteHeterogeneityFrontier.rawAteFormula P.1.law) hres
    (by omega) (by simp) (by linarith) (rawAte_mem_clip P.1)
    (by
      intro k hk
      rw [exactDesign_cellProbability] at hk
      rw [exactDesign_propensity P.1.law k hk]
      exact P.1.overlap k hk)
    (by
      intro k hk
      rw [exactDesign_cellProbability] at hk
      simpa [observedCenter, hk, DiscreteAteHeterogeneityFrontier.cellEffect] using P.2 k hk)
  rw [withinCellRegressionEstimator_eq_library]
  exact hb.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      Causalean.Stat.Sample.Stratified.TreatmentRegression.quarter_constant_le_paper
      (sq_nonneg M)) (by positivity))

/-- The radius-zero equality transfers the concrete one-cell two-point bound
into the exact-class minimax problem, independently of the frontier certificate. -/
-- @node: exactClassRisk_lower_quantitative
lemma exactClassRisk_lower_quantitative (n : ℕ) (M : ℝ)
    (hn : 3 ≤ n) (hM : 1 ≤ M) :
    (1 / 100 : ℝ) * M ^ 2 / n ≤ exactClassRisk n M := by
  rw [exactClassRisk_eq_radiusZeroMinimaxRisk]
  exact radiusZero_minimax_lower_quantitative n M hn hM

/-- Clipping an arbitrary measurable rule retains admissibility and can only
reduce its squared loss. The strict slack in the quantitative two-point bound
therefore yields the paper's all-estimator certificate. -/
-- @node: exactClass_arbitraryEstimator_lower
lemma exactClass_arbitraryEstimator_lower (n : ℕ) (M : ℝ)
    (hn : 3 ≤ n) (hM : 1 ≤ M)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T) :
    ∃ P : ExactClass n M,
      ENNReal.ofReal ((3 : ℝ) * M ^ 2 / (2048 * n)) ≤
        ∫⁻ x, ENNReal.ofReal
          ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.1.law) ^ 2)
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.1.law := by
  have hM0 : 0 ≤ M := by linarith
  let est : DiscreteAteHeterogeneityFrontier.Estimator n n M :=
    ⟨fun x => clipM M (T x),
      by unfold clipM; exact measurable_const.max (measurable_const.min hT),
      by
        intro x
        exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩
  have hmin : exactClassRisk n M ≤
      ⨆ P : ExactClass n M, DiscreteAteHeterogeneityFrontier.mse P.1.law est.1 :=
    Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (risk := fun (e : DiscreteAteHeterogeneityFrontier.Estimator n n M)
        (P : ExactClass n M) => DiscreteAteHeterogeneityFrontier.mse P.1.law e.1)
      (fun e P => integral_nonneg (fun _ => sq_nonneg _)) est
  have hgap : (3 : ℝ) * M ^ 2 / (2048 * n) < (1 / 100 : ℝ) * M ^ 2 / n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hMsq : 0 < M ^ 2 := by positivity
    field_simp
    nlinarith
  have hex : ∃ P : ExactClass n M,
      (3 : ℝ) * M ^ 2 / (2048 * n) <
        DiscreteAteHeterogeneityFrontier.mse P.1.law est.1 := by
    by_contra! hno
    have hs := Real.iSup_le hno (by positivity)
    exact (not_lt_of_ge hs)
      (hgap.trans_le ((exactClassRisk_lower_quantitative n M hn hM).trans hmin))
  obtain ⟨P, hP⟩ := hex
  refine ⟨P, (ENNReal.ofReal_le_ofReal hP.le).trans ?_⟩
  rw [knownRadiusClass_ofReal_mse P.1 est]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact Causalean.Mathlib.Analysis.clipIcc_sub_sq_le (rawAte_mem_clip P.1) (T x)

-- @node: prop:exact-homogeneity-reduction
theorem exact_homogeneity_reduction
    (hSampling : ∀ n (P : Law n),
      IidSampling n P (DiscreteAteHeterogeneityFrontier.productLaw n P)) :
    ∀ n M, 3 ≤ n → 1 ≤ M →
      (3 : ℝ) * M ^ 2 / (2048 * n) ≤ exactClassRisk n M ∧
      exactClassRisk n M ≤
        ⨆ P : ExactClass n M,
          DiscreteAteHeterogeneityFrontier.mse P.1.law
            (withinCellRegressionEstimator n M) ∧
      (⨆ P : ExactClass n M,
          DiscreteAteHeterogeneityFrontier.mse P.1.law
            (withinCellRegressionEstimator n M)) ≤
        (72 + 4 * (1296 + 729 / 64) : ℝ) * M ^ 2 / n ∧
      (∀ P : ExactClass n M,
        ∃ Q : KnownRadiusClass n M 0, Q.law = P.1.law) ∧
      (∀ Q : KnownRadiusClass n M 0,
        ∃ P : ExactClass n M, P.1.law = Q.law) ∧
      (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
        -- @realizes T(arbitrary measurable sample estimator)
        ∃ P : ExactClass n M,
          ENNReal.ofReal ((3 : ℝ) * M ^ 2 / (2048 * n)) ≤
            ∫⁻ x, ENNReal.ofReal
              ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.1.law) ^ 2)
              ∂DiscreteAteHeterogeneityFrontier.productLaw n P.1.law) := by
  intro n M hn hM
  -- Assemble the proved regression upper bound and concrete two-point converse.
  have hbounds :
      (3 : ℝ) * M ^ 2 / (2048 * n) ≤ exactClassRisk n M ∧
      (⨆ P : ExactClass n M,
        DiscreteAteHeterogeneityFrontier.mse P.1.law
          (withinCellRegressionEstimator n M)) ≤
        (72 + 4 * (1296 + 729 / 64) : ℝ) * M ^ 2 / n ∧
      (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
        ∃ P : ExactClass n M,
          ENNReal.ofReal ((3 : ℝ) * M ^ 2 / (2048 * n)) ≤
            ∫⁻ x, ENNReal.ofReal
              ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.1.law) ^ 2)
              ∂DiscreteAteHeterogeneityFrontier.productLaw n P.1.law) := by
    have hlower :
        (3 : ℝ) * M ^ 2 / (2048 * n) ≤ exactClassRisk n M ∧
        (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
          ∃ P : ExactClass n M,
            ENNReal.ofReal ((3 : ℝ) * M ^ 2 / (2048 * n)) ≤
              ∫⁻ x, ENNReal.ofReal
                ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.1.law) ^ 2)
                ∂DiscreteAteHeterogeneityFrontier.productLaw n P.1.law) := by
      constructor
      · have hl := exactClassRisk_lower_quantitative n M hn hM
        have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        apply le_trans _ hl
        field_simp
        nlinarith [sq_nonneg M]
      · exact exactClass_arbitraryEstimator_lower n M hn hM
    exact ⟨hlower.1, exactRegressionRisk_bound n M hn hM, hlower.2⟩
  exact ⟨hbounds.1, exactClassRisk_le_regressionRisk n M (by linarith),
    hbounds.2.1, fun P => exactClass_to_radiusZero P,
    fun Q => radiusZero_to_exactClass Q, hbounds.2.2⟩

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
