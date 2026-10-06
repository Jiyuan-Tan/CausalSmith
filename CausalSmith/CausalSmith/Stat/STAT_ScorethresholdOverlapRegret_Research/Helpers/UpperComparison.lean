module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScoreGrouping
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Regularization

/-! # Selector comparison for upper-bound peeling

Steps (1)–(3) of the upper-bound roadmap: empirical and population comparison
identities, exact-selector objective comparison, and localized shell inclusion.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators

/-- Every binary-policy contrast is bounded pointwise by the deleted score. -/
-- @node: upperComparison_abs_le_score
lemma upperComparison_abs_le_score (P : RowLaw) (a : ℝ)
    (π : ℝ → Bool) (o : Observation) :
    |comparisonIntegrand P a π o| ≤ |zScore a P.logger o| := by
  cases hp : π o.X <;> cases hc : canonicalPolicy P o.X <;>
    simp [comparisonIntegrand, hp, hc]

/-- The empirical contrast is the difference of the two empirical objectives. -/
-- @node: upperComparison_empirical_identity
lemma upperComparison_empirical_identity {n : ℕ} (P : RowLaw) (a : ℝ)
    (π : ℝ → Bool) (d : Fin n → Observation) :
    empiricalAverage (comparisonIntegrand P a π) d =
      empObjective a P.logger d π - empObjective a P.logger d (canonicalPolicy P) := by
  simp only [empiricalAverage, comparisonIntegrand, empObjective, sub_mul,
    Finset.sum_sub_distrib, mul_sub]

/-- Bounded deleted scores make the negative-action objective integrable for
any policy measurable on the supported score law. -/
-- @node: upperComparison_objective_integrable
@[fun_prop] lemma upperComparison_objective_integrable (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (π : ℝ → Bool)
    (hπ : AEMeasurable π P.PX) :
    Integrable (fun o : Observation => (if π o.X then (0:ℝ) else 1) *
      zScore a P.logger o) P.obsLaw := by
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  have hw := score_negative_action_aemeasurable π hπ
  have hwm : AEMeasurable (fun o : Observation => if π o.X then (0:ℝ) else 1)
      P.obsLaw := by
    have hm : AEMeasurable (fun x => if π x then (0:ℝ) else 1)
        (P.obsLaw.map Observation.X) := by
      rw [score_observation_X_map]
      exact hw
    exact hm.comp_measurable score_observation_X_measurable
  have hz := score_z_aemeasurable P hP.wf a
  have he : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  apply score_bounded_integrable (2/a) (hwm.mul hz)
  filter_upwards [zScore_abs_ae P a ha hP.wf he] with o ho
  cases hp : π o.X
  · simpa [hp] using ho
  · change |(if π o.X then (0:ℝ) else 1) * zScore a P.logger o| ≤ 2/a
    simp only [hp, ↓reduceIte, zero_mul, abs_zero]
    exact div_nonneg (by norm_num) ha.1.le

/-- The population contrast is the difference of the two population objectives. -/
-- @node: upperComparison_population_identity
lemma upperComparison_population_identity (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (π : ℝ → Bool)
    (hπ : π ∈ thresholdClass) :
    (∫ o, comparisonIntegrand P a π o ∂P.obsLaw) =
      popObjective P a π - popObjective P a (canonicalPolicy P) := by
  have hi := upperComparison_objective_integrable α γ θ n P e hP a ha π
    (score_policy_aemeasurable P hP.wf π (thresholdClass_mem_binaryPolicyClass π hπ))
  have hs := upperComparison_objective_integrable α γ θ n P e hP a ha
    (canonicalPolicy P) (score_canonical_aemeasurable P hP.wf)
  simp only [comparisonIntegrand, sub_mul]
  rw [integral_sub hi hs]
  rfl

/-- Exact empirical minimization against a canonical threshold representative
makes the selector's empirical comparison nonpositive. -/
-- @node: upperComparison_selector_empirical_nonpos
lemma upperComparison_selector_empirical_nonpos {n : ℕ} (P : RowLaw)
    (a : ℝ) (d : Fin n → Observation)
    (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (π0 : ℝ → Bool) (hπ0 : π0 ∈ thresholdClass)
    (hcanonical : ∀ i, π0 (d i).X = canonicalPolicy P (d i).X) :
    empiricalAverage (comparisonIntegrand P a (sortedSelector a P.logger d)) d ≤ 0 := by
  rw [upperComparison_empirical_identity]
  have he := empObjective_congr_sample_labels a P.logger d π0 (canonicalPolicy P) hcanonical
  rw [← he]
  exact sub_nonpos.mpr (sortedSelector_empObjective_le a P.logger d hd π0 hπ0)

/-- Regularization and exact empirical minimization give roadmap inequality (2). -/
-- @node: upperComparison_selector_basic_inequality
lemma upperComparison_selector_basic_inequality {n : ℕ} (α γ θ : ℝ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (d : Fin n → Observation)
    (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (π0 : ℝ → Bool) (hπ0 : π0 ∈ thresholdClass)
    (hcanonical : ∀ i, π0 (d i).X = canonicalPolicy P (d i).X) :
    regularizedLoss P a (sortedSelector a P.logger d)/4 - 2*biasFunctional P a ≤
      |empiricalAverage (comparisonIntegrand P a (sortedSelector a P.logger d)) d -
        ∫ o, comparisonIntegrand P a (sortedSelector a P.logger d) o ∂P.obsLaw| := by
  have hm : sortedSelector a P.logger d ∈ thresholdClass :=
    firstScannedMinimizer_mem_thresholdClass a P.logger d
  have hr := (regularization_inequality α γ θ n P e hP a _ ha hm).1
  rw [← upperComparison_population_identity α γ θ n P e hP a ha _ hm] at hr
  have hemp := upperComparison_selector_empirical_nonpos P a d hd π0 hπ0 hcanonical
  have habs := neg_le_abs (empiricalAverage
    (comparisonIntegrand P a (sortedSelector a P.logger d)) d -
      ∫ o, comparisonIntegrand P a (sortedSelector a P.logger d) o ∂P.obsLaw)
  linarith

/-- All localized empirical contrasts share a finite deterministic envelope,
so the real-valued supremum has the boundedness required by `le_ciSup`. -/
-- @node: upperComparison_process_bddAbove
lemma upperComparison_process_bddAbove {n : ℕ} (α γ θ : ℝ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (d : Fin n → Observation) :
    BddAbove (Set.range (fun π : {π : ℝ → Bool //
        π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z} =>
      |empiricalAverage (comparisonIntegrand P a π.1) d -
        ∫ o, comparisonIntegrand P a π.1 o ∂P.obsLaw|)) := by
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  have he : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  refine ⟨(n:ℝ)⁻¹ * ∑ i, |zScore a P.logger (d i)| + 2/a, ?_⟩
  rintro _ ⟨π, rfl⟩
  have hi : |∫ o, comparisonIntegrand P a π.1 o ∂P.obsLaw| ≤ 2/a := by
    have hb := norm_integral_le_of_norm_le_const (μ := P.obsLaw) (C := 2/a)
      (f := comparisonIntegrand P a π.1) (by
        filter_upwards [zScore_abs_ae P a ha hP.wf he] with o ho
        exact (upperComparison_abs_le_score P a π.1 o).trans ho)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  have hemp : |empiricalAverage (comparisonIntegrand P a π.1) d| ≤
      (n:ℝ)⁻¹ * ∑ i, |zScore a P.logger (d i)| := by
    unfold empiricalAverage
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => upperComparison_abs_le_score P a π.1 (d i))
  exact (abs_sub _ _).trans (add_le_add hemp hi)

/-- A selector lying in a dyadic loss shell forces a large localized process,
as in roadmap step (3). -/
-- @node: upperComparison_selector_shell
lemma upperComparison_selector_shell {n : ℕ} (α γ θ : ℝ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (d : Fin n → Observation)
    (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (π0 : ℝ → Bool) (hπ0 : π0 ∈ thresholdClass)
    (hcanonical : ∀ i, π0 (d i).X = canonicalPolicy P (d i).X)
    (z : ℝ) (hz : 16*biasFunctional P a ≤ z) (k : ℕ)
    (hlo : (2:ℝ)^k*z ≤ regularizedLoss P a (sortedSelector a P.logger d))
    (hhi : regularizedLoss P a (sortedSelector a P.logger d) < (2:ℝ)^(k+1)*z) :
    (2:ℝ)^k*z/8 ≤ localizedProcess P a ((2:ℝ)^(k+1)*z) d := by
  have hbasic := upperComparison_selector_basic_inequality α γ θ P e hP a ha
    d hd π0 hπ0 hcanonical
  have hsup := le_ciSup (upperComparison_process_bddAbove α γ θ P e hP a
    ((2:ℝ)^(k+1)*z) ha d)
    (⟨sortedSelector a P.logger d,
      firstScannedMinimizer_mem_thresholdClass a P.logger d, hhi.le⟩ :
      {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ (2:ℝ)^(k+1)*z})
  change _ ≤ localizedProcess P a ((2:ℝ)^(k+1)*z) d at hsup
  have hb0 : 0 ≤ biasFunctional P a := by
    unfold biasFunctional
    apply add_nonneg measureReal_nonneg
    apply integral_nonneg
    intro x
    dsimp only
    split_ifs with hx
    · have hp : 0 < overlap P x := lt_of_lt_of_le ha.1 hx.1
      change 0 ≤ min 1 (a / overlap P x) * 1
      exact mul_nonneg (le_min zero_le_one (div_nonneg ha.1.le hp.le)) zero_le_one
    · simp
  have hz0 : 0 ≤ z := (mul_nonneg (by norm_num) hb0).trans hz
  have hpow : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hzk : z ≤ (2:ℝ)^k*z := by nlinarith
  have hbound : (2:ℝ)^k*z/8 ≤
      regularizedLoss P a (sortedSelector a P.logger d)/4 - 2*biasFunctional P a := by
    linarith
  exact (hbound.trans hbasic).trans hsup

/-- The IID sample simultaneously lies in score support and agrees with a
canonical threshold representative at every observed score. -/
-- @node: upperComparison_sample_canonical_ae
lemma upperComparison_sample_canonical_ae (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e) :
    ∃ π0 ∈ thresholdClass, ∀ᵐ d ∂sampleLaw P n,
      (∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ i, π0 (d i).X = canonicalPolicy P (d i).X) := by
  obtain ⟨π0, hπ0, heq⟩ := hP.canonical
  refine ⟨π0, hπ0, ?_⟩
  have hrow : ∀ᵐ o ∂P.obsLaw, o.X ∈ Set.Icc (0:ℝ) 1 ∧
      π0 o.X = canonicalPolicy P o.X := by
    apply ae_of_ae_map score_observation_X_measurable.aemeasurable
      (p := fun x => x ∈ Set.Icc (0:ℝ) 1 ∧ π0 x = canonicalPolicy P x)
    rw [score_observation_X_map]
    exact (ae_iff.mpr hP.score.2).and heq
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  have hall : ∀ᵐ d ∂sampleLaw P n, ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ π0 (d i).X = canonicalPolicy P (d i).X := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P.obsLaw) (i := i)) hrow
  filter_upwards [hall] with d hd
  exact ⟨fun i => (hd i).1, fun i => (hd i).2⟩

/-- Roadmap step (2) holds almost surely for the actual supplied-logger selector. -/
-- @node: upperComparison_selector_basic_ae
lemma upperComparison_selector_basic_ae (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) :
    ∀ᵐ d ∂sampleLaw P n,
      regularizedLoss P a (sortedSelector a e d)/4 - 2*biasFunctional P a ≤
        |empiricalAverage (comparisonIntegrand P a (sortedSelector a e d)) d -
          ∫ o, comparisonIntegrand P a (sortedSelector a e d) o ∂P.obsLaw| := by
  obtain ⟨π0, hπ0, hsample⟩ := upperComparison_sample_canonical_ae α γ θ n P e hP
  filter_upwards [hsample] with d hd
  have he : Set.EqOn e P.logger (Set.Icc (0:ℝ) 1) := fun x hx =>
    hP.known hx
  rw [sortedSelector_congr_logger a e P.logger d hd.1 he]
  exact upperComparison_selector_basic_inequality α γ θ P e hP a ha d
    hd.1 π0 hπ0 hd.2

/-- Roadmap step (3) holds almost surely, for every dyadic shell at once,
with the supplied logger used by the finite-sample estimator. -/
-- @node: upperComparison_selector_shell_ae
lemma upperComparison_selector_shell_ae (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1/4) (z : ℝ)
    (hz : 16*biasFunctional P a ≤ z) :
    ∀ᵐ d ∂sampleLaw P n, ∀ k : ℕ,
      (2:ℝ)^k*z ≤ regularizedLoss P a (sortedSelector a e d) →
      regularizedLoss P a (sortedSelector a e d) < (2:ℝ)^(k+1)*z →
      (2:ℝ)^k*z/8 ≤ localizedProcess P a ((2:ℝ)^(k+1)*z) d := by
  obtain ⟨π0, hπ0, hsample⟩ := upperComparison_sample_canonical_ae α γ θ n P e hP
  filter_upwards [hsample] with d hd
  have he : Set.EqOn e P.logger (Set.Icc (0:ℝ) 1) := fun x hx =>
    hP.known hx
  rw [sortedSelector_congr_logger a e P.logger d hd.1 he]
  intro k hlo hhi
  exact upperComparison_selector_shell α γ θ P e hP a ha d hd.1 π0 hπ0 hd.2 z hz k hlo hhi

end CausalSmith.Stat.ScorethresholdOverlapRegret
