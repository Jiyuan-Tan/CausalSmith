module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.WeightedCostIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Regularity and eventual bandwidth conditions for explicit witnesses -/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A bounded a.e.-measurable additive direction with positive perturbed
intensity gives an integrable survival-retention weighted Poisson cost. -/
lemma weightedPoissonCost_intervalIntegrable_of_bounded
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (direction : ℝ → ℝ)
    (hlambda0 : 0 < lambda0)
    (hmeas : AEMeasurable direction
      (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |direction t| ≤ B)
    (hadd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 < lambda0 + direction t) :
    IntervalIntegrable
      (weightedPoissonCost
        (SubjectLaw.baseline reference lambda0 d0 hd0) true lambda0 direction)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let f := weightedPoissonCost Pbase true lambda0 direction
  have hweight : AEMeasurable
      (fun t => survival Pbase true t * retention Pbase true t)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (SubjectLaw.measurable_baseline_survival_mul_retention
      reference lambda0 d0 hd0 true).aemeasurable
  have hlam : AEMeasurable (fun t => lambda0 + direction t)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    measurable_const.aemeasurable.add hmeas
  have hcost : AEMeasurable (fun t =>
      (lambda0 + direction t) * Real.log ((lambda0 + direction t) / lambda0) -
        (lambda0 + direction t) + lambda0)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact (hlam.mul (hlam.div_const lambda0).log).sub hlam |>.add
      measurable_const.aemeasurable
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [show f = fun t =>
        (survival Pbase true t * retention Pbase true t) *
          ((lambda0 + direction t) * Real.log ((lambda0 + direction t) / lambda0) -
            (lambda0 + direction t) + lambda0) by
      funext t
      exact weightedPoissonCost_apply Pbase true lambda0 direction t]
    exact (hweight.mul hcost).aestronglyMeasurable
  apply IntegrableOn.of_bound measure_Ioc_lt_top hfmeas (B ^ 2 / lambda0)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hw := SubjectLaw.baseline_survival_mul_retention_mem_unitInterval
    reference lambda0 d0 hd0 (a := true) (t := t) ht.1.le
  have hc0 := poissonIntensityCost_nonneg (lambda0 + direction t) lambda0
    (hadd t ht).le hlambda0
  have hc := poissonIntensityCost_add_le_sq_div hlambda0 (hadd t ht)
  have hsq : direction t ^ 2 ≤ B ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg hB0]
    exact hbound t ht)
  have hdiv : direction t ^ 2 / lambda0 ≤ B ^ 2 / lambda0 :=
    div_le_div_of_nonneg_right hsq hlambda0.le
  have hf0 : 0 ≤ f t := by
    rw [show f t =
        (survival Pbase true t * retention Pbase true t) *
          ((lambda0 + direction t) * Real.log ((lambda0 + direction t) / lambda0) -
            (lambda0 + direction t) + lambda0) by
      exact weightedPoissonCost_apply Pbase true lambda0 direction t]
    exact mul_nonneg hw.1 hc0
  change ‖f t‖ ≤ B ^ 2 / lambda0
  rw [Real.norm_eq_abs, abs_of_nonneg hf0]
  calc
    f t ≤ 1 * (direction t ^ 2 / lambda0) := by
      simp only [f, weightedPoissonCost_apply]
      exact mul_le_mul hw.2 hc hc0 zero_le_one
    _ ≤ B ^ 2 / lambda0 := by simpa using hdiv

/-- Endpoint weighted costs are interval-integrable at every positive
bandwidth. -/
lemma endpoint_weightedPoissonCost_intervalIntegrable
    (c : ClassConstants) (reference : SubjectLaw)
    (lambda0 d0 : ℝ) (hd0 : 0 < d0) (cut : CutoffData c)
    {u h : ℝ} (hlambda0 : 0 < lambda0) (hh : 0 < h)
    (hadd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < lambda0 + endpointDirection c cut u h t) :
    IntervalIntegrable
      (weightedPoissonCost
        (SubjectLaw.baseline reference lambda0 d0 hd0) true lambda0
          (endpointDirection c cut u h)) volume 0 1 := by
  apply weightedPoissonCost_intervalIntegrable_of_bounded
    reference lambda0 d0 hd0 (endpointDirection c cut u h) hlambda0
      (B := |u| * h ^ c.beta * endpointBumpBound c cut)
  · exact (endpointDirection_measurable c cut u h hh.ne').aemeasurable
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg u) (Real.rpow_nonneg hh.le _))
      (endpointBumpBound_pos c cut).le
  · intro t ht
    exact abs_endpointDirection_le c cut hh.le
  · intro t ht
    exact hadd t ⟨ht.1.le, ht.2⟩

/-- Critical weighted costs are interval-integrable whenever the direction
is uniformly bounded and the perturbed intensity is positive. -/
lemma critical_weightedPoissonCost_intervalIntegrable
    (c : ClassConstants) (reference : SubjectLaw)
    (lambda0 d0 : ℝ) (hd0 : 0 < d0) (cut : CutoffData c)
    {u Cchi Cpsi : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hlambda0 : 0 < lambda0) (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    (hadd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < lambda0 + criticalDirection c cut u n t) :
    IntervalIntegrable
      (weightedPoissonCost
        (SubjectLaw.baseline reference lambda0 d0 hd0) true lambda0
          (criticalDirection c cut u n)) volume 0 1 := by
  let B := |u| * Cchi * Cpsi * (((n : ℝ) * Real.log n) ^
    (-(c.beta / (2 * c.beta + 2))))
  apply weightedPoissonCost_intervalIntegrable_of_bounded
    reference lambda0 d0 hd0 (criticalDirection c cut u n) hlambda0 (B := B)
  · exact criticalDirection_aemeasurable_restrict c cut u hn
  · exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg u) hCchi) hCpsi)
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))) _)
  · intro t ht
    exact criticalDirection_abs_le_rpow c cut hn hCchi hCpsi hchi hpsi
      ⟨ht.1.le, ht.2⟩
  · intro t ht
    exact hadd t ⟨ht.1.le, ht.2⟩

/-- The endpoint bandwidth eventually lies below the endpoint-tail radius. -/
lemma exists_endpointBandwidth_eventually_le_x0 (c : ClassConstants) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → endpointBandwidth c n ≤ c.x0 := by
  have hden : 0 < 2 * c.beta + c.kappa + 1 := by
    linarith [c.beta_pos, c.kappa_pos]
  have hexp : 0 < 1 / (2 * c.beta + c.kappa + 1) := div_pos one_pos hden
  have ht : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1))))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hx0 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1))) < c.x0 :=
    ht.eventually (Iio_mem_nhds c.x0_pos)
  have hboth : ∀ᶠ n : ℕ in atTop,
      3 ≤ n ∧ endpointBandwidth c n ≤ c.x0 := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hx0] with n hn hnx
    exact ⟨hn, (endpointBandwidth_eq c n).le.trans hnx.le⟩
  rcases (eventually_atTop.1 hboth) with ⟨N, hN⟩
  refine ⟨N, (hN N le_rfl).1, ?_⟩
  intro n hn
  exact (hN n hn).2

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
