module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.EndpointDirectionBounds
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalDirection

/-!
# KL and rate arithmetic for the lower-bound directions

This module turns the pointwise quadratic Poisson KL inequality into an
endpoint-direction bound and records the exact bandwidth cancellations used
after integrating the endpoint and critical alternatives.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Every censoring-retention probability is at most one. -/
lemma retention_le_one (P : SubjectLaw) (a : Arm) (t : ℝ) :
    retention P a t ≤ 1 := by
  unfold retention
  calc
    P.latent.real {z | ENNReal.ofReal t ≤ z.censor a} ≤
        P.latent.real Set.univ := by
      apply measureReal_mono
      · exact Set.subset_univ _
      · rw [P.prob]
        exact ENNReal.one_ne_top
    _ = 1 := by simp [measureReal_def, P.prob]

/-- On nonnegative times, a positive constant-hazard survival curve lies in
the unit interval. -/
lemma SubjectLaw.baseline_survival_mem_unitInterval
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    {a : Arm} {t : ℝ} (ht : 0 ≤ t) :
    survival (SubjectLaw.baseline reference lambda0 d0 hd0) a t ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Real.exp_nonneg _
  · unfold survival SubjectLaw.baseline
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- The survival-retention weight of a constant baseline is between zero and
one throughout the study horizon. -/
lemma SubjectLaw.baseline_survival_mul_retention_mem_unitInterval
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    {a : Arm} {t : ℝ} (ht : 0 ≤ t) :
    survival (SubjectLaw.baseline reference lambda0 d0 hd0) a t *
        retention (SubjectLaw.baseline reference lambda0 d0 hd0) a t ∈
      Set.Icc (0 : ℝ) 1 := by
  have hs := SubjectLaw.baseline_survival_mem_unitInterval
    reference lambda0 d0 hd0 (a := a) ht
  have hr0 : 0 ≤ retention
      (SubjectLaw.baseline reference lambda0 d0 hd0) a t := measureReal_nonneg
  have hr1 : retention
      (SubjectLaw.baseline reference lambda0 d0 hd0) a t ≤ 1 :=
    retention_le_one _ _ _
  exact ⟨mul_nonneg hs.1 hr0, (mul_le_mul hs.2 hr1 hr0 zero_le_one).trans (by norm_num)⟩

/-- The model-class endpoint expansion gives a uniform power upper bound on
censoring retention. -/
lemma retention_le_three_halves_gMax_rpow
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {x : ℝ} (hx : 0 < x) (hx0 : x ≤ c.x0) :
    retention P a (1 - x) ≤ (3 / 2 : ℝ) * c.gMax * x ^ c.kappa := by
  have hg0 : 0 < P.g a :=
    lt_of_lt_of_le c.gMin_pos (hP.endpointCoefficientBounds a).1
  have hxpow0 : 0 < x ^ c.kappa := Real.rpow_pos_of_pos hx _
  have hden : 0 < P.g a * x ^ c.kappa := mul_pos hg0 hxpow0
  have hrho : x ^ c.rho ≤ c.x0 ^ c.rho :=
    Real.rpow_le_rpow hx.le hx0 c.rho_pos.le
  have hsmall : c.LG * x ^ c.rho ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hrho c.LG_pos.le).trans hP.tailEnvelopeSmall
  have hupper := (abs_le.mp (hP.endpointRetention a x hx hx0)).2
  have hratio : retention P a (1 - x) / (P.g a * x ^ c.kappa) ≤ 3 / 2 := by
    linarith
  have hret : retention P a (1 - x) ≤ (3 / 2 : ℝ) *
      (P.g a * x ^ c.kappa) := (div_le_iff₀ hden).mp hratio
  calc
    retention P a (1 - x) ≤ (3 / 2 : ℝ) *
        (P.g a * x ^ c.kappa) := hret
    _ ≤ (3 / 2 : ℝ) * (c.gMax * x ^ c.kappa) := by
      gcongr
      exact (hP.endpointCoefficientBounds a).2
    _ = (3 / 2 : ℝ) * c.gMax * x ^ c.kappa := by ring

/-- A nonzero critical direction lies between the critical bandwidth and the
compact endpoint cutoff. -/
lemma criticalDirection_ne_zero_imp_band
    (c : ClassConstants) (cut : CutoffData c)
    {u : ℝ} {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hne : criticalDirection c cut u n t ≠ 0) :
    criticalBandwidth c n < 1 - t ∧ 1 - t < c.x0 := by
  have hlower : criticalBandwidth c n < 1 - t := by
    by_contra hnot
    exact hne (criticalDirection_eq_zero_of_endpoint_band c cut hn ht
      (le_of_not_gt hnot))
  have hpsi : cut.psi (1 - t) ≠ 0 := by
    intro hzero
    apply hne
    simp [criticalDirection, hzero]
  exact ⟨hlower, (cut.psi_support _ hpsi).2⟩

/-- The local Poisson KL cost of the endpoint direction is bounded by its
squared rescaled bump envelope. -/
lemma endpointDirection_poissonCost_le
    (c : ClassConstants) (cut : CutoffData c)
    {lambda0 u h t : ℝ} (hlambda0 : 0 < lambda0) (hh : 0 ≤ h)
    (hadd : 0 < lambda0 + endpointDirection c cut u h t) :
    (lambda0 + endpointDirection c cut u h t) *
          Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
        (lambda0 + endpointDirection c cut u h t) + lambda0 ≤
      (|u| * endpointBumpBound c cut) ^ 2 * h ^ (2 * c.beta) / lambda0 := by
  have hquad := poissonIntensityCost_add_le_sq_div hlambda0 hadd
  have hdir := abs_endpointDirection_le c cut (u := u) (h := h) (t := t) hh
  have hleft : 0 ≤ |endpointDirection c cut u h t| := abs_nonneg _
  have hright : 0 ≤ |u| * h ^ c.beta * endpointBumpBound c cut :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hh _))
      (endpointBumpBound_pos c cut).le
  have hsq : (endpointDirection c cut u h t) ^ 2 ≤
      (|u| * h ^ c.beta * endpointBumpBound c cut) ^ 2 := by
    rw [← sq_abs (endpointDirection c cut u h t)]
    exact (sq_le_sq₀ hleft hright).2 hdir
  refine hquad.trans (div_le_div_of_nonneg_right ?_ hlambda0.le)
  have hpow : (h ^ c.beta) ^ (2 : ℕ) = h ^ (2 * c.beta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh]
    congr 1
    ring
  calc
    (endpointDirection c cut u h t) ^ 2
        ≤ (|u| * h ^ c.beta * endpointBumpBound c cut) ^ 2 := hsq
    _ = (|u| * endpointBumpBound c cut) ^ 2 * h ^ (2 * c.beta) := by
      rw [mul_pow, mul_pow, hpow]
      ring

/-- The endpoint sample-size factor cancels exactly against the tuned
bandwidth once the weighted integral contributes the endpoint-tail power. -/
lemma endpointBandwidth_sample_factor
    (c : ClassConstants) {n : ℕ} (hn : 1 ≤ n) (A : ℝ) :
    (n : ℝ) * (A * endpointBandwidth c n ^
      (2 * c.beta + c.kappa + 1)) = A := by
  calc
    (n : ℝ) * (A * endpointBandwidth c n ^
        (2 * c.beta + c.kappa + 1)) =
      A * ((n : ℝ) * endpointBandwidth c n ^
        (2 * c.beta + c.kappa + 1)) := by ring
    _ = A := by rw [endpointBandwidth_balance c hn, mul_one]

/-- Any endpoint weighted-cost integral with the predicted
`h^(2β+κ+1)` envelope yields a sample KL bound independent of `n`. -/
lemma endpoint_sampleKL_factor_le
    (c : ClassConstants) {n : ℕ} (hn : 1 ≤ n)
    {p I A : ℝ} (hp1 : p ≤ 1) (hI0 : 0 ≤ I)
    (hI : I ≤ A * endpointBandwidth c n ^
      (2 * c.beta + c.kappa + 1)) :
    (n : ℝ) * p * I ≤ A := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  calc
    (n : ℝ) * p * I ≤
        (n : ℝ) * 1 * (A * endpointBandwidth c n ^
          (2 * c.beta + c.kappa + 1)) := by gcongr
    _ = (n : ℝ) * (A * endpointBandwidth c n ^
          (2 * c.beta + c.kappa + 1)) := by ring
    _ = A := endpointBandwidth_sample_factor c hn A

/-- The logarithm of the reciprocal critical bandwidth is exactly the
logarithmic scale divided by `2β+2`. -/
lemma neg_log_criticalBandwidth
    (c : ClassConstants) {n : ℕ} (hn : 2 ≤ n) :
    -Real.log (criticalBandwidth c n) =
      Real.log ((n : ℝ) * Real.log n) / (2 * c.beta + 2) := by
  have hz : 0 < (n : ℝ) * Real.log n :=
    mul_pos (by exact_mod_cast (show 0 < n by omega))
      (Real.log_pos (by exact_mod_cast hn))
  have hden : 2 * c.beta + 2 ≠ 0 := by nlinarith [c.beta_pos]
  unfold criticalBandwidth
  rw [Real.log_rpow hz]
  field_simp

/-- For integer sample sizes at least three, the logarithm of `n log n` is
at most twice the logarithm of `n`. -/
lemma log_nat_mul_log_nat_le_two_log_nat {n : ℕ} (hn : 3 ≤ n) :
    Real.log ((n : ℝ) * Real.log n) ≤ 2 * Real.log n := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hlog0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog_le : Real.log n ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hmul : (n : ℝ) * Real.log n ≤ (n : ℝ) * n :=
    mul_le_mul_of_nonneg_left hlog_le hn0.le
  calc
    Real.log ((n : ℝ) * Real.log n) ≤ Real.log ((n : ℝ) * n) :=
      Real.strictMonoOn_log.monotoneOn
        (mul_pos hn0 hlog0) (mul_pos hn0 hn0) hmul
    _ = 2 * Real.log n := by
      rw [Real.log_mul hn0.ne' hn0.ne']
      ring

/-- The critical logarithmic sample factor is uniformly bounded by the
inverse smoothness denominator. -/
lemma critical_log_sample_factor_le
    (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) / ((n : ℝ) * Real.log n) *
        (-Real.log (criticalBandwidth c n)) ≤ 1 / (c.beta + 1) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hlog0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hden : 0 < 2 * c.beta + 2 := by nlinarith [c.beta_pos]
  rw [neg_log_criticalBandwidth c (by omega)]
  have hlog := log_nat_mul_log_nat_le_two_log_nat hn
  calc
    (n : ℝ) / ((n : ℝ) * Real.log n) *
          (Real.log ((n : ℝ) * Real.log n) / (2 * c.beta + 2)) =
        Real.log ((n : ℝ) * Real.log n) /
          (Real.log n * (2 * c.beta + 2)) := by field_simp
    _ ≤ (2 * Real.log n) / (Real.log n * (2 * c.beta + 2)) := by
      exact div_le_div_of_nonneg_right hlog (mul_nonneg hlog0.le hden.le)
    _ = 1 / (c.beta + 1) := by field_simp

/-- Any critical weighted-cost integral with the predicted logarithmic
envelope yields a sample KL bound independent of `n`. -/
lemma critical_sampleKL_factor_le
    (c : ClassConstants) {n : ℕ} (hn : 3 ≤ n)
    {p I A : ℝ} (hp1 : p ≤ 1) (hI0 : 0 ≤ I) (hA : 0 ≤ A)
    (hI : I ≤ A / ((n : ℝ) * Real.log n) *
      (-Real.log (criticalBandwidth c n))) :
    (n : ℝ) * p * I ≤ A / (c.beta + 1) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlog0 : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  calc
    (n : ℝ) * p * I ≤ (n : ℝ) * 1 * I := by gcongr
    _ ≤
        (n : ℝ) * 1 *
          (A / ((n : ℝ) * Real.log n) *
            (-Real.log (criticalBandwidth c n))) := by gcongr
    _ = A * ((n : ℝ) / ((n : ℝ) * Real.log n) *
          (-Real.log (criticalBandwidth c n))) := by ring
    _ ≤ A * (1 / (c.beta + 1)) := by
      exact mul_le_mul_of_nonneg_left (critical_log_sample_factor_le c hn) hA
    _ = A / (c.beta + 1) := by ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
