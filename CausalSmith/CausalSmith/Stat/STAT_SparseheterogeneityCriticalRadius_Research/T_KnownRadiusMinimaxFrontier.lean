module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers
public import Causalean.Stat.Minimax.MinimaxValue

/-! The simultaneous known-radius minimax frontier, including its endpoint and
elbow conclusions. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

/-- The mean envelope bounds the mass-weighted target, including null cells. -/
-- @node: knownRadiusClass_ate_bound
lemma knownRadiusClass_ate_bound {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho) : |ateTarget P.law| ≤ M := by
  have hterm (k : Fin n) :
      |P.law.cellMass k * DiscreteAteHeterogeneityFrontier.cellEffect P.law k| ≤
        P.law.cellMass k * M := by
    have hp := (P.law.cellMass_range k).1
    by_cases hk : 0 < P.law.cellMass k
    · have h0 := P.mean_envelope false k hk
      have h1 := P.mean_envelope true k hk
      have he : |DiscreteAteHeterogeneityFrontier.cellEffect P.law k| ≤ M := by
        exact (abs_sub _ _).trans (by linarith)
      rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left he hp
    · have hz : P.law.cellMass k = 0 := le_antisymm (le_of_not_gt hk) hp
      simp [hz]
  calc
    _ ≤ ∑ k : Fin n, |P.law.cellMass k *
        DiscreteAteHeterogeneityFrontier.cellEffect P.law k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, P.law.cellMass k * M :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = M := by
      rw [← Finset.sum_mul, DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
      ring

/-- Clipped estimators have bounded squared loss under every law in the class. -/
-- @node: knownRadiusClass_loss_bound
lemma knownRadiusClass_loss_bound {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho)
    (est : DiscreteAteHeterogeneityFrontier.Estimator n n M)
    (x : Fin n → SampleObs n) :
    (est.1 x - ateTarget P.law) ^ 2 ≤ (2 * M) ^ 2 := by
  have hM : 0 ≤ M := by linarith [P.M_ge_one]
  have hest : |est.1 x| ≤ M := abs_le.mpr (est.2.2 x)
  have habs : |est.1 x - ateTarget P.law| ≤ 2 * M :=
    (abs_sub _ _).trans (by linarith [knownRadiusClass_ate_bound P])
  exact sq_le_sq.mpr (by simpa [abs_mul, abs_of_nonneg hM] using habs)

/-- Bounded loss supplies integrability without an extra regularity premise. -/
-- @node: knownRadiusClass_loss_integrable
lemma knownRadiusClass_loss_integrable {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho)
    (est : DiscreteAteHeterogeneityFrontier.Estimator n n M) :
    Integrable (fun x => (est.1 x - ateTarget P.law) ^ 2)
      (DiscreteAteHeterogeneityFrontier.productLaw n P.law) := by
  have hm : Measurable (fun x => (est.1 x - ateTarget P.law) ^ 2) :=
    (est.2.1.sub measurable_const).pow_const 2
  apply Integrable.of_bound (C := (2 * M) ^ 2) hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact knownRadiusClass_loss_bound P est x

/-- The extended loss certificate agrees with the real MSE for admissible estimators. -/
-- @node: knownRadiusClass_ofReal_mse
lemma knownRadiusClass_ofReal_mse {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho)
    (est : DiscreteAteHeterogeneityFrontier.Estimator n n M) :
    ENNReal.ofReal (DiscreteAteHeterogeneityFrontier.mse P.law est.1) =
      ∫⁻ x, ENNReal.ofReal ((est.1 x - ateTarget P.law) ^ 2)
        ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law := by
  exact ofReal_integral_eq_lintegral_ofReal
    (knownRadiusClass_loss_integrable P est) (ae_of_all _ (fun _ => sq_nonneg _))

/-- Uniform boundedness makes the real supremum retain its order meaning. -/
-- @node: knownRadiusClass_mse_bound
lemma knownRadiusClass_mse_bound {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho)
    (est : DiscreteAteHeterogeneityFrontier.Estimator n n M) :
    DiscreteAteHeterogeneityFrontier.mse P.law est.1 ≤ (2 * M) ^ 2 := by
  calc
    _ ≤ ∫ _, (2 * M) ^ 2 ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law :=
      integral_mono (knownRadiusClass_loss_integrable P est) (integrable_const _)
        (knownRadiusClass_loss_bound P est)
    _ = _ := by simp

/-- The all-estimator converse implies the minimax lower bound in roadmap (79)--(80).
The statistical certificate is supplied by `known_radius_converse_laws`. -/
-- @node: known_radius_minimax_lower_bound
lemma known_radius_minimax_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ n M rho, 3 ≤ n → 1 ≤ M → 0 ≤ rho → rho ≤ 2 →
        c * M ^ 2 * rate n rho ≤ knownRadiusMinimaxRisk n M rho ∧
        (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
          ∃ P : KnownRadiusClass n M rho,
            ENNReal.ofReal (c * M ^ 2 * rate n rho) ≤
              ∫⁻ x, ENNReal.ofReal
                ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2)
                ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) := by
  obtain ⟨c, hc, hcertificate⟩ := known_radius_converse_laws
  refine ⟨c, hc, ?_⟩
  intro n M rho hn hM hr0 hr2
  refine ⟨?_, ?_⟩
  · letI : Nonempty (DiscreteAteHeterogeneityFrontier.Estimator n n M) :=
      ⟨knownRadiusEstimatorAsEstimator n M rho (by linarith)⟩
    apply Causalean.Stat.le_minimaxValue
      (risk := fun (est : DiscreteAteHeterogeneityFrontier.Estimator n n M)
        (P : KnownRadiusClass n M rho) => DiscreteAteHeterogeneityFrontier.mse P.law est.1)
    intro est
    obtain ⟨P, hP, _⟩ := hcertificate n M rho hn hM hr0 hr2 est.1 est.2.1
    rw [← knownRadiusClass_ofReal_mse P est] at hP
    have hl : c * M ^ 2 * rate n rho ≤
        DiscreteAteHeterogeneityFrontier.mse P.law est.1 :=
      (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp hP
    have hbdd : BddAbove (Set.range (fun Q : KnownRadiusClass n M rho =>
        DiscreteAteHeterogeneityFrontier.mse Q.law est.1)) := by
      refine ⟨(2 * M) ^ 2, ?_⟩
      rintro r ⟨Q, rfl⟩
      exact knownRadiusClass_mse_bound Q est
    exact hl.trans (le_ciSup hbdd P)
  · intro T hT
    obtain ⟨P, hP, _⟩ := hcertificate n M rho hn hM hr0 hr2 T hT
    exact ⟨P, hP⟩

-- @node: frontier_rate_factor_tendsto_zero
lemma frontier_rate_factor_tendsto_zero :
    Tendsto (fun x : ℝ =>
      x / (Real.log (Real.exp 1 + x)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hlog : ContinuousAt (fun x : ℝ => Real.log (Real.exp 1 + x)) 0 := by
    exact ContinuousAt.log (continuousAt_const.add continuousAt_id) (by positivity)
  have hden : ContinuousAt (fun x : ℝ =>
      (Real.log (Real.exp 1 + x)) ^ 2) 0 := hlog.pow 2
  have hv : (Real.log (Real.exp 1 + (0 : ℝ))) ^ 2 ≠ 0 := by
    norm_num
  have hcont : ContinuousAt (fun x : ℝ =>
      x / (Real.log (Real.exp 1 + x)) ^ 2) 0 :=
    continuousAt_id.div hden hv
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

-- @node: frontier_rate_factor_tendsto_infinity
lemma frontier_rate_factor_tendsto_infinity :
    Tendsto (fun x : ℝ =>
      x / (Real.log (Real.exp 1 + x)) ^ 2) atTop atTop := by
  have hshift : Tendsto (fun x : ℝ => Real.exp 1 + x) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b - Real.exp 1)] with x hx
    simpa only [Set.mem_Ici] using (show b ≤ Real.exp 1 + x by linarith)
  have hbase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-Real.exp 1) 2 (by norm_num)).comp hshift
  have hratio : Tendsto (fun x : ℝ =>
      Real.log (Real.exp 1 + x) ^ 2 / x) atTop (𝓝 0) := by
    convert hbase using 1
    ext x
    simp only [Function.comp_def, one_mul]
    congr 1
    ring
  have hpos : ∀ᶠ x : ℝ in atTop,
      0 < Real.log (Real.exp 1 + x) ^ 2 / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hlog : 0 < Real.log (Real.exp 1 + x) :=
      Real.log_pos (by
        have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
        linarith)
    positivity
  have hright : Tendsto (fun x : ℝ =>
      Real.log (Real.exp 1 + x) ^ 2 / x) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hratio hpos
  have hinv := hright.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hlog : Real.log (Real.exp 1 + x) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  change (Real.log (Real.exp 1 + x) ^ 2 / x)⁻¹ =
    x / Real.log (Real.exp 1 + x) ^ 2
  field_simp [hlog, ne_of_gt hx]

/-- The total observable estimator is admissible in the minimax problem,
as used in the middle inequality of roadmap (80). -/
-- @node: knownRadiusMinimaxRisk_le_estimatorRisk
lemma knownRadiusMinimaxRisk_le_estimatorRisk (n : ℕ) (M rho : ℝ)
    (hM : 0 ≤ M) :
    knownRadiusMinimaxRisk n M rho ≤
      worstRisk n M rho (knownRadiusEstimator n M rho) := by
  exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (est : DiscreteAteHeterogeneityFrontier.Estimator n n M)
      (P : KnownRadiusClass n M rho) =>
        DiscreteAteHeterogeneityFrontier.mse P.law est.1)
    (fun est P => integral_nonneg (fun _ => sq_nonneg _))
    (knownRadiusEstimatorAsEstimator n M rho hM)

/-- Taking the supremum of the uniform per-law estimator bound supplies the
rightmost inequality in roadmap (80), including the empty-class convention. -/
-- @node: known_radius_estimator_worstRisk_bound
lemma known_radius_estimator_worstRisk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n M rho, 3 ≤ n → 1 ≤ M →
      worstRisk n M rho (knownRadiusEstimator n M rho) ≤
        C * M ^ 2 * rate n rho := by
  obtain ⟨C, hC, hbound⟩ := known_radius_estimator_risk_bound
  refine ⟨C, hC, ?_⟩
  intro n M rho hn hM
  classical
  by_cases hclass : Nonempty (KnownRadiusClass n M rho)
  · letI := hclass
    exact ciSup_le (fun P => hbound n M rho P hn)
  · letI : IsEmpty (KnownRadiusClass n M rho) := not_nonempty_iff.mp hclass
    have hr : 0 ≤ rate n rho := by
      unfold rate
      positivity
    simpa [worstRisk] using mul_nonneg (mul_nonneg hC.le (sq_nonneg M)) hr

/-- The unrestricted endpoint rate is uniformly comparable to the inverse
squared collision logarithm. This supplies the numerical endpoint step after (80). -/
-- @node: rate_two_log_comparison
lemma rate_two_log_comparison (n : ℕ) (hn : 3 ≤ n) :
    1 / (25 * benchmarkLog n ^ 2) ≤ rate n 2 ∧
      rate n 2 ≤ 20 / benchmarkLog n ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have he : 1 ≤ Real.exp (1 : ℝ) := (Real.one_le_exp_iff.mpr (by norm_num))
  have hb : benchmarkLog n = 1 + Real.log (n : ℝ) := by
    unfold benchmarkLog DiscreteAteHeterogeneityFrontier.logEN
    rw [Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
  have hL : 1 ≤ benchmarkLog n := by
    rw [hb]
    linarith [Real.log_nonneg hnone]
  let H := Real.log (Real.exp 1 + 4 * (n : ℝ))
  have hH : 1 ≤ H := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + 4 * (n : ℝ) by linarith)
    simpa [H] using h
  have hLH : benchmarkLog n ≤ 2 * H := by
    have h := Real.log_le_log hnpos
      (show (n : ℝ) ≤ Real.exp 1 + 4 * n by linarith)
    change Real.log (n : ℝ) ≤ H at h
    rw [hb]
    linarith
  have hHL : H ≤ 5 * benchmarkLog n := by
    have harg : Real.exp 1 + 4 * (n : ℝ) ≤ 5 * (Real.exp 1 * n) := by
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < Real.exp 1 + 4 * (n : ℝ)) harg
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity),
      Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp] at h
    have hfive := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    change H ≤ Real.log 5 + (1 + Real.log (n : ℝ)) at h
    rw [← hb] at h
    linarith
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hs_sq := Real.sq_sqrt hnpos.le
  have hlog := Real.log_le_sub_one_of_pos hspos
  rw [Real.log_sqrt hnpos.le] at hlog
  have hLs : benchmarkLog n ≤ 2 * Real.sqrt (n : ℝ) := by rw [hb]; linarith
  have hLn : benchmarkLog n ^ 2 ≤ 4 * (n : ℝ) := by nlinarith
  have hLsq : 0 < benchmarkLog n ^ 2 := by positivity
  have hHsq : 0 < H ^ 2 := by positivity
  rw [rate_two]
  change 1 / (25 * benchmarkLog n ^ 2) ≤ 1 / (n : ℝ) + 4 / H ^ 2 ∧
    1 / (n : ℝ) + 4 / H ^ 2 ≤ 20 / benchmarkLog n ^ 2
  constructor
  · have hsq : H ^ 2 ≤ 25 * benchmarkLog n ^ 2 := by nlinarith
    have hdiv : 1 / (25 * benchmarkLog n ^ 2) ≤ 4 / H ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) hHsq).2
      nlinarith
    exact hdiv.trans (le_add_of_nonneg_left (by positivity))
  · have hparam : 1 / (n : ℝ) ≤ 4 / benchmarkLog n ^ 2 :=
      (div_le_div_iff₀ hnpos hLsq).2 (by nlinarith)
    have hhet : 4 / H ^ 2 ≤ 16 / benchmarkLog n ^ 2 := by
      apply (div_le_div_iff₀ hHsq hLsq).2
      nlinarith
    calc
      _ ≤ 4 / benchmarkLog n ^ 2 + 16 / benchmarkLog n ^ 2 := add_le_add hparam hhet
      _ = _ := by ring

-- @node: thm:known-radius-minimax-frontier
theorem known_radius_minimax_frontier
    (hSampling : ∀ n (P : Law n),
      IidSampling n P (DiscreteAteHeterogeneityFrontier.productLaw n P)) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      -- @realizes c(universal lower constant) @realizes C(universal upper constant)
      (∀ n M rho, 3 ≤ n → 1 ≤ M → 0 ≤ rho → rho ≤ 2 →
        c * M ^ 2 * rate n rho ≤ knownRadiusMinimaxRisk n M rho ∧
        knownRadiusMinimaxRisk n M rho ≤
          worstRisk n M rho (knownRadiusEstimator n M rho) ∧
        worstRisk n M rho (knownRadiusEstimator n M rho) ≤
          C * M ^ 2 * rate n rho ∧
        (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
          -- @realizes T(arbitrary measurable sample estimator)
          ∃ P : KnownRadiusClass n M rho,
            ENNReal.ofReal (c * M ^ 2 * rate n rho) ≤
              ∫⁻ x, ENNReal.ofReal
                ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2)
                ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law)) ∧
      (∀ n M, 3 ≤ n → 1 ≤ M →
        c * M ^ 2 / n ≤ knownRadiusMinimaxRisk n M 0 ∧
        knownRadiusMinimaxRisk n M 0 ≤ C * M ^ 2 / n ∧
        c * M ^ 2 * rateCrit n ≤
          knownRadiusMinimaxRisk n M (criticalRadius n) ∧
        knownRadiusMinimaxRisk n M (criticalRadius n) ≤
          C * M ^ 2 * rateCrit n ∧
        c * M ^ 2 / (DiscreteAteHeterogeneityFrontier.logEN n) ^ 2 ≤
          knownRadiusMinimaxRisk n M 2 ∧
        knownRadiusMinimaxRisk n M 2 ≤
          C * M ^ 2 / (DiscreteAteHeterogeneityFrontier.logEN n) ^ 2) ∧
      (∀ n M (P : Law n), 3 ≤ n → 1 ≤ M →
        Consistency P → ConditionalExchangeability P → FixedOverlap P →
        MeanEnvelope M P → VarianceEnvelope M P →
        DiscreteAteHeterogeneityFrontier.ApproximateHomogeneity M 2 P) ∧
      Tendsto (fun x : ℝ =>
        x / (Real.log (Real.exp 1 + x)) ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ =>
        x / (Real.log (Real.exp 1 + x)) ^ 2) atTop atTop := by
  obtain ⟨C₀, hC₀, hupper⟩ := known_radius_estimator_worstRisk_bound
  -- Only the statistical converse remains in this assembly; the numerical
  -- endpoint comparisons are proved above and applied below.
  have hremaining : ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ n M rho, 3 ≤ n → 1 ≤ M → 0 ≤ rho → rho ≤ 2 →
        c₀ * M ^ 2 * rate n rho ≤ knownRadiusMinimaxRisk n M rho ∧
        (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
          ∃ P : KnownRadiusClass n M rho,
            ENNReal.ofReal (c₀ * M ^ 2 * rate n rho) ≤
              ∫⁻ x, ENNReal.ofReal
                ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2)
                ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law)) := by
    exact known_radius_minimax_lower_bound
  obtain ⟨c₀, hc₀, hlower⟩ := hremaining
  let c := c₀ / 25
  let C := 20 * (C₀ + c₀ + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcc₀ : c ≤ c₀ := by dsimp [c]; linarith
  have hC : C₀ ≤ C := by dsimp [C]; linarith
  have h20C : 20 * C₀ ≤ C := by dsimp [C]; linarith
  have hcC : c < C := by dsimp [c, C]; linarith
  have hrate (n : ℕ) (rho : ℝ) : 0 ≤ rate n rho := by unfold rate; positivity
  have hfrontier (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
      (hr0 : 0 ≤ rho) (hr2 : rho ≤ 2) :
      c * M ^ 2 * rate n rho ≤ knownRadiusMinimaxRisk n M rho ∧
      knownRadiusMinimaxRisk n M rho ≤
        worstRisk n M rho (knownRadiusEstimator n M rho) ∧
      worstRisk n M rho (knownRadiusEstimator n M rho) ≤ C * M ^ 2 * rate n rho ∧
      (∀ T : (Fin n → SampleObs n) → ℝ, Measurable T →
        ∃ P : KnownRadiusClass n M rho,
          ENNReal.ofReal (c * M ^ 2 * rate n rho) ≤
            ∫⁻ x, ENNReal.ofReal
              ((T x - DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2)
              ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) := by
    obtain ⟨hl, hcertificate⟩ := hlower n M rho hn hM hr0 hr2
    have hsmall : c * M ^ 2 * rate n rho ≤ c₀ * M ^ 2 * rate n rho :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcc₀ (sq_nonneg M)) (hrate n rho)
    refine ⟨hsmall.trans hl,
      knownRadiusMinimaxRisk_le_estimatorRisk n M rho (by linarith),
      (hupper n M rho hn hM).trans ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (sq_nonneg M)) (hrate n rho)
    · intro T hT
      obtain ⟨P, hP⟩ := hcertificate T hT
      exact ⟨P, (ENNReal.ofReal_le_ofReal hsmall).trans hP⟩
  refine ⟨c, C, hc, hcC, hfrontier, ?_, ?_,
    frontier_rate_factor_tendsto_zero, frontier_rate_factor_tendsto_infinity⟩
  · intro n M hn hM
    obtain ⟨hzl, hzm, hzu, _⟩ := hfrontier n M 0 hn hM (by norm_num) (by norm_num)
    obtain ⟨hcr0, hcr2⟩ := criticalRadius_range n hn
    obtain ⟨hcl, hcm, hcu, _⟩ := hfrontier n M (criticalRadius n) hn hM hcr0 hcr2
    have hcrit := rate_critical_identity n (by omega)
    have hzeroL : c * M ^ 2 / n ≤ knownRadiusMinimaxRisk n M 0 := by
      simpa only [rate_zero, mul_one_div] using hzl
    have hzeroU : knownRadiusMinimaxRisk n M 0 ≤ C * M ^ 2 / n := by
      simpa only [rate_zero, mul_one_div] using hzm.trans hzu
    have hcritL : c * M ^ 2 * rateCrit n ≤
        knownRadiusMinimaxRisk n M (criticalRadius n) := by simpa only [hcrit] using hcl
    have hcritU : knownRadiusMinimaxRisk n M (criticalRadius n) ≤
        C * M ^ 2 * rateCrit n := by simpa only [hcrit] using hcm.trans hcu
    obtain ⟨hrl, hru⟩ := rate_two_log_comparison n hn
    obtain ⟨htl, _⟩ := hlower n M 2 hn hM (by norm_num) (by norm_num)
    have htwoL : c * M ^ 2 / benchmarkLog n ^ 2 ≤ knownRadiusMinimaxRisk n M 2 := by
      calc
        _ = c₀ * M ^ 2 * (1 / (25 * benchmarkLog n ^ 2)) := by dsimp [c]; ring
        _ ≤ c₀ * M ^ 2 * rate n 2 :=
          mul_le_mul_of_nonneg_left hrl (mul_nonneg hc₀.le (sq_nonneg M))
        _ ≤ _ := htl
    have htwoU : knownRadiusMinimaxRisk n M 2 ≤ C * M ^ 2 / benchmarkLog n ^ 2 := by
      calc
        _ ≤ worstRisk n M 2 (knownRadiusEstimator n M 2) :=
          knownRadiusMinimaxRisk_le_estimatorRisk n M 2 (by linarith)
        _ ≤ C₀ * M ^ 2 * rate n 2 := hupper n M 2 hn hM
        _ ≤ C₀ * M ^ 2 * (20 / benchmarkLog n ^ 2) :=
          mul_le_mul_of_nonneg_left hru (mul_nonneg hC₀.le (sq_nonneg M))
        _ = (20 * C₀) * (M ^ 2 / benchmarkLog n ^ 2) := by ring
        _ ≤ C * (M ^ 2 / benchmarkLog n ^ 2) :=
          mul_le_mul_of_nonneg_right h20C (div_nonneg (sq_nonneg M) (sq_nonneg _))
        _ = _ := by ring
    exact ⟨hzeroL, hzeroU, hcritL, hcritU, htwoL, htwoU⟩
  · intro n M P hn hM hcons hexch hover hmean hvar
    exact radius_two_vacuous P hmean

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
