module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierLengthAssembly
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierLower
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierRates
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierRiskAssembly
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.Identification
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.TObservableUpper

/-!
# The complete-record MSE and honest-length precision frontier

The finite-population upper bounds, coverage, constants, and endpoint rates are
assembled from the observable-rule bounds. The specified rules attain vanishing
risk and honest length exactly when all three costs vanish. Separate supported
interval tests establish the connected-length lower bound. Law-level identification uses
positive assignment-cell probabilities and deterministic potential outcomes.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,ha,hH,hi), [the specified interval has finite-population coverage under every admissible design.](goal) -/
-- @node: Istar_honest
lemma Istar_honest (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) (D : Design (Fin n))
    (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r) (hi : DesignIndependent D) :
    Honest D d (Istar n d q r) := by
  intro η hη
  have hupper := observable_upper d q r (by simpa using hn) hd
    (by simpa using hdu) hqr D ha hH hi η hη
  simpa only [Fintype.card_fin, Istar, upperIntervalProc] using hupper.2.2.2.1

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,ha,hH,hi), [The attaining estimator's worst-case risk is bounded by forty times the public rate.](goal) -/
-- @node: Tstar_worstRisk_le_rate
lemma Tstar_worstRisk_le_rate (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) (D : Design (Fin n))
    (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r) (hi : DesignIndependent D) :
    worstRisk D d (Tstar n d q r) ≤ ENNReal.ofReal (CUpper * rho n d q r) := by
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro η
  have hrisk := upperEstimator_sqLoss_le_envelope η.1 d q r
    (by simpa using hn) hd η.2 hqr D ha hH hi
  have hrate := envelope_rate_le n d hn hd hdu q r hqr
  have hρ := (rho_pos n d hn hd hdu q r hqr).le
  have hrisk' : sqLoss D η.1 (Tstar n d q r) ≤
      ENNReal.ofReal (boundedEnvelope n d q r) := by
    simpa only [Fintype.card_fin, Tstar] using hrisk
  exact hrisk'.trans (ENNReal.ofReal_le_ofReal (by dsimp only [CUpper]; linarith))

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [The observable interval radius has the claimed square-root rate.](goal) -/
-- @node: upperInterval_radius_le_rate
lemma upperInterval_radius_le_rate (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) :
    2 * Real.sqrt (10 * boundedEnvelope n d q r) ≤ CUpper * ell n d q r := by
  have hrate := envelope_rate_le n d hn hd hdu q r hqr
  have hs : Real.sqrt (10 * boundedEnvelope n d q r) ≤
      Real.sqrt (200 * rho n d q r) := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 200)] at hs
  have hc : Real.sqrt 200 ≤ 20 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200), Real.sqrt_nonneg 200]
  have hprod := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (rho n d q r))
  dsimp only [CUpper, ell]
  linarith

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,ha,hH,hi), [Averaging the pointwise length bound over each probability record law gives the worst-case rate.](goal) -/
-- @node: Istar_worstLength_le_rate
lemma Istar_worstLength_le_rate (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) (D : Design (Fin n))
    (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r) (hi : DesignIndependent D) :
    worstLength D d (Istar n d q r) ≤ ENNReal.ofReal (CUpper * ell n d q r) := by
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro η
  have hD : IsProbabilityMeasure (D η.1) := by
    rw [design_eq_noisyDesign D q r ha hH hi]
    exact noisyDesign_probability q r hqr η.1
  letI := recordLaw_probability D η.1 hD
  unfold expLength
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (CUpper * ell n d q r) ∂recordLaw D η.1 := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact ((upperInterval_length_le n d q r x.1).trans (min_le_right _ _)).trans
        (upperInterval_radius_le_rate n d hn hd hdu q r hqr)
    _ = _ := by simp

open Filter Topology
/-- Given [the stated assumptions](hyp:hc,hf,w,hlower,hw), [A positive multiple of a nonnegative rate bounded by a vanishing decision loss
forces the rate itself to vanish.](goal) -/
-- @node: rate_vanishes_of_scaled_lower
lemma rate_vanishes_of_scaled_lower (f : ℕ → ℝ) (w : ℕ → ℝ≥0∞)
    (c : ℝ) (hc : 0 < c) (hf : ∀ᶠ n in atTop, 0 ≤ f n)
    (hlower : ∀ᶠ n in atTop, ENNReal.ofReal (c * f n) ≤ w n)
    (hw : Tendsto w atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hscaled : Tendsto (fun n => ENNReal.ofReal (c * f n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw
      (Filter.Eventually.of_forall (fun _ => zero_le)) hlower
  have hreal : Tendsto (fun n => c * f n) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hscaled
    have heq : (fun n => (ENNReal.ofReal (c * f n)).toReal) =ᶠ[atTop]
        (fun n => c * f n) := by
      filter_upwards [hf] with n hn
      exact ENNReal.toReal_ofReal (mul_nonneg hc.le hn)
    exact (tendsto_congr' heq).mp (by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using ht)
  have ht : Tendsto (fun n => c⁻¹ * (c * f n)) atTop (𝓝 (c⁻¹ * (0 : ℝ))) :=
    tendsto_const_nhds.mul hreal
  simpa [← mul_assoc, hc.ne'] using ht

/-- Given [the stated assumptions](hyp:hadm,hD,hcost), [When the three public costs vanish, the specified original-record rules
have vanishing worst-case MSE and finite-honest vanishing expected length.](goal) -/
-- @node: frontier_rules_vanish
lemma frontier_rules_vanish (ds : ℕ → ℕ) (qs rs : ℕ → ℝ)
    (hadm : AdmissibleSequences ds qs rs) (D : (n : ℕ) → Design (Fin n))
    (hD : ∀ n, 4 ≤ n → AssignmentLaw (D n) ∧
      AcquisitionLaw (D n) (qs n) (rs n) ∧ DesignIndependent (D n))
    (hcost : Tendsto (fun n => degRatio n (ds n)) atTop (𝓝 0) ∧
      Tendsto (fun n => missRatio n (ds n) (qs n)) atTop (𝓝 0) ∧
      Tendsto (fun n => falseRatio (qs n) (rs n)) atTop (𝓝 0)) :
    Tendsto (fun n => worstRisk (D n) (ds n) (Tstar n (ds n) (qs n) (rs n)))
      atTop (𝓝 0) ∧
    (∀ n, 4 ≤ n → Honest (D n) (ds n) (Istar n (ds n) (qs n) (rs n))) ∧
    Tendsto (fun n => worstLength (D n) (ds n) (Istar n (ds n) (qs n) (rs n)))
      atTop (𝓝 0) := by
  have hρ := (rate_tendsto_iff ds qs rs hadm).mpr hcost
  have hρreal : Tendsto (fun n => rho n (ds n) (qs n) (rs n)) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hρ
    have heq : (fun n => (ENNReal.ofReal (rho n (ds n) (qs n) (rs n))).toReal)
        =ᶠ[atTop] (fun n => rho n (ds n) (qs n) (rs n)) := by
      filter_upwards [eventually_ge_atTop 4] with n hn
      have hp := (hadm n hn).1
      exact ENNReal.toReal_ofReal (rho_pos n (ds n) hn hp.2.1 hp.2.2
        (qs n) (rs n) (hadm n hn).2).le
    exact (tendsto_congr' heq).mp (by simpa only [Function.comp_def, ENNReal.toReal_zero] using ht)
  have hℓreal : Tendsto (fun n => ell n (ds n) (qs n) (rs n)) atTop (𝓝 0) := by
    simpa only [ell, Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hρreal
  have hR : Tendsto (fun n => ENNReal.ofReal (CUpper * rho n (ds n) (qs n) (rs n)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hρreal)
  have hL : Tendsto (fun n => ENNReal.ofReal (CUpper * ell n (ds n) (qs n) (rs n)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hℓreal)
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_, ?_,
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_⟩
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hp := (hadm n hn).1
    have hdesign := hD n hn
    exact Tstar_worstRisk_le_rate n (ds n) hn hp.2.1 hp.2.2
      (qs n) (rs n) (hadm n hn).2 (D n) hdesign.1 hdesign.2.1 hdesign.2.2
  · intro n hn
    have hp := (hadm n hn).1
    have hdesign := hD n hn
    exact Istar_honest n (ds n) hn hp.2.1 hp.2.2
      (qs n) (rs n) (hadm n hn).2 (D n) hdesign.1 hdesign.2.1 hdesign.2.2
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hp := (hadm n hn).1
    have hdesign := hD n hn
    exact Istar_worstLength_le_rate n (ds n) hn hp.2.1 hp.2.2
      (qs n) (rs n) (hadm n hn).2 (D n) hdesign.1 hdesign.2.1 hdesign.2.2

/-- [Universal two-sided bounds for both decisions, finite-population honesty,
the two sequence equivalences, exact endpoint rates, and law-level identification.
The universal numerical constants are fixed before all public parameters.](goal) -/
-- @node: thm:complete-record-precision-frontier
theorem complete_record_precision_frontier :
    (0 < cLower ∧ CUpper = 40 ∧ nZero = 512) ∧
    (∀ (n : ℕ), nZero ≤ n → ∀ (d : ℕ), 1 ≤ d → d ≤ n-1 →
      ∀ q r : ℝ, ChannelDomain q r → ∀ D : Design (Fin n),
      AssignmentLaw D → AcquisitionLaw D q r → DesignIndependent D →
      ENNReal.ofReal (cLower*rho n d q r) ≤ minimaxRisk D d ∧
      minimaxRisk D d ≤ worstRisk D d (Tstar n d q r) ∧
      worstRisk D d (Tstar n d q r) ≤ ENNReal.ofReal (CUpper*rho n d q r) ∧
      ENNReal.ofReal (cLower*ell n d q r) ≤ minimaxLength D d ∧
      minimaxLength D d ≤ worstLength D d (Istar n d q r) ∧
      worstLength D d (Istar n d q r) ≤ ENNReal.ofReal (CUpper*ell n d q r)) ∧
    (∀ (n : ℕ), 4 ≤ n → ∀ (d : ℕ), 1 ≤ d → d ≤ n-1 →
      ∀ q r : ℝ, ChannelDomain q r → ∀ D : Design (Fin n),
      AssignmentLaw D → AcquisitionLaw D q r → DesignIndependent D →
      Measurable (upperRule (V := Fin n) n d q r) ∧
      Measurable (upperInterval (V := Fin n) n d q r) ∧ Honest D d (Istar n d q r)) ∧
    (∀ (ds : ℕ → ℕ) (qs rs : ℕ → ℝ), AdmissibleSequences ds qs rs →
      ∀ D : (n : ℕ) → Design (Fin n),
      (∀ n, 4 ≤ n → AssignmentLaw (D n) ∧ AcquisitionLaw (D n) (qs n) (rs n) ∧ DesignIndependent (D n)) →
      ((∃ T : (n : ℕ) → Estimator (Fin n),
        Tendsto (fun n => worstRisk (D n) (ds n) (T n)) atTop (𝓝 0)) ↔
        (Tendsto (fun n => degRatio n (ds n)) atTop (𝓝 0) ∧
         Tendsto (fun n => missRatio n (ds n) (qs n)) atTop (𝓝 0) ∧
         Tendsto (fun n => falseRatio (qs n) (rs n)) atTop (𝓝 0))) ∧
      ((∃ I : (n : ℕ) → IntervalProc (Fin n),
        (∀ n, 4 ≤ n → Honest (D n) (ds n) (I n)) ∧
        Tendsto (fun n => worstLength (D n) (ds n) (I n)) atTop (𝓝 0)) ↔
        (Tendsto (fun n => degRatio n (ds n)) atTop (𝓝 0) ∧
         Tendsto (fun n => missRatio n (ds n) (qs n)) atTop (𝓝 0) ∧
         Tendsto (fun n => falseRatio (qs n) (rs n)) atTop (𝓝 0)))) ∧
    (∀ (n d : ℕ), 4 ≤ n → 1 ≤ d → d ≤ n-1 →
      (∀ q : ℝ, q ∈ Set.Icc 0 1 → 0 < q → rho n d q 0 = min 1 ((d : ℝ)^2/n + d/(n*q))) ∧
      (∀ q : ℝ, q ∈ Set.Icc 0 1 → rho n d q q = 1) ∧
      min 1 ((d : ℝ)^2/n) ≤ rho n d 1 0 ∧ rho n d 1 0 ≤ 2 * min 1 ((d : ℝ)^2/n)) ∧
    (∀ (n : ℕ), 4 ≤ n → ∀ q r : ℝ, ChannelDomain q r →
      ∀ D : Design (Fin n), AssignmentLaw D → AcquisitionLaw D q r → DesignIndependent D →
      ∀ η : Schedule (Fin n),
      (∀ z : Bool,
        recordLaw D η {x | x.1.2.1 = fun _ => z} = (2 : ℝ≥0∞)⁻¹ ^ n ∧
        ∀ i : Fin n,
          (∫ x in {x : Record (Fin n) × ℝ | x.1.2.1 = fun _ => z}, x.1.2.2 i ∂recordLaw D η) /
            (recordLaw D η {x | x.1.2.1 = fun _ => z}).toReal =
              CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i (fun _ => z)) ∧
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η = (n : ℝ)⁻¹ * ∑ i : Fin n,
        ((∫ x in {x : Record (Fin n) × ℝ | x.1.2.1 = fun _ => true}, x.1.2.2 i ∂recordLaw D η) /
          (recordLaw D η {x | x.1.2.1 = fun _ => true}).toReal -
         (∫ x in {x : Record (Fin n) × ℝ | x.1.2.1 = fun _ => false}, x.1.2.2 i ∂recordLaw D η) /
          (recordLaw D η {x | x.1.2.1 = fun _ => false}).toReal)) := by
  -- Separate supported risk and interval tests give both finite converses.
  have hlower : ∀ (n : ℕ), nZero ≤ n → ∀ (d : ℕ), 1 ≤ d → d ≤ n-1 →
      ∀ q r : ℝ, ChannelDomain q r → ∀ D : Design (Fin n),
      AssignmentLaw D → AcquisitionLaw D q r → DesignIndependent D →
      ENNReal.ofReal (cLower * rho n d q r) ≤ minimaxRisk D d ∧
      ENNReal.ofReal (cLower * ell n d q r) ≤ minimaxLength D d := by
    intro n hn d hd hdu q r hqr D ha hH hi
    constructor
    · rw [design_eq_noisyDesign D q r ha hH hi]
      exact frontier_risk_lower n d hn hd hdu q r hqr
    · rw [design_eq_noisyDesign D q r ha hH hi]
      exact frontier_length_lower n d hn hd hdu q r hqr
  refine ⟨⟨constants_valid.1, rfl, rfl⟩, ?_, ?_, ?_, frontier_endpoints, ?_⟩
  · intro n hn d hd hdu q r hqr D ha hH hi
    have hn4 : 4 ≤ n := constants_valid.2.2.trans hn
    have hhonest := Istar_honest n d hn4 hd hdu q r hqr D ha hH hi
    have hminLength : minimaxLength D d ≤ worstLength D d (Istar n d q r) := by
      exact iInf_le (fun I : {I : IntervalProc (Fin n) // Honest D d I} =>
        worstLength D d I.1) ⟨Istar n d q r, hhonest⟩
    refine ⟨?_, Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk (Tstar n d q r),
      Tstar_worstRisk_le_rate n d hn4 hd hdu q r hqr D ha hH hi, ?_,
      hminLength,
      Istar_worstLength_le_rate n d hn4 hd hdu q r hqr D ha hH hi⟩
    · exact (hlower n hn d hd hdu q r hqr D ha hH hi).1
    · exact (hlower n hn d hd hdu q r hqr D ha hH hi).2
  · intro n hn d hd hdu q r hqr D ha hH hi
    exact ⟨upperRule_measurable _ _ _ _, upperInterval_measurable _ _ _ _,
      Istar_honest n d hn hd hdu q r hqr D ha hH hi⟩
  · intro ds qs rs hadm D hD
    constructor
    · constructor
      · rintro ⟨T, hT⟩
        apply (rate_tendsto_iff ds qs rs hadm).mp
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        apply rate_vanishes_of_scaled_lower _ _ cLower constants_valid.1 _ _ hT
        · filter_upwards [eventually_ge_atTop 4] with n hn
          have hp := (hadm n hn).1
          exact (rho_pos n (ds n) hn hp.2.1 hp.2.2
            (qs n) (rs n) (hadm n hn).2).le
        · filter_upwards [eventually_ge_atTop nZero] with n hn
          have hn4 := constants_valid.2.2.trans hn
          have hp := (hadm n hn4).1
          have hdesign := hD n hn4
          exact ((hlower n hn (ds n) hp.2.1 hp.2.2 (qs n) (rs n)
            (hadm n hn4).2 (D n) hdesign.1 hdesign.2.1 hdesign.2.2).1).trans
              (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk (T n))
      · intro hcost
        exact ⟨fun n => Tstar n (ds n) (qs n) (rs n),
          (frontier_rules_vanish ds qs rs hadm D hD hcost).1⟩
    · constructor
      · rintro ⟨I, hhonest, hI⟩
        have hℓ : Tendsto (fun n => ell n (ds n) (qs n) (rs n)) atTop (𝓝 0) := by
          apply rate_vanishes_of_scaled_lower _ _ cLower constants_valid.1 _ _ hI
          · exact Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)
          · filter_upwards [eventually_ge_atTop nZero] with n hn
            have hn4 := constants_valid.2.2.trans hn
            have hp := (hadm n hn4).1
            have hdesign := hD n hn4
            have hmin : minimaxLength (D n) (ds n) ≤ worstLength (D n) (ds n) (I n) :=
              iInf_le (fun J : {J : IntervalProc (Fin n) // Honest (D n) (ds n) J} =>
                worstLength (D n) (ds n) J.1) ⟨I n, hhonest n hn4⟩
            exact ((hlower n hn (ds n) hp.2.1 hp.2.2 (qs n) (rs n)
              (hadm n hn4).2 (D n) hdesign.1 hdesign.2.1 hdesign.2.2).2).trans hmin
        have heq : (fun n => ell n (ds n) (qs n) (rs n) ^ 2) =ᶠ[atTop]
            (fun n => rho n (ds n) (qs n) (rs n)) := by
          filter_upwards [eventually_ge_atTop 4] with n hn
          have hp := (hadm n hn).1
          exact Real.sq_sqrt (rho_pos n (ds n) hn hp.2.1 hp.2.2
            (qs n) (rs n) (hadm n hn).2).le
        apply (rate_tendsto_iff ds qs rs hadm).mp
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        exact (tendsto_congr' heq).mp (by simpa using hℓ.pow 2)
      · intro hcost
        exact ⟨fun n => Istar n (ds n) (qs n) (rs n),
          (frontier_rules_vanish ds qs rs hadm D hD hcost).2⟩
  · intro n hn q r hqr D ha hH hi η
    refine ⟨?_, ?_⟩
    · intro z
      exact ⟨by simpa using recordLaw_assignment_mass D η ha (fun _ => z),
        fun i => recordLaw_assignment_mean D η ha (fun _ => z) i⟩
    · simp_rw [recordLaw_assignment_mean D η ha]
      simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte,
        Fintype.card_fin, potentialOutcome]

end CausalSmith.Experimentation.NoisygraphTtePrecision
