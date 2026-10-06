module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExplicitInterpolation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExplicitRiskEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FourthOrderBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.GeneralBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureProductLaw
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrencePoissonMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SecondOrderBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpContinuationRemainder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpFirstOrderTaylor
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpSecondOrderTaylor
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ThirdOrderBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly
public import Causalean.Stat.Sample.Stratified.NestedCountBound
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Uniform risk of the observable estimator

The risk bound separates continuation bias, inverse-risk variance, and
extinction probability, all with constants fixed over the model class.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The declared explicit bias coefficient is valid when the endpoint Taylor
polynomial has order zero. -/
-- @node: explicitBias_orderZero
lemma explicitBias_orderZero (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hzero : holderOrder c = 0)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    |truncatedMean c P a band - armMean P a| ≤
      explicitBiasEnvelope c * band ^ (c.beta + 1) := by
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t
  let r : ℝ → ℝ := fun t => f t - f 1
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (modelClass_survival_continuousOn c P hP a).mul
      (hP.recurrenceHolder a).1.continuousOn
  have hhalf : band ≤ 1 / 2 := by linarith [c.x0_le]
  have hC : 0 ≤ c.Llambda + c.dMax * c.lambdaMax := by
    have hd := c.dMin_pos.le.trans c.dMin_lt.le
    have hl := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
    exact add_nonneg c.Llambda_pos.le (mul_nonneg hd hl)
  have hr := continuationWeight_sharp_remainder_bound 0 hb hhalf c.beta_pos hC r
    (hf.sub continuousOn_const) (by
      intro t ht
      exact survival_product_orderZero_remainder c P hP a hzero
        ⟨by linarith [ht.1], ht.2⟩)
  have hi := continuationWeight_remainder_identity 0 (fun _ => f 1) hb hhalf f
    (modelClass_target_intervalIntegrable c P hP a)
    (by simpa only [hzero, f, mul_assoc] using
      modelClass_weightedTarget_intervalIntegrable c P hP a hb hhalf)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, pow_zero,
    mul_one, add_zero] at hi
  change (∫ t in (0 : ℝ)..(1 - band), continuationWeight 0 band t * f t) -
    ∫ t in (0 : ℝ)..1, f t = _ at hi
  have he : |truncatedMean c P a band - armMean P a| =
      |(∫ t in (0 : ℝ)..(1 - band), continuationWeight 0 band t * r t) -
        ∫ t in (0 : ℝ)..1, r t| := by
    simpa only [truncatedMean, armMean, hzero, f, r, mul_assoc] using congrArg abs hi
  rw [he]
  have hc : explicitBiasEnvelope c =
      (c.Llambda + c.dMax * c.lambdaMax) *
        ((∑ m : Fin (0 + 1),
          |((continuationGram 0)⁻¹.mulVec (continuationRhs 0)) m| * (2 : ℝ) ^ m.val) *
          ((2 : ℝ) ^ (c.beta + 1) - 1) / (c.beta + 1) + 1 / (c.beta + 1)) := by
    simp only [explicitBiasEnvelope, taylorRatio, productHolderEnvelope,
      hzero, Nat.cast_zero, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, one_mul, survivalDerivativeEnvelope, derivativeHolderEnvelope,
      derivativeEnvelope, survivalHolderEnvelope, Nat.lt_irrefl, ↓reduceIte,
      Nat.sub_self, continuationNorm, continuationCoeff]
    rw [hzero]
  rw [hc]
  exact hr

/-- Squaring the order-zero continuation bound supplies the bias-risk term. -/
-- @node: explicitBiasRisk_orderZero
lemma explicitBiasRisk_orderZero (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hzero : holderOrder c = 0)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    2 * (truncatedMean c P a band - armMean P a) ^ 2 ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) := by
  have h := explicitBias_orderZero c P hP a hzero hb hcap
  have hn : 0 ≤ explicitBiasEnvelope c * band ^ (c.beta + 1) :=
    (abs_nonneg _).trans h
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).2 h
  rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast hb.le] at hs
  simp only [Nat.cast_ofNat,
    show (c.beta + 1) * (2 : ℝ) = 2 * c.beta + 2 by ring] at hs
  unfold explicitBiasRisk
  linarith only [hs]

/-- The full declared finite-sample envelope is proved for order zero. -/
-- @node: upper_risk_explicit_orderZero
lemma upper_risk_explicit_orderZero (c : ClassConstants) (P : SubjectLaw)
    (h : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n)
    (band : ℝ) (hband : 0 < band ∧ band ≤ c.x0 / 2) (hzero : holderOrder c = 0) :
    Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c band a) (armMean P a) ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) +
      explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
    explicitExtinctionRisk c *
        Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) := by
  have hr := upper_risk_with_actual_bias c P h a n hn hband.1 hband.2
  have hb := explicitBiasRisk_orderZero c P h a hzero hband.1 hband.2
  change _ ≤ 2 * _ + explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
    explicitExtinctionRisk c *
      Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) at hr
  linarith only [hr, hb]

/-- The explicit first-order product seminorm envelope is nonnegative. -/
-- @node: productHolderEnvelope_orderOne_nonneg
lemma productHolderEnvelope_orderOne_nonneg (c : ClassConstants)
    (hone : holderOrder c = 1) : 0 ≤ productHolderEnvelope c := by
  have hD := derivativeEnvelope_orderOne_nonneg c hone
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_orderOne_nonneg c hone
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
  have hL := c.Llambda_pos.le
  simp [productHolderEnvelope, hone, Finset.sum_range_succ, survivalDerivativeEnvelope,
    derivativeHolderEnvelope, survivalHolderEnvelope]
  positivity

/-- Sharp first-order Taylor remainder plus continuation moment matching
proves the declared bias constant for the first positive Taylor order. -/
-- @node: explicitBias_orderOne
lemma explicitBias_orderOne (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hone : holderOrder c = 1)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    |truncatedMean c P a band - armMean P a| ≤
      explicitBiasEnvelope c * band ^ (c.beta + 1) := by
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t
  let v : Fin (1 + 1) → ℝ := fun j =>
    if j.val = 0 then f 1 else -derivWithin f (Icc (0 : ℝ) 1) 1
  let r : ℝ → ℝ := fun t => f t - ∑ j : Fin (1 + 1), v j * (1 - t) ^ j.val
  have hpoly (t : ℝ) : (∑ j : Fin (1 + 1), v j * (1 - t) ^ j.val) =
      f 1 + derivWithin f (Icc (0 : ℝ) 1) 1 * (t - 1) := by
    simp [v, Fin.sum_univ_succ]
    ring
  have hf := survival_product_orderOne_holder c P hP hone a
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := hf.1.continuousOn
  have hr : ContinuousOn r (Icc (0 : ℝ) 1) := by
    simp_rw [r, hpoly]
    exact hc.sub (continuousOn_const.add (continuousOn_const.mul
      (continuousOn_id.sub continuousOn_const)))
  have hhalf : band ≤ 1 / 2 := by linarith [c.x0_le]
  have hα := (holderOrder_remainder_exponent c).1
  simp only [hone, Nat.cast_one] at hα
  have hC : 0 ≤ productHolderEnvelope c / c.beta :=
    div_nonneg (productHolderEnvelope_orderOne_nonneg c hone) c.beta_pos.le
  have hrem : ∀ t ∈ Icc (1 - 2 * band) 1,
      |r t| ≤ (productHolderEnvelope c / c.beta) * (1 - t) ^ c.beta := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hs := firstOrder_remainder_bound f hα hf (by norm_num : (1 : ℝ) ∈ Icc 0 1) ht'
    simp only [show c.beta - 1 + 1 = c.beta by ring,
      abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] at hs
    simpa only [r, hpoly, sub_add_eq_sub_sub] using hs
  have hsharp := continuationWeight_sharp_remainder_bound 1 hb hhalf c.beta_pos
    hC r hr hrem
  have hi := continuationWeight_remainder_identity 1 v hb hhalf f
    (modelClass_target_intervalIntegrable c P hP a)
    (by simpa only [hone, f, mul_assoc] using
      modelClass_weightedTarget_intervalIntegrable c P hP a hb hhalf)
  have he : |truncatedMean c P a band - armMean P a| =
      |(∫ t in (0 : ℝ)..(1 - band), continuationWeight 1 band t * r t) -
        ∫ t in (0 : ℝ)..1, r t| := by
    simpa only [truncatedMean, armMean, hone, f, r, mul_assoc] using congrArg abs hi
  rw [he]
  have hcoef : explicitBiasEnvelope c =
      (productHolderEnvelope c / c.beta) *
        ((∑ m : Fin (1 + 1),
          |((continuationGram 1)⁻¹.mulVec (continuationRhs 1)) m| * (2 : ℝ) ^ m.val) *
          ((2 : ℝ) ^ (c.beta + 1) - 1) / (c.beta + 1) + 1 / (c.beta + 1)) := by
    simp only [explicitBiasEnvelope, taylorRatio_orderOne c hone,
      continuationNorm, continuationCoeff]
    rw [hone]
    ring
  rw [hcoef]
  exact hsharp

/-- Squaring the sharp first-order bias supplies its declared risk term. -/
-- @node: explicitBiasRisk_orderOne
lemma explicitBiasRisk_orderOne (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hone : holderOrder c = 1)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    2 * (truncatedMean c P a band - armMean P a) ^ 2 ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) := by
  have h := explicitBias_orderOne c P hP a hone hb hcap
  have hn : 0 ≤ explicitBiasEnvelope c * band ^ (c.beta + 1) :=
    (abs_nonneg _).trans h
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).2 h
  rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast hb.le] at hs
  simp only [Nat.cast_ofNat,
    show (c.beta + 1) * (2 : ℝ) = 2 * c.beta + 2 by ring] at hs
  unfold explicitBiasRisk
  linarith only [hs]

/-- Combining the sharp first-order bias with the verified stochastic risk
closes the full finite-sample explicit envelope at order one. -/
-- @node: upper_risk_explicit_orderOne
lemma upper_risk_explicit_orderOne (c : ClassConstants) (P : SubjectLaw)
    (h : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n)
    (band : ℝ) (hband : 0 < band ∧ band ≤ c.x0 / 2) (hone : holderOrder c = 1) :
    Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c band a) (armMean P a) ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) +
      explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
      explicitExtinctionRisk c *
        Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) := by
  have hr := upper_risk_with_actual_bias c P h a n hn hband.1 hband.2
  have hb := explicitBiasRisk_orderOne c P h a hone hband.1 hband.2
  change _ ≤ 2 * _ + explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
    explicitExtinctionRisk c *
      Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) at hr
  linarith only [hr, hb]

-- @node: upper_risk_explicit
lemma upper_risk_explicit (c : ClassConstants) (P : SubjectLaw)
    (h : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n)
    (band : ℝ) (hband : 0 < band ∧ band ≤ c.x0 / 2) :
    Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c band a) (armMean P a) ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) +
      explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
      explicitExtinctionRisk c *
        Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) := by
  have hr := upper_risk_with_actual_bias c P h a n hn hband.1 hband.2
  have hb := explicitBiasRisk_general c P h a hband.1 hband.2
  change _ ≤ 2 * _ + explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
    explicitExtinctionRisk c *
      Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) at hr
  linarith only [hr, hb]

noncomputable def bandwidthExponent (c : ClassConstants) : ℝ :=
  if c.kappa ≤ 1 then (2 * c.beta + 2)⁻¹
  else (2 * c.beta + c.kappa + 1)⁻¹

noncomputable def riskExponent (c : ClassConstants) : ℝ :=
  (2 * c.beta + 2) / (2 * c.beta + c.kappa + 1)

noncomputable def varianceRateEnvelope (c : ClassConstants) : ℝ :=
  let hcap := c.x0 / 2
  let a := bandwidthExponent c
  if c.kappa < 1 then 1 else if c.kappa = 1 then
    a + (1 + Real.log (1 / hcap)) / Real.log 3
  else max 1 (hcap ^ (1 - c.kappa) * (3 : ℝ) ^ (riskExponent c - 1))

noncomputable def capReleaseIndex (c : ClassConstants) : ℕ :=
  max 3 (Nat.ceil ((c.x0 / 2) ^ (-(bandwidthExponent c)⁻¹)))

noncomputable def extinctionPreEnvelope (c : ClassConstants) : ℝ :=
  sSup {x : ℝ | ∃ n ∈ Finset.Ico 3 (capReleaseIndex c),
    x = Real.exp (-(extinctionExponent c * n *
      (bandwidth c n) ^ c.kappa)) / riskScale c n}

noncomputable def extinctionTailEnvelope (c : ClassConstants) : ℝ :=
  let N := (capReleaseIndex c : ℝ)
  let δ := 1 - bandwidthExponent c * c.kappa
  let q := if c.kappa > 1 then riskExponent c else 1
  let z := max N ((q / (extinctionExponent c * δ)) ^ (1 / δ))
  if c.kappa = 1 then z * Real.exp (-(extinctionExponent c * z ^ δ)) /
    Real.log 3
  else z ^ q * Real.exp (-(extinctionExponent c * z ^ δ))

noncomputable def honestConstant (c : ClassConstants) (alpha : ℝ) : ℝ :=
  4 * (explicitBiasRisk c + explicitVarianceRisk c * varianceRateEnvelope c +
    explicitExtinctionRisk c *
      max (extinctionPreEnvelope c) (extinctionTailEnvelope c)) / alpha

-- @node: lem:upper-risk
lemma upper_risk (c : ClassConstants) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ (P : SubjectLaw) (_h : ModelClass c P) (a : Arm) (n : ℕ) (h : ℝ),
        3 ≤ n → 0 < h → h ≤ c.x0 / 2 →
        Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c h a) (armMean P a) ≤
          C * (h ^ (2 * c.beta + 2) + (n : ℝ)⁻¹ * varianceFactor c h +
            Real.exp (-(c₀ * n * h ^ c.kappa))) := by
  obtain ⟨B, hB, hBias⟩ := continuation_bias c
  refine ⟨extinctionExponent c,
    |(2 * B ^ 2)| + |explicitVarianceRisk c| +
      |explicitExtinctionRisk c| + 1, ?_, ?_, ?_⟩
  · unfold extinctionExponent
    have hp : 0 < c.pMin := c.pMin_pos
    have hg : 0 < c.gMin := c.gMin_pos
    have he : 0 < Real.exp (-c.dMax) := Real.exp_pos _
    positivity
  · positivity
  · intro P hP a n h hn hh hhcap
    have hactual := upper_risk_with_actual_bias c P hP a n hn hh hhcap
    have hbi := hBias P hP a h hh hhcap
    have hsq : (truncatedMean c P a h - armMean P a) ^ 2 ≤
        B ^ 2 * h ^ (2 * c.beta + 2) := by
      have hp : 0 ≤ B * h ^ (c.beta + 1) :=
        mul_nonneg hB (Real.rpow_nonneg hh.le _)
      have hb := (sq_le_sq₀ (abs_nonneg _) hp).2 hbi
      rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast hh.le] at hb
      simpa only [Nat.cast_ofNat,
        show (c.beta + 1) * (2 : ℝ) = 2 * c.beta + 2 by ring] using hb
    have hrisk : Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c h a) (armMean P a) ≤
        (2 * B ^ 2) * h ^ (2 * c.beta + 2) +
          explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c h +
          explicitExtinctionRisk c *
            Real.exp (-(extinctionExponent c * n * h ^ c.kappa)) := by
      change _ ≤ 2 * _ + explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c h +
        explicitExtinctionRisk c *
          Real.exp (-(extinctionExponent c * n * h ^ c.kappa)) at hactual
      linarith only [hactual, hsq]
    have hx : 0 ≤ h ^ (2 * c.beta + 2) :=
      (Real.rpow_pos_of_pos hh _).le
    have hn' : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hv : 0 ≤ varianceFactor c h := by
      unfold varianceFactor
      split_ifs with hlt heq
      · norm_num
      · have hsmall : h ≤ 1 := by
          have hx0 := c.x0_le
          linarith
        have hrec : 1 ≤ 1 / h := (one_le_div₀ hh).2 hsmall
        have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg hrec
        linarith
      · exact (Real.rpow_pos_of_pos hh _).le
    have hy : 0 ≤ (n : ℝ)⁻¹ * varianceFactor c h := mul_nonneg hn' hv
    have hz : 0 ≤ Real.exp (-(extinctionExponent c * n * h ^ c.kappa)) :=
      (Real.exp_pos _).le
    have hb : (2 * B ^ 2) ≤
        |(2 * B ^ 2)| + |explicitVarianceRisk c| +
          |explicitExtinctionRisk c| + 1 := by
      have := le_abs_self ((2 * B ^ 2))
      linarith [abs_nonneg (explicitVarianceRisk c), abs_nonneg (explicitExtinctionRisk c)]
    have hvar : explicitVarianceRisk c ≤
        |(2 * B ^ 2)| + |explicitVarianceRisk c| +
          |explicitExtinctionRisk c| + 1 := by
      have := le_abs_self (explicitVarianceRisk c)
      linarith [abs_nonneg ((2 * B ^ 2)), abs_nonneg (explicitExtinctionRisk c)]
    have hext : explicitExtinctionRisk c ≤
        |(2 * B ^ 2)| + |explicitVarianceRisk c| +
          |explicitExtinctionRisk c| + 1 := by
      have := le_abs_self (explicitExtinctionRisk c)
      linarith [abs_nonneg ((2 * B ^ 2)), abs_nonneg (explicitVarianceRisk c)]
    calc
      Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c h a) (armMean P a)
          ≤ (2 * B ^ 2) * h ^ (2 * c.beta + 2) +
              explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c h +
              explicitExtinctionRisk c *
                Real.exp (-(extinctionExponent c * n * h ^ c.kappa)) := hrisk
      _ ≤ (|(2 * B ^ 2)| + |explicitVarianceRisk c| +
              |explicitExtinctionRisk c| + 1) *
            (h ^ (2 * c.beta + 2) + (n : ℝ)⁻¹ * varianceFactor c h +
              Real.exp (-(extinctionExponent c * n * h ^ c.kappa))) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hb) hx,
            mul_nonneg (sub_nonneg.mpr hvar) hy,
            mul_nonneg (sub_nonneg.mpr hext) hz]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
