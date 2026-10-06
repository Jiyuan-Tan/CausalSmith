module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ThirdOrderSurvivalEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpContinuationRemainder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly

/-! # Explicit cubic continuation bias and risk

Sharp cubic Taylor remainders and continuation moment matching give the
declared explicit bias constant and close the order-three finite-sample risk.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Sharp cubic Taylor expansion and continuation moment matching
supply the declared explicit bias coefficient. -/
-- @node: explicitBias_orderThree
lemma explicitBias_orderThree (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hthree : holderOrder c = 3)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    |truncatedMean c P a band - armMean P a| ≤
      explicitBiasEnvelope c * band ^ (c.beta + 1) := by
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t
  let v : Fin (3 + 1) → ℝ := fun j =>
    (-1 : ℝ) ^ j.val * iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) 1 /
      (j.val.factorial : ℝ)
  let r : ℝ → ℝ := fun t => f t - ∑ j : Fin (3 + 1), v j * (1 - t) ^ j.val
  have hpoly (t : ℝ) : (∑ j : Fin (3 + 1), v j * (1 - t) ^ j.val) =
      f 1 + derivWithin f (Icc (0 : ℝ) 1) 1 * (t - 1) +
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) 1 * (t - 1) ^ 2 / 2 +
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) 1 * (t - 1) ^ 3 / 6 := by
    simp [v, Fin.sum_univ_succ, iteratedDerivWithin_one]
    ring
  have hf := survival_product_orderThree_holder c P hP hthree a
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := hf.1.continuousOn
  have hr : ContinuousOn r (Icc (0 : ℝ) 1) := by
    simp_rw [r, hpoly]
    exact hc.sub (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_id.sub continuousOn_const))).add
        ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)).div_const 2)).add
          ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 3)).div_const 6))
  have hhalf : band ≤ 1 / 2 := by linarith [c.x0_le]
  have hα := (holderOrder_remainder_exponent c).1
  simp only [hthree, Nat.cast_ofNat] at hα
  have hβ1 : 0 ≤ c.beta - 1 := by linarith
  have hβ2 : 0 ≤ c.beta - 2 := by linarith
  have hC : 0 ≤ productHolderEnvelope c / ((c.beta - 2) * (c.beta - 1) * c.beta) :=
    div_nonneg (productHolderEnvelope_orderThree_nonneg c hthree)
      (mul_nonneg (mul_nonneg hβ2 hβ1) c.beta_pos.le)
  have hrem : ∀ t ∈ Icc (1 - 2 * band) 1,
      |r t| ≤ (productHolderEnvelope c / ((c.beta - 2) * (c.beta - 1) * c.beta)) *
        (1 - t) ^ c.beta := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hs := thirdOrder_remainder_bound f hα hf
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) ht'
    simp only [show c.beta - 3 + 1 = c.beta - 2 by ring,
      show c.beta - 3 + 2 = c.beta - 1 by ring,
      show c.beta - 3 + 3 = c.beta by ring,
      abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] at hs
    simpa only [r, hpoly, sub_add_eq_sub_sub] using hs
  have hsharp := continuationWeight_sharp_remainder_bound 3 hb hhalf c.beta_pos
    hC r hr hrem
  have hi := continuationWeight_remainder_identity 3 v hb hhalf f
    (modelClass_target_intervalIntegrable c P hP a)
    (by simpa only [hthree, f, mul_assoc] using
      modelClass_weightedTarget_intervalIntegrable c P hP a hb hhalf)
  have he : |truncatedMean c P a band - armMean P a| =
      |(∫ t in (0 : ℝ)..(1 - band), continuationWeight 3 band t * r t) -
        ∫ t in (0 : ℝ)..1, r t| := by
    simpa only [truncatedMean, armMean, hthree, f, r, mul_assoc] using congrArg abs hi
  rw [he]
  have hcoef : explicitBiasEnvelope c =
      (productHolderEnvelope c / ((c.beta - 2) * (c.beta - 1) * c.beta)) *
        ((∑ m : Fin (3 + 1),
          |((continuationGram 3)⁻¹.mulVec (continuationRhs 3)) m| * (2 : ℝ) ^ m.val) *
          ((2 : ℝ) ^ (c.beta + 1) - 1) / (c.beta + 1) + 1 / (c.beta + 1)) := by
    simp only [explicitBiasEnvelope, taylorRatio_orderThree c hthree,
      continuationNorm, continuationCoeff]
    rw [hthree]
    ring
  rw [hcoef]
  exact hsharp

/-- Squaring the sharp third-order bias supplies its declared risk term. -/
-- @node: explicitBiasRisk_orderThree
lemma explicitBiasRisk_orderThree (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hthree : holderOrder c = 3)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    2 * (truncatedMean c P a band - armMean P a) ^ 2 ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) := by
  have h := explicitBias_orderThree c P hP a hthree hb hcap
  have hn : 0 ≤ explicitBiasEnvelope c * band ^ (c.beta + 1) :=
    (abs_nonneg _).trans h
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).2 h
  rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast hb.le] at hs
  simp only [Nat.cast_ofNat,
    show (c.beta + 1) * (2 : ℝ) = 2 * c.beta + 2 by ring] at hs
  unfold explicitBiasRisk
  linarith only [hs]

/-- Combining the sharp third-order bias with the verified stochastic risk
closes the full finite-sample explicit envelope at order three. -/
-- @node: upper_risk_explicit_orderThree
lemma upper_risk_explicit_orderThree (c : ClassConstants) (P : SubjectLaw)
    (h : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n)
    (band : ℝ) (hband : 0 < band ∧ band ≤ c.x0 / 2) (hthree : holderOrder c = 3) :
    Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c band a) (armMean P a) ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) +
      explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
      explicitExtinctionRisk c *
        Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) := by
  have hr := upper_risk_with_actual_bias c P h a n hn hband.1 hband.2
  have hb := explicitBiasRisk_orderThree c P h a hthree hband.1 hband.2
  change _ ≤ 2 * _ + explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c band +
    explicitExtinctionRisk c *
      Real.exp (-(extinctionExponent c * n * band ^ c.kappa)) at hr
  linarith only [hr, hb]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
