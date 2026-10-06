module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.GeneralSurvivalEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpContinuationRemainder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly

/-! # Sharp continuation bias at arbitrary Holder order

Within-interval Taylor coefficients and moment cancellation give the exact
explicit bias envelope, uniformly over all positive smoothness indices.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Within-Taylor evaluation at the horizon has the endpoint monomial form
needed for continuation moment cancellation. -/
-- @node: taylorWithinEval_one_eq_endpoint_sum
lemma taylorWithinEval_one_eq_endpoint_sum (k : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    taylorWithinEval f k (Icc (0 : ℝ) 1) 1 t =
      ∑ j : Fin (k + 1),
        ((-1 : ℝ) ^ j.val * iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) 1 /
          (j.val.factorial : ℝ)) * (1 - t) ^ j.val := by
  rw [taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  rw [show t - 1 = (-1 : ℝ) * (1 - t) by ring, mul_pow]
  ring

/-- Sharp arbitrary-order Taylor expansion and continuation moment matching
supply the declared explicit bias coefficient for unrestricted beta. -/
-- @node: explicitBias_general
lemma explicitBias_general (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    |truncatedMean c P a band - armMean P a| ≤
      explicitBiasEnvelope c * band ^ (c.beta + 1) := by
  let k := holderOrder c
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t
  let v : Fin (k + 1) → ℝ := fun j =>
    (-1 : ℝ) ^ j.val * iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) 1 /
      (j.val.factorial : ℝ)
  let r : ℝ → ℝ := fun t => f t - ∑ j : Fin (k + 1), v j * (1 - t) ^ j.val
  have hpoly (t : ℝ) : (∑ j : Fin (k + 1), v j * (1 - t) ^ j.val) =
      taylorWithinEval f k (Icc (0 : ℝ) 1) 1 t :=
    (taylorWithinEval_one_eq_endpoint_sum k f t).symm
  have hf := survival_product_holder c P hP a
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := hf.1.continuousOn
  have hr : ContinuousOn r (Icc (0 : ℝ) 1) := by
    apply hc.sub
    have hp : Continuous (fun t : ℝ => ∑ j : Fin (k + 1), v j * (1 - t) ^ j.val) := by
      fun_prop
    exact hp.continuousOn
  have hhalf : band ≤ 1 / 2 := by linarith [c.x0_le]
  have hα := holderOrder_remainder_exponent c
  have hC : 0 ≤ taylorRatio c * productHolderEnvelope c := by
    rw [taylorRatio_eq_sharpTaylorRatio]
    apply mul_nonneg _ (productHolderEnvelope_nonneg c)
    unfold sharpTaylorRatio
    apply div_nonneg
    · exact (Real.Gamma_pos_of_pos (by linarith [hα.1])).le
    · exact (Real.Gamma_pos_of_pos (by linarith [hα.1])).le
  have hrem : ∀ t ∈ Icc (1 - 2 * band) 1,
      |r t| ≤ (taylorRatio c * productHolderEnvelope c) * (1 - t) ^ c.beta := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hs := sharp_holder_taylor_endpoint_remainder k f hα.1 hα.2
      (productHolderEnvelope_nonneg c) hf ht'
    simpa only [r, hpoly, taylorRatio_eq_sharpTaylorRatio, k,
      show (holderOrder c : ℝ) + (c.beta - holderOrder c) = c.beta by ring] using hs
  have hsharp := continuationWeight_sharp_remainder_bound k hb hhalf c.beta_pos
    hC r hr hrem
  have hi := continuationWeight_remainder_identity k v hb hhalf f
    (modelClass_target_intervalIntegrable c P hP a)
    (by simpa only [k, f, mul_assoc] using
      modelClass_weightedTarget_intervalIntegrable c P hP a hb hhalf)
  have he : |truncatedMean c P a band - armMean P a| =
      |(∫ t in (0 : ℝ)..(1 - band), continuationWeight k band t * r t) -
        ∫ t in (0 : ℝ)..1, r t| := by
    simpa only [truncatedMean, armMean, k, f, r, mul_assoc] using congrArg abs hi
  rw [he]
  simpa only [explicitBiasEnvelope, continuationNorm, continuationCoeff, k] using hsharp

/-- Squaring the sharp uniform bias gives its exact declared risk term. -/
-- @node: explicitBiasRisk_general
lemma explicitBiasRisk_general (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    {band : ℝ} (hb : 0 < band) (hcap : band ≤ c.x0 / 2) :
    2 * (truncatedMean c P a band - armMean P a) ^ 2 ≤
      explicitBiasRisk c * band ^ (2 * c.beta + 2) := by
  have h := explicitBias_general c P hP a hb hcap
  have hn : 0 ≤ explicitBiasEnvelope c * band ^ (c.beta + 1) :=
    (abs_nonneg _).trans h
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).2 h
  rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast hb.le] at hs
  simp only [Nat.cast_ofNat,
    show (c.beta + 1) * (2 : ℝ) = 2 * c.beta + 2 by ring] at hs
  unfold explicitBiasRisk
  linarith only [hs]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
