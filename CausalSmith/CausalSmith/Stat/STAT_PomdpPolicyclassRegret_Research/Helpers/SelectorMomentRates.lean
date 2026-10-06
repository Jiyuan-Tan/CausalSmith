module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockMoments
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorTuning

/-!
# Tuned block moment rates

Evaluate the arbitrary-start moment bounds at the prescribed adaptive depth.
The variance factorization and transient bias estimate implement equation (15)
and the moment part of (16) in the observable-selector roadmap.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Dividing the balanced variance coordinate by the block length gives the square of the
adaptive rate. For [the sample size](hyp:n), [the q](hyp:q), [the β](hyp:β),
[the sample size assumption](hyp:hn), and [the q assumption](hyp:hq), this establishes
[the selector variance rate factorization result](goal). -/
-- @node: selector_variance_rate_factorization
lemma selector_variance_rate_factorization (n : Nat) (q β : ℝ)
    (hn : 0 < n) (hq : 0 < q) :
    ((n : ℝ) * q ^ 2) ^ (1 - β) / n =
      q ^ (2 * (1 - β)) * (n : ℝ) ^ (-β) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.mul_rpow hnR.le (sq_nonneg q), ← Real.rpow_two,
    ← Real.rpow_mul hq.le]
  have hnPower : (n : ℝ) ^ (1 - β) / n = (n : ℝ) ^ (-β) := by
    rw [show 1 - β = -β + 1 by ring, Real.rpow_add hnR, Real.rpow_one]
    field_simp
  calc
    _ = q ^ (2 * (1 - β)) * ((n : ℝ) ^ (1 - β) / n) := by ring
    _ = _ := by rw [hnPower]

/-- The variance term at the uncapped adaptive depth is bounded by the square of the
radius-adaptive rate, using the usable half-block length. For [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the large assumption](hyp:hlarge), and
[the cap assumption](hyp:hcap), this establishes
[the selector adaptive depth variance rate result](goal). -/
-- @node: selector_adaptiveDepth_variance_rate
lemma selector_adaptiveDepth_variance_rate (n : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat)) :
    policyFactor zeta ^ (adaptiveDepth n t0 zeta C + 1) /
      (n - adaptiveDepth n t0 zeta C : Nat) ≤
        2 * policyFactor zeta * overlapRadius C ^ (2 * (1 - rateExponent t0 zeta)) *
          (n : ℝ) ^ (-rateExponent t0 zeta) := by
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    norm_num [this] at hlarge
  have hq0 : 0 ≤ overlapRadius C := by
    unfold overlapRadius
    exact div_nonneg (by linarith) (by linarith)
  have hq : 0 < overlapRadius C := by
    by_contra h
    have : overlapRadius C = 0 := le_antisymm (le_of_not_gt h) hq0
    norm_num [this] at hlarge
  have hN := selector_adaptiveDepth_usable n t0 zeta C hn
  have hNR : (0 : ℝ) < (n - adaptiveDepth n t0 zeta C : Nat) := by
    exact_mod_cast hN.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < policyFactor zeta := Real.exp_pos _
  have hf := (selector_adaptiveDepth_floor_bounds n t0 zeta C ht0 hzeta hlarge hcap).2
  have hv := selector_depth_variance_power_le n (adaptiveDepth n t0 zeta C)
    t0 zeta C hzeta hlarge hf
  rw [selector_tuning_variance_identity t0 zeta ht0 hzeta] at hv
  calc
    _ ≤ (policyFactor zeta * ((n : ℝ) * overlapRadius C ^ 2) ^
        (1 - rateExponent t0 zeta)) / (n - adaptiveDepth n t0 zeta C : Nat) :=
      div_le_div_of_nonneg_right hv hNR.le
    _ ≤ (policyFactor zeta * ((n : ℝ) * overlapRadius C ^ 2) ^
        (1 - rateExponent t0 zeta)) / ((n : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hN.2
    _ = 2 * policyFactor zeta *
        (((n : ℝ) * overlapRadius C ^ 2) ^ (1 - rateExponent t0 zeta) / n) := by ring
    _ = _ := by rw [selector_variance_rate_factorization n _ _ hn hq]; ring

/-- The stationary-start correction is at most a regime constant times n⁻¹, independently of the
radius and depth tuning branch. For [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), and [the sample size assumption](hyp:hn), this
establishes [the selector adaptive depth transient bias bound result](goal). -/
-- @node: selector_adaptiveDepth_transient_bias_le
lemma selector_adaptiveDepth_transient_bias_le (n : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hn : 0 < n) :
    mixingAlpha t0 ^ adaptiveDepth n t0 zeta C /
      ((n - adaptiveDepth n t0 zeta C : Nat) * (1 - mixingAlpha t0)) ≤
        (2 / (1 - mixingAlpha t0)) / n := by
  have hα : 0 ≤ mixingAlpha t0 := (Real.exp_pos _).le
  have hα1 : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (by positivity)
  have hpow : mixingAlpha t0 ^ adaptiveDepth n t0 zeta C ≤ 1 :=
    pow_le_one₀ hα hα1.le
  have hN := selector_adaptiveDepth_usable n t0 zeta C hn
  have hNR : (0 : ℝ) < (n - adaptiveDepth n t0 zeta C : Nat) := by
    exact_mod_cast hN.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ 1 / ((n - adaptiveDepth n t0 zeta C : Nat) * (1 - mixingAlpha t0)) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ 1 / (((n : ℝ) / 2) * (1 - mixingAlpha t0)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hN.2 (by positivity))
    _ = _ := by field_simp

/-- Combine the floor bias rate with the transient correction before applying conditional
Chebyshev and the block median argument. For [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the large assumption](hyp:hlarge), and
[the cap assumption](hyp:hcap), this establishes
[the selector adaptive depth total bias bound result](goal). -/
-- @node: selector_adaptiveDepth_total_bias_le
lemma selector_adaptiveDepth_total_bias_le (n : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat)) :
    mixingAlpha t0 ^ adaptiveDepth n t0 zeta C *
      (overlapRadius C + 1 / ((n - adaptiveDepth n t0 zeta C : Nat) *
        (1 - mixingAlpha t0))) ≤
      (mixingAlpha t0)⁻¹ * overlapRadius C ^ (1 - rateExponent t0 zeta) *
        (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) +
          (2 / (1 - mixingAlpha t0)) / n := by
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    norm_num [this] at hlarge
  have hb := selector_adaptiveDepth_bias_rate n t0 zeta C ht0 hzeta hC hlarge hcap
  have ht := selector_adaptiveDepth_transient_bias_le n t0 zeta C ht0 hn
  calc
    _ = overlapRadius C * mixingAlpha t0 ^ adaptiveDepth n t0 zeta C +
        mixingAlpha t0 ^ adaptiveDepth n t0 zeta C /
          ((n - adaptiveDepth n t0 zeta C : Nat) * (1 - mixingAlpha t0)) := by ring
    _ ≤ _ := add_le_add hb ht

/-- The square of the adaptive standard-deviation coordinate is the variance coordinate; all
powers are real powers on nonnegative bases. For [the sample size](hyp:n), [the q](hyp:q),
[the β](hyp:β), and [the q assumption](hyp:hq), this establishes
[the selector adaptive rate sq result](goal). -/
-- @node: selector_adaptive_rate_sq
lemma selector_adaptive_rate_sq (n : Nat) (q β : ℝ) (hq : 0 ≤ q) :
    (q ^ (1 - β) * (n : ℝ) ^ (-(β / 2))) ^ 2 =
      q ^ (2 * (1 - β)) * (n : ℝ) ^ (-β) := by
  rw [mul_pow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hq,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1 <;> congr 1 <;> ring

/-- Equation (15) for the standard deviation follows from the tuned variance bound, without a
new probabilistic assumption. For [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the large assumption](hyp:hlarge), and
[the cap assumption](hyp:hcap), this establishes
[the selector adaptive depth sd rate result](goal). -/
-- @node: selector_adaptiveDepth_sd_rate
lemma selector_adaptiveDepth_sd_rate (n : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat)) :
    Real.sqrt (policyFactor zeta ^ (adaptiveDepth n t0 zeta C + 1) /
      (n - adaptiveDepth n t0 zeta C : Nat)) ≤
        Real.sqrt (2 * policyFactor zeta) * overlapRadius C ^ (1 - rateExponent t0 zeta) *
          (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) := by
  have hq : 0 ≤ overlapRadius C := by
    unfold overlapRadius
    exact div_nonneg (by linarith) (by linarith)
  have hL : 0 < policyFactor zeta := Real.exp_pos _
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hv := selector_adaptiveDepth_variance_rate n t0 zeta C
      ht0 hzeta hC hlarge hcap
    convert hv using 1
    rw [mul_assoc, mul_pow, Real.sq_sqrt (by positivity),
      selector_adaptive_rate_sq n _ _ hq]
    ring

/-- Arbitrary initial state laws obey the balanced block bias and variance rates. This supplies
the tuned inputs to the conditional median argument. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the sample size assumption](hyp:hn),
[the large assumption](hyp:hlarge), [the cap assumption](hyp:hcap),
[the candidate index](hyp:j), [the initial distribution](hyp:nu), and
[the initial distribution assumption](hyp:hnu), this establishes
[the selector tuned block moments result](goal). -/
-- @node: selector_tuned_block_moments
lemma selector_tuned_block_moments {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hn : 4 ≤ n)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat))
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) :
    |∫ w, phiwRaw (adaptiveDepth n t0 zeta C) m.Mx.b (m.Mx.E j) w
        ∂((segmentLaw m hClass.finite_state nu n).map obsProj) - policyValue m j| ≤
      (mixingAlpha t0)⁻¹ * overlapRadius C ^ (1 - rateExponent t0 zeta) *
        (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) +
          (2 / (1 - mixingAlpha t0)) / n ∧
    ProbabilityTheory.variance
        (phiwRaw (adaptiveDepth n t0 zeta C) m.Mx.b (m.Mx.E j))
        ((segmentLaw m hClass.finite_state nu n).map obsProj) ≤
      (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
        (2 * policyFactor zeta * overlapRadius C ^ (2 * (1 - rateExponent t0 zeta)) *
          (n : ℝ) ^ (-rateExponent t0 zeta)) := by
  have hm := block_phiw_moments t0 zeta C m hClass ht0 hzeta j
    (adaptiveDepth n t0 zeta C) (selector_adaptiveDepth_half n t0 zeta C) hn nu hnu
  have hα1 : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (by positivity)
  have hL1 : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  constructor
  · exact hm.1.trans (selector_adaptiveDepth_total_bias_le n t0 zeta C
      ht0 hzeta hClass.C_ge_one hlarge hcap)
  · calc
      _ ≤ _ := hm.2
      _ = (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
          (policyFactor zeta ^ (adaptiveDepth n t0 zeta C + 1) /
            (n - adaptiveDepth n t0 zeta C : Nat)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (selector_adaptiveDepth_variance_rate n t0 zeta C
          ht0 hzeta hClass.C_ge_one hlarge hcap) (by positivity)

/-- In the low-radius branch q is at most n⁻¹ᐟ². For [the sample size](hyp:n), [the q](hyp:q),
[the sample size assumption](hyp:hn), and [the small assumption](hyp:hsmall), this establishes
[the selector low radius bound sqrt result](goal). -/
-- @node: selector_low_radius_le_sqrt
lemma selector_low_radius_le_sqrt (n : Nat) (q : ℝ) (hn : 0 < n)
    (hsmall : (n : ℝ) * q ^ 2 ≤ 1) :
    q ≤ Real.sqrt (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 / (n : ℝ))
  have hs0 := Real.sqrt_nonneg (1 / (n : ℝ))
  have hq2 : q ^ 2 ≤ 1 / (n : ℝ) := (le_div_iff₀ hnR).mpr (by nlinarith)
  nlinarith

/-- The inverse block length is no larger than its square root. For [the sample size](hyp:n) and
[the sample size assumption](hyp:hn), this establishes
[the selector inv len bound sqrt result](goal). -/
-- @node: selector_inv_len_le_sqrt
lemma selector_inv_len_le_sqrt (n : Nat) (hn : 0 < n) :
    1 / (n : ℝ) ≤ Real.sqrt (1 / (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hx1 : (1 : ℝ) / n ≤ 1 := (div_le_one (by positivity)).mpr hnR
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg (1 / (n : ℝ))
  nlinarith [sq_nonneg (1 / (n : ℝ) - 1)]

/-- Equation (14): zero-depth block bias is O(n⁻¹ᐟ²), and its variance is A₀L/n. The initial law
remains arbitrary. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the sample size assumption](hyp:hn), [the small assumption](hyp:hsmall),
[the candidate index](hyp:j), [the initial distribution](hyp:nu), and
[the initial distribution assumption](hyp:hnu), this establishes
[the selector low radius block moments result](goal). -/
-- @node: selector_low_radius_block_moments
lemma selector_low_radius_block_moments {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hn : 4 ≤ n)
    (hsmall : (n : ℝ) * overlapRadius C ^ 2 ≤ 1)
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) :
    |∫ w, phiwRaw (adaptiveDepth n t0 zeta C) m.Mx.b (m.Mx.E j) w
        ∂((segmentLaw m hClass.finite_state nu n).map obsProj) - policyValue m j| ≤
      (1 + 1 / (1 - mixingAlpha t0)) * Real.sqrt (1 / (n : ℝ)) ∧
    ProbabilityTheory.variance
        (phiwRaw (adaptiveDepth n t0 zeta C) m.Mx.b (m.Mx.E j))
        ((segmentLaw m hClass.finite_state nu n).map obsProj) ≤
      (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
        policyFactor zeta / n := by
  have hk := selector_adaptiveDepth_zero n t0 zeta C hsmall
  rw [hk]
  have hm := block_phiw_moments t0 zeta C m hClass ht0 hzeta j 0 (by omega) hn nu hnu
  simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, pow_one] at hm
  have hα1 : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (by positivity)
  have hqbound := selector_low_radius_le_sqrt n _ (by omega) hsmall
  have htrans := mul_le_mul_of_nonneg_left (selector_inv_len_le_sqrt n (by omega))
    (by positivity : 0 ≤ 1 / (1 - mixingAlpha t0))
  constructor
  · refine hm.1.trans ?_
    calc
      _ = overlapRadius C + (1 / (1 - mixingAlpha t0)) * (1 / (n : ℝ)) := by
        simp only [one_div, mul_inv_rev]
      _ ≤ Real.sqrt (1 / (n : ℝ)) +
          (1 / (1 - mixingAlpha t0)) * Real.sqrt (1 / (n : ℝ)) := add_le_add hqbound htrans
      _ = _ := by ring
  · exact hm.2

end CausalSmith.Stat.PomdpPolicyclassRegret
