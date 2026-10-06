module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorMomentRates

/-!
# Arbitrary-start block deviation bounds

The bias and variance envelopes imply the one-block Chebyshev bound in
(10) of the observable-selector roadmap. The starting-state distribution
remains arbitrary, as required for later chronological conditioning.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- A bias envelope shifts the usual centered Chebyshev threshold. For
[the sample space](hyp:Ω), [the measure](hyp:μ), [the event family](hyp:F),
[the parameter](hyp:θ), [the behavior policy](hyp:b), [the codeword index](hyp:v),
[the observed state](hyp:x), [the event family assumption](hyp:hF),
[the observed state assumption](hyp:hx), [the behavior policy assumption](hyp:hb), and
[the codeword index assumption](hyp:hv), this establishes
[the selector bias variance tail result](goal). -/
-- @node: selector_bias_variance_tail
lemma selector_bias_variance_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (θ b v x : ℝ)
    (hF : MemLp F 2 μ) (hx : 0 < x)
    (hb : |(∫ w, F w ∂μ) - θ| ≤ b) (hv : variance F μ ≤ v) :
    μ {w | b + x < |F w - θ|} ≤ ENNReal.ofReal (v / x ^ 2) := by
  have hsub : {w | b + x < |F w - θ|} ⊆
      {w | x ≤ |F w - ∫ z, F z ∂μ|} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    have htriangle : |F w - θ| ≤
        |F w - ∫ z, F z ∂μ| + |(∫ z, F z ∂μ) - θ| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (F w - ∫ z, F z ∂μ) ((∫ z, F z ∂μ) - θ)
    linarith
  calc
    _ ≤ μ {w | x ≤ |F w - ∫ z, F z ∂μ|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance F μ / x ^ 2) := meas_ge_le_variance_div_sq hF hx
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hv (sq_nonneg x))

/-- Equation (10) for every starting-state distribution, without independence between rewards
and successor states or between adjacent blocks. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the candidate index](hyp:j),
[the history length](hyp:k), [the history length assumption](hyp:hk),
[the sample size assumption](hyp:hn), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the observed state](hyp:x), and
[the observed state assumption](hyp:hx), this establishes
[the selector block chebyshev result](goal). -/
-- @node: selector_block_chebyshev
lemma selector_block_chebyshev {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (j : Fin M)
    (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (x : ℝ) (hx : 0 < x) :
    ((segmentLaw m hClass.finite_state nu n).map obsProj)
      {w | mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j) w - policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) := by
  let : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  have hm := block_phiw_moments t0 zeta C m hClass ht0 hzeta j k hk hn nu hnu
  exact selector_bias_variance_tail _ _ _ _ _ x
    (phiwRaw_observedSegment_memLp t0 zeta C m hClass j nu hnu k 2) hx hm.1 hm.2

/-- The real-valued version of the biased tail bound can be used in finite union bounds and in
expectation estimates. For [the sample space](hyp:Ω), [the measure](hyp:μ),
[the event family](hyp:F), [the parameter](hyp:θ), [the behavior policy](hyp:b),
[the codeword index](hyp:v), [the observed state](hyp:x), [the event family assumption](hyp:hF),
[the observed state assumption](hyp:hx), [the behavior policy assumption](hyp:hb), and
[the codeword index assumption](hyp:hv), this establishes
[the selector bias variance tail real result](goal). -/
-- @node: selector_bias_variance_tail_real
lemma selector_bias_variance_tail_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (θ b v x : ℝ)
    (hF : MemLp F 2 μ) (hx : 0 < x)
    (hb : |(∫ w, F w ∂μ) - θ| ≤ b) (hv : variance F μ ≤ v) :
    (μ {w | b + x < |F w - θ|}).toReal ≤ v / x ^ 2 := by
  have hv0 : 0 ≤ v := (variance_nonneg F μ).trans hv
  have ht := selector_bias_variance_tail μ F θ b v x hF hx hb hv
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  simpa only [ENNReal.toReal_ofReal (div_nonneg hv0 (sq_nonneg x))] using hr

/-- At twice the standard-deviation envelope, a block is bad with probability at most one
quarter. This is the uniform one-block input to the median argument. For
[the sample space](hyp:Ω), [the measure](hyp:μ), [the event family](hyp:F),
[the parameter](hyp:θ), [the behavior policy](hyp:b), [the codeword index](hyp:v),
[the event family assumption](hyp:hF), [the v0 assumption](hyp:hv0),
[the behavior policy assumption](hyp:hb), and [the codeword index assumption](hyp:hv), this
establishes [the selector bias variance tail quarter result](goal). -/
-- @node: selector_bias_variance_tail_quarter
lemma selector_bias_variance_tail_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (θ b v : ℝ)
    (hF : MemLp F 2 μ) (hv0 : 0 < v)
    (hb : |(∫ w, F w ∂μ) - θ| ≤ b) (hv : variance F μ ≤ v) :
    μ {w | b + 2 * Real.sqrt v < |F w - θ|} ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have ht := selector_bias_variance_tail μ F θ b v (2 * Real.sqrt v)
    hF (by positivity) hb hv
  have heq : v / (2 * Real.sqrt v) ^ 2 = (1 / 4 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hv0.le]
    field_simp
    ring
  simpa only [heq] using ht

/-- In the low-radius branch the arbitrary-start tail has the n⁻¹ᐟ² bias threshold and the A₀L/n
variance envelope from equation (14). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the sample size assumption](hyp:hn),
[the small assumption](hyp:hsmall), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector low radius block tail result](goal). -/
-- @node: selector_low_radius_block_tail
lemma selector_low_radius_block_tail {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hn : 4 ≤ n)
    (hsmall : (n : ℝ) * overlapRadius C ^ 2 ≤ 1)
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (x : ℝ) (hx : 0 < x) :
    ((segmentLaw m hClass.finite_state nu n).map obsProj)
      {w | (1 + 1 / (1 - mixingAlpha t0)) * Real.sqrt (1 / (n : ℝ)) + x <
        |phiwRaw (adaptiveDepth n t0 zeta C) m.Mx.b (m.Mx.E j) w -
          policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta / n) / x ^ 2) := by
  let : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  have hm := selector_low_radius_block_moments t0 zeta C m hClass
    ht0 hzeta hn hsmall j nu hnu
  exact selector_bias_variance_tail _ _ _ _ _ x
    (phiwRaw_observedSegment_memLp t0 zeta C m hClass j nu hnu
      (adaptiveDepth n t0 zeta C) 2) hx hm.1 hm.2

/-- In the balanced branch the arbitrary-start tail uses the bias and variance rates from
equations (15)–(16). For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the sample size assumption](hyp:hn), [the large assumption](hyp:hlarge),
[the cap assumption](hyp:hcap), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector tuned block tail result](goal). -/
-- @node: selector_tuned_block_tail
lemma selector_tuned_block_tail {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hn : 4 ≤ n)
    (hlarge : 1 < (n : ℝ) * overlapRadius C ^ 2)
    (hcap : Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)) ≤
        (n / 2 : Nat))
    (j : Fin M) (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (x : ℝ) (hx : 0 < x) :
    ((segmentLaw m hClass.finite_state nu n).map obsProj)
      {w | (mixingAlpha t0)⁻¹ * overlapRadius C ^ (1 - rateExponent t0 zeta) *
        (n : ℝ) ^ (-(rateExponent t0 zeta / 2)) +
          (2 / (1 - mixingAlpha t0)) / n + x <
            |phiwRaw (adaptiveDepth n t0 zeta C) m.Mx.b (m.Mx.E j) w -
              policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * (2 * policyFactor zeta *
          overlapRadius C ^ (2 * (1 - rateExponent t0 zeta)) *
            (n : ℝ) ^ (-rateExponent t0 zeta))) / x ^ 2) := by
  let : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  have hm := selector_tuned_block_moments t0 zeta C m hClass
    ht0 hzeta hn hlarge hcap j nu hnu
  exact selector_bias_variance_tail _ _ _ _ _ x
    (phiwRaw_observedSegment_memLp t0 zeta C m hClass j nu hnu
      (adaptiveDepth n t0 zeta C) 2) hx hm.1 hm.2

/-- Every legal arbitrary-start block has bad probability at most one quarter at the bias plus
twice its standard-deviation envelope. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the candidate index](hyp:j),
[the history length](hyp:k), [the history length assumption](hyp:hk),
[the sample size assumption](hyp:hn), [the initial distribution](hyp:nu), and
[the initial distribution assumption](hyp:hnu), this establishes
[the selector block tail quarter result](goal). -/
-- @node: selector_block_tail_quarter
lemma selector_block_tail_quarter {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (j : Fin M)
    (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) :
    ((segmentLaw m hClass.finite_state nu n).map obsProj)
      {w | mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) +
          2 * Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
            4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
              (n - k : Nat)) < |phiwRaw k m.Mx.b (m.Mx.E j) w - policyValue m j|} ≤
      ENNReal.ofReal (1 / 4 : ℝ) := by
  let : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  have hα1 : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (by positivity)
  have hL1 : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hN : (0 : ℝ) < (n - k : Nat) := by
    exact_mod_cast (show 0 < n - k by omega)
  have hv0 : 0 < (1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
        (n - k : Nat) := by
    have hL : 0 < policyFactor zeta := Real.exp_pos _
    positivity
  have hm := block_phiw_moments t0 zeta C m hClass ht0 hzeta j k hk hn nu hnu
  exact selector_bias_variance_tail_quarter _ _ _ _ _
    (phiwRaw_observedSegment_memLp t0 zeta C m hClass j nu hnu k 2) hv0 hm.1 hm.2

end CausalSmith.Stat.PomdpPolicyclassRegret
