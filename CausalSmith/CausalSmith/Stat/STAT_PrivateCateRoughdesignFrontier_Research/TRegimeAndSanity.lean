module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.RateRegimes
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.TMatchedRiskFrontier
/-! Exact public-budget regimes, the unrestricted nonprivate order, and the exact condition
for consistency along budget sequences. -/
public section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- The matched risk frontier transfers the benchmark's exact consistency criterion to risk.  [the theorem's stated inputs and assumptions](hyp:boundedDifferences_of_gate,cayley_of_gate,budgets,he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:efronStein_of_gate). -/
-- @node: private_risk_consistency_iff
lemma private_risk_consistency_iff (efronStein_of_gate : EfronSteinReplacement)
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount)
    (budgets : ℕ → ℝ) (he : ∀ j, 2 ≤ j → 0 < budgets j ∧ budgets j ≤ 1) :
    Tendsto (fun j => privateMinimaxRisk j (budgets j)) atTop (𝓝 0) ↔
      Tendsto (fun j : ℕ => (j : ℝ)*budgets j) atTop atTop := by
  have hfront := fun j hj => matched_risk_frontier efronStein_of_gate
    boundedDifferences_of_gate cayley_of_gate j (budgets j) hj (he j hj)
  rw [← rate_consistency_iff budgets (fun j hj => (he j hj).1)]
  constructor
  · intro hrisk
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop 2] with j hj
      exact ha.trans (rate_pos j (budgets j) (by omega))
    · intro a ha
      have hc : (0 : ℝ) < (2 : ℝ)^(-20 : ℤ) := by positivity
      have hca : 0 < (2 : ℝ)^(-20 : ℤ)*a := mul_pos hc ha
      have hbound := (tendsto_order.1 hrisk).2 _ (ENNReal.ofReal_pos.mpr hca)
      filter_upwards [hbound, eventually_ge_atTop 2] with j hj hj2
      have hlt := lt_of_le_of_lt (hfront j hj2).1 hj
      have hre := (ENNReal.ofReal_lt_ofReal_iff hca).mp hlt
      exact (mul_lt_mul_iff_right₀ hc).mp hre
  · intro hr
    have hu : Tendsto (fun j => ENNReal.ofReal (2^18*rate j (budgets j))) atTop (𝓝 0) := by
      simpa only [mul_zero, ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal (hr.const_mul (2^18 : ℝ))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact Filter.Eventually.of_forall (fun _ => bot_le)
    · filter_upwards [eventually_ge_atTop 2] with j hj
      exact (hfront j hj).2.1

/-- The unit-budget release also attains the sampling upper bound without privacy constraints.  [the theorem's stated inputs and assumptions](hyp:boundedDifferences_of_gate,cayley_of_gate,n,hn), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:efronStein_of_gate). -/
-- @node: nonprivate_sampling_upper
lemma nonprivate_sampling_upper (efronStein_of_gate : EfronSteinReplacement)
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount)
    (n : ℕ) (hn : 2 ≤ n) :
    nonprivateMinimaxRisk n ≤ ENNReal.ofReal (2^18*(n : ℝ)^(-1/4 : ℝ)) := by
  obtain ⟨_, _, hM, _, hR⟩ := matched_risk_frontier efronStein_of_gate
    boundedDifferences_of_gate cayley_of_gate n 1 hn ⟨zero_lt_one, le_rfl⟩
  rw [rate_unit_budget n hn] at hR
  exact (iInf_le_of_le (publicTunedRelease n 1) (iInf_le_of_le hM le_rfl)).trans hR

/-- The explicit sign mixture at one quarter of the sampling radius gives the unrestricted
nonprivate lower bound, through chi-square comparison and Le Cam testing.  [the theorem's stated inputs and assumptions](hyp:boundedDifferences_of_gate,cayley_of_gate,n,hn), and [the asserted conclusion follows](goal). -/
-- @node: nonprivate_sampling_lower
lemma nonprivate_sampling_lower
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount)
    (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ)*(n : ℝ)^(-1/4 : ℝ)) ≤
      nonprivateMinimaxRisk n := by
  obtain ⟨s0, s1, F0, F1, Delta, hs0, hs1, hd, hF0, hF1,
    hrepr, _⟩ := frontier_testing_priors.{0} boundedDifferences_of_gate
      cayley_of_gate n 1 hn ⟨zero_lt_one, le_rfl⟩
  obtain ⟨hL, hhL, hradius, hnull, hsign, _⟩ := hrepr
  have hx : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hr := rate_unit_budget n hn
  have huses : testingUsesSigns n 1 := by
    dsimp [testingUsesSigns]
    refine ⟨by simpa using (show (1 : ℝ) < n from by exact_mod_cast (show 1 < n by omega)), Or.inl ?_⟩
    constructor
    · exact (sparse_le_sampling_iff (n : ℝ) 1 hx zero_lt_one).2
        (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
    · exact (dense_le_sampling_iff (n : ℝ) 1 hx zero_lt_one).2
        (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
  obtain ⟨_, hmix⟩ := hsign huses
  have hnullmix : finiteProductMixture n s0 F0 = dataLaw n fairNull := by
    ext E hE
    simp only [finiteProductMixture, Measure.smul_apply, smul_eq_mul,
      Measure.finsetSum_apply, hnull, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel
      (by exact_mod_cast hs0.ne') (by simp), one_mul]
  obtain ⟨_, _, _, _, _, hchi, hac, hint⟩ :=
    positive_family_certificate hL hhL boundedDifferences_of_gate n
  have hrad : hL = (n : ℝ)^(-1/4 : ℝ) / 4 := by simpa [hr] using hradius
  have hpow : (n : ℝ)^2 * ((n : ℝ)^(-1/4 : ℝ))^8 = 1 := by
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
    exact mul_inv_cancel₀ (pow_ne_zero _ hx.ne')
  have hexponent : 160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL =
      160 * (2 : ℝ)^(-40 : ℤ) := by
    rw [hrad]
    dsimp [separation, kappa, deltaL]
    norm_num
    nlinarith [hpow]
  have hexp : Real.exp (160 * (2 : ℝ)^(-40 : ℤ)) - 1 ≤ 1/4 := by
    have h := exp_privacy_increment_le (160 * (2 : ℝ)^(-40 : ℤ))
      ⟨by norm_num, by norm_num⟩
    norm_num at h ⊢
    linarith
  let : IsProbabilityMeasure (finiteProductMixture n s0 F0) :=
    finiteProductMixture_probability n s0 F0 hs0
  let : IsProbabilityMeasure (finiteProductMixture n s1 F1) :=
    finiteProductMixture_probability n s1 F1 hs1
  have hprob0 : IsProbabilityMeasure (dataLaw n fairNull) := hnullmix ▸ inferInstance
  have hprob1 : IsProbabilityMeasure (signMixture hL hhL n) := hmix ▸ inferInstance
  let : IsProbabilityMeasure (dataLaw n fairNull) := hprob0
  let : IsProbabilityMeasure (signMixture hL hhL n) := hprob1
  have hdata : TV (finiteProductMixture n s0 F0) (finiteProductMixture n s1 F1) ≤ 1/4 := by
    rw [hnullmix, hmix]
    change Causalean.Stat.tvDist _ _ ≤ _
    rw [Causalean.Stat.tvDist_symm]
    have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
      (signMixture hL hhL n) (dataLaw n fairNull) hac hint
    have hb : Causalean.Stat.chiSqDiv (signMixture hL hhL n)
        (dataLaw n fairNull) ≤ 1/4 := by
      rw [hexponent] at hchi
      exact hchi.trans hexp
    have hsqrt : Real.sqrt (Causalean.Stat.chiSqDiv
        (signMixture hL hhL n) (dataLaw n fairNull)) ≤ 1/2 :=
      (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hb]⟩
    linarith
  have hrpos : 0 < rate n 1 := rate_pos n 1 (by omega)
  unfold nonprivateMinimaxRisk
  refine le_iInf fun M => le_iInf fun hM => ?_
  let : IsMarkovKernel M := hM
  have htest := finite_priors_scalar_lower n s0 s1 F0 F1 hs0 hs1 M Delta
    (le_trans (by positivity) hd) hF0 hF1
    ((kernel_TV_contraction M _ _).trans hdata)
  apply (ENNReal.ofReal_le_ofReal ?_).trans htest
  rw [hr] at hd
  have hc : (2 : ℝ)^(-20 : ℤ) ≤ (3/16) * (2 : ℝ)^(-14 : ℤ) := by norm_num
  have ha : 0 ≤ (n : ℝ)^(-1/4 : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc ha]

/-- Given the [Efron--Stein gate](hyp:efronStein_of_gate),
[bounded-differences gate](hyp:boundedDifferences_of_gate), and
[Cayley gate](hyp:cayley_of_gate), the unrestricted minimax risk at every
[sample size](hyp:n) [at least two](hyp:hn) [lies between the explicit constants
`2⁻²⁰` and `2¹⁸` times the fourth-root rate](goal). -/
-- keep: separate unrestricted two-sided minimax benchmark required by the resolved R1 scope
lemma nonprivate_sampling_bounds (efronStein_of_gate : EfronSteinReplacement)
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount)
    (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ)*(n : ℝ)^(-1/4 : ℝ)) ≤ nonprivateMinimaxRisk n ∧
      nonprivateMinimaxRisk n ≤ ENNReal.ofReal (2^18*(n : ℝ)^(-1/4 : ℝ)) := by
  exact ⟨nonprivate_sampling_lower boundedDifferences_of_gate cayley_of_gate n hn,
    nonprivate_sampling_upper efronStein_of_gate boundedDifferences_of_gate cayley_of_gate n hn⟩

/-- [The benchmark has four exact regimes, its unit-budget scale is exactly the nonprivate
fourth-root order, and private minimax consistency holds exactly when sample size times the
privacy budget diverges.](goal)
The [Efron--Stein gate](hyp:efronStein_of_gate),
[bounded-differences gate](hyp:boundedDifferences_of_gate), and
[Cayley gate](hyp:cayley_of_gate) specify the conditional scope. -/
-- @node: prop:regime-and-sanity
theorem regime_and_sanity (efronStein_of_gate : EfronSteinReplacement)
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount) :
    (∀ (n : ℕ) (epsilon : ℝ), 2 ≤ n → 0 < epsilon ∧ epsilon ≤ 1 →
    (((n : ℝ)^(-1/4 : ℝ) ≤ epsilon) → rate n epsilon = (n : ℝ)^(-1/4 : ℝ)) ∧
    (((n : ℝ)^(-3/5 : ℝ) ≤ epsilon ∧ epsilon ≤ (n : ℝ)^(-1/4 : ℝ)) →
      rate n epsilon = ((n : ℝ)^2*epsilon)^(-1/7 : ℝ)) ∧
    (((n : ℝ)^(-1 : ℤ) ≤ epsilon ∧ epsilon ≤ (n : ℝ)^(-3/5 : ℝ)) →
      rate n epsilon = ((n : ℝ)*epsilon)^(-1/2 : ℝ)) ∧
    (epsilon ≤ (n : ℝ)^(-1 : ℤ) → rate n epsilon = 1) ∧
    rate n 1 = (n : ℝ)^(-1/4 : ℝ)) ∧
    (∀ budgets : ℕ → ℝ, (∀ j, 2 ≤ j → 0 < budgets j ∧ budgets j ≤ 1) →
      (Tendsto (fun j => privateMinimaxRisk j (budgets j)) atTop (𝓝 0) ↔
        Tendsto (fun j : ℕ => (j : ℝ)*budgets j) atTop atTop)) := by
  constructor
  · intro n epsilon hn he
    exact ⟨rate_sampling_regime n epsilon hn he.1,
      rate_sparse_regime n epsilon hn he.1,
      rate_dense_regime n epsilon hn he.1,
      rate_capped_regime n epsilon hn he.1,
      rate_unit_budget n hn⟩
  · intro budgets he
    exact private_risk_consistency_iff efronStein_of_gate boundedDifferences_of_gate
      cayley_of_gate budgets he
end CausalSmith.Stat.PrivateCateRoughdesign
