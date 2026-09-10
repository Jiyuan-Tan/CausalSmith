import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseMomentMatchingLower
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Numerical exponential-tail estimates for the dense moment-matching lower bound. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open Filter MeasureTheory
open scoped BigOperators ProbabilityTheory

-- @node: denseLikelihoodTail_le_geometric
/-- The factorial tail at the calibrated dense intensity is dominated by the
geometric series with ratio `exp(1) / 64` used in the paper. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseLikelihoodTail_le_geometric (n d : ℕ) (hregime : DenseRegime n d) :
    denseLikelihoodTail n d ≤
      (Real.exp 1 / 64) ^ (lowerDegree d + 1) /
        (1 - Real.exp 1 / 64) := by
  rw [denseLikelihoodTail_eq_exponentialSeriesTail,
    poissonCellIntensity_mul_denseAmplitude_sq n d hregime]
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
  let q : ℝ := Real.exp 1 / 64
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    linarith [Real.exp_one_lt_three]
  have hterm : ∀ r : ℕ, lowerDegree d < r →
      ((lowerDegree d : ℝ) / 64) ^ r / (r.factorial : ℝ) ≤ q ^ r := by
    intro r hr
    have hrpos : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hr
    have hKr : (lowerDegree d : ℝ) ≤ r := by exact_mod_cast (Nat.le_of_lt hr)
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * r) := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have harg : (1 : ℝ) ≤ 2 * Real.pi * r := by
        calc
          (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
          _ ≤ 2 * Real.pi * r := by
            gcongr
            exact_mod_cast hrpos
      exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using harg)
    have hfac := Stirling.le_factorial_stirling r
    have hbase : 0 ≤ (r : ℝ) / Real.exp 1 := by positivity
    have hpow : ((lowerDegree d : ℝ) / Real.exp 1) ^ r ≤
        ((r : ℝ) / Real.exp 1) ^ r := by
      gcongr
    have hfac' : ((lowerDegree d : ℝ) / Real.exp 1) ^ r ≤
        (r.factorial : ℝ) := by
      calc
        _ ≤ ((r : ℝ) / Real.exp 1) ^ r := hpow
        _ ≤ Real.sqrt (2 * Real.pi * r) * ((r : ℝ) / Real.exp 1) ^ r := by
          exact le_mul_of_one_le_left (pow_nonneg hbase r) hsqrt
        _ ≤ (r.factorial : ℝ) := hfac
    have hfacpos : (0 : ℝ) < r.factorial := by positivity
    rw [div_le_iff₀ hfacpos]
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    rw [show (lowerDegree d : ℝ) / 64 =
        q * ((lowerDegree d : ℝ) / Real.exp 1) by
      dsimp [q]
      field_simp]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hfac' (pow_nonneg hq0 r)
  have hg : Summable (fun r : ℕ => q ^ r) :=
    summable_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0])
  have hgTail : Summable (fun r : ℕ => if lowerDegree d < r then q ^ r else 0) :=
    Summable.of_nonneg_of_le (f := fun r : ℕ => q ^ r)
      (fun r => by positivity)
      (fun r => by
        by_cases hr : lowerDegree d < r
        · simp [hr]
        · simp [hr, pow_nonneg hq0]) hg
  have hleft : Summable (fun r : ℕ => if lowerDegree d < r then
      ((lowerDegree d : ℝ) / 64) ^ r / (r.factorial : ℝ) else 0) := by
    exact Summable.of_nonneg_of_le
      (f := fun r : ℕ => if lowerDegree d < r then q ^ r else 0)
      (g := fun r : ℕ => if lowerDegree d < r then
        ((lowerDegree d : ℝ) / 64) ^ r / (r.factorial : ℝ) else 0)
      (fun r => by positivity)
      (fun r => by
        by_cases hr : lowerDegree d < r
        · simp only [hr, if_true]
          exact hterm r hr
        · simp [hr]) hgTail
  calc
    (∑' r : ℕ, if lowerDegree d < r then
        ((lowerDegree d : ℝ) / 64) ^ r / (r.factorial : ℝ) else 0) ≤
        ∑' r : ℕ, if lowerDegree d < r then q ^ r else 0 := by
      apply hleft.tsum_le_tsum
      · intro r
        by_cases hr : lowerDegree d < r
        · simp only [hr, if_true]
          exact hterm r hr
        · simp [hr]
      · exact hgTail
    _ = q ^ (lowerDegree d + 1) / (1 - q) := by
      let f : ℕ → ℝ := fun r => if lowerDegree d < r then q ^ r else 0
      have hsplit := hgTail.sum_add_tsum_nat_add (lowerDegree d + 1)
      have hzero : ∑ r ∈ Finset.range (lowerDegree d + 1), f r = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        simp only [f]
        rw [if_neg]
        have hr' := Finset.mem_range.1 hr
        omega
      have hshift : (∑' r : ℕ, f (r + (lowerDegree d + 1))) =
          q ^ (lowerDegree d + 1) * (1 - q)⁻¹ := by
        simp only [f, show ∀ r : ℕ, lowerDegree d < r + (lowerDegree d + 1) by omega,
          if_true, pow_add]
        rw [tsum_mul_right, tsum_geometric_of_norm_lt_one]
        · ring
        · simpa [Real.norm_eq_abs, abs_of_nonneg hq0]
      change (∑' r : ℕ, f r) = _
      rw [← hsplit, hzero, zero_add, hshift]
      rw [div_eq_mul_inv]
    _ = _ := rfl

-- @node: eventually_denseGeometric_tv_le
/-- The geometric likelihood-tail envelope is uniformly small after a
universal alphabet cutoff. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma eventually_denseGeometric_tv_le :
    ∃ D0 : ℕ, ∀ d : ℕ, D0 ≤ d →
      (d : ℝ) * Real.sqrt
        ((Real.exp 1 / 64) ^ (lowerDegree d + 1) /
          (1 - Real.exp 1 / 64)) ≤ 1 / 16 := by
  refine ⟨2, ?_⟩
  intro d hd
  let q : ℝ := Real.exp 1 / 64
  have hdNat : 2 ≤ d := hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hdNat
  have hed : 0 < Real.exp 1 * (d : ℝ) := mul_pos (Real.exp_pos 1) (by positivity)
  have hq0 : 0 ≤ q := by positivity
  have hqexp : q ≤ Real.exp (-2) := by
    rw [show Real.exp (-2) = (Real.exp 1)⁻¹ ^ 2 by
      calc
        Real.exp (-2) = Real.exp (-1 + -1) := by norm_num
        _ = Real.exp (-1) * Real.exp (-1) := Real.exp_add _ _
        _ = (Real.exp 1)⁻¹ ^ 2 := by rw [Real.exp_neg]; ring]
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    rw [inv_pow, inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < (Real.exp 1) ^ 2)).2
    dsimp [q]
    field_simp
    nlinarith [sq_pos_of_pos hepos]
  have hK : (8 * logAlphabet d : ℝ) ≤ lowerDegree d :=
    (lowerDegree_log_bounds d).1
  have hlogpos : 0 < logAlphabet d := by
    unfold logAlphabet
    have hegt : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact Real.log_pos (by nlinarith [Real.exp_pos 1])
  have hpow : q ^ (lowerDegree d + 1) ≤
      Real.exp (-2) ^ (lowerDegree d + 1) := by
    gcongr
  have hexpK : Real.exp (-2) ^ (lowerDegree d + 1) ≤
      Real.exp (-16 * logAlphabet d) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hrewrite : Real.exp (-16 * logAlphabet d) =
      (Real.exp 1 * (d : ℝ))⁻¹ ^ 16 := by
    rw [show -16 * logAlphabet d = (16 : ℕ) * (-logAlphabet d) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_neg, logAlphabet, Real.exp_log hed]
  have hsmall : (Real.exp 1 * (d : ℝ))⁻¹ ^ 16 ≤
      1 / (512 * (d : ℝ) ^ 2) := by
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hbase : 2 ≤ Real.exp 1 * (d : ℝ) := by nlinarith [Real.exp_pos 1]
    have hpos : 0 < Real.exp 1 * (d : ℝ) := hed
    rw [inv_pow]
    rw [inv_eq_one_div]
    have hd2 : (0 : ℝ) ≤ d := by positivity
    have hbasepow : (2 : ℝ) ^ 10 ≤ (Real.exp 1 * (d : ℝ)) ^ 10 := by gcongr
    have hdPow : (d : ℝ) ^ 2 ≤ (Real.exp 1 * (d : ℝ)) ^ 2 := by
      have hde : (d : ℝ) ≤ Real.exp 1 * d := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hd2
      exact pow_le_pow_left₀ hd2 hde 2
    apply one_div_le_one_div_of_le (by positivity : 0 < 512 * (d : ℝ) ^ 2)
    calc
      512 * (d : ℝ) ^ 2 ≤ 2 ^ 10 * (d : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (d : ℝ)]
      _ ≤ (Real.exp 1 * (d : ℝ)) ^ 10 *
          (Real.exp 1 * (d : ℝ)) ^ 2 := by gcongr
      _ ≤ (Real.exp 1 * (d : ℝ)) ^ 16 := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by linarith [hbase]) (by norm_num : 12 ≤ 16)
  have hqpow : q ^ (lowerDegree d + 1) ≤
      1 / (512 * (d : ℝ) ^ 2) := by
    calc
      _ ≤ Real.exp (-2) ^ (lowerDegree d + 1) := hpow
      _ ≤ Real.exp (-16 * logAlphabet d) := hexpK
      _ = (Real.exp 1 * (d : ℝ))⁻¹ ^ 16 := hrewrite
      _ ≤ _ := hsmall
  have hden : (1 / 2 : ℝ) ≤ 1 - q := by
    dsimp [q]
    nlinarith [Real.exp_one_lt_three]
  have hfrac : q ^ (lowerDegree d + 1) / (1 - q) ≤
      1 / (256 * (d : ℝ) ^ 2) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - q)).2
    calc
      q ^ (lowerDegree d + 1) ≤ 1 / (512 * (d : ℝ) ^ 2) := hqpow
      _ ≤ 1 / (256 * (d : ℝ) ^ 2) * (1 - q) := by
        have hdpos : (0 : ℝ) < d := by positivity
        apply (div_le_iff₀ (by positivity : 0 < 512 * (d : ℝ) ^ 2)).2
        field_simp
        nlinarith
  have hsqrt : Real.sqrt (q ^ (lowerDegree d + 1) / (1 - q)) ≤
      1 / (16 * d) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / (16 * (d : ℝ)))]
    apply Real.sqrt_le_sqrt
    convert hfrac using 1 <;> field_simp <;> ring
  dsimp [q] at hsqrt ⊢
  have hdpos : (0 : ℝ) < d := by positivity
  calc
    (d : ℝ) * Real.sqrt
        ((Real.exp 1 / 64) ^ (lowerDegree d + 1) /
          (1 - Real.exp 1 / 64)) ≤ d * (1 / (16 * d)) := by gcongr
    _ = 1 / 16 := by field_simp

-- @node: eventually_densePoissonTail_absorbed
/-- In the dense regime the mean-`2n` Poisson lower tail is eventually
absorbed by any fixed positive multiple of the target dense rate. This uses [the stated c condition holds](hyp:hc). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma eventually_densePoissonTail_absorbed (c : ℝ) (hc : 0 < c) :
    ∃ D0 : ℕ, ∀ d n : ℕ, D0 ≤ d → d ^ 2 < n →
      (ProbabilityTheory.poissonMeasure (Real.toNNReal (2 * n))
          {k | k < n}).toReal ≤ c * d / (n * logAlphabet d) := by
  have hlogLittle : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x) :=
    Real.isLittleO_log_id_atTop
  have hlogBound : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (c / 3) * x := by
    have hb := hlogLittle.bound (div_pos hc (by norm_num : (0 : ℝ) < 3))
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (by positivity : 0 ≤ x)] using hx
  have ht : Tendsto (fun d : ℕ => Real.exp 1 * (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1)
  have hlogNat : ∀ᶠ d : ℕ in atTop, logAlphabet d ≤ c * d := by
    filter_upwards [hlogBound.filter_mono ht] with d hd
    unfold logAlphabet
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hd0 : (0 : ℝ) ≤ d := by positivity
    calc
      Real.log (Real.exp 1 * (d : ℝ)) ≤
          (c / 3) * (Real.exp 1 * d) := hd
      _ ≤ c * d := by
        have := mul_le_mul_of_nonneg_right he.le hd0
        nlinarith
  rw [eventually_atTop] at hlogNat
  obtain ⟨Dlog, hDlog⟩ := hlogNat
  refine ⟨max 20 Dlog, ?_⟩
  intro d n hd hn
  have hd20 : 20 ≤ d := le_trans (Nat.le_max_left _ _) hd
  have hdlog : Dlog ≤ d := le_trans (Nat.le_max_right _ _) hd
  have hdSq : 20 ^ 2 ≤ d ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hd20 hd20
  have hn400 : 400 ≤ n := by omega
  have hdpos : (0 : ℝ) < d := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  have hLpos : 0 < logAlphabet d := by
    unfold logAlphabet
    have hegt : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact Real.log_pos (by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      nlinarith [Real.exp_pos 1])
  have htail :=
    Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.poisson_two_n_lower_tail n
  have hparam : Real.toNNReal (2 * (n : ℝ)) = 2 * (n : NNReal) := by
    apply NNReal.eq
    simp [Real.coe_toNNReal (2 * (n : ℝ)) (by positivity)]
  have htailReal :
      (ProbabilityTheory.poissonMeasure (Real.toNNReal (2 * n))
          {k | k < n}).toReal ≤ Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
    rw [hparam]
    calc
      (ProbabilityTheory.poissonMeasure (2 * (n : NNReal))
          {k | k < n}).toReal ≤
          (ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2)))).toReal :=
        ENNReal.toReal_mono (by simp) htail
      _ = Real.exp (-(n : ℝ) * (1 - Real.log 2)) :=
        ENNReal.toReal_ofReal (Real.exp_nonneg _)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnpos.le
  have hsqrt20 : 20 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 20)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn400)
  have hlogn : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hnpos.le (by norm_num)
      _ = 2 * Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        ring
  have halpha : (3 / 10 : ℝ) < 1 - Real.log 2 := by
    nlinarith [Real.log_two_lt_d9]
  have hbudget : 2 * Real.log (n : ℝ) ≤
      (n : ℝ) * (1 - Real.log 2) := by
    nlinarith
  have hexp : Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
      (n : ℝ)⁻¹ ^ 2 := by
    calc
      Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
          Real.exp (-2 * Real.log (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (n : ℝ)⁻¹ ^ 2 := by
        rw [show -2 * Real.log (n : ℝ) =
            -(Real.log (n : ℝ)) + -(Real.log (n : ℝ)) by ring,
          Real.exp_add, Real.exp_neg, Real.exp_log hnpos]
        ring
  have hinvRate : (n : ℝ)⁻¹ ^ 2 ≤ c * d / (n * logAlphabet d) := by
    rw [inv_pow, inv_eq_one_div]
    have hLn : logAlphabet d ≤ c * d * n := by
      calc
        logAlphabet d ≤ c * d := hDlog d hdlog
        _ ≤ c * d * n := by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          nlinarith [mul_pos hc hdpos]
    rw [div_le_div_iff₀ (sq_pos_of_pos hnpos) (mul_pos hnpos hLpos)]
    nlinarith [mul_pos hc hdpos]
  exact htailReal.trans (hexp.trans hinvRate)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
