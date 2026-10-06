module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ComparisonPluginRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.EmpiricalTableAdjustment
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ExperimentComparison
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.KnownMarginalUpper
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.T_RareLabelFloor
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.T_UniformBaseline
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.SideInformation.Finite.Comparison

/-!
Same-class benchmark recovery and exact-marginal quantitative experiment comparison.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


open Filter

/-- [Under the stated inputs and conditions](hyp:n,hn,heps,hscale,eps,M0), The capped label benchmark has a positive uniform floor on bounded label scales.  This gives [the stated result](goal).-/
-- @node: benchmark_label_floor_on_bounded_scale
lemma benchmark_label_floor_on_bounded_scale (n : Nat) (eps M0 : Real)
    (hn : 1 ≤ n) (heps : 0 < eps)
    (hscale : (n : Real) * eps ≤ M0) :
    1 / max 1 M0 ≤ labelBenchmark n eps := by
  have hn' : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < (n : Real) * eps := mul_pos hn' heps
  have hmax : 0 < max (1 : Real) M0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  change 1 / max 1 M0 ≤ min 1 (((n : Real) * eps)⁻¹)
  refine le_min ?_ ?_
  · exact (div_le_one hmax).2 (le_max_left _ _)
  · simpa only [one_div] using
      one_div_le_one_div_of_le hS (hscale.trans (le_max_right _ _))

/-- Under the stated inputs and conditions, The fixed-parameter comparison error vanishes as the auxiliary sample grows.  This gives [the stated result](goal). -/
-- @node: benchmark_comparison_error_tendsto
lemma benchmark_comparison_error_tendsto (n d : Nat) :
    Tendsto (fun m : Nat =>
      6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m)) atTop (nhds 0) := by
  have hinv : Tendsto (fun m : Nat => (m : Real)⁻¹) atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun m : Nat => 2 * (d : Real) / m) atTop (nhds (0 : Real)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2 * (d : Real))
  simpa only [Real.sqrt_zero, mul_zero] using
    hdiv.sqrt.const_mul (6 * ((n : Real) + 2))

/-- [Under the stated inputs and conditions](hyp:eps,hcomparison,n,d), A quantitative comparison with the exact-marginal experiment implies its limit.  This gives [the stated result](goal).-/
-- @node: benchmark_limit_of_comparison
lemma benchmark_limit_of_comparison (n d : Nat) (eps : Real)
    (hcomparison : ∀ m : Nat, 1 ≤ m →
      0 ≤ minimaxRisk n m d eps - knownMarginalRisk n d eps ∧
      minimaxRisk n m d eps - knownMarginalRisk n d eps ≤
        min 1 (6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m))) :
    Tendsto (fun m => minimaxRisk n m d eps) atTop (nhds (knownMarginalRisk n d eps)) := by
  have hnonneg : ∀ᶠ m : Nat in atTop,
      0 ≤ minimaxRisk n m d eps - knownMarginalRisk n d eps := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hcomparison m hm).1
  have hupper : ∀ᶠ m : Nat in atTop,
      minimaxRisk n m d eps - knownMarginalRisk n d eps ≤
        6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hcomparison m hm).2.trans (min_le_right _ _)
  have hzero := squeeze_zero' hnonneg hupper (benchmark_comparison_error_tendsto n d)
  simpa only [sub_add_cancel, zero_add] using hzero.add_const (knownMarginalRisk n d eps)

/-- [Under the stated inputs and conditions](hyp:hd,heps,heps',hbaseline,n,m,d,eps,C), The baseline guarantee bounds the infimum over all original-data Borel rules.  This gives [the stated result](goal).-/
-- @node: benchmark_minimax_le_baseline
lemma benchmark_minimax_le_baseline (n m d : Nat) (eps C : Real)
    (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hbaseline : ∀ P : ClassLaw d eps,
      ruleRisk (liftRule (baselineEstimator n m d)) P.1 ≤ C) :
    minimaxRisk n m d eps ≤ C := by
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps'⟩
  letI : Nonempty (ClassLaw d eps) := ⟨P0⟩
  let T : Rule n m d := ⟨liftRule (baselineEstimator n m d),
    (baselineEstimator_measurable n m d).comp measurable_fst,
    fun z => baselineEstimator_mem_Icc n m d z.1⟩
  apply (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
    (fun T P => integral_nonneg (fun z => sq_nonneg _)) T).trans
  exact ciSup_le hbaseline

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,n,m), With two covariate cells the baseline comparison is at most five label benchmarks.  This gives [the stated result](goal).-/
-- @node: benchmark_binary_baseline_rate
lemma benchmark_binary_baseline_rate (n m : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps) :
    min 1 (1 / ((n : Real) * eps) + (2 / (((n : Real) + m) * eps)) ^ 2) ≤
      5 * labelBenchmark n eps := by
  have hn' : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < (n : Real) * eps := mul_pos hn' heps
  have hN : (n : Real) * eps ≤ ((n : Real) + m) * eps := by
    nlinarith [Nat.cast_nonneg (α := Real) m]
  by_cases hlarge : 1 ≤ (n : Real) * eps
  · have hratio : 2 / (((n : Real) + m) * eps) ≤ 2 / ((n : Real) * eps) :=
      div_le_div_of_nonneg_left (by norm_num) hS hN
    have hsq : (2 / (((n : Real) + m) * eps)) ^ 2 ≤
        (2 / ((n : Real) * eps)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hratio 2
    have hinv : 0 ≤ 1 / ((n : Real) * eps) := by positivity
    have hinv' : 1 / ((n : Real) * eps) ≤ 1 := (div_le_one hS).2 hlarge
    have hbound : 1 / ((n : Real) * eps) +
        (2 / (((n : Real) + m) * eps)) ^ 2 ≤ 5 / ((n : Real) * eps) := by
      have htwo : 2 / ((n : Real) * eps) = 2 * (1 / ((n : Real) * eps)) := by ring
      rw [htwo] at hsq
      have hfive : 5 / ((n : Real) * eps) = 5 * (1 / ((n : Real) * eps)) := by ring
      rw [hfive]
      nlinarith [mul_nonneg hinv (sub_nonneg.mpr hinv')]
    calc
      min 1 _ ≤ 5 / ((n : Real) * eps) := (min_le_right _ _).trans hbound
      _ = 5 * labelBenchmark n eps := by
        simp only [labelBenchmark, labelScale, min_eq_right (inv_le_one_of_one_le₀ hlarge),
          one_div, div_eq_mul_inv]
  · have hbench : labelBenchmark n eps = 1 := by
      dsimp only [labelBenchmark, labelScale]
      exact min_eq_left ((one_le_inv₀ hS).2 (by linarith))
    rw [hbench]
    exact (min_le_left _ _).trans (by norm_num)

/-- [Under the stated inputs and conditions](hyp:n,eps,hn,heps,heps'), Uniform logarithmic comparisons at a fixed positive overlap floor.  This gives [the stated result](goal).-/
-- @node: benchmark_log_comparison
lemma benchmark_log_comparison (n : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    1 ≤ logScale n eps ∧
    logScale n eps ≤ 2 * Real.log (Real.exp 1 * n) ∧
    Real.log (Real.exp 1 * n) ≤
      (2 + Real.log (1 / eps)) * logScale n eps := by
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hS : 0 < (n : Real) * eps := mul_pos hn0 heps
  have hlogn : 0 ≤ Real.log (n : Real) := Real.log_nonneg hn1
  have hlogeps : 0 ≤ Real.log (1 / eps) :=
    Real.log_nonneg ((one_le_div heps).2 (by linarith))
  have hLambda : Real.log (Real.exp 1 * n) = 1 + Real.log (n : Real) := by
    rw [Real.log_mul he.ne' hn0.ne', Real.log_exp]
  have hlow : 1 ≤ logScale n eps := by
    simpa only [Real.log_exp, logScale, labelScale] using
      Real.log_le_log he (show Real.exp 1 ≤ Real.exp 1 + (n : Real) * eps by linarith)
  have he2 : Real.exp 1 + 1 ≤ Real.exp 2 := by
    have hgt : 2 < Real.exp 1 := by
      convert Real.add_one_lt_exp (show (1 : Real) ≠ 0 by norm_num) using 1
      norm_num
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hu := Real.log_le_log (add_pos he hS)
    (show Real.exp 1 + (n : Real) * eps ≤ Real.exp 2 * n by
      have hprod := mul_le_mul_of_nonneg_right he2 hn0.le
      nlinarith)
  rw [Real.log_mul (Real.exp_pos _).ne' hn0.ne', Real.log_exp] at hu
  have hl := Real.log_le_log hn0
    (show (n : Real) ≤ (Real.exp 1 + (n : Real) * eps) * (1 / eps) by
      field_simp
      linarith)
  rw [Real.log_mul (add_pos he hS).ne' (one_div_pos.mpr heps).ne'] at hl
  change Real.log (n : Real) ≤ logScale n eps + Real.log (1 / eps) at hl
  refine ⟨hlow, ?_, ?_⟩
  · rw [hLambda]
    change Real.log (Real.exp 1 + (n : Real) * eps) ≤ _
    linarith
  · rw [hLambda]
    nlinarith [mul_nonneg hlogeps (sub_nonneg.mpr hlow)]

/-- [Under the stated hypotheses](hyp:heps,heps'), Fixed-floor logarithmic comparisons give the uncapped and capped rate comparisons.  This gives [the stated result](goal). -/
-- @node: benchmark_fixed_overlap_comparison
lemma benchmark_fixed_overlap_comparison (eps : Real)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    ∃ B : Real, 0 < B ∧ ∀ (n m d : Nat), 1 ≤ n →
      fixedOverlapBenchmark n m d ≤ frontierRate n m d eps ∧
      frontierRate n m d eps ≤ B * fixedOverlapBenchmark n m d := by
  let K : Real := 2 + Real.log (1 / eps)
  let B : Real := max 1 (max (1 / eps) (K / eps) ^ 2)
  have hlogeps : 0 ≤ Real.log (1 / eps) :=
    Real.log_nonneg ((one_le_div heps).2 (by linarith))
  have hK : 0 < K := by dsimp [K]; linarith
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have hEinv : 1 ≤ 1 / eps := (one_le_div heps).2 (by linarith)
  have hbase : 1 / eps ≤ B := by
    have hz : 1 ≤ max (1 / eps) (K / eps) := hEinv.trans (le_max_left _ _)
    have hs : max (1 / eps) (K / eps) ≤ max (1 / eps) (K / eps) ^ 2 := by nlinarith
    exact (le_max_left _ _).trans (hs.trans (le_max_right _ _))
  have hfactor : (K / eps) ^ 2 ≤ B :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2).trans (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro n m d hn
  have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n : Real) + m := by positivity
  obtain ⟨hl1, hlu, hll⟩ := benchmark_log_comparison n eps hn heps heps'
  let ell := logScale n eps
  let Lam := Real.log (Real.exp 1 * n)
  have hl : 0 < ell := zero_lt_one.trans_le hl1
  have hLam : 0 < Lam := by
    dsimp [Lam]
    rw [Real.log_mul (Real.exp_pos _).ne' hn0.ne', Real.log_exp]
    linarith [Real.log_nonneg (show (1 : Real) ≤ n by exact_mod_cast hn)]
  have hden : ((n : Real) + m) * eps * ell ≤ ((n : Real) + m) * Lam := by
    have : eps * ell ≤ Lam := by nlinarith
    nlinarith
  have hratio : (d : Real) / (((n : Real) + m) * Lam) ≤
      (d : Real) / (((n : Real) + m) * eps * ell) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hratio' : (d : Real) / (((n : Real) + m) * eps * ell) ≤
      (K / eps) * ((d : Real) / (((n : Real) + m) * Lam)) := by
    apply (div_le_iff₀ (by positivity : 0 < ((n : Real) + m) * eps * ell)).2
    have hid : (K / eps) * ((d : Real) / (((n : Real) + m) * Lam)) *
        (((n : Real) + m) * eps * ell) = (d : Real) * (K * ell / Lam) := by
      field_simp
    rw [hid]
    exact le_mul_of_one_le_right (by positivity)
      ((le_div_iff₀ hLam).2 (by simpa only [one_mul] using hll))
  have hterm : (d : Real) ^ 2 / (((n : Real) + m) ^ 2 * Lam ^ 2) =
      ((d : Real) / (((n : Real) + m) * Lam)) ^ 2 := by
    rw [div_pow, mul_pow]
  have hlo : 1 / (n : Real) + (d : Real) ^ 2 /
        (((n : Real) + m) ^ 2 * Lam ^ 2) ≤
      1 / ((n : Real) * eps) + ((d : Real) / (((n : Real) + m) * eps * ell)) ^ 2 := by
    rw [hterm]
    exact add_le_add (one_div_le_one_div_of_le (by positivity) (by nlinarith))
      (pow_le_pow_left₀ (by positivity) hratio 2)
  have hhi : 1 / ((n : Real) * eps) +
        ((d : Real) / (((n : Real) + m) * eps * ell)) ^ 2 ≤
      B * (1 / (n : Real) + (d : Real) ^ 2 / (((n : Real) + m) ^ 2 * Lam ^ 2)) := by
    rw [hterm, mul_add]
    apply add_le_add
    · calc
        1 / ((n : Real) * eps) = (1 / eps) * (1 / (n : Real)) := by ring
        _ ≤ B * (1 / (n : Real)) := mul_le_mul_of_nonneg_right hbase (by positivity)
    · calc
        _ ≤ ((K / eps) * ((d : Real) / (((n : Real) + m) * Lam))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hratio' 2
        _ = (K / eps) ^ 2 * ((d : Real) / (((n : Real) + m) * Lam)) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
  constructor
  · exact min_le_min_left _ hlo
  · change min 1 _ ≤ B * min 1 _
    rw [mul_min_of_nonneg _ _ hB.le]
    exact le_min ((min_le_left _ _).trans (by simpa using hB1))
      ((min_le_right _ _).trans hhi)

-- @node: prop:benchmark-recovery
/-- Under the stated inputs and conditions, Fixed-floor recovery, binary-alphabet and oracle orders, quantitative comparison, and
limit. This gives [the stated conclusion](goal). -/
theorem benchmark_recovery :
    (∀ eps : Real, 0 < eps → eps ≤ 1 / 4 →
      ∃ a Bc : Real, 0 < a ∧ 0 < Bc ∧ ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
        a * fixedOverlapBenchmark n m d ≤ frontierRate n m d eps ∧
        frontierRate n m d eps ≤ Bc * fixedOverlapBenchmark n m d) ∧
    (∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ (n m d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
        (c * labelBenchmark n eps ≤ minimaxRisk n m 2 eps ∧
          minimaxRisk n m 2 eps ≤ C * labelBenchmark n eps) ∧
        (c * labelBenchmark n eps ≤ knownMarginalRisk n d eps ∧
          knownMarginalRisk n d eps ≤ C * labelBenchmark n eps)) ∧
    (∀ (n m d : Nat) (eps : Real), 1 ≤ n → 1 ≤ m → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      0 ≤ minimaxRisk n m d eps - knownMarginalRisk n d eps ∧
      minimaxRisk n m d eps - knownMarginalRisk n d eps ≤
        min 1 (6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m))) ∧
    (∀ (n d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      Tendsto (fun m => minimaxRisk n m d eps) atTop (nhds (knownMarginalRisk n d eps))) ∧
    (∀ M0 : Real, 0 < M0 → ∃ kappa : Real, 0 < kappa ∧
      ∀ (n m d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
        (n : Real) * eps ≤ M0 → kappa ≤ minimaxRisk n m d eps) := by
  have hcomparison : ∀ (n m d : Nat) (eps : Real),
      1 ≤ n → 1 ≤ m → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      0 ≤ minimaxRisk n m d eps - knownMarginalRisk n d eps ∧
      minimaxRisk n m d eps - knownMarginalRisk n d eps ≤
        min 1 (6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m)) := by
    intro n m d eps hn hm hd heps heps'
    obtain ⟨hlower, hcap⟩ := comparison_difference_bounds n m d eps hd heps heps'
    refine ⟨hlower, le_min hcap ?_⟩
    have hupper := comparison_minimax_le_known_add n m d eps hm hd heps heps'
    linarith
  refine ⟨?_, ?_, hcomparison, ?_, ?_⟩
  · intro eps heps heps'
    obtain ⟨B, hB, hcmp⟩ := benchmark_fixed_overlap_comparison eps heps heps'
    refine ⟨1, B, zero_lt_one, hB, ?_⟩
    intro n m d hn hd
    simpa only [one_mul] using hcmp n m d hn
  · obtain ⟨c, hc, hfloor⟩ := rare_label_floor.1
    obtain ⟨CB, hCB, hbaseline⟩ := uniform_baseline
    refine ⟨c, max (5 * CB) 2, hc,
      lt_of_lt_of_le (by norm_num : (0 : Real) < 2) (le_max_right _ _), ?_⟩
    intro n m d eps hn hd heps heps'
    obtain ⟨_, _, hbase⟩ := hbaseline n m 2 eps hn (by omega) heps heps'
    have hbinary : minimaxRisk n m 2 eps ≤ 5 * CB * labelBenchmark n eps := by
      calc
        minimaxRisk n m 2 eps ≤ CB *
            min 1 (1 / ((n : Real) * eps) + (2 / (((n : Real) + m) * eps)) ^ 2) :=
          benchmark_minimax_le_baseline n m 2 eps _ (by omega) heps heps' (by
            simpa only [Nat.cast_ofNat] using hbase)
        _ ≤ CB * (5 * labelBenchmark n eps) := mul_le_mul_of_nonneg_left
          (benchmark_binary_baseline_rate n m eps hn heps) hCB.le
        _ = 5 * CB * labelBenchmark n eps := by ring
    have hbench : 0 ≤ labelBenchmark n eps := by
      dsimp only [labelBenchmark, labelScale]
      positivity
    refine ⟨⟨(hfloor n m 2 eps hn (by omega) heps heps').1,
      hbinary.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbench)⟩,
      (hfloor n m d eps hn hd heps heps').2, ?_⟩
    exact (knownMarginalRisk_le_labelBenchmark n d eps hn hd heps heps').trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hbench)
  · intro n d eps hn hd heps heps'
    exact benchmark_limit_of_comparison n d eps
      (fun m hm => hcomparison n m d eps hn hm hd heps heps')
  · intro M0 hM0
    obtain ⟨c, hc, hfloor⟩ := rare_label_floor.1
    have hmax : 0 < max (1 : Real) M0 :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨c * (1 / max 1 M0), mul_pos hc (one_div_pos.mpr hmax), ?_⟩
    intro n m d eps hn hd heps heps' hscale
    exact (mul_le_mul_of_nonneg_left
      (benchmark_label_floor_on_bounded_scale n eps M0 hn heps hscale) hc.le).trans
      (hfloor n m d eps hn hd heps heps').1

end CausalSmith.Stat.AnnotationRarearmFrontier
