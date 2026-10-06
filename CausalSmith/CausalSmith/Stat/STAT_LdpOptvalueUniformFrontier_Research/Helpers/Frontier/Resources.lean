module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Upper
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellError

/-!
# Resource comparisons for the frontier fallback

The deterministic third split and randomized-response signal bound control the
vector noise. Comparing its logarithm with the rate logarithm certifies the
insufficient-degree fallback without any sampling moment assumptions.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hn condition](hyp:hn). [The third split used by the frontier has at least one fifth of the people](goal). -/
-- @node: frontier_third_block_lower
lemma frontier_third_block_lower (n : ℕ) (hn : 3 ≤ n) :
    0 < n / 3 ∧ (n : ℝ)/5 ≤ (n / 3 : ℕ) := by
  have hm : 0 < n / 3 := by omega
  have hb : n ≤ 5 * (n / 3) := by omega
  refine ⟨hm, ?_⟩
  have hr : (n : ℝ) ≤ 5 * (n / 3 : ℕ) := by exact_mod_cast hb
  linarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed) and [the stated hn condition](hyp:hn). [The evaluation-block noise obeys the upper half of equation (11)](goal). -/
-- @node: frontier_sigmaSquared_upper
lemma frontier_sigmaSquared_upper (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) :
    sigmaSquared d (n / 3) eps ≤ 80 * (d : ℝ) ^ 2/((n : ℝ) * eps ^ 2) := by
  have hn3 : 3 ≤ n := by have := hAllowed.1; omega
  obtain ⟨hm, hb⟩ := frontier_third_block_lower n hn3
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmp : (0 : ℝ) < (n / 3 : ℕ) := by exact_mod_cast hm
  have heps := hAllowed.2.2.1
  have hdelta := privacyDelta_lower_quarter eps hAllowed.2.2
  have hdp : 0 < privacyDelta eps := by linarith
  unfold sigmaSquared noiseScale
  calc
    (d / privacyDelta eps) ^ 2 / (n / 3 : ℕ) ≤
        (d / privacyDelta eps) ^ 2 / ((n : ℝ)/5) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hb
    _ = 80 * (d : ℝ) ^ 2/((n : ℝ) * (4 * privacyDelta eps) ^ 2) := by
      field_simp
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hnp.le
      nlinarith

/-- Assume [the stated l condition](hyp:hL), [the stated hz condition](hyp:hz), [the stated hs0 condition](hyp:hs0), and [the stated hs condition](hyp:hs). [A noise inflation of at most eighty inflates the rate logarithm by at most six](goal). -/
-- @node: frontier_noise_log_upper
lemma frontier_noise_log_upper (L z s : ℝ) (hL : 0 ≤ L) (hz : 0 ≤ z) (hs0 : 0 ≤ s)
    (hs : s * L ≤ 80 * z) :
    Real.log (Real.exp 1+s * L) ≤ 6 * Real.log (Real.exp 1+z) := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hw : 1 ≤ Real.log (Real.exp 1+z) := by
    simpa using Real.log_le_log he (show Real.exp 1 ≤ Real.exp 1+z by linarith)
  have h80 : Real.log (80 : ℝ) ≤ 5 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (show (2.7 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 5
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  calc
    _ ≤ Real.log (80 * (Real.exp 1+z)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 80 + Real.log (Real.exp 1+z) :=
      Real.log_mul (by norm_num) (by positivity)
    _ ≤ _ := by linarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated hbranch condition](hyp:hbranch), and [the stated hfallback condition](hyp:hfallback). [The insufficient-degree branch keeps the intermediate rate uniformly positive](goal). -/
-- @node: frontier_fallback_rate_lower
lemma frontier_fallback_rate_lower (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (hbranch : (n : ℝ) * eps ^ 2 < (d : ℝ) ^ 2* logDim d)
    (hfallback : logDim d / (1024 *
      Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) < 4) :
    (1 / 24576 : ℝ) ^ 2 ≤ rateR .NI n d eps := by
  let L := logDim d
  let t := (n : ℝ) * eps ^ 2
  let z := (d : ℝ) ^ 2* L / t
  let w := Real.log (Real.exp 1+z)
  let H := Real.log (Real.exp 1+sigmaSquared d (n / 3) eps * L)
  have hLp : 0 < L := logDim_pos d hAllowed.2.1
  have htp : 0 < t := by
    dsimp [t]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
    exact mul_pos hnpos (sq_pos_of_pos hAllowed.2.2.1)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hs : 0 ≤ sigmaSquared d (n / 3) eps := by unfold sigmaSquared; positivity
  have hHp : 0 < H := by
    have hh : 1 ≤ H := by
      dsimp [H]
      simpa using Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 ≤ Real.exp 1 + sigmaSquared d (n / 3) eps * L by
          nlinarith [mul_nonneg hs hLp.le])
    linarith
  have hnoise : sigmaSquared d (n / 3) eps * L ≤ 80 * z := by
    have hh := mul_le_mul_of_nonneg_right (frontier_sigmaSquared_upper n d eps hAllowed hn) hLp.le
    dsimp [z, t]
    convert hh using 1 <;> first | rfl | ring
  have hH : H ≤ 6 * w := frontier_noise_log_upper L z _ hLp.le hz hs hnoise
  have hLH : L < 4096 * H := by
    have hh := (div_lt_iff₀ (show 0 < 1024 * H by positivity)).mp hfallback
    dsimp [L, H] at *
    linarith
  have hratio : (1 / 24576 : ℝ) ≤ w / L := by
    apply (le_div_iff₀ hLp).mpr
    linarith
  change rho t d ≥ _
  rw [rho, if_neg (not_le.mpr hbranch)]
  change _ ≤ (min 1 (w / L)) ^ 2
  have hm : (1 / 24576 : ℝ) ≤ min 1 (w / L) := le_min (by norm_num) hratio
  exact pow_le_pow_left₀ (by norm_num) hm 2

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated l condition](hyp:hL), and [the stated hbranch condition](hyp:hbranch). [In the intermediate branch a bounded logarithmic dimension bounds the rate away from zero](goal). -/
-- @node: frontier_smallDim_intermediate_rate_lower
lemma frontier_smallDim_intermediate_rate_lower (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hL : logDim d < 4096)
    (hbranch : (n : ℝ) * eps ^ 2 < (d : ℝ) ^ 2 * logDim d) :
    (1 / 4096 : ℝ) ^ 2 ≤ rateR .NI n d eps := by
  have hLp := logDim_pos d hAllowed.2.1
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have htp : 0 < (n : ℝ) * eps ^ 2 := mul_pos hnp (sq_pos_of_pos hAllowed.2.2.1)
  have hz : 0 ≤ (d : ℝ) ^ 2 * logDim d / ((n : ℝ) * eps ^ 2) := by positivity
  have hw : 1 ≤ Real.log (Real.exp 1 +
      (d : ℝ) ^ 2 * logDim d / ((n : ℝ) * eps ^ 2)) := by
    simpa using Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 +
        (d : ℝ) ^ 2 * logDim d / ((n : ℝ) * eps ^ 2) by linarith)
  have hr : (1 / 4096 : ℝ) ≤ Real.log (Real.exp 1 +
      (d : ℝ) ^ 2 * logDim d / ((n : ℝ) * eps ^ 2)) / logDim d := by
    apply (le_div_iff₀ hLp).mpr
    linarith
  unfold rateR rho
  rw [if_neg (not_le.mpr hbranch)]
  exact pow_le_pow_left₀ (by norm_num) (le_min (by norm_num) hr) 2

/-- Assume [the stated hb condition](hyp:hb). [Reading the branch selector exposes the fallback's two resource inequalities](goal). -/
-- @node: frontier_fallback_resources
lemma frontier_fallback_resources (n d : ℕ) (eps : ℝ)
    (hb : (frontierResources n d eps).branch = .fallbackQuarter) :
    n ≠ 2 ∧ (n : ℝ) * eps ^ 2 < (d : ℝ) ^ 2 * logDim d ∧
      logDim d / (1024 * Real.log
        (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) < 4 := by
  simp only [frontierResources] at hb
  split_ifs at hb with hn hL hd hf
  exact ⟨hn, lt_of_not_ge hd, hf⟩

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), and [the stated hdense condition](hyp:hdense). [Dense resources select exactly the calibrated hybrid degree and fit its moments in the evaluation block, as in the upper-bound roadmap](goal). -/
-- @node: frontier_hybrid_resources
lemma frontier_hybrid_resources (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) (hL : 4096 ≤ logDim d)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2) :
    (frontierResources n d eps).branch = .hybrid ∧
    (frontierResources n d eps).degree = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊ ∧
    2*(frontierResources n d eps).degree ≤ n / 3 := by
  have hsmall : ¬ logDim d < 4096 := not_lt.mpr hL
  have hdegree : (frontierResources n d eps).degree = 2*⌊logDim d/2048⌋₊ := by
    simp only [frontierResources, if_pos hdense]
  refine ⟨by simp [frontierResources, hn, hsmall, hdense], ?_, ?_⟩
  · rw [hdegree]
    congr 2
    ring
  · have hn3 : 3 ≤ n := by have := hAllowed.1; omega
    have hblock := (frontier_third_block_lower n hn3).2
    have hd : (2 : ℝ) ≤ d := by exact_mod_cast hAllowed.2.1
    have hnp : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have ht : (n : ℝ) * eps^2 ≤ n := by
      have he2 : eps^2 ≤ 1 := by nlinarith [hAllowed.2.2.1, hAllowed.2.2.2]
      nlinarith
    have hfloor := Nat.floor_le (show 0 ≤ logDim d / 2048 by linarith)
    rw [hdegree]
    have hfit : (2 * (2 * ⌊logDim d/2048⌋₊) : ℝ) ≤ (n / 3 : ℕ) := by
      have hdim : 4 * logDim d ≤ (d : ℝ)^2 * logDim d :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      nlinarith
    exact_mod_cast hfit

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), and [the stated hdense condition](hyp:hdense). [The calibrated hybrid MSE and binary baseline noise have dense rate order](goal). -/
-- @node: frontier_hybrid_dense_resource_bound
lemma frontier_hybrid_dense_resource_bound (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2) :
    24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) *
        (500000000 * sigmaSquared d (n / 3) eps / logDim d) ≤
      (10 : ℝ)^16 * rateR .NI n d eps := by
  have hLp := logDim_pos d hAllowed.2.1
  have hnp : (0 : ℝ) < n := by
    exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht := mul_pos hnp (sq_pos_of_pos hAllowed.2.2.1)
  have hnoise := frontier_sigmaSquared_upper n d eps hAllowed hn
  have hr : rateR .NI n d eps =
      (d : ℝ)^2 / (((n : ℝ) * eps^2) * logDim d) := by
    simp only [rateR, rho, if_pos hdense]
  have hr0 : 0 ≤ rateR .NI n d eps := by rw [hr]; positivity
  have hbase : 1 / ((n : ℝ) * eps^2) ≤ rateR .NI n d eps := by
    have hLd := (logDim_bounds d hAllowed.2.1).2
    have hd : (2 : ℝ) ≤ d := by exact_mod_cast hAllowed.2.1
    rw [hr]
    apply (div_le_div_iff₀ ht (mul_pos ht hLp)).mpr
    have hdim : logDim d ≤ (d : ℝ)^2 := by nlinarith
    simpa only [one_mul, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hdim ht.le
  have hnorm : 500000000 * sigmaSquared d (n / 3) eps / logDim d ≤
      40000000000 * rateR .NI n d eps := by
    calc
      _ ≤ 500000000 * (80 * (d : ℝ)^2 / ((n : ℝ) * eps^2)) / logDim d := by
        gcongr
      _ = _ := by rw [hr]; ring
  calc
    _ ≤ 24 * rateR .NI n d eps + (1/2 : ℝ) *
        (40000000000 * rateR .NI n d eps) := by
      apply add_le_add
      · convert mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 24) using 1 <;> ring
      · exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ ≤ _ := by nlinarith

end CausalSmith.Stat.LdpOptvalueUniformFrontier
