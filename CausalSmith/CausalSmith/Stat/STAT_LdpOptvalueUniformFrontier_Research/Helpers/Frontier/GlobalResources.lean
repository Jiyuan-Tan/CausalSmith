module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Resources
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.NormCalibration

/-!
# Intermediate global-polynomial resources

The selected even degree has the roadmap's rounding bounds and fits in the
finite evaluation block. Its exponential variance and approximation error
are compared with the nonsaturated intermediate rate.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [dimension at least two](hyp:hd). [The noise logarithm is at least one](goal). -/
-- @node: frontier_noise_log_one
lemma frontier_noise_log_one (n d : ℕ) (eps : ℝ) (hd : 2 ≤ d) :
    1 ≤ Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d) := by
  have hs : 0 ≤ sigmaSquared d (n / 3) eps := by unfold sigmaSquared; positivity
  have hL := (logDim_pos d hd).le
  simpa using Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d by
      nlinarith [mul_nonneg hs hL])

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), and [the stated hf condition](hyp:hf). [Intermediate resources that avoid the fallback select the global branch and an even degree between half and all of the unrounded budget](goal). -/
-- @node: frontier_global_rounding
lemma frontier_global_rounding (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) (hL : 4096 ≤ logDim d)
    (hdense : ¬ (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2)
    (hf : (frontierResources n d eps).branch ≠ .fallbackQuarter) :
    (frontierResources n d eps).branch = .globalPoly ∧
    Even (frontierResources n d eps).degree ∧
    2 ≤ (frontierResources n d eps).degree ∧
    ((frontierResources n d eps).degree : ℝ) ≤ logDim d /
      (1024 * Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) ∧
    logDim d / (2048 * Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) ≤
      (frontierResources n d eps).degree := by
  let H := Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) (frontier_noise_log_one n d eps hAllowed.2.1)
  have hsmall : ¬ logDim d < 4096 := not_lt.mpr hL
  have hf' : ¬ logDim d / (1024 * H) < 4 := by
    intro h
    apply hf
    simp [frontierResources, hn, hsmall, hdense, H, h]
  have hx : 2 ≤ logDim d / (2048 * H) := by
    have := le_of_not_gt hf'
    have heq : logDim d / (1024 * H) = 2 * (logDim d / (2048 * H)) := by ring
    linarith
  have hdeg : (frontierResources n d eps).degree = 2 * ⌊logDim d / (2048 * H)⌋₊ := by
    simp [frontierResources, hdense, H]
  have hfloor := Nat.floor_le (show 0 ≤ logDim d / (2048 * H) by linarith)
  have hsucc := Nat.lt_floor_add_one (logDim d / (2048 * H))
  have hnat : 2 ≤ ⌊logDim d / (2048 * H)⌋₊ := Nat.le_floor hx
  refine ⟨by simp [frontierResources, hn, hsmall, hdense, H, hf'], ?_, ?_, ?_, ?_⟩
  · rw [hdeg]; exact even_two_mul _
  · rw [hdeg]; omega
  · rw [hdeg]; push_cast
    change 2 * (⌊logDim d / (2048 * H)⌋₊ : ℝ) ≤ logDim d / (1024 * H)
    have heq : logDim d / (1024 * H) = 2 * (logDim d / (2048 * H)) := by ring
    rw [heq]; linarith
  · rw [hdeg]; push_cast
    have hnatR : (2 : ℝ) ≤ ⌊logDim d / (2048 * H)⌋₊ := by exact_mod_cast hnat
    change logDim d / (2048 * H) ≤ 2 * (⌊logDim d / (2048 * H)⌋₊ : ℝ)
    linarith

/-- Assume [a positive privacy budget](hyp:heps). [The vector noise is at least the dimension squared divided by block size, since the randomized-response signal is below one](goal). -/
-- @node: frontier_sigmaSquared_lower_block
lemma frontier_sigmaSquared_lower_block (n d : ℕ) (eps : ℝ)
    (heps : 0 < eps) :
    (d : ℝ)^2 / (n / 3 : ℕ) ≤ sigmaSquared d (n / 3) eps := by
  have hdelta := privacyDelta_bounds eps heps.le
  have hpos : 0 < privacyDelta eps := by
    rw [privacyDelta_exp_formula]
    exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr heps)) (by positivity)
  have hscale : (d : ℝ) ≤ noiseScale d eps := by
    unfold noiseScale
    apply (le_div_iff₀ hpos).mpr
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  unfold sigmaSquared
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hscale 2

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated d condition](hyp:hD), and [the stated degree condition](hyp:hDegree). [The selected global degree fits its distinct-person moments in the block. An undersized block would make the noise logarithm at least the dimension logarithm, contradicting the nonfallback degree budget](goal). -/
-- @node: frontier_global_moment_fit
lemma frontier_global_moment_fit (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (hD : 2 ≤ (frontierResources n d eps).degree)
    (hDegree : ((frontierResources n d eps).degree : ℝ) ≤ logDim d /
      (1024 * Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d))) :
    2 * (frontierResources n d eps).degree ≤ n / 3 := by
  let H := Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)
  have hHone : 1 ≤ H := frontier_noise_log_one n d eps hAllowed.2.1
  have hHp : 0 < H := by linarith
  have hLp := logDim_pos d hAllowed.2.1
  have hm : 0 < n / 3 := by have := hAllowed.1; omega
  have hmR : (0 : ℝ) < (n / 3 : ℕ) := by exact_mod_cast hm
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hAllowed.2.1
  have hDp : (2 : ℝ) ≤ (frontierResources n d eps).degree := by exact_mod_cast hD
  have hbudget : ((frontierResources n d eps).degree : ℝ) * (1024 * H) ≤ logDim d :=
    (le_div_iff₀ (by positivity)).mp hDegree
  by_contra hfit
  have hmSmall : (n / 3 : ℕ) < 2 * (frontierResources n d eps).degree := by omega
  have hmSmallR : ((n / 3 : ℕ) : ℝ) < 2 * (frontierResources n d eps).degree := by
    exact_mod_cast hmSmall
  have hmL : (n / 3 : ℕ) < logDim d / 512 := by
    nlinarith [mul_le_mul_of_nonneg_left hHone
      (show 0 ≤ ((frontierResources n d eps).degree : ℝ) by positivity)]
  have hs := frontier_sigmaSquared_lower_block n d eps hAllowed.2.2.1
  have hsprod : (d : ℝ)^2 ≤ sigmaSquared d (n / 3) eps * (n / 3 : ℕ) :=
    (div_le_iff₀ hmR).mp hs
  have hs0 : 0 ≤ sigmaSquared d (n / 3) eps := by unfold sigmaSquared; positivity
  have hnoise : Real.exp 1 * d ≤ Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d := by
    have he := Real.exp_one_lt_d9
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hmL) hs0
    nlinarith
  have hLH : logDim d ≤ H := by
    unfold logDim
    exact Real.log_le_log (by positivity) hnoise
  nlinarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed) and [the protocol-class label](hyp:hs). [Below saturation, the elementary parametric comparison absorbs baseline noise without imposing any new estimator assumptions](goal). -/
-- @node: frontier_nonsaturated_baseline_comparison
lemma frontier_nonsaturated_baseline_comparison (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hs : rateR .NI n d eps ≠ 1) :
    1 / ((n : ℝ) * eps^2) ≤ rateR .NI n d eps := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht := mul_pos hnp (sq_pos_of_pos hAllowed.2.2.1)
  have hr : rateR .NI n d eps ≤ 1 := rho_le_one d _ hAllowed.2.1 ht
  have hl := (rho_elementary_comparisons n d eps hAllowed).1
  have hi : 1 / ((n : ℝ) * eps^2) < 1 := by
    by_contra h
    have he : min 1 (1 / ((n : ℝ) * eps^2)) = 1 := min_eq_left (le_of_not_gt h)
    rw [he] at hl
    exact hs (le_antisymm hr hl)
  simpa only [min_eq_right hi.le, rateR] using hl

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hn condition](hyp:hn), [the stated l condition](hyp:hL), [the stated hdense condition](hyp:hdense), [the protocol-class label](hyp:hs), [the stated degree condition](hyp:hDegree), and [the stated lower condition](hyp:hLower). [The global polynomial variance and approximation bias have intermediate rate order. This uses the rounded degree, the eighty-fold noise comparison, and the established exponential dimension bound](goal). -/
-- @node: frontier_global_resource_bound
lemma frontier_global_resource_bound (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2) (hL : 4096 ≤ logDim d)
    (hdense : ¬ (d : ℝ)^2 * logDim d ≤ (n : ℝ) * eps^2)
    (hs : rateR .NI n d eps ≠ 1)
    (hDegree : ((frontierResources n d eps).degree : ℝ) ≤ logDim d /
      (1024 * Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)))
    (hLower : logDim d /
      (2048 * Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) ≤
      (frontierResources n d eps).degree) :
    24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) *
      (Real.exp (9*(frontierResources n d eps).degree *
        Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d))/(2*d) +
        (1/((frontierResources n d eps).degree+1 : ℝ))^2) ≤
      (10 : ℝ)^16 * rateR .NI n d eps := by
  let L := logDim d
  let H := Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * L)
  let z := (d : ℝ)^2 * L / ((n : ℝ) * eps^2)
  let w := Real.log (Real.exp 1 + z)
  let D := (frontierResources n d eps).degree
  have hLp : 0 < L := logDim_pos d hAllowed.2.1
  have hHp : 0 < H := lt_of_lt_of_le (by norm_num)
    (frontier_noise_log_one n d eps hAllowed.2.1)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hw : 1 ≤ w := by
    dsimp [w]
    simpa using Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + z by linarith)
  have hs0 : 0 ≤ sigmaSquared d (n / 3) eps := by unfold sigmaSquared; positivity
  have hnoise : sigmaSquared d (n / 3) eps * L ≤ 80 * z := by
    have hh := mul_le_mul_of_nonneg_right (frontier_sigmaSquared_upper n d eps hAllowed hn) hLp.le
    dsimp [z]
    convert hh using 1 <;> first | rfl | ring
  have hH : H ≤ 6 * w := frontier_noise_log_upper L z _ hLp.le hz hs0 hnoise
  have hr : rateR .NI n d eps = (w/L)^2 := by
    have hm : w / L < 1 := by
      by_contra h
      apply hs
      change rho ((n : ℝ) * eps^2) d = 1
      rw [rho, if_neg hdense]
      change (min 1 (w/L))^2 = 1
      rw [min_eq_left (le_of_not_gt h)]; norm_num
    change rho ((n : ℝ) * eps^2) d = _
    rw [rho, if_neg hdense]
    change (min 1 (w/L))^2 = _
    rw [min_eq_right hm.le]
  have hbudget : (D : ℝ) * (1024 * H) ≤ L :=
    (le_div_iff₀ (by positivity)).mp hDegree
  have hvariance : Real.exp (9*(D : ℝ)*H)/(2*d) ≤ 2/L^2 := by
    have hexp : Real.exp (9*(D : ℝ)*H) ≤ Real.exp (L/100) := by
      apply Real.exp_le_exp.mpr
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      nlinarith
    have hdim := hybrid_dimension_exp_bound (by have := hAllowed.2.1; omega) hL
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by have := hAllowed.2.1; omega : 0 < d)
    calc
      _ ≤ Real.exp (L/100)/(2*d) := div_le_div_of_nonneg_right hexp (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hLp)).mpr
        dsimp [L] at *
        nlinarith [hdim]
  have hinv : 1/((D : ℝ)+1) ≤ 2048*H/L := by
    have hlower : L ≤ (D : ℝ) * (2048 * H) :=
      (div_le_iff₀ (by positivity)).mp hLower
    apply (div_le_div_iff₀ (by positivity) hLp).mpr
    nlinarith
  have hbias : (1/((D : ℝ)+1))^2 ≤ (12288 * (w/L))^2 := by
    have hratio : 2048*H/L ≤ 12288*(w/L) := by
      apply (div_le_iff₀ hLp).mpr
      have heq : (12288*(w/L))*L = 12288*w := by field_simp
      rw [heq]; linarith
    exact pow_le_pow_left₀ (by positivity) (hinv.trans hratio) 2
  have hvarianceRate : 2/L^2 ≤ 2 * rateR .NI n d eps := by
    rw [hr]
    have hratio : 1/L ≤ w/L := div_le_div_of_nonneg_right hw hLp.le
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1/L) hratio 2
    have heq : 2/L^2 = 2*(1/L)^2 := by ring
    rw [heq]; linarith
  have hbase := frontier_nonsaturated_baseline_comparison n d eps hAllowed hs
  have hr0 : 0 ≤ rateR .NI n d eps := by rw [hr]; positivity
  change 24 / ((n : ℝ) * eps^2) + (1/2 : ℝ) *
    (Real.exp (9*(D : ℝ)*H)/(2*d) + (1/((D : ℝ)+1))^2) ≤ _
  have hbiasRate : (1/((D : ℝ)+1))^2 ≤ 150994944 * rateR .NI n d eps := by
    rw [hr]; nlinarith [hbias]
  have hbase24 : 24 / ((n : ℝ) * eps^2) ≤ 24 * rateR .NI n d eps := by
    convert mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 24) using 1 <;> first | rfl | ring
  nlinarith [hvariance.trans hvarianceRate]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
