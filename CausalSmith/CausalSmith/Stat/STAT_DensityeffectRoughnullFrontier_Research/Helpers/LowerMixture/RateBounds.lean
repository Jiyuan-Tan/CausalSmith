module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OutcomeWeights
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Procedure

/-! Deterministic lower-experiment scale bounds in (28) and (44). -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The squared bump denominator has the uniform positive envelope used in (26). -/
-- @node: lowerCphi_denominator_bounds
lemma lowerCphi_denominator_bounds (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4))
    (z : ℝ) :
    1 - tau ^ 2 ≤ 1 - tau ^ 2 * (lowerBump z) ^ 2 ∧
    0 < 1 - tau ^ 2 * (lowerBump z) ^ 2 ∧
    1 - tau ^ 2 * (lowerBump z) ^ 2 ≤ 1 := by
  have hb := abs_le.mp (lowerBump_abs_le_one z)
  have hb2 : (lowerBump z) ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
  have hp := mul_le_mul_of_nonneg_left hb2 (sq_nonneg tau)
  have hn := mul_nonneg (sq_nonneg tau) (sq_nonneg (lowerBump z))
  constructor
  · linarith
  constructor
  · nlinarith [ht.1, ht.2]
  · linarith

/-- The rational square in (26) is integrable, derived from the bump envelope. -/
-- @node: lowerCphi_integrable
lemma lowerCphi_integrable (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4)) :
    Integrable (fun z => (lowerBump z) ^ 2 /
      (1 - tau ^ 2 * (lowerBump z) ^ 2)) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by apply Measurable.aestronglyMeasurable; fun_prop) 2
  filter_upwards [] with z
  have hd := lowerCphi_denominator_bounds tau ht z
  have hb := abs_le.mp (lowerBump_abs_le_one z)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hd.2.1.le)]
  apply (div_le_iff₀ hd.2.1).2
  nlinarith [ht.1, ht.2, hb.1, hb.2, hd.1]

/-- Integrating the two denominator inequalities gives exactly (26). -/
-- @node: lowerCphi_bounds
lemma lowerCphi_bounds (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4)) :
    (1 / 210 : ℝ) ≤ lowerCphi tau ∧
    lowerCphi tau ≤ (1 / 210 : ℝ) / (1 - tau ^ 2) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi : Integrable (fun z => (lowerBump z) ^ 2) unitVolume := by
    apply Integrable.of_bound (by apply Measurable.aestronglyMeasurable; fun_prop) 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := abs_le.mp (lowerBump_abs_le_one z)
    nlinarith [hb.1, hb.2]
  have hd : 0 < 1 - tau ^ 2 := by nlinarith [ht.1, ht.2]
  constructor
  · have h := integral_mono hi (lowerCphi_integrable tau ht) (fun z => by
      have hden := lowerCphi_denominator_bounds tau ht z
      apply (le_div_iff₀ hden.2.1).2
      exact mul_le_of_le_one_right (sq_nonneg _) hden.2.2)
    simpa only [lower_bump_moments, lowerCphi] using h
  · have h := integral_mono (lowerCphi_integrable tau ht) (hi.div_const (1 - tau ^ 2))
      (fun z => div_le_div_of_nonneg_left (sq_nonneg _) hd
        (lowerCphi_denominator_bounds tau ht z).1)
    simpa only [integral_div, lower_bump_moments, lowerCphi] using h

/-- The lower propensity amplitude can be written with a positive rank denominator. -/
-- @node: lowerTau_eq_div_rank
lemma lowerTau_eq_div_rank (theta : ℝ) (k : ℕ) :
    lowerTau theta k = theta / (k : ℝ) ^ (1 / 10 : ℝ) := by
  unfold lowerTau
  rw [show (-1 / 10 : ℝ) = -(1 / 10) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg k)]
  simp only [div_eq_mul_inv]

/-- Substituting the smallest allowed outcome rank gives the first scale in (44). -/
-- @node: lower_first_scale_le
lemma lower_first_scale_le (theta : ℝ) (k j : ℕ) (hk : 0 < k)
    (hj : (k : ℝ) ^ (1 / 10 : ℝ) ≤ j) :
    (lowerTau theta k) ^ 4 * (lowerGamma theta j) ^ 4 / ((k : ℝ) ^ 2 * j) ≤
      theta ^ 8 * (k : ℝ) ^ (-29 / 10 : ℝ) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < (k : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hkp _
  have hjp : (0 : ℝ) < j := hs.trans_le hj
  rw [lowerTau_eq_div_rank]
  unfold lowerGamma
  have hden : (k : ℝ) ^ 2 * ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 5 ≤
      (k : ℝ) ^ 2 * (j : ℝ) ^ 5 := by gcongr
  have heq : ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 4 *
      ((k : ℝ) ^ 2 * ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 5) =
      (k : ℝ) ^ (29 / 10 : ℝ) := by
    rw [← Real.rpow_mul_natCast hkp.le, ← Real.rpow_mul_natCast hkp.le,
      ← Real.rpow_natCast _ 2, ← Real.rpow_add hkp, ← Real.rpow_add hkp]
    norm_num
  calc
    _ = theta ^ 8 / (((k : ℝ) ^ (1 / 10 : ℝ)) ^ 4 * ((k : ℝ) ^ 2 * (j : ℝ) ^ 5)) := by
      field_simp
    _ ≤ theta ^ 8 / (((k : ℝ) ^ (1 / 10 : ℝ)) ^ 4 *
        ((k : ℝ) ^ 2 * ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 5)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by rw [heq, div_eq_mul_inv, ← Real.rpow_neg hkp.le]; norm_num

/-- The second scale in (44) uses the same minimum outcome rank. -/
-- @node: lower_second_scale_le
lemma lower_second_scale_le (theta : ℝ) (k j : ℕ) (hk : 0 < k)
    (hj : (k : ℝ) ^ (1 / 10 : ℝ) ≤ j) :
    (lowerGamma theta j) ^ 4 / ((k : ℝ) * j) ≤
      theta ^ 4 * (k : ℝ) ^ (-3 / 2 : ℝ) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < (k : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hkp _
  have hjp : (0 : ℝ) < j := hs.trans_le hj
  have hden : (k : ℝ) * ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 5 ≤
      (k : ℝ) * (j : ℝ) ^ 5 := by gcongr
  have heq : (k : ℝ) * ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 5 =
      (k : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hkp.le]
    nth_rw 1 [← Real.rpow_one (k : ℝ)]
    rw [← Real.rpow_add hkp]
    norm_num
  unfold lowerGamma
  calc
    _ = theta ^ 4 / ((k : ℝ) * (j : ℝ) ^ 5) := by field_simp
    _ ≤ theta ^ 4 / ((k : ℝ) * ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 5) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by rw [heq, div_eq_mul_inv, ← Real.rpow_neg hkp.le]; norm_num

/-- The covariate rank in (20) cancels the fourth sample-size power in (44). -/
-- @node: lower_first_rank_decay
lemma lower_first_rank_decay (n k : ℕ) (hn : 0 < n)
    (hk : (n : ℝ) ^ (40 / 29 : ℝ) ≤ k) :
    (n : ℝ) ^ 4 * (k : ℝ) ^ (-29 / 10 : ℝ) ≤ 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hnp (40 / 29)) hk (by norm_num : (-29 / 10 : ℝ) ≤ 0)
  rw [← Real.rpow_mul hnp.le] at h
  have hh : (k : ℝ) ^ (-29 / 10 : ℝ) ≤ (n : ℝ) ^ (-4 : ℝ) := by
    convert h using 1; norm_num
  calc
    _ ≤ (n : ℝ) ^ 4 * (n : ℝ) ^ (-4 : ℝ) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 1 := by rw [← Real.rpow_natCast _ 4, ← Real.rpow_add hnp]; norm_num

/-- The second sample-size scale has the strictly decaying slack in (44). -/
-- @node: lower_second_rank_decay
lemma lower_second_rank_decay (n k : ℕ) (hn : 0 < n)
    (hk : (n : ℝ) ^ (40 / 29 : ℝ) ≤ k) :
    (n : ℝ) ^ 2 * (k : ℝ) ^ (-3 / 2 : ℝ) ≤
      (n : ℝ) ^ (-2 / 29 : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hnp (40 / 29)) hk (by norm_num : (-3 / 2 : ℝ) ≤ 0)
  rw [← Real.rpow_mul hnp.le] at h
  calc
    _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ ((40 / 29 : ℝ) * (-3 / 2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [← Real.rpow_natCast _ 2, ← Real.rpow_add hnp]; norm_num

/-- Both terms in (44) are bounded after substituting the actual amplitudes (24). -/
-- @node: lower_fixed_size_scales_le
lemma lower_fixed_size_scales_le (theta : ℝ) (n k j : ℕ) (hn : 0 < n) (hkp : 0 < k)
    (hk : (n : ℝ) ^ (40 / 29 : ℝ) ≤ k)
    (hj : (k : ℝ) ^ (1 / 10 : ℝ) ≤ j) :
    (n : ℝ) ^ 4 * (lowerTau theta k) ^ 4 * (lowerGamma theta j) ^ 4 /
        ((k : ℝ) ^ 2 * j) ≤ theta ^ 8 ∧
    (n : ℝ) ^ 2 * (lowerGamma theta j) ^ 4 / ((k : ℝ) * j) ≤
      theta ^ 4 * (n : ℝ) ^ (-2 / 29 : ℝ) := by
  constructor
  · have h := mul_le_mul_of_nonneg_left (lower_first_scale_le theta k j hkp hj)
      (by positivity : 0 ≤ (n : ℝ) ^ 4)
    have h' := mul_le_mul_of_nonneg_left (lower_first_rank_decay n k hn hk)
      (by positivity : 0 ≤ theta ^ 8)
    calc
      _ ≤ (n : ℝ) ^ 4 * (theta ^ 8 * (k : ℝ) ^ (-29 / 10 : ℝ)) := by
        simpa only [mul_div_assoc, mul_assoc] using h
      _ = theta ^ 8 * ((n : ℝ) ^ 4 * (k : ℝ) ^ (-29 / 10 : ℝ)) := by ring
      _ ≤ theta ^ 8 := by simpa using h'
  · have h := mul_le_mul_of_nonneg_left (lower_second_scale_le theta k j hkp hj)
      (by positivity : 0 ≤ (n : ℝ) ^ 2)
    have h' := mul_le_mul_of_nonneg_left (lower_second_rank_decay n k hn hk)
      (by positivity : 0 ≤ theta ^ 4)
    calc
      _ ≤ (n : ℝ) ^ 2 * (theta ^ 4 * (k : ℝ) ^ (-3 / 2 : ℝ)) := by
        simpa only [mul_div_assoc, mul_assoc] using h
      _ = theta ^ 4 * ((n : ℝ) ^ 2 * (k : ℝ) ^ (-3 / 2 : ℝ)) := by ring
      _ ≤ _ := h'

/-- The upper outcome-rank rounding bound preserves the separation in (28). -/
-- @node: lowerSeparation_rank_lower_bound
lemma lowerSeparation_rank_lower_bound (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j)
    (hj : (j : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 10 : ℝ)) :
    theta ^ 4 / (4 * (210 : ℝ) ^ 3) * (k : ℝ) ^ (-2 / 5 : ℝ) ≤
      lowerSeparation theta k j := by
  have hk : (0 : ℝ) < k := by exact_mod_cast lower_dyadic_one_le hp.2.1
  have hjp : (0 : ℝ) < j := by exact_mod_cast lower_dyadic_one_le hp.2.2.1
  let s : ℝ := (k : ℝ) ^ (1 / 10 : ℝ)
  have hs : 0 < s := Real.rpow_pos_of_pos hk _
  have hc := (lowerCphi_bounds (lowerTau theta k) (lowerTau_mem_Icc theta k j hp)).1
  have hcs : (1 / 210 : ℝ) ^ 2 ≤ (lowerCphi (lowerTau theta k)) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith)).2 hc
  have hden : s ^ 2 * (j : ℝ) ^ 2 ≤ 4 * s ^ 4 := by
    have hjs : (j : ℝ) ^ 2 ≤ (2 * s) ^ 2 :=
      (sq_le_sq₀ hjp.le (by positivity)).2 hj
    nlinarith [mul_le_mul_of_nonneg_left hjs (sq_nonneg s)]
  have heq : s ^ 4 = (k : ℝ) ^ (2 / 5 : ℝ) := by
    dsimp [s]
    rw [← Real.rpow_mul_natCast hk.le]
    norm_num
  calc
    _ = (theta ^ 4 / (4 * s ^ 4)) * (1 / 210 : ℝ) ^ 2 / 210 := by
      rw [heq, show (-2 / 5 : ℝ) = -(2 / 5) by norm_num, Real.rpow_neg hk.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      ring
    _ ≤ (theta ^ 4 / (s ^ 2 * (j : ℝ) ^ 2)) * (1 / 210 : ℝ) ^ 2 / 210 := by
      gcongr
    _ ≤ (theta ^ 4 / (s ^ 2 * (j : ℝ) ^ 2)) *
        (lowerCphi (lowerTau theta k)) ^ 2 / 210 := by
      gcongr
    _ = _ := by
      unfold lowerSeparation
      rw [lowerTau_eq_div_rank]
      unfold lowerGamma
      change _ = (theta / s) ^ 2 * (theta / j) ^ 2 * _ / 210
      field_simp

/-- The upper covariate-rank rounding bound turns (28) into the frontier rate. -/
-- @node: lowerSeparation_frontier_lower_bound
lemma lowerSeparation_frontier_lower_bound (theta : ℝ) (n k j : ℕ) (hn : 0 < n)
    (hp : LowerParameters theta k j)
    (hk : (k : ℝ) ≤ 2 * (n : ℝ) ^ (40 / 29 : ℝ))
    (hj : (j : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 10 : ℝ)) :
    (theta ^ 4 / (4 * (210 : ℝ) ^ 3) * (2 : ℝ) ^ (-2 / 5 : ℝ)) *
      frontierRate n ≤ lowerSeparation theta k j := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast lower_dyadic_one_le hp.2.1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_nonpos hkp hk (by norm_num : (-2 / 5 : ℝ) ≤ 0)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnp.le _),
    ← Real.rpow_mul hnp.le] at h
  have hscale : (2 : ℝ) ^ (-2 / 5 : ℝ) * frontierRate n ≤
      (k : ℝ) ^ (-2 / 5 : ℝ) := by
    unfold frontierRate
    convert h using 1; norm_num
  have hmul := mul_le_mul_of_nonneg_left hscale
    (by positivity : 0 ≤ theta ^ 4 / (4 * (210 : ℝ) ^ 3))
  simpa only [mul_assoc] using hmul.trans
    (lowerSeparation_rank_lower_bound theta k j hp hj)

/-- The covariate rank in the lower-bound construction (20). -/
-- @node: lowerCovariateRank
def lowerCovariateRank (n : ℕ) : ℕ :=
  2 ^ ⌈(40 / 29 : ℝ) * Real.logb 2 n⌉₊

/-- The outcome rank in the lower-bound construction (20). -/
-- @node: lowerOutcomeRank
def lowerOutcomeRank (k : ℕ) : ℕ :=
  2 ^ ⌈(1 / 10 : ℝ) * Real.logb 2 k⌉₊

/-- Rounding a nonnegative logarithmic exponent loses at most a factor two. -/
-- @node: lower_dyadic_rounding_bounds
lemma lower_dyadic_rounding_bounds (z : ℝ) (hz : 0 ≤ z) :
    (2 : ℝ) ^ z ≤ (2 ^ ⌈z⌉₊ : ℕ) ∧
    (2 ^ ⌈z⌉₊ : ℕ) ≤ 2 * (2 : ℝ) ^ z := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil z)
  · have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.ceil_lt_add_one hz).le
    simpa only [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      mul_comm] using h

/-- The frozen lower covariate rank satisfies both bounds in (20). -/
-- @node: lowerCovariateRank_bounds
lemma lowerCovariateRank_bounds (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (40 / 29 : ℝ) ≤ lowerCovariateRank n ∧
    (lowerCovariateRank n : ℝ) ≤ 2 * (n : ℝ) ^ (40 / 29 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz : 0 ≤ (40 / 29 : ℝ) * Real.logb 2 n :=
    mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) hn1)
  have heq : (2 : ℝ) ^ ((40 / 29 : ℝ) * Real.logb 2 n) =
      (n : ℝ) ^ (40 / 29 : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity : (0 : ℝ) < n)]
  simpa only [heq, lowerCovariateRank] using lower_dyadic_rounding_bounds _ hz

/-- The frozen lower outcome rank satisfies both bounds in (20). -/
-- @node: lowerOutcomeRank_bounds
lemma lowerOutcomeRank_bounds (k : ℕ) (hk : 0 < k) :
    (k : ℝ) ^ (1 / 10 : ℝ) ≤ lowerOutcomeRank k ∧
    (lowerOutcomeRank k : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 10 : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : 0 ≤ (1 / 10 : ℝ) * Real.logb 2 k :=
    mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) hk1)
  have heq : (2 : ℝ) ^ ((1 / 10 : ℝ) * Real.logb 2 k) =
      (k : ℝ) ^ (1 / 10 : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity : (0 : ℝ) < k)]
  simpa only [heq, lowerOutcomeRank] using lower_dyadic_rounding_bounds _ hz

/-- The explicit ranks provide every model-membership parameter condition. -/
-- @node: lower_tuned_parameters
lemma lower_tuned_parameters (theta : ℝ) (ht : theta ∈ Set.Ioc 0 (1 / 4)) (n : ℕ) :
    LowerParameters theta (lowerCovariateRank n) (lowerOutcomeRank (lowerCovariateRank n)) := by
  have hk : Dyadic (lowerCovariateRank n) := ⟨_, rfl⟩
  refine ⟨ht, hk, ⟨_, rfl⟩, ?_⟩
  exact (lowerOutcomeRank_bounds _ (lower_dyadic_one_le hk)).1

/-- The explicit family separation attains the promised lower frontier scale (28). -/
-- @node: lower_tuned_separation_bound
lemma lower_tuned_separation_bound (theta : ℝ) (ht : theta ∈ Set.Ioc 0 (1 / 4))
    (n : ℕ) (hn : 0 < n) :
    (theta ^ 4 / (4 * (210 : ℝ) ^ 3) * (2 : ℝ) ^ (-2 / 5 : ℝ)) * frontierRate n ≤
      lowerSeparation theta (lowerCovariateRank n) (lowerOutcomeRank (lowerCovariateRank n)) := by
  exact lowerSeparation_frontier_lower_bound theta n _ _ hn
    (lower_tuned_parameters theta ht n) (lowerCovariateRank_bounds n hn).2
    (lowerOutcomeRank_bounds _ (lower_dyadic_one_le ⟨_, rfl⟩)).2

/-- The constant in (28) is strictly positive for every legal public amplitude. -/
-- @node: lower_separation_constant_pos
lemma lower_separation_constant_pos (theta : ℝ) (ht : 0 < theta) :
    0 < theta ^ 4 / (4 * (210 : ℝ) ^ 3) * (2 : ℝ) ^ (-2 / 5 : ℝ) := by
  positivity

/-- From sixteen records onwards the explicit lower covariate rank is at least 2n. -/
-- @node: lowerCovariateRank_two_mul_le
lemma lowerCovariateRank_two_mul_le (n : ℕ) (hn : 16 ≤ n) :
    2 * (n : ℝ) ≤ lowerCovariateRank n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnp : (0 : ℝ) < n := by positivity
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    norm_num
  have hroot : (2 : ℝ) ≤ (n : ℝ) ^ (11 / 29 : ℝ) := by
    calc
      _ = (16 : ℝ) ^ (1 / 4 : ℝ) := h16.symm
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn) (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  calc
    _ ≤ (n : ℝ) * (n : ℝ) ^ (11 / 29 : ℝ) := by nlinarith
    _ = (n : ℝ) ^ (40 / 29 : ℝ) := by
      nth_rw 1 [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hnp]
      norm_num
    _ ≤ _ := (lowerCovariateRank_bounds n (by omega)).1

/-- The actual Poisson cell mean xi=2n/k lies in the collision regime for n>=16. -/
-- @node: lower_tuned_poisson_mean_le_one
lemma lower_tuned_poisson_mean_le_one (n : ℕ) (hn : 16 ≤ n) :
    2 * (n : ℝ) / lowerCovariateRank n ≤ 1 := by
  have hk : (0 : ℝ) < lowerCovariateRank n := by
    exact_mod_cast lower_dyadic_one_le (show Dyadic (lowerCovariateRank n) from ⟨_, rfl⟩)
  exact (div_le_one hk).2 (lowerCovariateRank_two_mul_le n hn)

/-- Inserting the explicit ranks into the rational bound (43) gives (44),
with all numerical constants retained and independent of the sample size. -/
-- @node: lower_tuned_poisson_budget_le
lemma lower_tuned_poisson_budget_le (theta C : ℝ) (n : ℕ) (hn : 0 < n) :
    let k := lowerCovariateRank n
    let j := lowerOutcomeRank k
    8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * C * (2 * (n : ℝ) / k) ^ 2 *
        (lowerTau theta k) ^ 2 * (lowerGamma theta j) ^ 2) ^ 2 +
      ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        (16 * (k : ℝ) * (2 * (n : ℝ) / k) ^ 2 * (lowerGamma theta j) ^ 4)) ≤
    (128 * (100 / 81 : ℝ) * (1 / 210) ^ 2 * C ^ 2) * theta ^ 8 +
    (512 * (100 / 81 : ℝ) * (1 / 210) ^ 2) *
      (theta ^ 4 * (n : ℝ) ^ (-2 / 29 : ℝ)) := by
  dsimp only
  have hk : 0 < lowerCovariateRank n := lower_dyadic_one_le ⟨_, rfl⟩
  have hj : 0 < lowerOutcomeRank (lowerCovariateRank n) := lower_dyadic_one_le ⟨_, rfl⟩
  rw [lower_poisson_budget_eq_fixed_size n _ _ hk hj]
  have h := lower_fixed_size_scales_le theta n _ _ hn hk
    (lowerCovariateRank_bounds n hn).1 (lowerOutcomeRank_bounds _ hk).1
  exact add_le_add
    (mul_le_mul_of_nonneg_left h.1 (by positivity))
    (mul_le_mul_of_nonneg_left h.2 (by positivity))

end CausalSmith.Stat.DensityEffectRoughNull
