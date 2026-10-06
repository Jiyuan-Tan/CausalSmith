module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CorrectedMean
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Deterministic dyadic refinement at the sharp rough-null rate. The proved helpers
establish finite-sample rank compatibility, the operator-budget rate (53), the
role-size conversion, and the inversion-budget reduction (58). The final
rate assembly is provided downstream by `RateAssembly`.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Downward dyadic rounding always gives a positive power of two. -/
-- @node: dyadicFloor_dyadic
lemma dyadicFloor_dyadic (z : ℝ) : Dyadic (dyadicFloor z) :=
  ⟨Nat.log 2 ⌊z⌋₊, rfl⟩

/-- Above one, downward rounding never exceeds its real input. -/
-- @node: dyadicFloor_le
lemma dyadicFloor_le (z : ℝ) (hz : 1 ≤ z) : (dyadicFloor z : ℝ) ≤ z := by
  have hf : ⌊z⌋₊ ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hz)
  have hp : (dyadicFloor z : ℝ) ≤ (⌊z⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hf
  exact hp.trans (Nat.floor_le (by linarith))

/-- Downward rounding loses less than a factor of two, including nonintegral inputs. -/
-- @node: lt_two_mul_dyadicFloor
lemma lt_two_mul_dyadicFloor (z : ℝ) : z < 2 * (dyadicFloor z : ℝ) := by
  have hn := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊z⌋₊
  have hz := Nat.lt_floor_add_one z
  have he : ⌊z⌋₊ + 1 ≤ 2 * dyadicFloor z := by
    simpa only [dyadicFloor, pow_succ, Nat.mul_comm] using Nat.succ_le_of_lt hn
  exact hz.trans_le (by exact_mod_cast he)

/-- The third-order rank is at most its sample size for a nonempty role. -/
-- @node: tunedQ_le_roleSize
lemma tunedQ_le_roleSize (m : ℕ) (hm : 1 ≤ m) : tunedQ m ≤ m := by
  exact_mod_cast dyadicFloor_le m (by exact_mod_cast hm)

/-- The third-order rank is at least half its sample size. -/
-- @node: roleSize_lt_two_mul_tunedQ
lemma roleSize_lt_two_mul_tunedQ (m : ℕ) : (m : ℝ) < 2 * (tunedQ m : ℝ) :=
  lt_two_mul_dyadicFloor m

/-- Downward dyadic rounding is monotone, so compatible pilot ranks stay below q. -/
-- @node: dyadicFloor_mono
lemma dyadicFloor_mono : Monotone dyadicFloor := by
  intro x y hxy
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.log_mono_right (Nat.floor_mono hxy))

/-- The upward dyadic rank bounds the unrounded bias--variance balancing scale. -/
-- @node: tunedL_rpow_lower
lemma tunedL_rpow_lower (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ (4 / 29 : ℝ) ≤ (tunedL m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have he : (2 : ℝ) ^ ((4 / 29 : ℝ) * Real.logb 2 m) =
      (m : ℝ) ^ (4 / 29 : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hmpos]
  rw [← he]
  simpa only [tunedL, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.le_ceil ((4 / 29 : ℝ) * Real.logb 2 m))

/-- Upward dyadic rounding increases the balancing scale by less than two. -/
-- @node: tunedL_rpow_upper
lemma tunedL_rpow_upper (m : ℕ) (hm : 1 ≤ m) :
    (tunedL m : ℝ) < 2 * (m : ℝ) ^ (4 / 29 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hx : 0 ≤ (4 / 29 : ℝ) * Real.logb 2 m := by
    exact mul_nonneg (by norm_num)
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast hm))
  have he : (2 : ℝ) ^ ((4 / 29 : ℝ) * Real.logb 2 m) =
      (m : ℝ) ^ (4 / 29 : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hmpos]
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (Nat.ceil_lt_add_one hx)
  simpa only [Real.rpow_add (by norm_num : (0 : ℝ) < 2), he, Real.rpow_one,
    mul_comm, tunedL, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using h

/-- The pilot input is well posed and bounded by m when log m is at least one. -/
-- @node: pilot_input_mem_Icc
lemma pilot_input_mem_Icc (m : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ Real.log m) :
    (m : ℝ) / Real.log m ∈ Set.Icc 1 (m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogpos : 0 < Real.log m := by linarith
  constructor
  · apply (le_div_iff₀ hlogpos).2
    simpa only [one_mul] using (Real.log_le_sub_one_of_pos hmpos).trans (by linarith)
  · exact div_le_self hmpos.le hlog

/-- Both unrounded pilot powers lie between one and the corresponding power of m. -/
-- @node: pilot_power_bounds
lemma pilot_power_bounds (m : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ Real.log m)
    (a : ℝ) (ha : 0 ≤ a) :
    1 ≤ ((m : ℝ) / Real.log m) ^ a ∧
      ((m : ℝ) / Real.log m) ^ a ≤ (m : ℝ) ^ a := by
  have h := pilot_input_mem_Icc m hm hlog
  exact ⟨by simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h.1 ha,
    Real.rpow_le_rpow (by linarith [h.1]) h.2 ha⟩

/-- The covariate pilot input is at most m, so the dyadic pilot rank is at most q. -/
-- @node: tunedMx_le_tunedQ
lemma tunedMx_le_tunedQ (m : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ Real.log m) :
    tunedMx m ≤ tunedQ m := by
  apply dyadicFloor_mono
  exact (pilot_power_bounds m hm hlog (10 / 13) (by norm_num)).2.trans
    (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hm : (1 : ℝ) ≤ m) (by norm_num : (10 / 13 : ℝ) ≤ 1))

/-- The outcome pilot fits below the initial outcome rank, as in equation (48). -/
-- @node: tunedMy_le_tunedL
lemma tunedMy_le_tunedL (m : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ Real.log m) :
    tunedMy m ≤ tunedL m := by
  have hp := pilot_power_bounds m hm hlog (1 / 13) (by norm_num)
  have h := (dyadicFloor_le _ hp.1).trans hp.2
  exact_mod_cast h.trans ((Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hm : (1 : ℝ) ≤ m) (by norm_num : (1 / 13 : ℝ) ≤ 4 / 29)).trans
    (tunedL_rpow_lower m hm))

/-- The band count recovers the exponent in the upward dyadic rounding. -/
-- @node: tunedT_eq_ceiling
lemma tunedT_eq_ceiling (m : ℕ) :
    tunedT m = ⌈(4 / 29 : ℝ) * Real.logb 2 m⌉₊ := by
  exact Nat.log_pow (by norm_num) _

/-- The initial outcome rank is exactly the power of two indexed by the band count. -/
-- @node: tunedL_eq_pow_tunedT
lemma tunedL_eq_pow_tunedT (m : ℕ) : tunedL m = 2 ^ tunedT m := by
  rw [tunedT_eq_ceiling]; rfl

/-- The final rank agrees with the multiband projection's required rank. -/
-- @node: tunedJ_eq_multiband_rank
lemma tunedJ_eq_multiband_rank (m : ℕ) :
    tunedJ m = 2 ^ tunedT m * tunedL m := by
  rw [← tunedL_eq_pow_tunedT, tunedJ, pow_two]

/-- The initial correction rank has ten times the initial outcome exponent. -/
-- @node: tunedK_eq_pow_tunedT
lemma tunedK_eq_pow_tunedT (m : ℕ) : tunedK m = 2 ^ (10 * tunedT m) := by
  rw [tunedK, tunedL_eq_pow_tunedT, ← pow_mul, Nat.mul_comm]

/-- The initial correction grid is large enough to contain the dyadic pilot grid. -/
-- @node: tunedMx_le_tunedK
lemma tunedMx_le_tunedK (m : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ Real.log m) :
    tunedMx m ≤ tunedK m := by
  have hp := pilot_power_bounds m hm hlog (10 / 13) (by norm_num)
  have hpilot := (dyadicFloor_le _ hp.1).trans hp.2
  have hscale : (m : ℝ) ^ (40 / 29 : ℝ) ≤ (tunedL m : ℝ) ^ 10 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ) ^ (4 / 29 : ℝ))
      (tunedL_rpow_lower m hm) 10
    rwa [← Real.rpow_mul_natCast (by positivity), show (4 / 29 : ℝ) * (10 : ℕ) = 40 / 29 by norm_num] at h
  have h := hpilot.trans ((Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hm : (1 : ℝ) ≤ m) (by norm_num : (10 / 13 : ℝ) ≤ 40 / 29)).trans hscale)
  exact_mod_cast h

/-- Dividing two dyadic ranks is exact when the denominator exponent is smaller. -/
-- @node: dyadic_quotient_eq
lemma dyadic_quotient_eq (a b : ℕ) (h : b ≤ a) :
    2 ^ a / 2 ^ b = 2 ^ (a - b) := by
  have he : a = (a - b) + b := by omega
  rw [he, pow_add, Nat.mul_div_cancel _ (by positivity)]
  congr 1
  omega

/-- Every sparse correction denominator is within the initial correction rank. -/
-- @node: tunedK_quotient_eq
lemma tunedK_quotient_eq (m t : ℕ) (ht : t ≤ tunedT m) :
    tunedK m / 2 ^ (5 * t) = 2 ^ (10 * tunedT m - 5 * t) := by
  rw [tunedK_eq_pow_tunedT]
  exact dyadic_quotient_eq _ _ (by omega)

/-- The maximum of two positive dyadic ranks is another dyadic rank. -/
-- @node: dyadic_max
lemma dyadic_max {a b : ℕ} (ha : Dyadic a) (hb : Dyadic b) : Dyadic (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

/-- Positive dyadic ranks are nested by divisibility whenever they are ordered. -/
-- @node: dyadic_dvd_of_le
lemma dyadic_dvd_of_le {a b : ℕ} (ha : Dyadic a) (hb : Dyadic b) (hab : a ≤ b) :
    a ∣ b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hab
  refine ⟨2 ^ (j - i), ?_⟩
  rw [← pow_add, Nat.add_sub_of_le hij]

/-- All correction ranks used by the tuned construction are positive dyadic integers. -/
-- @node: tunedKt_dyadic
lemma tunedKt_dyadic (m t : ℕ) (ht : t ≤ tunedT m) : Dyadic (tunedKt m t) := by
  by_cases hz : t = 0
  · simp only [tunedKt, if_pos hz]
    exact ⟨10 * tunedT m, tunedK_eq_pow_tunedT m⟩
  · simp only [tunedKt, if_neg hz]
    exact dyadic_max (dyadicFloor_dyadic _)
      ⟨10 * tunedT m - 5 * t, tunedK_quotient_eq m t ht⟩

/-- The initial band retains the initial correction rank. -/
-- @node: tunedKt_zero
lemma tunedKt_zero (m : ℕ) : tunedKt m 0 = tunedK m := by
  simp [tunedKt]

/-- Every tuned correction rank is at most the initial rank once the pilot rank is. -/
-- @node: tunedKt_le_tunedK
lemma tunedKt_le_tunedK (m t : ℕ) (hmx : tunedMx m ≤ tunedK m) :
    tunedKt m t ≤ tunedK m := by
  by_cases hz : t = 0
  · simp [tunedKt, hz]
  · simp only [tunedKt, if_neg hz]
    exact max_le hmx (Nat.div_le_self _ _)

/-- The operator allowance's finite maximum is exactly the initial correction rank. -/
-- @node: tunedKt_sup_eq
lemma tunedKt_sup_eq (m : ℕ) (hmx : tunedMx m ≤ tunedK m) :
    (Finset.range (tunedT m + 1)).sup (tunedKt m) = tunedK m := by
  apply le_antisymm
  · exact Finset.sup_le (fun t _ => tunedKt_le_tunedK m t hmx)
  · rw [← tunedKt_zero m]
    exact Finset.le_sup (f := tunedKt m) (by simp)

/-- The exact tuned operator allowance contains no band-count logarithm. -/
-- @node: tunedW_eq_initial_rank
lemma tunedW_eq_initial_rank (n : ℕ)
    (hn : roleSize n ≠ 0) (hmx : tunedMx (roleSize n) ≤ tunedK (roleSize n)) :
    tunedW n = (2 : ℝ) ^ 24 * ((roleSize n : ℝ)⁻¹ +
      (roleSize n : ℝ) ^ (-2 : ℤ) * (tunedL (roleSize n) : ℝ) ^ 10) := by
  simp only [tunedW, WAllow, if_neg hn, tunedKt_sup_eq _ hmx, tunedK, Nat.cast_pow]

/-- Even the sparsest correction grid has at least L^5 cells. -/
-- @node: tunedKt_ge_fifth_power
lemma tunedKt_ge_fifth_power (m t : ℕ) (ht : t ≤ tunedT m) :
    (tunedL m) ^ 5 ≤ tunedKt m t := by
  have hp : (tunedL m) ^ 5 = 2 ^ (5 * tunedT m) := by
    rw [tunedL_eq_pow_tunedT, ← pow_mul, Nat.mul_comm]
  by_cases hz : t = 0
  · rw [hz, tunedKt_zero, tunedK_eq_pow_tunedT, hp]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · rw [tunedKt, if_neg hz]
    apply le_trans _ (le_max_right _ _)
    rw [tunedK_quotient_eq m t ht, hp]
    exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Every sparse correction grid refines the pilot grid once the initial grid does. -/
-- @node: tunedMx_dvd_tunedKt
lemma tunedMx_dvd_tunedKt (m t : ℕ) (ht : t ≤ tunedT m)
    (hmx : tunedMx m ≤ tunedK m) : tunedMx m ∣ tunedKt m t := by
  apply dyadic_dvd_of_le (dyadicFloor_dyadic _) (tunedKt_dyadic m t ht)
  by_cases hz : t = 0
  · simpa only [hz, tunedKt_zero, tunedMx] using hmx
  · simp only [tunedKt, if_neg hz]
    exact le_max_left _ _

/-- All algebraic corrected-mean rank restrictions reduce to three scalar rank comparisons. -/
-- @node: tuned_meanRanks_of_comparisons
lemma tuned_meanRanks_of_comparisons (m : ℕ)
    (hmy : tunedMy m ≤ tunedL m) (hmx : tunedMx m ≤ tunedK m)
    (hq : tunedMx m ≤ tunedQ m) :
    MeanRanks (tunedMx m) (tunedMy m) (tunedK m) (tunedL m) (tunedT m)
      (tunedJ m) (tunedQ m) (tunedKt m) := by
  exact ⟨dyadicFloor_dyadic _, dyadicFloor_dyadic _,
    ⟨tunedT m, tunedL_eq_pow_tunedT m⟩,
    ⟨10 * tunedT m, tunedK_eq_pow_tunedT m⟩,
    dyadicFloor_dyadic _, tunedKt_dyadic m, tunedJ_eq_multiband_rank m,
    hmy, tunedKt_zero m, fun t ht => tunedMx_dvd_tunedKt m t ht hmx,
    dyadic_dvd_of_le (dyadicFloor_dyadic _) (dyadicFloor_dyadic _) hq⟩

/-- The concrete tuning satisfies every corrected-mean compatibility restriction. -/
-- @node: tuned_meanRanks
lemma tuned_meanRanks (m : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ Real.log m) :
    MeanRanks (tunedMx m) (tunedMy m) (tunedK m) (tunedL m) (tunedT m)
      (tunedJ m) (tunedQ m) (tunedKt m) := by
  exact tuned_meanRanks_of_comparisons m (tunedMy_le_tunedL m hm hlog)
    (tunedMx_le_tunedK m hm hlog) (tunedMx_le_tunedQ m hm hlog)

/-- Every nontrivial sample-size branch has log m at least one. -/
-- @node: one_le_log_of_three_le
lemma one_le_log_of_three_le (m : ℕ) (hm : 3 ≤ m) : 1 ≤ Real.log m := by
  apply (Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < m))).2
  exact (Real.exp_one_lt_three.le).trans (by exact_mod_cast hm)

/-- The frozen ranks satisfy all refinement restrictions at every nontrivial sample size. -/
-- @node: tuned_rank_compatibility
lemma tuned_rank_compatibility (m : ℕ) (hm : 3 ≤ m) :
    tunedMx m ≤ m ∧ tunedQ m ≤ m ∧
      MeanRanks (tunedMx m) (tunedMy m) (tunedK m) (tunedL m) (tunedT m)
        (tunedJ m) (tunedQ m) (tunedKt m) := by
  have hlog := one_le_log_of_three_le m hm
  have hmone : 1 ≤ m := by omega
  have hq := tunedQ_le_roleSize m hmone
  exact ⟨(tunedMx_le_tunedQ m hmone hlog).trans hq, hq,
    tuned_meanRanks m hmone hlog⟩

/-- The operator allowance obeys the strict smaller-order rate in equation (53). -/
-- @node: tunedW_role_rate_bound
lemma tunedW_role_rate_bound (n : ℕ) (hn : 3 ≤ roleSize n) :
    tunedW n ≤ ((2 : ℝ) ^ 24 * 1025) *
      (roleSize n : ℝ) ^ (-18 / 29 : ℝ) := by
  let m := roleSize n
  have hm : 3 ≤ m := hn
  have hmone : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hl := (tunedL_rpow_upper m hmone).le
  have hl10 : (tunedL m : ℝ) ^ 10 ≤ 1024 * (m : ℝ) ^ (40 / 29 : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ tunedL m) hl 10
    rwa [mul_pow, ← Real.rpow_mul_natCast hmpos.le,
      show (4 / 29 : ℝ) * (10 : ℕ) = 40 / 29 by norm_num,
      show (2 : ℝ) ^ 10 = 1024 by norm_num] at h
  have hinv : (m : ℝ)⁻¹ ≤ (m : ℝ) ^ (-18 / 29 : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hmone) (by norm_num)
  have hprod : (m : ℝ) ^ (-2 : ℤ) * (m : ℝ) ^ (40 / 29 : ℝ) =
      (m : ℝ) ^ (-18 / 29 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hmpos]
    norm_num
  rw [tunedW_eq_initial_rank n (by omega)
    (tunedMx_le_tunedK m hmone (one_le_log_of_three_le m hm))]
  have hterm := mul_le_mul_of_nonneg_left hl10 (by positivity : 0 ≤ (m : ℝ) ^ (-2 : ℤ))
  change (2 : ℝ) ^ 24 * ((m : ℝ)⁻¹ + (m : ℝ) ^ (-2 : ℤ) * (tunedL m : ℝ) ^ 10) ≤ _
  have hreorder : (m : ℝ) ^ (-2 : ℤ) * (1024 * (m : ℝ) ^ (40 / 29 : ℝ)) =
      1024 * (m : ℝ) ^ (-18 / 29 : ℝ) := by
    rw [← mul_assoc, mul_comm ((m : ℝ) ^ (-2 : ℤ)) 1024, mul_assoc, hprod]
  rw [hreorder] at hterm
  nlinarith [Real.rpow_nonneg hmpos.le (-18 / 29 : ℝ)]

/-- Dropping the incomplete block costs at most a factor 26 once there is a complete block. -/
-- @node: sampleSize_le_twentySix_roleSize
lemma sampleSize_le_twentySix_roleSize (n : ℕ) (hn : 1 ≤ roleSize n) :
    n ≤ 26 * roleSize n := by
  have hrem := Nat.mod_lt n (by norm_num : 0 < 13)
  have hdecomp := Nat.div_add_mod n 13
  dsimp [roleSize] at hn ⊢
  omega

/-- The floor role-size conversion preserves every negative-power rate up to a fixed constant. -/
-- @node: roleSize_rpow_le_sampleSize_rpow
lemma roleSize_rpow_le_sampleSize_rpow (n : ℕ) (hn : 1 ≤ roleSize n)
    (a : ℝ) (ha : a ≤ 0) :
    (roleSize n : ℝ) ^ a ≤ (26 : ℝ) ^ (-a) * (n : ℝ) ^ a := by
  have hmpos : (0 : ℝ) < roleSize n := by exact_mod_cast (by omega : 0 < roleSize n)
  have hnpos : (0 : ℝ) < n := by
    have h := Nat.div_le_self n 13
    change roleSize n ≤ n at h
    exact_mod_cast (by omega : 0 < n)
  have hsize : (n : ℝ) / 26 ≤ roleSize n := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 26)).2
    rw [mul_comm]
    exact_mod_cast sampleSize_le_twentySix_roleSize n hn
  have h := Real.rpow_le_rpow_of_nonpos (div_pos hnpos (by norm_num)) hsize ha
  rw [Real.div_rpow hnpos.le (by norm_num), div_eq_mul_inv,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 26), mul_comm] at h
  exact h

/-- The operator allowance also fits the delivered sample-size rate, without logarithmic loss. -/
-- @node: tunedW_frontier_rate_bound
lemma tunedW_frontier_rate_bound (n : ℕ) (hn : 3 ≤ roleSize n) :
    tunedW n ≤ ((2 : ℝ) ^ 24 * 1025 * (26 : ℝ) ^ (16 / 29 : ℝ)) * frontierRate n := by
  have hmone : 1 ≤ roleSize n := by omega
  have hpower : (roleSize n : ℝ) ^ (-18 / 29 : ℝ) ≤
      (roleSize n : ℝ) ^ (-16 / 29 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hmone) (by norm_num)
  have hrole := roleSize_rpow_le_sampleSize_rpow n hmone (-16 / 29) (by norm_num)
  have hrole' : (roleSize n : ℝ) ^ (-16 / 29 : ℝ) ≤
      (26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n := by
    simpa only [neg_div, neg_neg, frontierRate] using hrole
  calc
    tunedW n ≤ ((2 : ℝ) ^ 24 * 1025) * (roleSize n : ℝ) ^ (-18 / 29 : ℝ) :=
      tunedW_role_rate_bound n hn
    _ ≤ ((2 : ℝ) ^ 24 * 1025) * ((26 : ℝ) ^ (16 / 29 : ℝ) * frontierRate n) :=
      mul_le_mul_of_nonneg_left (hpower.trans hrole') (by positivity)
    _ = _ := by ring

/-- The explicit inversion length budget reduces to the four component rates in (58). -/
-- @node: inversion_budget_le_components
lemma inversion_budget_le_components (B W V : ℝ) (J : ℕ) (hW : 0 ≤ W) :
    4 * ((aci B W) ^ 2 + dci B W V J) ≤
      120 * B ^ 2 + 500 * W + 1600 * (J : ℝ) ^ (-2 : ℤ) + 20 * Real.sqrt V := by
  have hs := Real.sq_sqrt hW
  have hcross := sq_nonneg (B - Real.sqrt W)
  dsimp [aci, dci]
  nlinarith

end CausalSmith.Stat.DensityEffectRoughNull
