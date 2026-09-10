/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TPhaseDiagram
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Divergence

/-!
# One-cell early-kill calibration

The concrete one-stratum design has density `2a`, a triangular width-`h`
Bernoulli regression perturbation, its exact integrated KL, and target separation.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set Topology

noncomputable section

/-- The concrete one-cell assignment density. -/
def oneCellDensity (a : ℝ) : ℝ := 2 * a
  -- @realizes pi_x(one-stratum calibration density pi(a)=2a)

/-- Unit triangular localization around the moving threshold. -/
def oneCellTent (delta h a : ℝ) : ℝ := max 0 (1 - |a - delta| / h)

/-- Null Bernoulli regression. -/
def oneCellRegression0 (_a : ℝ) : ℝ := 1 / 2

/-- Width-`h`, height-`h` localized Bernoulli alternative for beta one. -/
def oneCellRegression1 (delta h a : ℝ) : ℝ :=
  1 / 2 + h * oneCellTent delta h a

/-- Product KL of the concrete localized Bernoulli alternatives. -/
def oneCellProductKL (n : ℕ) (delta h : ℝ) : ℝ :=
  (n : ℝ) * ∫ a in Set.Icc (0 : ℝ) 1,
    (InformationTheory.klDiv
      (Causalean.Mathlib.Probability.bernoulliLaw (oneCellRegression1 delta h a))
      (Causalean.Mathlib.Probability.bernoulliLaw (oneCellRegression0 a))).toReal *
        oneCellDensity a

/-- Total clamp-target separation of the concrete one-cell pair: the retained-
course integral plus the collapsed-atom contribution. -/
def oneCellTargetSeparation (delta h : ℝ) : ℝ :=
  (∫ a in Set.Ioc delta 1,
      (oneCellRegression1 delta h a - oneCellRegression0 a) * oneCellDensity a) +
    (∫ a in Set.Icc (0 : ℝ) delta, oneCellDensity a) *
      (oneCellRegression1 delta h delta - oneCellRegression0 delta)

/-- On an interior right-hand localization window, the one-cell target
separation is the atom contribution plus the exact retained-course integral. The result uses [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hwindow` condition](hyp:hwindow). [This is the stated conclusion](goal).
-/
-- @node: oneCellTargetSeparation_eq
lemma oneCellTargetSeparation_eq (delta h : ℝ) (hdelta : 0 ≤ delta)
    (hh : 0 < h) (hwindow : delta + h ≤ 1) :
    oneCellTargetSeparation delta h =
      delta ^ 2 * h + delta * h ^ 2 + h ^ 3 / 3 := by
  have hsmall : Set.Ioc delta (delta + h) ⊆ Set.Ioc delta 1 := by
    intro a ha
    exact ⟨ha.1, ha.2.trans hwindow⟩
  have hcut : (∫ a in Set.Ioc delta 1,
      h * max 0 (1 - |a - delta| / h) * (2 * a)) =
      ∫ a in Set.Ioc delta (delta + h),
        h * max 0 (1 - |a - delta| / h) * (2 * a) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsmall
    intro a ha
    have had : delta ≤ a := ha.1.1.le
    have hha : h ≤ a - delta := by
      have : delta + h ≤ a :=
        le_of_not_gt (fun halt => ha.2 ⟨ha.1.1, halt.le⟩)
      linarith
    have : 1 - |a - delta| / h ≤ 0 := by
      rw [abs_of_nonneg (sub_nonneg.mpr had)]
      apply sub_nonpos.mpr
      exact (le_div_iff₀ hh).2 (by simpa using hha)
    simp [max_eq_left this]
  have hpoly : (∫ a in Set.Ioc delta (delta + h),
      h * max 0 (1 - |a - delta| / h) * (2 * a)) =
      ∫ a in Set.Ioc delta (delta + h),
        (2 * (delta + h) * a - 2 * a ^ 2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    have had : 0 ≤ a - delta := sub_nonneg.mpr ha.1.le
    have hratio : |a - delta| / h ≤ 1 := by
      rw [abs_of_nonneg had]
      exact (div_le_one hh).2 (by linarith [ha.2])
    rw [max_eq_right (sub_nonneg.mpr hratio), abs_of_nonneg had]
    field_simp
    ring
  have hint : (∫ a in Set.Ioc delta (delta + h),
      (2 * (delta + h) * a - 2 * a ^ 2)) =
      delta * h ^ 2 + h ^ 3 / 3 := by
    have hf : IntervalIntegrable
        (fun a : ℝ => 2 * (delta + h) * a) volume delta (delta + h) :=
      intervalIntegral.intervalIntegrable_id.const_mul _
    have hg : IntervalIntegrable (fun a : ℝ => 2 * a ^ 2)
        volume delta (delta + h) :=
      (intervalIntegral.intervalIntegrable_pow 2).const_mul _
    rw [← intervalIntegral.integral_of_le (by linarith : delta ≤ delta + h),
      intervalIntegral.integral_sub hf hg, intervalIntegral.integral_const_mul,
      integral_id, intervalIntegral.integral_const_mul, integral_pow]
    ring
  have hmass : (∫ a in Set.Icc (0 : ℝ) delta, 2 * a) = delta ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hdelta,
      intervalIntegral.integral_const_mul, integral_id]
    ring
  simp [oneCellTargetSeparation, oneCellRegression1, oneCellRegression0,
    oneCellTent, oneCellDensity]
  rw [hcut, hpoly, hint, hmass]
  ring

/-- The squared triangular perturbation has an exact design-weighted mass on
an interior localization window. The result uses [the `hh` condition](hyp:hh), [the `hleft` condition](hyp:hleft), [the `hright` condition](hyp:hright). [This is the stated conclusion](goal).
-/
-- @node: oneCellTentSqIntegral_eq
lemma oneCellTentSqIntegral_eq (delta h : ℝ) (hh : 0 < h)
    (hleft : h ≤ delta) (hright : delta + h ≤ 1) :
    (∫ a in Set.Icc (0 : ℝ) 1,
      (h * oneCellTent delta h a) ^ 2 * oneCellDensity a) =
      (4 / 3 : ℝ) * delta * h ^ 3 := by
  have hdelta : 0 ≤ delta := hh.le.trans hleft
  have hdh : 0 ≤ delta - h := sub_nonneg.mpr hleft
  have hsub : Set.Ioc (delta - h) (delta + h) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro a ha
    exact ⟨hdh.trans ha.1.le, ha.2.trans hright⟩
  have hcut : (∫ a in Set.Icc (0 : ℝ) 1,
      (h * oneCellTent delta h a) ^ 2 * oneCellDensity a) =
      ∫ a in Set.Ioc (delta - h) (delta + h),
        (h * oneCellTent delta h a) ^ 2 * oneCellDensity a := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub
    intro a ha
    have hout : h ≤ |a - delta| := by
      by_cases had : a ≤ delta
      · rw [abs_of_nonpos (sub_nonpos.mpr had)]
        have : a ≤ delta - h := le_of_not_gt fun halt => ha.2 ⟨halt, by linarith⟩
        linarith
      · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge had))]
        have : delta + h ≤ a := le_of_not_gt fun halt => ha.2 ⟨by linarith, halt.le⟩
        linarith
    have hzero : 1 - |a - delta| / h ≤ 0 := by
      exact sub_nonpos.mpr ((le_div_iff₀ hh).2 (by simpa using hout))
    simp [oneCellTent, max_eq_left hzero]
  rw [hcut]
  rw [← intervalIntegral.integral_of_le (by linarith : delta - h ≤ delta + h)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := delta)]
  · have hleftEq : (∫ a in delta - h..delta,
        (h * oneCellTent delta h a) ^ 2 * oneCellDensity a) =
        ∫ a in delta - h..delta, 2 * a * (a - delta + h) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro a ha
      have habounds : a ∈ Set.Icc (delta - h) delta := by
        simpa [uIcc_of_le (by linarith : delta - h ≤ delta)] using ha
      have had : a ≤ delta := habounds.2
      have hratio : |a - delta| / h ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr had)]
        exact (div_le_one hh).2 (by linarith [habounds.1])
      simp only [oneCellTent, oneCellDensity, max_eq_right (sub_nonneg.mpr hratio)]
      rw [abs_of_nonpos (sub_nonpos.mpr had)]
      field_simp
      ring
    have hrightEq : (∫ a in delta..delta + h,
        (h * oneCellTent delta h a) ^ 2 * oneCellDensity a) =
        ∫ a in delta..delta + h, 2 * a * (delta + h - a) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro a ha
      have habounds : a ∈ Set.Icc delta (delta + h) := by
        simpa [uIcc_of_le (by linarith : delta ≤ delta + h)] using ha
      have had : delta ≤ a := habounds.1
      have hratio : |a - delta| / h ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr had)]
        exact (div_le_one hh).2 (by linarith [habounds.2])
      simp only [oneCellTent, oneCellDensity, max_eq_right (sub_nonneg.mpr hratio)]
      rw [abs_of_nonneg (sub_nonneg.mpr had)]
      field_simp
      ring
    rw [hleftEq, hrightEq]
    simp_rw [show (fun a : ℝ => 2 * a * (a - delta + h) ^ 2) =
        fun a => 2 * a ^ 3 + (4 * (h - delta)) * a ^ 2 +
          (2 * (h - delta) ^ 2) * a by funext a; ring]
    simp_rw [show (fun a : ℝ => 2 * a * (delta + h - a) ^ 2) =
        fun a => 2 * a ^ 3 - (4 * (delta + h)) * a ^ 2 +
          (2 * (delta + h) ^ 2) * a by funext a; ring]
    have hpolyInt (a b A B C : ℝ) :
        (∫ x in a..b, A * x ^ 3 + B * x ^ 2 + C * x) =
          A * ((b ^ 4 - a ^ 4) / 4) +
            B * ((b ^ 3 - a ^ 3) / 3) + C * ((b ^ 2 - a ^ 2) / 2) := by
      have h3 := (intervalIntegral.intervalIntegrable_pow 3
        (μ := volume) (a := a) (b := b)).const_mul A
      have h2 := (intervalIntegral.intervalIntegrable_pow 2
        (μ := volume) (a := a) (b := b)).const_mul B
      have h1 := (intervalIntegral.intervalIntegrable_id
        (μ := volume) (a := a) (b := b)).const_mul C
      rw [intervalIntegral.integral_add (h3.add h2) h1,
        intervalIntegral.integral_add h3 h2,
        intervalIntegral.integral_const_mul, integral_pow,
        intervalIntegral.integral_const_mul, integral_pow,
        intervalIntegral.integral_const_mul, integral_id]
      norm_num
    rw [hpolyInt]
    have hrightPoly : (∫ a in delta..delta + h,
        2 * a ^ 3 - 4 * (delta + h) * a ^ 2 + 2 * (delta + h) ^ 2 * a) =
        2 * (((delta + h) ^ 4 - delta ^ 4) / 4) +
          (-4 * (delta + h)) * (((delta + h) ^ 3 - delta ^ 3) / 3) +
          (2 * (delta + h) ^ 2) * (((delta + h) ^ 2 - delta ^ 2) / 2) := by
      calc
        _ = ∫ a in delta..delta + h,
            2 * a ^ 3 + (-4 * (delta + h)) * a ^ 2 +
              (2 * (delta + h) ^ 2) * a := by
                apply intervalIntegral.integral_congr
                intro a ha
                ring
        _ = _ := hpolyInt delta (delta + h) 2 (-4 * (delta + h))
          (2 * (delta + h) ^ 2)
    rw [hrightPoly]
    ring
  · exact (by
      unfold oneCellTent oneCellDensity
      fun_prop : Continuous (fun a : ℝ =>
        (h * oneCellTent delta h a) ^ 2 * oneCellDensity a)).intervalIntegrable _ _
  · exact (by
      unfold oneCellTent oneCellDensity
      fun_prop : Continuous (fun a : ℝ =>
        (h * oneCellTent delta h a) ^ 2 * oneCellDensity a)).intervalIntegrable _ _

/-- Above the one-cell edge scale, the balance bandwidth is comparable to the
interior bandwidth and its localization window is eventually interior. The result uses [the `hdeltaBar` condition](hyp:hdeltaBar), [the `hdelta` condition](hyp:hdelta), [the `hfar` condition](hyp:hfar). [This is the stated conclusion](goal).
-/
-- @node: oneCellBandwidth_far
lemma oneCellBandwidth_far (deltaBar : ℝ)
    (hdeltaBar : 0 < deltaBar ∧ deltaBar < 1)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hfar : Tendsto (fun n => deltaSeq n / (n : ℝ) ^ (-(1 : ℝ) / 4))
      atTop atTop) :
    let hSeq := fun n => infoBandwidth n (deltaSeq n) 1 1 deltaBar
    AsympSeq hSeq (fun n => ((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3)) ∧
      ∀ᶠ n in atTop, 0 < hSeq n ∧ hSeq n ≤ deltaSeq n ∧
        deltaSeq n + hSeq n ≤ 1 ∧ hSeq n ≤ 1 / 4 := by
  dsimp
  have hbalance := infoBandwidth_eventually_balance 1 1 deltaBar (by norm_num)
    (by norm_num) hdeltaBar deltaSeq hdelta
  let c : ℝ := 2 ^ (-(1 : ℝ) / 3)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hcOne : c ≤ 1 := by
    rw [show (1 : ℝ) = 2 ^ (0 : ℝ) by norm_num]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  have hratio := (Filter.tendsto_atTop.1 hfar) 1
  have hevent : ∀ᶠ n in atTop,
      0 < infoBandwidth n (deltaSeq n) 1 1 deltaBar ∧
      infoBandwidth n (deltaSeq n) 1 1 deltaBar ≤ deltaSeq n ∧
      deltaSeq n + infoBandwidth n (deltaSeq n) 1 1 deltaBar ≤ 1 ∧
      infoBandwidth n (deltaSeq n) 1 1 deltaBar ≤ 1 / 4 ∧
      c * (((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3)) ≤
        infoBandwidth n (deltaSeq n) 1 1 deltaBar ∧
      infoBandwidth n (deltaSeq n) 1 1 deltaBar ≤
        ((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3) := by
    filter_upwards [hbalance, hratio, eventually_ge_atTop 257] with n hn hratioN hn257
    have hnpos : 0 < (n : ℝ) := by
      by_contra hn0
      have hnzero : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn0) (Nat.cast_nonneg n)
      rw [hnzero, zero_mul] at hn
      norm_num at hn
    have hedgePos : 0 < (n : ℝ) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos hnpos _
    have hdeltaPos : 0 < deltaSeq n := by
      have hle : (n : ℝ) ^ (-(1 : ℝ) / 4) ≤ deltaSeq n := by
        simpa using (le_div_iff₀ hedgePos).mp hratioN
      exact hedgePos.trans_le hle
    let h := infoBandwidth n (deltaSeq n) 1 1 deltaBar
    let w := ((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3)
    have hedge : (n : ℝ) ^ (-1 / ((3 : ℝ) + 1)) ≤ deltaSeq n := by
      have hbase : (n : ℝ) ^ (-(1 : ℝ) / 4) ≤ deltaSeq n := by
        simpa using (le_div_iff₀ hedgePos).mp hratioN
      convert hbase using 1 <;> norm_num
    have hwUpper : h ≤ w := by
      simpa [w, Real.rpow_one] using
        balance_root_le_interior_scale (n : ℝ) (deltaSeq n) h 3 1 hnpos
        hdeltaPos hn.1 (by norm_num) (by norm_num)
        (by norm_num [h, Real.rpow_natCast] at hn ⊢; simpa using hn.2.2)
    have hwDelta : w ≤ deltaSeq n := by
      simpa [w, Real.rpow_one] using
        interior_scale_le_threshold_of_edge_le (n : ℝ) (deltaSeq n) 3 1
        hnpos hdeltaPos (by norm_num) (by norm_num) hedge
    have hwLower : c * w ≤ h := by
      simpa [c, w, Real.rpow_one] using
        interior_scale_le_balance_root (n : ℝ) (deltaSeq n) h 3 1 hnpos
        hdeltaPos hn.1 (by norm_num) (by norm_num) (hwUpper.trans hwDelta)
        (by norm_num [h, Real.rpow_natCast] at hn ⊢; simpa using hn.2.2)
    have hwindow : deltaSeq n + h ≤ 1 :=
      (add_le_add (hdelta n).2 hn.2.1).trans_eq (by ring)
    have hhquarter : h ≤ 1 / 4 := by
      by_contra hnot
      have hhlarge : (1 : ℝ) / 4 < h := lt_of_not_ge hnot
      have hEq : (n : ℝ) * h ^ 3 * (deltaSeq n + h) = 1 := by
        norm_num [h, Real.rpow_natCast, Real.rpow_one] at hn ⊢
        simpa using hn.2.2
      have hstrict : 1 < (n : ℝ) * h ^ 3 * h := by
        calc
          1 = (256 : ℝ) * ((1 : ℝ) / 4) ^ 3 * ((1 : ℝ) / 4) := by norm_num
          _ < (n : ℝ) * h ^ 3 * h := by
            gcongr
            · exact_mod_cast hn257
      have : (n : ℝ) * h ^ 3 * h ≤ (n : ℝ) * h ^ 3 * (deltaSeq n + h) := by
        gcongr
        linarith [(hdelta n).1]
      linarith
    refine ⟨hn.1, hwUpper.trans hwDelta, hwindow, hhquarter, hwLower, hwUpper⟩
  constructor
  · exact ⟨c, 1, hc, hcOne, hevent.mono fun n hn =>
      ⟨hn.2.2.2.2.1, by simpa using hn.2.2.2.2.2⟩⟩
  · exact hevent.mono fun n hn => ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩

/-- On an interior quarter-height window, the concrete product KL is trapped
between fixed multiples of `n * delta * h^3`. The result uses [the `hh` condition](hyp:hh), [the `hleft` condition](hyp:hleft), [the `hright` condition](hyp:hright), [the `hquarter` condition](hyp:hquarter). [This is the stated conclusion](goal).
-/
-- @node: oneCellProductKL_bounds
lemma oneCellProductKL_bounds (n : ℕ) (delta h : ℝ) (hh : 0 < h)
    (hleft : h ≤ delta) (hright : delta + h ≤ 1) (hquarter : h ≤ 1 / 4) :
    (8 / 3 : ℝ) * (n : ℝ) * delta * h ^ 3 ≤ oneCellProductKL n delta h ∧
      oneCellProductKL n delta h ≤ (16 / 3 : ℝ) * (n : ℝ) * delta * h ^ 3 := by
  let gamma : ℝ → ℝ := fun a => h * oneCellTent delta h a
  have htent : ∀ a, oneCellTent delta h a ∈ Set.Icc (0 : ℝ) 1 := by
    intro a
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      have : 0 ≤ |a - delta| / h := div_nonneg (abs_nonneg _) hh.le
      linarith
  have hgamma0 : ∀ a, 0 ≤ gamma a := fun a => mul_nonneg hh.le (htent a).1
  have hgammah : ∀ a, gamma a ≤ h := fun a => by
    dsimp [gamma]
    simpa using mul_le_mul_of_nonneg_left (htent a).2 hh.le
  have hgamma_meas : Measurable gamma := by
    dsimp [gamma]
    unfold oneCellTent
    fun_prop
  have hkl_meas : Measurable fun a =>
      (InformationTheory.klDiv
        (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
        (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal := by
    have hform : (fun a =>
        (InformationTheory.klDiv
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal) =
        fun a => (1 / 2 + gamma a) * Real.log ((1 / 2 + gamma a) / (1 / 2)) +
          (1 - (1 / 2 + gamma a)) *
            Real.log ((1 - (1 / 2 + gamma a)) / (1 - (1 / 2))) := by
      funext a
      apply Causalean.Mathlib.Probability.bernoulliLaw_klDiv_toReal
      · linarith [hgamma0 a]
      · linarith [hgammah a]
      · norm_num
      · norm_num
    rw [hform]
    fun_prop
  have hpi_int : Integrable oneCellDensity
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply IntegrableOn.of_bound (C := 2) measure_Icc_lt_top
    · unfold oneCellDensity
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      change |2 * a| ≤ 2
      rw [abs_of_nonneg (mul_nonneg (by norm_num) ha.1)]
      nlinarith [ha.2]
  have hband := localized_design_kl_band oneCellDensity gamma hpi_int
    hgamma_meas hkl_meas
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
        exact mul_nonneg (by norm_num) ha.1)
    (fun a ha => by
      rw [abs_of_nonneg (hgamma0 a)]
      exact (hgammah a).trans hquarter)
  have hsquare := oneCellTentSqIntegral_eq delta h hh hleft hright
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor
  · rw [oneCellProductKL]
    change (8 / 3 : ℝ) * (n : ℝ) * delta * h ^ 3 ≤
      (n : ℝ) * ∫ a in Set.Icc (0 : ℝ) 1,
        (InformationTheory.klDiv
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal *
            oneCellDensity a
    calc
      (8 / 3 : ℝ) * (n : ℝ) * delta * h ^ 3 =
          (n : ℝ) * (2 * ((4 / 3 : ℝ) * delta * h ^ 3)) := by ring
      _ = (n : ℝ) * (2 * ∫ a in Set.Icc (0 : ℝ) 1,
          (gamma a) ^ 2 * oneCellDensity a) := by rw [hsquare]
      _ ≤ _ := mul_le_mul_of_nonneg_left hband.1 hn0
  · rw [oneCellProductKL]
    change (n : ℝ) * ∫ a in Set.Icc (0 : ℝ) 1,
        (InformationTheory.klDiv
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2 + gamma a))
          (Causalean.Mathlib.Probability.bernoulliLaw (1 / 2))).toReal *
            oneCellDensity a ≤ (16 / 3 : ℝ) * (n : ℝ) * delta * h ^ 3
    calc
      _ ≤ (n : ℝ) * (4 * ∫ a in Set.Icc (0 : ℝ) 1,
          (gamma a) ^ 2 * oneCellDensity a) :=
        mul_le_mul_of_nonneg_left hband.2 hn0
      _ = (16 / 3 : ℝ) * (n : ℝ) * delta * h ^ 3 := by rw [hsquare]; ring

/-- The normalized interior one-cell atom scale is the `5/3` power of the
threshold measured in critical-scale units. The result uses [the `hn` condition](hyp:hn), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: oneCellNormalizedScale_eq
lemma oneCellNormalizedScale_eq (n : ℕ) (delta : ℝ) (hn : 0 < n)
    (hdelta : 0 < delta) :
    (delta ^ 2 * ((n : ℝ) * delta) ^ (-(1 : ℝ) / 3)) /
        (n : ℝ) ^ (-(1 : ℝ) / 2) =
      (delta / (n : ℝ) ^ (-(1 : ℝ) / 10)) ^ ((5 : ℝ) / 3) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcrit : 0 < (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_pos_of_pos hnR _
  rw [Real.div_rpow hdelta.le hcrit.le, Real.mul_rpow hnR.le hdelta.le]
  rw [show delta ^ 2 * ((n : ℝ) ^ (-(1 : ℝ) / 3) *
      delta ^ (-(1 : ℝ) / 3)) =
      (n : ℝ) ^ (-(1 : ℝ) / 3) *
        (delta ^ 2 * delta ^ (-(1 : ℝ) / 3)) by ring]
  rw [show delta ^ 2 = delta ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
  rw [← Real.rpow_add hdelta, ← Real.rpow_mul hnR.le]
  field_simp
  norm_num
  rw [show (n : ℝ) ^ (-(1 / 3 : ℝ)) * delta ^ ((5 : ℝ) / 3) *
      (n : ℝ) ^ (-(1 / 6 : ℝ)) =
      delta ^ ((5 : ℝ) / 3) * ((n : ℝ) ^ (-(1 / 3 : ℝ)) *
        (n : ℝ) ^ (-(1 / 6 : ℝ))) by ring]
  rw [← Real.rpow_add hnR]
  norm_num
  ring

/-- For beta=kappa=one, the bandwidth, KL, separation, and transition exponent
are exactly the one-cell calibration stated in the note. The result uses [the `hdeltaBar` condition](hyp:hdeltaBar), [the `hdelta` condition](hyp:hdelta), [the `hfar` condition](hyp:hfar). [This is the stated conclusion](goal).
-/
-- @node: prop:one-cell-calibration
theorem one_cell_calibration (deltaBar : ℝ)
    (hdeltaBar : 0 < deltaBar ∧ deltaBar < 1)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hfar : Tendsto (fun n => deltaSeq n / (n : ℝ) ^ (-(1 : ℝ) / 4))
      atTop atTop) :
    let hSeq := fun n => infoBandwidth n (deltaSeq n) 1 1 deltaBar
    AsympSeq hSeq (fun n => ((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3)) ∧
    AsympSeq (fun n => oneCellProductKL n (deltaSeq n) (hSeq n))
      (fun n => (n : ℝ) * deltaSeq n * (hSeq n) ^ 3) ∧
    AsympSeq (fun n => oneCellTargetSeparation (deltaSeq n) (hSeq n))
      (fun n => (deltaSeq n) ^ 2 * hSeq n) ∧
    (AsympSeq deltaSeq (fun n => (n : ℝ) ^ (-(1 : ℝ) / 10)) ↔
      AsympSeq (fun n => oneCellTargetSeparation (deltaSeq n) (hSeq n))
        (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2))) := by
  dsimp
  have hb := oneCellBandwidth_far deltaBar hdeltaBar deltaSeq hdelta hfar
  have hbw := hb.1
  have hwin := hb.2
  refine ⟨hbw, ?_, ?_, ?_⟩
  · refine ⟨8 / 3, 16 / 3, by norm_num, by norm_num, ?_⟩
    filter_upwards [hwin] with n hn
    simpa [mul_assoc] using oneCellProductKL_bounds n (deltaSeq n)
      (infoBandwidth n (deltaSeq n) 1 1 deltaBar) hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  · refine ⟨1, 7 / 3, by norm_num, by norm_num, ?_⟩
    filter_upwards [hwin] with n hn
    have hdelta0 : 0 ≤ deltaSeq n := hn.1.le.trans hn.2.1
    have heq := oneCellTargetSeparation_eq (deltaSeq n)
      (infoBandwidth n (deltaSeq n) 1 1 deltaBar) hdelta0 hn.1 hn.2.2.1
    rw [heq]
    constructor
    · nlinarith [sq_nonneg (deltaSeq n),
        sq_nonneg (infoBandwidth n (deltaSeq n) 1 1 deltaBar)]
    · have hh0 : 0 ≤ infoBandwidth n (deltaSeq n) 1 1 deltaBar := hn.1.le
      have hh_le : infoBandwidth n (deltaSeq n) 1 1 deltaBar ≤ deltaSeq n := hn.2.1
      nlinarith [mul_nonneg (sq_nonneg (infoBandwidth n (deltaSeq n) 1 1 deltaBar))
        (sub_nonneg.mpr hh_le),
        mul_nonneg (sq_nonneg (deltaSeq n)) (sub_nonneg.mpr hh_le)]
  · rcases hbw with ⟨ch, Ch, hch, hchCh, hbwEv⟩
    have hscale : ∀ᶠ n in atTop,
        ch * (deltaSeq n ^ 2 *
            (((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3))) ≤
          oneCellTargetSeparation (deltaSeq n)
            (infoBandwidth n (deltaSeq n) 1 1 deltaBar) ∧
        oneCellTargetSeparation (deltaSeq n)
            (infoBandwidth n (deltaSeq n) 1 1 deltaBar) ≤
          ((7 / 3 : ℝ) * Ch) * (deltaSeq n ^ 2 *
            (((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3))) := by
      filter_upwards [hwin, hbwEv] with n hn hbn
      let h := infoBandwidth n (deltaSeq n) 1 1 deltaBar
      let w := ((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3)
      have hd0 : 0 ≤ deltaSeq n := hn.1.le.trans hn.2.1
      have heq := oneCellTargetSeparation_eq (deltaSeq n) h hd0 hn.1 hn.2.2.1
      have htargetLo : deltaSeq n ^ 2 * h ≤
          oneCellTargetSeparation (deltaSeq n) h := by
        rw [heq]
        nlinarith [sq_nonneg (deltaSeq n), sq_nonneg h]
      have htargetHi : oneCellTargetSeparation (deltaSeq n) h ≤
          (7 / 3 : ℝ) * (deltaSeq n ^ 2 * h) := by
        rw [heq]
        have hh0 : 0 ≤ h := hn.1.le
        have hh_le : h ≤ deltaSeq n := hn.2.1
        nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh_le),
          mul_nonneg (sq_nonneg (deltaSeq n)) (sub_nonneg.mpr hh_le)]
      have hsq0 : 0 ≤ deltaSeq n ^ 2 := sq_nonneg _
      constructor
      · calc
          ch * (deltaSeq n ^ 2 * w) = deltaSeq n ^ 2 * (ch * w) := by ring
          _ ≤ deltaSeq n ^ 2 * h :=
            mul_le_mul_of_nonneg_left hbn.1 hsq0
          _ ≤ _ := htargetLo
      · calc
          _ ≤ (7 / 3 : ℝ) * (deltaSeq n ^ 2 * h) := htargetHi
          _ ≤ (7 / 3 : ℝ) * (deltaSeq n ^ 2 * (Ch * w)) := by
            gcongr
            exact hbn.2
          _ = ((7 / 3 : ℝ) * Ch) * (deltaSeq n ^ 2 * w) := by ring
    constructor
    · rintro ⟨cd, Cd, hcd, hcdC, hdEv⟩
      let cOut : ℝ := ch * cd ^ ((5 : ℝ) / 3)
      let COut : ℝ := ((7 / 3 : ℝ) * Ch) * Cd ^ ((5 : ℝ) / 3)
      have hCd : 0 < Cd := hcd.trans_le hcdC
      have hCh : 0 < Ch := hch.trans_le hchCh
      have hcOut : 0 < cOut := mul_pos hch (Real.rpow_pos_of_pos hcd _)
      have hCOut : 0 < COut := by
        dsimp [COut]
        exact mul_pos (mul_pos (by norm_num) hCh) (Real.rpow_pos_of_pos hCd _)
      have hcC : cOut ≤ COut := by
        dsimp [cOut, COut]
        have : ch ≤ (7 / 3 : ℝ) * Ch := by nlinarith
        gcongr
      refine ⟨cOut, COut, hcOut, hcC, ?_⟩
      filter_upwards [hscale, hdEv, hwin, eventually_ge_atTop 1] with n hs hd hwn hn1
      have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hnPos
      have hdPos : 0 < deltaSeq n := hwn.1.trans_le hwn.2.1
      have hcrit : 0 < (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_pos_of_pos hnR _
      have hroot : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
      let ratio := deltaSeq n / (n : ℝ) ^ (-(1 : ℝ) / 10)
      let atom := deltaSeq n ^ 2 * (((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3))
      have hratioLo : cd ≤ ratio := by
        exact (le_div_iff₀ hcrit).2 (by simpa [ratio, mul_comm] using hd.1)
      have hratioHi : ratio ≤ Cd := by
        exact (div_le_iff₀ hcrit).2 (by simpa [ratio, mul_comm] using hd.2)
      have hnorm : atom / (n : ℝ) ^ (-(1 : ℝ) / 2) = ratio ^ ((5 : ℝ) / 3) := by
        simpa [atom, ratio] using oneCellNormalizedScale_eq n (deltaSeq n) hnPos hdPos
      have hatom : atom = ratio ^ ((5 : ℝ) / 3) *
          (n : ℝ) ^ (-(1 : ℝ) / 2) := (div_eq_iff hroot.ne').mp hnorm
      have hpowLo := Real.rpow_le_rpow hcd.le hratioLo (by norm_num : (0 : ℝ) ≤ 5 / 3)
      have hpowHi := Real.rpow_le_rpow (le_trans hcd.le hratioLo) hratioHi
        (by norm_num : (0 : ℝ) ≤ 5 / 3)
      constructor
      · calc
          cOut * (n : ℝ) ^ (-(1 : ℝ) / 2) =
              ch * (cd ^ ((5 : ℝ) / 3) * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
                simp [cOut]; ring
          _ ≤ ch * atom := by rw [hatom]; gcongr
          _ ≤ _ := hs.1
      · calc
          _ ≤ ((7 / 3 : ℝ) * Ch) * atom := hs.2
          _ ≤ ((7 / 3 : ℝ) * Ch) *
              (Cd ^ ((5 : ℝ) / 3) * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
                rw [hatom]
                gcongr
          _ = COut * (n : ℝ) ^ (-(1 : ℝ) / 2) := by simp [COut]; ring
    · rintro ⟨cs, Cs, hcs, hcsC, hsEv⟩
      let K : ℝ := (7 / 3 : ℝ) * Ch
      have hCh : 0 < Ch := hch.trans_le hchCh
      have hK : 0 < K := mul_pos (by norm_num) hCh
      let lo : ℝ := (cs / K) ^ ((3 : ℝ) / 5)
      let up : ℝ := (Cs / ch) ^ ((3 : ℝ) / 5)
      have hCs : 0 < Cs := hcs.trans_le hcsC
      have hlo : 0 < lo := Real.rpow_pos_of_pos (div_pos hcs hK) _
      have hup : 0 < up := Real.rpow_pos_of_pos (div_pos hCs hch) _
      refine ⟨lo, lo + up, hlo, le_add_of_nonneg_right hup.le, ?_⟩
      filter_upwards [hscale, hsEv, hwin, eventually_ge_atTop 1] with n hscaleN hsN hwn hn1
      have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hnPos
      have hdPos : 0 < deltaSeq n := hwn.1.trans_le hwn.2.1
      have hcrit : 0 < (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_pos_of_pos hnR _
      have hroot : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
      let ratio := deltaSeq n / (n : ℝ) ^ (-(1 : ℝ) / 10)
      let atom := deltaSeq n ^ 2 * (((n : ℝ) * deltaSeq n) ^ (-(1 : ℝ) / 3))
      have hratio : 0 < ratio := div_pos hdPos hcrit
      have hnorm : atom / (n : ℝ) ^ (-(1 : ℝ) / 2) = ratio ^ ((5 : ℝ) / 3) := by
        simpa [atom, ratio] using oneCellNormalizedScale_eq n (deltaSeq n) hnPos hdPos
      have hatom : atom = ratio ^ ((5 : ℝ) / 3) *
          (n : ℝ) ^ (-(1 : ℝ) / 2) := (div_eq_iff hroot.ne').mp hnorm
      have hpLo : cs / K ≤ ratio ^ ((5 : ℝ) / 3) := by
        apply (div_le_iff₀ hK).2
        have hmul := hsN.1.trans (by simpa [K] using hscaleN.2)
        change cs * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ K * atom at hmul
        rw [hatom] at hmul
        nlinarith
      have hpHi : ratio ^ ((5 : ℝ) / 3) ≤ Cs / ch := by
        apply (le_div_iff₀ hch).2
        have hmul := hscaleN.1.trans hsN.2
        change ch * atom ≤ Cs * (n : ℝ) ^ (-(1 : ℝ) / 2) at hmul
        rw [hatom] at hmul
        nlinarith
      have hloRatio : lo ≤ ratio := by
        have hp := Real.rpow_le_rpow (div_nonneg hcs.le hK.le) hpLo
          (by norm_num : (0 : ℝ) ≤ 3 / 5)
        have hcollapse : (ratio ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) = ratio := by
          rw [← Real.rpow_mul hratio.le]
          norm_num
        simpa [lo, hcollapse] using hp
      have hratioUp : ratio ≤ up := by
        have hp := Real.rpow_le_rpow (Real.rpow_nonneg hratio.le _) hpHi
          (by norm_num : (0 : ℝ) ≤ 3 / 5)
        have hcollapse : (ratio ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) = ratio := by
          rw [← Real.rpow_mul hratio.le]
          norm_num
        simpa [up, hcollapse] using hp
      constructor
      · exact (le_div_iff₀ hcrit).mp (by simpa [ratio, mul_comm] using hloRatio)
      · have hdu : deltaSeq n ≤ up * (n : ℝ) ^ (-(1 : ℝ) / 10) :=
          (div_le_iff₀ hcrit).mp (by simpa [ratio] using hratioUp)
        exact hdu.trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hlo.le) hcrit.le)

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
