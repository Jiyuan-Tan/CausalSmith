import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Geometry
import Mathlib.Analysis.Calculus.LHopital

/-! # Consistency under an exponential horn -/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @node: exponentialModulus_integral_hasDerivAt
lemma exponentialModulus_integral_hasDerivAt (α h : ℝ) (hh : 0 < h) :
    HasDerivAt (fun h => ∫ u in (0:ℝ)..h, 2 * Real.exp (-(u ^ (-α))))
      (2 * Real.exp (-(h ^ (-α)))) h := by
  apply intervalIntegral.integral_hasDerivAt_right
  · rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne) (M := 2)
    · fun_prop
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with u hu
      have hu0 : 0 ≤ u := by
        simp [min_eq_left hh.le, max_eq_right hh.le] at hu
        exact hu.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have he : Real.exp (-(u ^ (-α))) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Real.rpow_nonneg hu0 _))
      linarith [Real.exp_pos (-(u ^ (-α)))]
  · apply ContinuousAt.stronglyMeasurableAtFilter (s := Ioi 0) isOpen_Ioi
    · intro x hx
      exact continuousAt_const.mul
        (Real.continuous_exp.continuousAt.comp
          (Real.continuousAt_rpow_const x (-α) (Or.inl (ne_of_gt hx))).neg)
    · exact hh
  · exact continuousAt_const.mul
      (Real.continuous_exp.continuousAt.comp
        (Real.continuousAt_rpow_const h (-α) (Or.inl (ne_of_gt hh))).neg)

-- @node: exponentialModulus_denominator_hasDerivAt
lemma exponentialModulus_denominator_hasDerivAt (α h : ℝ) (hh : 0 < h) :
    HasDerivAt ((fun x : ℝ => x ^ (α + 1)) *
        (Real.exp ∘ (- fun x : ℝ => x ^ (-α))))
      ((α + 1) * h ^ α * Real.exp (-(h ^ (-α))) +
        h ^ (α + 1) * (Real.exp (-(h ^ (-α))) * (α * h ^ (-α - 1)))) h := by
  have hhne : h ≠ 0 := ne_of_gt hh
  have he : HasDerivAt (- fun x : ℝ => x ^ (-α))
      (α * h ^ (-α - 1)) h := by
    simpa only [neg_mul, neg_neg] using
      (Real.hasDerivAt_rpow_const (x := h) (p := -α) (Or.inl hhne)).neg
  simpa only [Function.comp_apply, Pi.neg_apply, add_sub_cancel_right] using
    (Real.hasDerivAt_rpow_const (x := h) (p := α + 1) (Or.inl hhne)).mul
      ((Real.hasDerivAt_exp (-(h ^ (-α)))).comp h he)

-- @node: exponentialModulus_derivative_ratio
lemma exponentialModulus_derivative_ratio (α h : ℝ) (hh : 0 < h) :
    (2 * Real.exp (-(h ^ (-α)))) /
      ((α + 1) * h ^ α * Real.exp (-(h ^ (-α))) +
        h ^ (α + 1) * (Real.exp (-(h ^ (-α))) * (α * h ^ (-α - 1)))) =
      2 / ((α + 1) * h ^ α + α) := by
  field_simp [ne_of_gt (Real.exp_pos (-(h ^ (-α))))]
  have hcancel : h ^ (α + 1) * h ^ (-α - 1) = 1 := by
    rw [← Real.rpow_add hh]
    norm_num
  rw [mul_assoc α, hcancel, mul_one]

-- @node: exponentialModulus_ratio_tendsto
lemma exponentialModulus_ratio_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun h : ℝ =>
      (∫ u in (0:ℝ)..h, 2 * Real.exp (-(u ^ (-α)))) /
        (h ^ (α + 1) * Real.exp (-(h ^ (-α)))))
      (𝓝[>] 0) (𝓝 (2 / α)) := by
  let F : ℝ → ℝ := fun h => ∫ u in (0:ℝ)..h, 2 * Real.exp (-(u ^ (-α)))
  let G : ℝ → ℝ := (fun x : ℝ => x ^ (α + 1)) *
        (Real.exp ∘ (- fun x : ℝ => x ^ (-α)))
  let F' : ℝ → ℝ := fun h => 2 * Real.exp (-(h ^ (-α)))
  let G' : ℝ → ℝ := fun h =>
    (α + 1) * h ^ α * Real.exp (-(h ^ (-α))) +
      h ^ (α + 1) * (Real.exp (-(h ^ (-α))) * (α * h ^ (-α - 1)))
  have hFderiv : ∀ᶠ h in 𝓝[>] (0 : ℝ), HasDerivAt F (F' h) h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact exponentialModulus_integral_hasDerivAt α h hh
  have hGderiv : ∀ᶠ h in 𝓝[>] (0 : ℝ), HasDerivAt G (G' h) h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact exponentialModulus_denominator_hasDerivAt α h hh
  have hG' : ∀ᶠ h in 𝓝[>] (0 : ℝ), G' h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    have hpow : 0 < h ^ α := Real.rpow_pos_of_pos hh _
    have hexp : 0 < Real.exp (-(h ^ (-α))) := Real.exp_pos _
    have hsum : 0 < (α + 1) * h ^ α + α := by positivity
    have hcancel : h ^ (α + 1) * h ^ (-α - 1) = 1 := by
      rw [← Real.rpow_add hh]
      norm_num
    dsimp [G']
    have hform : (α + 1) * h ^ α * Real.exp (-(h ^ (-α))) +
        h ^ (α + 1) * (Real.exp (-(h ^ (-α))) * (α * h ^ (-α - 1))) =
        Real.exp (-(h ^ (-α))) * ((α + 1) * h ^ α + α) := by
      calc
        _ = Real.exp (-(h ^ (-α))) *
            ((α + 1) * h ^ α + α * (h ^ (α + 1) * h ^ (-α - 1))) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rw [hform]
    exact mul_ne_zero (ne_of_gt hexp) (ne_of_gt hsum)
  have hF0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (g := fun h : ℝ => 2 * h)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      change 0 < h at hh
      exact intervalIntegral.integral_nonneg hh.le (fun u _ => by positivity)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      change 0 < h at hh
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun u : ℝ => 2 * Real.exp (-(u ^ (-α)))) (a := 0) (b := h) (C := 2) (by
          intro u hu
          have hu0 : 0 ≤ u := by
            have hmin : min 0 h = 0 := min_eq_left hh.le
            linarith [hu.1]
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have he : Real.exp (-(u ^ (-α))) ≤ 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Real.rpow_nonneg hu0 _))
          linarith [Real.exp_pos (-(u ^ (-α)))])
      have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..h, 2 * Real.exp (-(u ^ (-α))) :=
        intervalIntegral.integral_nonneg (μ := volume) hh.le (fun u _ => by positivity)
      change (∫ u in (0 : ℝ)..h, 2 * Real.exp (-(u ^ (-α)))) ≤ 2 * h
      rw [← abs_of_nonneg hnonneg, ← Real.norm_eq_abs]
      simpa [abs_of_pos hh] using hb
    · have ht := (show ContinuousAt (fun h : ℝ => 2 * h) 0 by fun_prop).tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
      simpa using ht
  have hpow0 : Tendsto (fun h : ℝ => h ^ (α + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hp : 0 < α + 1 := by linarith
    have hid := (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa [Real.zero_rpow (ne_of_gt hp)] using hid.rpow_const (Or.inr hp.le)
  have hexp0 : Tendsto (fun h : ℝ => Real.exp (-(h ^ (-α)))) (𝓝[>] 0) (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hα))
  have hG0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    change Tendsto (fun h : ℝ => h ^ (α + 1) * Real.exp (-(h ^ (-α))))
      (𝓝[>] 0) (𝓝 0)
    simpa only [mul_zero] using hpow0.mul hexp0
  have hratio : Tendsto (fun h => F' h / G' h) (𝓝[>] (0 : ℝ)) (𝓝 (2 / α)) := by
    have hpowa : Tendsto (fun h : ℝ => h ^ α) (𝓝[>] 0) (𝓝 0) := by
      have hid := (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
      simpa [Real.zero_rpow (ne_of_gt hα)] using hid.rpow_const (Or.inr hα.le)
    have hd : Tendsto (fun h : ℝ => 2 / ((α + 1) * h ^ α + α))
        (𝓝[>] 0) (𝓝 (2 / α)) := by
      have hden : Tendsto (fun h : ℝ => (α + 1) * h ^ α + α)
          (𝓝[>] 0) (𝓝 α) := by
        simpa using (hpowa.const_mul (α + 1)).add_const α
      exact tendsto_const_nhds.div hden (ne_of_gt hα)
    apply hd.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    exact (exponentialModulus_derivative_ratio α h hh).symm
  simpa [F, G, Function.comp_apply] using
    HasDerivAt.lhopital_zero_nhdsGT hFderiv hGderiv hG' hF0 hG0 hratio

-- @node: natCast_div_log_tendsto
lemma natCast_div_log_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) atTop atTop := by
  have hzero : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    have hreal := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    convert hnat using 1
    funext n
    simp [Function.comp_apply]
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n / (n : ℝ) := by
    filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
    exact div_pos (Real.log_pos hn1) (by positivity)
  have hinv := (tendsto_nhdsWithin_iff.2 ⟨hzero, hpos⟩).inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  change (Real.log (n : ℝ) / (n : ℝ))⁻¹ = (n : ℝ) / Real.log n
  rw [inv_div]

-- @node: exists_slow_positive_sequence
lemma exists_slow_positive_sequence
    (m : ℝ → ℝ) (h0 : ℝ) (hh0 : 0 < h0)
    (hm : ∀ h, 0 < h → h ≤ h0 → 0 < m h) :
    ∃ hseq : ℕ → ℝ, Tendsto hseq atTop (𝓝 0) ∧
      (∀ n, 0 < hseq n ∧ hseq n ≤ h0) ∧
      Tendsto (fun n : ℕ => n * m (hseq n) / Real.log n) atTop atTop := by
  let b : ℕ → ℝ := fun k => min (h0 / 2) (1 / (k + 1 : ℝ))
  have hbpos (k : ℕ) : 0 < b k := by
    dsimp [b]
    positivity
  have hble (k : ℕ) : b k ≤ h0 := by
    dsimp [b]
    exact (min_le_left _ _).trans (by linarith)
  have hmb (k : ℕ) : 0 < m (b k) := hm _ (hbpos k) (hble k)
  have hrate (k : ℕ) :
      Tendsto (fun n : ℕ => ((n : ℝ) / Real.log n) * m (b k)) atTop atTop :=
    by simpa [mul_comm] using natCast_div_log_tendsto.const_mul_atTop (hmb k)
  have hex (k : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n →
      (k : ℝ) ≤ ((n : ℝ) / Real.log n) * m (b k) :=
    eventually_atTop.1 (tendsto_atTop.1 (hrate k) (k : ℝ))
  choose N hN using hex
  let K : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hKtop : Tendsto K atTop atTop := by
    rw [tendsto_atTop]
    intro k
    filter_upwards [eventually_atTop.2 ⟨max k (N k), fun n hn => hn⟩] with n hn
    apply Nat.le_findGreatest
    · exact le_trans (le_max_left _ _) hn
    · exact le_trans (le_max_right _ _) hn
  have hbzero : Tendsto b atTop (𝓝 0) := by
    have hone : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ)) atTop (𝓝 0) := by
      have hadd : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      convert hadd.inv_tendsto_atTop using 1
      funext k
      simp [one_div]
    have hc : Tendsto (fun _ : ℕ => h0 / 2) atTop (𝓝 (h0 / 2)) := tendsto_const_nhds
    simpa [b, min_eq_right (by positivity : (0 : ℝ) ≤ h0 / 2)] using hc.min hone
  refine ⟨fun n => b (K n), hbzero.comp hKtop, fun n => ⟨hbpos _, hble _⟩, ?_⟩
  have hKreal : Tendsto (fun n => (K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKtop
  apply tendsto_atTop_mono' atTop _ hKreal
  filter_upwards [eventually_atTop.2 ⟨N 0, fun n hn => hn⟩] with n hn
  have hspec : N (K n) ≤ n := Nat.findGreatest_spec (P := fun k => N k ≤ n)
    (Nat.zero_le n) hn
  have hkbound := hN (K n) n hspec
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hkbound

-- @node: prop:exponential-horn-consistency
/-- A fixed exponential horn has positive mass, the stated incomplete-Gamma
asymptotic, and admits a bandwidth sequence with diverging effective count. -/
theorem exponential_horn_consistency (α h0 : ℝ)
    (hα : AdmissibleSeverityExponent α) (hh0 : 0 < h0 ∧ h0 < 1) :
    (∀ h, 0 < h → h ≤ h0 → 0 < exponentialModulus α h0 h) ∧
    (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ᶠ h : ℝ in 𝓝[>] 0,
        c * (h ^ (α + 1) * Real.exp (-(h ^ (-α)))) ≤ exponentialModulus α h0 h ∧
        exponentialModulus α h0 h ≤
          C * (h ^ (α + 1) * Real.exp (-(h ^ (-α))))) ∧
    ∃ hseq : ℕ → ℝ, Tendsto hseq atTop (𝓝 0) ∧
      (∀ n, 0 < hseq n ∧ hseq n ≤ h0) ∧
      Tendsto (fun n : ℕ => n * exponentialModulus α h0 (hseq n) / Real.log n)
        atTop atTop := by
  have ha : 0 < α := hα
  have hpos : ∀ h, 0 < h → h ≤ h0 → 0 < exponentialModulus α h0 h := by
    intro h hh hhle
    rw [exponentialModulus, if_pos ⟨ha, hh, hhle⟩]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · rw [intervalIntegrable_iff]
      apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne) (M := 2)
      · fun_prop
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with u hu
        have hu0 : 0 ≤ u := by
          have hmin : min 0 h = 0 := min_eq_left hh.le
          linarith [hu.1]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have he : Real.exp (-(u ^ (-α))) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Real.rpow_nonneg hu0 _))
        linarith [Real.exp_pos (-(u ^ (-α)))]
    · intro u hu
      positivity
    · exact hh
  refine ⟨hpos, ?_, ?_⟩
  · refine ⟨1 / α, 3 / α, div_pos zero_lt_one ha,
      div_le_div_of_nonneg_right (by norm_num) ha.le, ?_⟩
    have hr := exponentialModulus_ratio_tendsto α ha
    have hc : 1 / α < 2 / α := div_lt_div_of_pos_right (by norm_num) ha
    have hC : 2 / α < 3 / α := div_lt_div_of_pos_right (by norm_num) ha
    have hl := (tendsto_order.1 hr).1 _ hc
    have hu := (tendsto_order.1 hr).2 _ hC
    have hs : ∀ᶠ h : ℝ in 𝓝[>] 0, h < h0 :=
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left) (Iio_mem_nhds hh0.1)
    filter_upwards [hl, hu, hs, self_mem_nhdsWithin] with h hl hu hh0' hh
    change 0 < h at hh
    have hd : 0 < h ^ (α + 1) * Real.exp (-(h ^ (-α))) := by positivity
    rw [exponentialModulus, if_pos ⟨ha, hh, hh0'.le⟩]
    constructor
    · exact (lt_div_iff₀ hd).mp hl |>.le
    · exact (div_lt_iff₀ hd).mp hu |>.le
  · exact exists_slow_positive_sequence (exponentialModulus α h0) h0 hh0.1 hpos

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
