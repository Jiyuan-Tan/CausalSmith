module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RiskEnvelopes

/-!
# Explicit death-error risk bound

This module converts the finite-sample death-error energy bound into the
explicit model-class envelope used by the paper's upper-risk theorem.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

lemma retention_ge_half_gMin_rpow (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Set.Ioo (1 - c.x0) 1) :
    c.gMin / 2 * (1 - t) ^ c.kappa ≤ retention P a t := by
  let x := 1 - t
  have hx : 0 < x := by dsimp [x]; linarith [ht.2]
  have hx0 : x ≤ c.x0 := by dsimp [x]; linarith [ht.1]
  have hg : c.gMin ≤ P.g a := (hP.endpointCoefficientBounds a).1
  have hpow0 : 0 < x ^ c.kappa := Real.rpow_pos_of_pos hx _
  have hden : 0 < P.g a * x ^ c.kappa :=
    mul_pos (lt_of_lt_of_le c.gMin_pos hg) hpow0
  have hrho : x ^ c.rho ≤ c.x0 ^ c.rho :=
    Real.rpow_le_rpow hx.le hx0 c.rho_pos.le
  have hsmall : c.LG * x ^ c.rho ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hrho c.LG_pos.le).trans hP.tailEnvelopeSmall
  have hlower := (abs_le.mp (hP.endpointRetention a x hx hx0)).1
  have hratio : 1 / 2 ≤ retention P a (1 - x) / (P.g a * x ^ c.kappa) := by
    linarith
  have hret : P.g a * x ^ c.kappa / 2 ≤ retention P a (1 - x) := by
    have := (le_div_iff₀ hden).mp hratio
    linarith
  calc
    c.gMin / 2 * (1 - t) ^ c.kappa
        ≤ P.g a * x ^ c.kappa / 2 := by
          dsimp [x]
          nlinarith [mul_le_mul_of_nonneg_right hg hpow0.le]
    _ ≤ retention P a (1 - x) := hret
    _ = retention P a t := by simp [x]

lemma inv_retention_le_endpoint_power (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {t : ℝ}
    (ht : t ∈ Set.Ioo (1 - c.x0) 1) :
    (retention P a t)⁻¹ ≤ (2 / c.gMin) * (1 - t) ^ (-c.kappa) := by
  have hr := retention_ge_half_gMin_rpow c P hP a ht
  have hx : 0 < 1 - t := by linarith [ht.2]
  have hlower : 0 < c.gMin / 2 * (1 - t) ^ c.kappa :=
    mul_pos (div_pos c.gMin_pos (by norm_num))
      (Real.rpow_pos_of_pos hx _)
  have hret : 0 < retention P a t := lt_of_lt_of_le hlower hr
  rw [← one_div]
  calc
    1 / retention P a t ≤ 1 / (c.gMin / 2 * (1 - t) ^ c.kappa) :=
      one_div_le_one_div_of_le hlower hr
    _ = (2 / c.gMin) * (1 - t) ^ (-c.kappa) := by
      rw [Real.rpow_neg hx.le]
      field_simp [ne_of_gt c.gMin_pos,
        ne_of_gt (Real.rpow_pos_of_pos hx c.kappa)]

lemma inv_retention_integrableOn (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {U : ℝ}
    (hU0 : 0 ≤ U) (hU1 : U < 1) :
    IntegrableOn (fun t => (retention P a t)⁻¹) (Set.Icc 0 U) := by
  have hrU : 0 < retention P a U :=
    retention_pos_of_modelClass c P hP a U hU0 hU1
  refine (integrableOn_const (C := (retention P a U)⁻¹)
      (hs := measure_Icc_lt_top.ne)).mono'
    (measurable_retention P a).aestronglyMeasurable.inv₀.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hret0 : 0 ≤ retention P a t := measureReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hret0)]
  exact (inv_le_inv₀ (hrU.trans_le ((retention_antitone P a) ht.2)) hrU).2
    ((retention_antitone P a) ht.2)

lemma inv_retention_le_piecewise (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (retention P a t)⁻¹ ≤
      if t ≤ 1 - c.x0 then c.Gint⁻¹
      else (2 / c.gMin) * (1 - t) ^ (-c.kappa) := by
  split_ifs with hinterior
  · have hr : c.Gint ≤ retention P a t :=
      hP.interiorRetention a t ⟨ht0, hinterior⟩
    exact (inv_le_inv₀ (c.Gint_pos.trans_le hr) c.Gint_pos).2 hr
  · exact inv_retention_le_endpoint_power c P hP a
      ⟨lt_of_not_ge hinterior, ht1⟩

lemma endpoint_inverse_power_integral {x h kappa : ℝ}
    (hx : 0 < x) (hh : 0 < h) (hhx : h ≤ x) (hk : kappa ≠ 1) :
    (∫ t in (1 - x)..(1 - h), (1 - t) ^ (-kappa)) =
      (x ^ (1 - kappa) - h ^ (1 - kappa)) / (1 - kappa) := by
  rw [intervalIntegral.integral_comp_sub_left
    (f := fun u : ℝ => u ^ (-kappa)) (d := (1 : ℝ))]
  rw [integral_rpow (Or.inr ⟨by
    intro he
    apply hk
    linarith, by
    simp only [sub_sub_cancel]
    rw [Set.uIcc_of_le hhx]
    exact fun hmem => (not_le_of_gt hh) hmem.1⟩)]
  ring_nf

lemma endpoint_inverse_integral {x h : ℝ}
    (hx : 0 < x) (hh : 0 < h) (hhx : h ≤ x) :
    (∫ t in (1 - x)..(1 - h), (1 - t)⁻¹) = Real.log (x / h) := by
  rw [intervalIntegral.integral_comp_sub_left
    (f := fun u : ℝ => u⁻¹) (d := (1 : ℝ))]
  simpa only [sub_sub_cancel] using integral_inv (by
    rw [Set.uIcc_of_le hhx]
    exact fun hmem => (not_le_of_gt hh) hmem.1)

lemma inv_retention_integral_le_split (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ}
    (hh : 0 < h) (hhx : h ≤ c.x0) :
    (∫ t in Set.Icc 0 (1 - h), (retention P a t)⁻¹) ≤
      (1 - c.x0) / c.Gint +
        (2 / c.gMin) *
          ∫ t in (1 - c.x0)..(1 - h), (1 - t) ^ (-c.kappa) := by
  have hx0 : 0 < c.x0 := c.x0_pos
  have hx01 : c.x0 < 1 := lt_of_le_of_lt c.x0_le (by norm_num)
  have hU0 : 0 ≤ 1 - h := by linarith [hhx, c.x0_le]
  have hU1 : 1 - h < 1 := by linarith
  have hsplit : 0 ≤ 1 - c.x0 := by linarith [c.x0_le]
  have hsplitU : 1 - c.x0 ≤ 1 - h := by linarith
  have hinv := inv_retention_integrableOn c P hP a hU0 hU1
  have hinvInt : IntervalIntegrable (fun t => (retention P a t)⁻¹)
      volume 0 (1 - h) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hU0]
    exact hinv
  have hinvLeft := hinvInt.mono_set (by
    rw [Set.uIcc_of_le hsplit, Set.uIcc_of_le hU0]
    exact Set.Icc_subset_Icc le_rfl hsplitU)
  have hinvRight := hinvInt.mono_set (by
    rw [Set.uIcc_of_le hsplitU, Set.uIcc_of_le hU0]
    exact Set.Icc_subset_Icc hsplit le_rfl)
  have hpowInt : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-c.kappa))
      volume (1 - c.x0) (1 - h) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hsplitU
    apply (continuousOn_const.sub continuousOn_id).rpow_const
    intro t ht
    left
    change 1 - t ≠ 0
    linarith [ht.2, hh]
  have hleft :
      (∫ t in (0 : ℝ)..(1 - c.x0), (retention P a t)⁻¹) ≤
        (1 - c.x0) / c.Gint := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..(1 - c.x0), c.Gint⁻¹ := by
        apply intervalIntegral.integral_mono_on hsplit hinvLeft
          ((continuousOn_const : ContinuousOn (fun _ : ℝ => c.Gint⁻¹)
            (Set.Icc 0 (1 - c.x0))).intervalIntegrable_of_Icc hsplit)
        intro t ht
        exact inv_retention_le_piecewise c P hP a ht.1
          (ht.2.trans_lt (by linarith [hx0]))
          |>.trans_eq (if_pos ht.2)
      _ = _ := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul, sub_zero]
        ring
  have hright :
      (∫ t in (1 - c.x0)..(1 - h), (retention P a t)⁻¹) ≤
        (2 / c.gMin) *
          ∫ t in (1 - c.x0)..(1 - h), (1 - t) ^ (-c.kappa) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hsplitU hinvRight
      (hpowInt.const_mul (2 / c.gMin))
    intro t ht
    by_cases heq : t = 1 - c.x0
    · subst t
      -- The endpoint formula reaches the joining point by monotonicity.
      have hj : c.gMin / 2 * c.x0 ^ c.kappa ≤
          retention P a (1 - c.x0) := by
        have hlim := hP.endpointRetention a c.x0 c.x0_pos le_rfl
        have hpow0 : 0 < c.x0 ^ c.kappa := Real.rpow_pos_of_pos c.x0_pos _
        have hg := (hP.endpointCoefficientBounds a).1
        have hden : 0 < P.g a * c.x0 ^ c.kappa :=
          mul_pos (c.gMin_pos.trans_le hg) hpow0
        have hrho : c.LG * c.x0 ^ c.rho ≤ 1 / 2 := hP.tailEnvelopeSmall
        have hlo := (abs_le.mp hlim).1
        have hq : 1 / 2 ≤ retention P a (1 - c.x0) /
            (P.g a * c.x0 ^ c.kappa) := by linarith
        have hm := (le_div_iff₀ hden).mp hq
        nlinarith [mul_le_mul_of_nonneg_right hg hpow0.le]
      have := one_div_le_one_div_of_le
        (mul_pos (div_pos c.gMin_pos (by norm_num))
          (Real.rpow_pos_of_pos c.x0_pos _)) hj
      simp only [sub_sub_cancel]
      calc
        (retention P a (1 - c.x0))⁻¹ ≤
            1 / (c.gMin / 2 * c.x0 ^ c.kappa) := by simpa only [one_div] using this
        _ = 2 / c.gMin * c.x0 ^ (-c.kappa) := by
          rw [Real.rpow_neg c.x0_pos.le]
          field_simp [ne_of_gt c.gMin_pos,
            ne_of_gt (Real.rpow_pos_of_pos c.x0_pos c.kappa)]
    · exact inv_retention_le_endpoint_power c P hP a
        ⟨lt_of_le_of_ne ht.1 (Ne.symm heq), ht.2.trans_lt hU1⟩
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hU0]
  rw [← intervalIntegral.integral_add_adjacent_intervals hinvLeft hinvRight]
  linarith

lemma endpoint_inverse_power_integral_le_varianceFactor
    (c : ClassConstants) {h : ℝ} (hh : 0 < h) (hhx : h ≤ c.x0) :
    (2 / c.gMin) *
        ∫ t in (1 - c.x0)..(1 - h), (1 - t) ^ (-c.kappa) ≤
      (if c.kappa < 1 then
          2 * c.x0 ^ (1 - c.kappa) / (c.gMin * (1 - c.kappa))
        else if c.kappa = 1 then 2 / c.gMin
        else 2 / (c.gMin * (c.kappa - 1))) * varianceFactor c h := by
  by_cases hklt : c.kappa < 1
  · have hkne : c.kappa ≠ 1 := ne_of_lt hklt
    rw [endpoint_inverse_power_integral c.x0_pos hh hhx hkne]
    rw [if_pos hklt, varianceFactor, if_pos hklt]
    have hp : 0 < 1 - c.kappa := by linarith
    have hhpow : 0 ≤ h ^ (1 - c.kappa) := Real.rpow_nonneg hh.le _
    have hg : 0 < c.gMin := c.gMin_pos
    have hden : 0 < c.gMin * (1 - c.kappa) := mul_pos hg hp
    have hnormLeft :
        2 / c.gMin *
            ((c.x0 ^ (1 - c.kappa) - h ^ (1 - c.kappa)) /
              (1 - c.kappa)) =
          (2 * (c.x0 ^ (1 - c.kappa) - h ^ (1 - c.kappa))) /
            (c.gMin * (1 - c.kappa)) := by
      field_simp [ne_of_gt hg, ne_of_gt hp]
    have hnormRight :
        2 * c.x0 ^ (1 - c.kappa) /
            (c.gMin * (1 - c.kappa)) * 1 =
          (2 * c.x0 ^ (1 - c.kappa)) /
            (c.gMin * (1 - c.kappa)) := by ring
    rw [hnormLeft, hnormRight]
    exact (div_le_div_iff₀ hden hden).2 (by nlinarith)
  · by_cases hkeq : c.kappa = 1
    · rw [hkeq]
      simp only [Real.rpow_neg_one]
      rw [endpoint_inverse_integral c.x0_pos hh hhx]
      simp only [lt_self_iff_false, ↓reduceIte]
      rw [varianceFactor]
      simp only [hkeq, ↓reduceIte]
      simp only [lt_self_iff_false, ↓reduceIte]
      have hx1 : c.x0 ≤ 1 := c.x0_le.trans (by norm_num)
      have hlogx : Real.log c.x0 ≤ 0 := Real.log_nonpos c.x0_pos.le hx1
      have hloginv : Real.log (1 / h) = -Real.log h := by
        rw [one_div, Real.log_inv]
      rw [Real.log_div (ne_of_gt c.x0_pos) (ne_of_gt hh), hloginv]
      have hcoef : 0 ≤ 2 / c.gMin := div_nonneg (by norm_num) c.gMin_pos.le
      nlinarith
    · have hkgt : 1 < c.kappa := lt_of_le_of_ne (le_of_not_gt hklt)
          (Ne.symm hkeq)
      rw [endpoint_inverse_power_integral c.x0_pos hh hhx hkeq]
      rw [if_neg hklt, if_neg hkeq, varianceFactor, if_neg hklt, if_neg hkeq]
      have hp : 0 < c.kappa - 1 := by linarith
      have hhpow : 0 ≤ h ^ (1 - c.kappa) := Real.rpow_nonneg hh.le _
      have hxpow : 0 ≤ c.x0 ^ (1 - c.kappa) :=
        Real.rpow_nonneg c.x0_pos.le _
      have hg : 0 < c.gMin := c.gMin_pos
      have hden : 0 < c.gMin * (c.kappa - 1) := mul_pos hg hp
      have hrewrite :
          (c.x0 ^ (1 - c.kappa) - h ^ (1 - c.kappa)) /
              (1 - c.kappa) =
            (h ^ (1 - c.kappa) - c.x0 ^ (1 - c.kappa)) /
              (c.kappa - 1) := by
        field_simp [ne_of_gt hp]
        ring
      rw [hrewrite]
      have hnormLeft :
          2 / c.gMin *
              ((h ^ (1 - c.kappa) - c.x0 ^ (1 - c.kappa)) /
                (c.kappa - 1)) =
            (2 * (h ^ (1 - c.kappa) - c.x0 ^ (1 - c.kappa))) /
              (c.gMin * (c.kappa - 1)) := by
        field_simp [ne_of_gt hg, ne_of_gt hp]
      have hnormRight :
          2 / (c.gMin * (c.kappa - 1)) * h ^ (1 - c.kappa) =
            (2 * h ^ (1 - c.kappa)) /
              (c.gMin * (c.kappa - 1)) := by ring
      rw [hnormLeft, hnormRight]
      exact (div_le_div_iff₀ hden hden).2 (by nlinarith)

lemma reciprocal_retention_integral_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ}
    (hh : 0 < h) (hhx : h ≤ c.x0) :
    (∫ t in Set.Icc 0 (1 - h), (retention P a t)⁻¹) ≤
      reciprocalRetentionEnvelope c * varianceFactor c h := by
  have hsplit := inv_retention_integral_le_split c P hP a hh hhx
  have hend := endpoint_inverse_power_integral_le_varianceFactor c hh hhx
  unfold reciprocalRetentionEnvelope
  have hinterior : 0 ≤ (1 - c.x0) / c.Gint := by
    exact div_nonneg (by linarith [c.x0_le]) c.Gint_pos.le
  have hv : 1 ≤ varianceFactor c h := by
    unfold varianceFactor
    split_ifs with hklt hkeq
    · rfl
    · have hh1 : h ≤ 1 := hhx.trans c.x0_le |>.trans (by norm_num)
      have hlog : 0 ≤ Real.log (1 / h) :=
        Real.log_nonneg ((one_le_div₀ hh).2 hh1)
      linarith
    · have hkgt : 1 < c.kappa := lt_of_le_of_ne (le_of_not_gt hklt)
          (Ne.symm hkeq)
      have hh1 : h ≤ 1 := hhx.trans c.x0_le |>.trans (by norm_num)
      simpa only [Real.one_rpow] using
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hh1 (by linarith))
  nlinarith [mul_le_mul_of_nonneg_left hv hinterior]

lemma remainingTarget_abs_le_weightEnvelope (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h t : ℝ}
    (hh : 0 < h) (ht : t ∈ Set.Icc 0 (1 - h)) :
    |remainingTarget c P a h t| ≤ weightEnvelope c * c.lambdaMax := by
  have hh1 : h ≤ 1 := by linarith [ht.1, ht.2]
  have hU1 : 1 - h ≤ 1 := by linarith
  have hweight : ∀ u,
      |continuationWeight (holderOrder c) h u| ≤ weightEnvelope c := by
    intro u
    change |continuationWeight (holderOrder c) h u| ≤
      1 + ∑ m : Fin (holderOrder c + 1),
        |((continuationGram (holderOrder c))⁻¹.mulVec
          (continuationRhs (holderOrder c))) m| * (2 : ℝ) ^ m.val
    exact continuationWeight_abs_le_coeffSum (holderOrder c) hh
  have henv0 : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hlam0 : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hbound : ∀ u ∈ Set.uIoc t (1 - h),
      ‖continuationWeight (holderOrder c) h u * survival P a u * P.lam a u‖ ≤
        weightEnvelope c * c.lambdaMax := by
    intro u hu
    rw [Set.uIoc_of_le ht.2] at hu
    have hu01 : u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨ht.1.trans hu.1.le, hu.2.trans hU1⟩
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a hu01).2
    have hs0 : 0 ≤ survival P a u := (Real.exp_pos _).le
    have hlam := (hP.recurrenceBounds a u hu01).2
    have hlamPos : 0 ≤ P.lam a u :=
      c.lambdaMin_pos.le.trans (hP.recurrenceBounds a u hu01).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0,
      abs_of_nonneg hlamPos]
    calc
      _ ≤ weightEnvelope c * 1 * c.lambdaMax := by
        gcongr
        exact hweight u
      _ = weightEnvelope c * c.lambdaMax := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  unfold remainingTarget
  rw [Real.norm_eq_abs] at hnorm
  have hlen : |(1 - h) - t| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
    linarith [ht.1]
  exact hnorm.trans (by
    nlinarith [mul_nonneg henv0 hlam0])

lemma deathRateEnergy_density_le_explicit (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h t : ℝ}
    (hh : 0 < h) (ht : t ∈ Set.Icc 0 (1 - h)) :
    (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
        (retention P a t * survival P a t) ≤
      (weightEnvelope c) ^ 2 * c.lambdaMax ^ 2 * c.dMax *
        Real.exp (3 * c.dMax) * (retention P a t)⁻¹ := by
  have hh1 : h ≤ 1 := by linarith [ht.1, ht.2]
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2, hh]⟩
  have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht01
  have hs0 : 0 < survival P a t := Real.exp_pos _
  have hr0 : 0 < retention P a t :=
    retention_pos_of_modelClass c P hP a t ht.1 (by linarith [ht.2, hh])
  have hrem := remainingTarget_abs_le_weightEnvelope c P hP a hh ht
  have henv0 : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hlam0 : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have htarget : |deathTargetWeight c P a h t| ≤
      weightEnvelope c * c.lambdaMax * Real.exp c.dMax := by
    rw [deathTargetWeight, if_pos ht, abs_div, abs_of_pos hs0]
    have hinvSurv : (survival P a t)⁻¹ ≤ Real.exp c.dMax := by
      calc
        _ ≤ (Real.exp (-c.dMax))⁻¹ :=
          (inv_le_inv₀ hs0 (Real.exp_pos (-c.dMax))).2 hs.1
        _ = Real.exp c.dMax := by rw [Real.exp_neg]; simp
    rw [div_eq_mul_inv]
    exact mul_le_mul hrem hinvSurv (inv_nonneg.mpr hs0.le)
      (mul_nonneg henv0 hlam0)
  have hhaz := (hP.deathBounds a t ht01).2
  have hhaz0 : 0 ≤ P.hazard a t :=
    c.dMin_pos.le.trans (hP.deathBounds a t ht01).1
  have hsurvInv : (survival P a t)⁻¹ ≤ Real.exp c.dMax := by
    calc
      _ ≤ (Real.exp (-c.dMax))⁻¹ :=
        (inv_le_inv₀ hs0 (Real.exp_pos (-c.dMax))).2 hs.1
      _ = Real.exp c.dMax := by rw [Real.exp_neg]; simp
  have hB0 : 0 ≤ weightEnvelope c * c.lambdaMax * Real.exp c.dMax :=
    mul_nonneg (mul_nonneg henv0 hlam0) (Real.exp_pos _).le
  have hsq : (deathTargetWeight c P a h t) ^ 2 ≤
      (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (deathTargetWeight c P a h t)) hB0).2 htarget
  have hdm0 : 0 ≤ c.dMax := c.dMin_pos.le.trans c.dMin_lt.le
  have hinvret0 : 0 ≤ (retention P a t)⁻¹ := inv_nonneg.mpr hr0.le
  have hab : (deathTargetWeight c P a h t) ^ 2 * P.hazard a t ≤
      (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2 * c.dMax :=
    mul_le_mul hsq hhaz hhaz0 (sq_nonneg _)
  have hrs : (retention P a t)⁻¹ * (survival P a t)⁻¹ ≤
      (retention P a t)⁻¹ * Real.exp c.dMax :=
    mul_le_mul_of_nonneg_left hsurvInv hinvret0
  rw [div_eq_mul_inv, mul_inv]
  calc
    _ ≤ (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2 *
          c.dMax * ((retention P a t)⁻¹ * Real.exp c.dMax) := by
      exact mul_le_mul hab hrs
        (mul_nonneg hinvret0 (inv_nonneg.mpr hs0.le))
        (mul_nonneg (sq_nonneg _) hdm0)
    _ = _ := by
      have hexp : (Real.exp c.dMax) ^ 2 * Real.exp c.dMax =
          Real.exp (3 * c.dMax) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [show (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2 =
          weightEnvelope c ^ 2 * c.lambdaMax ^ 2 * (Real.exp c.dMax) ^ 2 by ring]
      rw [← hexp]
      ring

lemma deathRateEnergy_le_explicit (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ}
    (hh : 0 < h) (hhx : h ≤ c.x0) :
    (∫ t in Set.Icc 0 (1 - h),
        (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
          (retention P a t * survival P a t)) ≤
      (weightEnvelope c) ^ 2 * c.lambdaMax ^ 2 * c.dMax *
        Real.exp (3 * c.dMax) * reciprocalRetentionEnvelope c *
          varianceFactor c h := by
  let K := (weightEnvelope c) ^ 2 * c.lambdaMax ^ 2 * c.dMax *
    Real.exp (3 * c.dMax)
  have hh1 : h ≤ 1 := hhx.trans c.x0_le |>.trans (by norm_num)
  have hU0 : 0 ≤ 1 - h := by linarith
  have hU1 : 1 - h < 1 := by linarith
  have hf := DeathCP.deathRateEnergy_integrableOn c P hP a hh hh1
  have hinv := inv_retention_integrableOn c P hP a hU0 hU1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _)
        (sq_nonneg _)) (c.dMin_pos.le.trans c.dMin_lt.le))
      (Real.exp_pos _).le
  have hg : IntegrableOn (fun t => K * (retention P a t)⁻¹)
      (Set.Icc 0 (1 - h)) := hinv.const_mul K
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 (1 - h))),
      (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
          (retention P a t * survival P a t) ≤
        K * (retention P a t)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact deathRateEnergy_density_le_explicit c P hP a hh ht
  calc
    _ ≤ ∫ t in Set.Icc 0 (1 - h), K * (retention P a t)⁻¹ :=
      integral_mono_ae hf hg hpoint
    _ = K * ∫ t in Set.Icc 0 (1 - h), (retention P a t)⁻¹ := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ K * (reciprocalRetentionEnvelope c * varianceFactor c h) :=
      mul_le_mul_of_nonneg_left
        (reciprocal_retention_integral_le c P hP a hh hhx) hK0
    _ = _ := by dsimp [K]; ring

lemma deathError_secondMoment_le_explicit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hhx : h ≤ c.x0) :
    ∫ s, (deathError c P a s h) ^ 2 ∂sampleLaw P n ≤
      2 * reciprocalRetentionEnvelope c * (weightEnvelope c) ^ 2 /
        c.pMin * c.lambdaMax ^ 2 * c.dMax * Real.exp (3 * c.dMax) *
          (n : ℝ)⁻¹ * varianceFactor c h := by
  have hh1 : h ≤ 1 := hhx.trans c.x0_le |>.trans (by norm_num)
  have hfinite := DeathCP.deathError_secondMoment_le_finiteRateEnergy
    c P hP a hn hh hh1
  have henergy := deathRateEnergy_le_explicit c P hP a hh hhx
  have hcoef : 0 ≤ 2 / ((n : ℝ) * c.pMin) :=
    div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg n) c.pMin_pos.le)
  calc
    _ ≤ (2 / ((n : ℝ) * c.pMin)) *
        ∫ t in Set.Icc 0 (1 - h),
          (deathTargetWeight c P a h t) ^ 2 * P.hazard a t /
            (retention P a t * survival P a t) := hfinite
    _ ≤ (2 / ((n : ℝ) * c.pMin)) *
        ((weightEnvelope c) ^ 2 * c.lambdaMax ^ 2 * c.dMax *
          Real.exp (3 * c.dMax) * reciprocalRetentionEnvelope c *
            varianceFactor c h) := mul_le_mul_of_nonneg_left henergy hcoef
    _ = _ := by
      field_simp [ne_of_gt c.pMin_pos, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
