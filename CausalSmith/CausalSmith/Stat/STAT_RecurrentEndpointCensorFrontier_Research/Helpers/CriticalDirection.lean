module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DirectionAnalytics

/-!
# Analytic bounds for the critical lower-bound direction

This module records positivity of the critical bandwidth and removes the
apparent endpoint singularity of the critical direction on the study horizon.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- From sample size two onward, the logarithmic critical bandwidth is
strictly positive. -/
lemma criticalBandwidth_pos (c : ClassConstants) {n : ℕ} (hn : 2 ≤ n) :
    0 < criticalBandwidth c n := by
  unfold criticalBandwidth
  apply Real.rpow_pos_of_pos
  exact mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))

/-- Multiplying the square-root normalization by the critical bandwidth gives
the advertised negative-power amplitude rate. -/
lemma critical_normalization_eq_rpow (c : ClassConstants) {n : ℕ}
    (hn : 2 ≤ n) :
    1 / (Real.sqrt ((n : ℝ) * Real.log n) * criticalBandwidth c n) =
      ((n : ℝ) * Real.log n) ^
        (-(c.beta / (2 * c.beta + 2))) := by
  let z : ℝ := (n : ℝ) * Real.log n
  have hz : 0 < z := mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))
  have hden : 2 * c.beta + 2 ≠ 0 := by nlinarith [c.beta_pos]
  unfold criticalBandwidth
  change 1 / (Real.sqrt z * z ^ (-(1 / (2 * c.beta + 2)))) =
    z ^ (-(c.beta / (2 * c.beta + 2)))
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hz]
  calc
    1 / z ^ ((1 / 2 : ℝ) + -(1 / (2 * c.beta + 2))) =
        z ^ (-((1 / 2 : ℝ) + -(1 / (2 * c.beta + 2)))) := by
          rw [one_div, Real.rpow_neg hz.le]
    _ = z ^ (-(c.beta / (2 * c.beta + 2))) := by
      congr 1
      have hb : 1 + c.beta ≠ 0 := by linarith [c.beta_pos]
      have hb' : c.beta + 1 ≠ 0 := by linarith [c.beta_pos]
      have hden' : 2 + c.beta * 2 ≠ 0 := by nlinarith [c.beta_pos]
      field_simp [hden, hden', hb, hb']
      ring

/-- On the study horizon, distance to the endpoint divided by the critical
bandwidth is nonnegative. -/
lemma critical_scaled_nonneg (c : ClassConstants) {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 - t) / criticalBandwidth c n := by
  exact div_nonneg (sub_nonneg.mpr ht.2) (criticalBandwidth_pos c hn).le

/-- The critical direction vanishes throughout its endpoint plateau. -/
lemma criticalDirection_eq_zero_of_endpoint_band
    (c : ClassConstants) (cut : CutoffData c) {u : ℝ} {n : ℕ}
    (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hband : 1 - t ≤ criticalBandwidth c n) :
    criticalDirection c cut u n t = 0 := by
  by_cases hx : 1 - t = 0
  · simp [criticalDirection, hx]
  · apply criticalDirection_eq_zero_of_scaled_le_one c cut hx
    · exact critical_scaled_nonneg c hn ht
    · exact (div_le_one (criticalBandwidth_pos c hn)).2 hband

/-- The critical direction is continuous on the closed study horizon.  The
zero plateau of `chi` supplies continuity at the endpoint where the displayed
formula contains a division by `1 - t`. -/
lemma criticalDirection_continuousOn (c : ClassConstants) (cut : CutoffData c)
    (u : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ContinuousOn (criticalDirection c cut u n) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  by_cases ht1 : t = 1
  · subst t
    have hzero : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) 1] (1 : ℝ),
        criticalDirection c cut u n s = 0 := by
      have hc : ContinuousWithinAt (fun s : ℝ => 1 - s)
          (Set.Icc (0 : ℝ) 1) 1 := by fun_prop
      have hlt : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) 1] (1 : ℝ),
          1 - s < criticalBandwidth c n :=
        hc.eventually_lt_const (by simpa using criticalBandwidth_pos c hn)
      filter_upwards [hlt, eventually_mem_nhdsWithin] with s hs hsmem
      exact criticalDirection_eq_zero_of_endpoint_band c cut hn hsmem hs.le
    exact (show ContinuousWithinAt (fun _ : ℝ => (0 : ℝ))
        (Set.Icc (0 : ℝ) 1) 1 from continuousWithinAt_const).congr_of_eventuallyEq
      hzero (criticalDirection_at_one c cut u n)
  · have hx : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have harg : ContinuousOn
        (fun s : ℝ => (1 - s) / criticalBandwidth c n) (Set.Icc (0 : ℝ) 1) :=
      (continuous_const.sub continuous_id).div_const _ |>.continuousOn
    have harg_mem : Set.MapsTo
        (fun s : ℝ => (1 - s) / criticalBandwidth c n)
        (Set.Icc (0 : ℝ) 1) (Set.Ici 0) := by
      intro s hs
      exact critical_scaled_nonneg c hn hs
    have hchi : ContinuousOn
        (fun s : ℝ => cut.chi ((1 - s) / criticalBandwidth c n))
        (Set.Icc (0 : ℝ) 1) :=
      cut.chi_smooth.continuousOn.comp harg harg_mem
    have hxmap : Set.MapsTo (fun s : ℝ => 1 - s)
        (Set.Icc (0 : ℝ) 1) (Set.Ici 0) := by
      intro s hs
      exact sub_nonneg.mpr hs.2
    have hpsi : ContinuousOn (fun s : ℝ => cut.psi (1 - s))
        (Set.Icc (0 : ℝ) 1) :=
      cut.psi_smooth.continuousOn.comp
        (continuous_const.sub continuous_id).continuousOn hxmap
    rw [show criticalDirection c cut u n = fun s =>
        if 1 - s = 0 then 0 else
          (u / Real.sqrt ((n : ℝ) * Real.log n)) *
            cut.chi ((1 - s) / criticalBandwidth c n) * cut.psi (1 - s) /
              (1 - s) by
      funext s
      simp only [criticalDirection]]
    have hregular : ContinuousWithinAt
        (fun s : ℝ =>
          (u / Real.sqrt ((n : ℝ) * Real.log n)) *
            cut.chi ((1 - s) / criticalBandwidth c n) * cut.psi (1 - s) /
              (1 - s)) (Set.Icc (0 : ℝ) 1) t :=
      (((continuousWithinAt_const.mul (hchi t ht)).mul (hpsi t ht)).div
        ((continuousAt_const.sub continuousAt_id).continuousWithinAt) hx)
    have hne : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) 1] t, 1 - s ≠ 0 := by
      have hne' : ∀ᶠ s in 𝓝 t, s ≠ 1 :=
        isOpen_compl_singleton.mem_nhds ht1
      filter_upwards [hne'.filter_mono inf_le_left] with s hs
      exact sub_ne_zero.mpr (Ne.symm hs)
    apply ContinuousWithinAt.congr_of_eventuallyEq hregular
    · filter_upwards [hne] with s hs
      rw [if_neg hs]
    · rw [if_neg hx]

/-- The critical direction is integrable on the study horizon. -/
lemma criticalDirection_integrableOn (c : ClassConstants) (cut : CutoffData c)
    (u : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (criticalDirection c cut u n) (Set.Icc (0 : ℝ) 1) volume :=
  (criticalDirection_continuousOn c cut u hn).integrableOn_compact isCompact_Icc

/-- The critical direction is measurable modulo the restricted horizon
measure, which is the measurability notion used by `withDensity`. -/
lemma criticalDirection_aemeasurable_restrict
    (c : ClassConstants) (cut : CutoffData c) (u : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    AEMeasurable (criticalDirection c cut u n)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  exact ((criticalDirection_integrableOn c cut u hn).mono_set
    Set.Ioc_subset_Icc_self).aestronglyMeasurable.aemeasurable

/-- Adding the critical direction to a constant baseline produces a finite
restricted recurrence intensity. -/
lemma criticalDirection_intensity_isFinite
    (c : ClassConstants) (cut : CutoffData c) (lambda0 u : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    IsFiniteMeasure ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (lambda0 + criticalDirection c cut u n t))) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact ((continuousOn_const.add
    (criticalDirection_continuousOn c cut u hn)).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioc_subset_Icc_self |>.2

/-- The local Poisson KL cost of an additive perturbation is bounded by its
squared amplitude divided by the baseline intensity. -/
lemma poissonIntensityCost_add_le_sq_div {lambda0 d : ℝ}
    (hlambda0 : 0 < lambda0) (hadd : 0 < lambda0 + d) :
    (lambda0 + d) * Real.log ((lambda0 + d) / lambda0) -
        (lambda0 + d) + lambda0 ≤ d ^ 2 / lambda0 := by
  have hratio : 0 < (lambda0 + d) / lambda0 := div_pos hadd hlambda0
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hmul := mul_le_mul_of_nonneg_left hlog hadd.le
  calc
    (lambda0 + d) * Real.log ((lambda0 + d) / lambda0) -
          (lambda0 + d) + lambda0
        ≤ (lambda0 + d) * (((lambda0 + d) / lambda0) - 1) -
            (lambda0 + d) + lambda0 := by linarith
    _ = d ^ 2 / lambda0 := by
      field_simp
      ring

/-- A pointwise envelope for the critical direction.  The lower cutoff of
`chi` turns any nonzero value into the denominator bound
`criticalBandwidth ≤ 1 - t`. -/
lemma criticalDirection_abs_le
    (c : ClassConstants) (cut : CutoffData c) {u Cchi Cpsi : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |criticalDirection c cut u n t| ≤
      |u| * Cchi * Cpsi /
        (Real.sqrt ((n : ℝ) * Real.log n) * criticalBandwidth c n) := by
  let z : ℝ := (n : ℝ) * Real.log n
  have hz : 0 < z := mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))
  have hsqrt : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hh : 0 < criticalBandwidth c n := criticalBandwidth_pos c hn
  by_cases hx : 1 - t = 0
  · rw [show criticalDirection c cut u n t = 0 by simp [criticalDirection, hx], abs_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg u) hCchi) hCpsi)
      (mul_nonneg (Real.sqrt_nonneg _) hh.le)
  by_cases hsmall : (1 - t) / criticalBandwidth c n ≤ 1
  · rw [criticalDirection_eq_zero_of_scaled_le_one c cut hx
      (critical_scaled_nonneg c hn ht) hsmall, abs_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg u) hCchi) hCpsi)
      (mul_nonneg (Real.sqrt_nonneg _) hh.le)
  · have hxpos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht.2) (Ne.symm hx)
    have hscaled : (1 : ℝ) < (1 - t) / criticalBandwidth c n := lt_of_not_ge hsmall
    have hhx : criticalBandwidth c n ≤ 1 - t := by
      simpa only [one_mul] using (le_div_iff₀ hh).mp hscaled.le
    have hchi' := hchi ((1 - t) / criticalBandwidth c n)
      (critical_scaled_nonneg c hn ht)
    have hpsi' := hpsi (1 - t) ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
    rw [criticalDirection]
    simp only [hx, ↓reduceIte, abs_div, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hxpos]
    rw [show |u| / Real.sqrt ((n : ℝ) * Real.log n) *
          |cut.chi ((1 - t) / criticalBandwidth c n)| * |cut.psi (1 - t)| /
            (1 - t) =
        (|u| * |cut.chi ((1 - t) / criticalBandwidth c n)| *
          |cut.psi (1 - t)|) /
            (Real.sqrt ((n : ℝ) * Real.log n) * (1 - t)) by
      field_simp]
    have hnum : |u| * |cut.chi ((1 - t) / criticalBandwidth c n)| *
        |cut.psi (1 - t)| ≤ |u| * Cchi * Cpsi := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hchi' (abs_nonneg u)) hpsi'
        (abs_nonneg _) (mul_nonneg (abs_nonneg u) hCchi)
    exact div_le_div₀ (mul_nonneg (mul_nonneg (abs_nonneg u) hCchi) hCpsi)
      hnum (mul_pos hsqrt hh) (mul_le_mul_of_nonneg_left hhx hsqrt.le)

/-- The pointwise critical-direction envelope in its simplified power-rate
form. -/
lemma criticalDirection_abs_le_rpow
    (c : ClassConstants) (cut : CutoffData c) {u Cchi Cpsi : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |criticalDirection c cut u n t| ≤
      |u| * Cchi * Cpsi * (((n : ℝ) * Real.log n) ^
        (-(c.beta / (2 * c.beta + 2)))) := by
  calc
    |criticalDirection c cut u n t| ≤
        |u| * Cchi * Cpsi /
          (Real.sqrt ((n : ℝ) * Real.log n) * criticalBandwidth c n) :=
      criticalDirection_abs_le c cut hn hCchi hCpsi hchi hpsi ht
    _ = _ := by
      rw [div_eq_mul_inv]
      congr 1
      simpa [one_div] using critical_normalization_eq_rpow c hn

/-- Smoothness and the cutoff identities provide finite absolute envelopes
for both factors appearing in the critical direction. -/
lemma CutoffData.exists_critical_abs_bounds (c : ClassConstants)
    (cut : CutoffData c) :
    ∃ Cchi Cpsi : ℝ, 0 ≤ Cchi ∧ 0 ≤ Cpsi ∧
      (∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi) := by
  have hchiCont : ContinuousOn (fun y : ℝ => |cut.chi y|)
      (Set.Icc (0 : ℝ) 2) :=
    (cut.chi_smooth.continuousOn.mono (Set.Icc_subset_Ici_self)).abs
  have hchiBdd : BddAbove ((fun y : ℝ => |cut.chi y|) '' Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.bddAbove_image hchiCont
  have hpsiCont : ContinuousOn (fun x : ℝ => |cut.psi x|)
      (Set.Icc (0 : ℝ) 1) :=
    (cut.psi_smooth.continuousOn.mono (Set.Icc_subset_Ici_self)).abs
  have hpsiBdd : BddAbove ((fun x : ℝ => |cut.psi x|) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hpsiCont
  let Cchi := max 1 (sSup ((fun y : ℝ => |cut.chi y|) '' Set.Icc (0 : ℝ) 2))
  let Cpsi := max 0 (sSup ((fun x : ℝ => |cut.psi x|) '' Set.Icc (0 : ℝ) 1))
  refine ⟨Cchi, Cpsi, le_trans zero_le_one (le_max_left _ _), le_max_left _ _, ?_, ?_⟩
  · intro y hy
    by_cases hy2 : y ≤ 2
    · exact (le_csSup hchiBdd ⟨y, ⟨hy, hy2⟩, rfl⟩).trans (le_max_right _ _)
    · rw [cut.chi_one y (le_of_not_ge hy2)]
      simp [Cchi]
  · intro x hx
    exact (le_csSup hpsiBdd ⟨x, hx, rfl⟩).trans (le_max_right _ _)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
