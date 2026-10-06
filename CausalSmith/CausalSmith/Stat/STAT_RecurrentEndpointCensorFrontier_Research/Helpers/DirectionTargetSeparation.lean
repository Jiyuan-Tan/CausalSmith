module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.TargetSeparationBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rate-scale lower bounds for direction integrals

This file proves quantitative lower bounds for the survival-weighted endpoint
and critical directions at the explicit midpoint baseline.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Survival at the horizon under the constant midpoint death hazard. -/
@[no_expose]
noncomputable def midpointSurvivalFloor (c : ClassConstants) (P₀ : SubjectLaw) : ℝ :=
  survival (midpointBaseline c P₀) true 1

lemma midpointSurvivalFloor_pos (c : ClassConstants) (P₀ : SubjectLaw) :
    0 < midpointSurvivalFloor c P₀ := by
  rw [midpointSurvivalFloor, midpointBaseline_eq_baseline]
  unfold survival SubjectLaw.baseline
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact Real.exp_pos _

lemma midpointSurvivalFloor_le (c : ClassConstants) (P₀ : SubjectLaw)
    {t : ℝ} (ht : t ≤ 1) :
    midpointSurvivalFloor c P₀ ≤ survival (midpointBaseline c P₀) true t := by
  simpa [midpointSurvivalFloor, midpointBaseline_eq_baseline] using
    SubjectLaw.baseline_survival_antitone P₀ (midpointLambda c)
      (midpointDeath c) (midpointDeath_pos c) true ht

lemma midpointBaseline_survival_continuous (c : ClassConstants) (P₀ : SubjectLaw)
    (a : Arm) : Continuous (survival (midpointBaseline c P₀) a) := by
  rw [midpointBaseline_eq_baseline]
  unfold survival SubjectLaw.baseline
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  fun_prop

/-- The endpoint direction integral is bounded below by its exact bump mass,
the terminal survival floor, and the classical `h^(beta+1)` scaling. -/
lemma endpointDirection_integral_lower
    (c : ClassConstants) (P₀ : SubjectLaw) (cut : CutoffData c)
    {u h : ℝ} (hu : 0 < u) (hh : 0 < h) (hh1 : h ≤ 1) :
    midpointSurvivalFloor c P₀ * u * endpointBumpMass c cut * h ^ (c.beta + 1) ≤
      ∫ t in (0 : ℝ)..1,
        survival (midpointBaseline c P₀) true t * endpointDirection c cut u h t := by
  let S := fun t : ℝ ↦ survival (midpointBaseline c P₀) true t
  let d := endpointDirection c cut u h
  have hdcont : Continuous d := endpointDirection_continuous c cut u h hh.ne'
  have hfcont : Continuous (fun t ↦ S t * d t) :=
    (midpointBaseline_survival_continuous c P₀ true).mul hdcont
  have hfullInt : IntervalIntegrable (fun t ↦ S t * d t) volume 0 1 :=
    hfcont.intervalIntegrable _ _
  have hnonneg : ∀ t : ℝ, 0 ≤ S t * d t := by
    intro t
    exact mul_nonneg (Real.exp_nonneg _)
      (endpointDirection_nonneg c cut (t := t) hu.le hh.le)
  have hrestrict :
      (∫ t in (1 - h)..1, S t * d t) ≤ ∫ t in (0 : ℝ)..1, S t * d t := by
    exact intervalIntegral.integral_mono_interval (sub_nonneg.mpr hh1) (by linarith) le_rfl
      (Filter.Eventually.of_forall hnonneg) hfullInt
  have hsubInt : IntervalIntegrable (fun t ↦ S t * d t) volume (1 - h) 1 :=
    hfullInt.mono_set (Set.uIcc_subset_uIcc
      (by simp [hh1, hh.le])
      (by simp))
  have hlowerInt : IntervalIntegrable (fun t ↦ midpointSurvivalFloor c P₀ * d t)
      volume (1 - h) 1 :=
    (continuous_const.mul hdcont).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (1 - h) (1 : ℝ),
      midpointSurvivalFloor c P₀ * d t ≤ S t * d t := by
    intro t ht
    exact mul_le_mul_of_nonneg_right (midpointSurvivalFloor_le c P₀ ht.2)
      (endpointDirection_nonneg c cut (t := t) hu.le hh.le)
  have hmono := intervalIntegral.integral_mono_on (by linarith : 1 - h ≤ (1 : ℝ))
    hlowerInt hsubInt hpoint
  have hdirInt :
      (∫ t in (1 - h)..1, u * h ^ c.beta * cut.bump ((1 - t) / h)) =
        u * h ^ c.beta * (∫ t in (1 - h)..1,
          cut.bump ((1 - t) / h)) := by
    rw [intervalIntegral.integral_const_mul]
  calc
    midpointSurvivalFloor c P₀ * u * endpointBumpMass c cut * h ^ (c.beta + 1) =
        ∫ t in (1 - h)..1, midpointSurvivalFloor c P₀ * d t := by
      rw [intervalIntegral.integral_const_mul]
      simp only [d, endpointDirection]
      rw [hdirInt]
      rw [integral_rescaled_endpointBump c cut hh, Real.rpow_add hh,
        Real.rpow_one]
      ring
    _ ≤ ∫ t in (1 - h)..1, S t * d t := hmono
    _ ≤ ∫ t in (0 : ℝ)..1, S t * d t := hrestrict

lemma endpointBandwidth_beta_add_one (c : ClassConstants) {n : ℕ} (hn : 1 ≤ n) :
    endpointBandwidth c n ^ (c.beta + 1) =
      (n : ℝ) ^ (-(c.beta + 1) / (2 * c.beta + c.kappa + 1)) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  rw [endpointBandwidth_eq, ← Real.rpow_mul hn0]
  congr 1
  have hden : 2 * c.beta + c.kappa + 1 ≠ 0 := by
    nlinarith [c.beta_pos, c.kappa_pos]
  field_simp [hden]

/-- Endpoint directions achieve the frozen polynomial target-separation rate
with a positive coefficient independent of sample size. -/
lemma endpointDirection_integral_rate_lower
    (c : ClassConstants) (P₀ : SubjectLaw) (cut : CutoffData c) {u : ℝ}
    (hu : 0 < u) {n : ℕ} (hn : 1 ≤ n) :
    let delta := midpointSurvivalFloor c P₀ * u * endpointBumpMass c cut
    0 < delta ∧
      delta * (n : ℝ) ^ (-(c.beta + 1) /
        (2 * c.beta + c.kappa + 1)) ≤
        ∫ t in (0 : ℝ)..1,
          survival (midpointBaseline c P₀) true t *
            endpointDirection c cut u (endpointBandwidth c n) t := by
  dsimp only
  have hdelta : 0 < midpointSurvivalFloor c P₀ * u * endpointBumpMass c cut :=
    mul_pos (mul_pos (midpointSurvivalFloor_pos c P₀) hu)
      (endpointBumpMass_pos c cut)
  refine ⟨hdelta, ?_⟩
  rw [← endpointBandwidth_beta_add_one c hn]
  exact endpointDirection_integral_lower c P₀ cut hu
    (endpointBandwidth_pos c hn) (endpointBandwidth_le_one c hn)

/-- On any endpoint-distance annulus, the possibly signed critical integral is
bounded below by the inverse-distance envelope. -/
lemma criticalDirection_integral_band_lower
    (c : ClassConstants) (P₀ : SubjectLaw) (cut : CutoffData c)
    {u Cchi Cpsi a b : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    -( |u| * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n) *
        Real.log (b / a)) ≤
      ∫ t in (1 - b)..(1 - a),
        survival (midpointBaseline c P₀) true t * criticalDirection c cut u n t := by
  let S := fun t : ℝ ↦ survival (midpointBaseline c P₀) true t
  let d := criticalDirection c cut u n
  let A := |u| * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n)
  have hbpos : 0 < b := ha.trans_le hab
  have hz : 0 < (n : ℝ) * Real.log n := mul_pos
    (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))
  have hA : 0 ≤ A := div_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg u) hCchi) hCpsi) (Real.sqrt_nonneg _)
  have hdcont : ContinuousOn d (Set.Icc (0 : ℝ) 1) :=
    criticalDirection_continuousOn c cut u hn
  have hscont : Continuous S := midpointBaseline_survival_continuous c P₀ true
  have hsub : Set.Icc (1 - b) (1 - a) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1, hb], by linarith [ht.2, ha]⟩
  have hright : IntervalIntegrable (fun t ↦ S t * d t) volume (1 - b) (1 - a) :=
    (hscont.continuousOn.mul (hdcont.mono hsub)).intervalIntegrable_of_Icc
      (by linarith)
  have hleft : IntervalIntegrable (fun t ↦ -A * (1 - t)⁻¹) volume
      (1 - b) (1 - a) := by
    have hxcont : ContinuousOn (fun t : ℝ ↦ 1 - t)
        (Set.Icc (1 - b) (1 - a)) :=
      (continuous_const.sub continuous_id).continuousOn
    have hxne : ∀ t ∈ Set.Icc (1 - b) (1 - a), 1 - t ≠ 0 := by
      intro t ht hzero
      linarith [ht.2, ha]
    apply ContinuousOn.intervalIntegrable_of_Icc
    · exact sub_le_sub_left hab 1
    · exact continuousOn_const.mul (hxcont.inv₀ hxne)
  have hpoint : ∀ t ∈ Set.Icc (1 - b) (1 - a),
      -A * (1 - t)⁻¹ ≤ S t * d t := by
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := hsub ht
    have ht1 : t < 1 := by linarith [ht.2, ha]
    have hs := SubjectLaw.baseline_survival_mem_unitInterval P₀
      (midpointLambda c) (midpointDeath c) (midpointDeath_pos c)
      (a := true) ht01.1
    have hs' : S t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [S, midpointBaseline_eq_baseline] using hs
    have hdabs := criticalDirection_abs_le_distance c cut (u := u) hn hCchi hCpsi
      hchi hpsi ht01 ht1
    have hx : 0 < 1 - t := by linarith
    have hprod : |S t * d t| ≤ A * (1 - t)⁻¹ := by
      rw [abs_mul, abs_of_nonneg hs'.1]
      calc
        S t * |d t| ≤ 1 * |d t| := mul_le_mul_of_nonneg_right hs'.2 (abs_nonneg _)
        _ ≤ A * (1 - t)⁻¹ := by
          calc
            1 * |d t| ≤
                |u| * Cchi * Cpsi /
                  (Real.sqrt ((n : ℝ) * Real.log n) * (1 - t)) := by
                    simpa [d] using hdabs
            _ = A * (1 - t)⁻¹ := by
              dsimp [A]
              field_simp [Real.sqrt_ne_zero'.mpr hz, hx.ne']
    simpa only [neg_mul] using neg_le_of_abs_le hprod
  have hmono := intervalIntegral.integral_mono_on (by linarith : 1 - b ≤ 1 - a)
    hleft hright hpoint
  have hinv : (∫ t in (1 - b)..(1 - a), (1 - t)⁻¹) = Real.log (b / a) := by
    rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x⁻¹) 1]
    convert integral_inv_of_pos ha hbpos using 1 <;> ring
  calc
    -( |u| * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n) *
        Real.log (b / a)) =
        ∫ t in (1 - b)..(1 - a), -A * (1 - t)⁻¹ := by
      rw [intervalIntegral.integral_const_mul, hinv]
      simp only [A]
      ring
    _ ≤ _ := hmono

/-- On the central critical band both cutoffs equal one, so the logarithmic
inverse-distance mass has a positive survival-weighted lower bound. -/
lemma criticalDirection_integral_core_lower
    (c : ClassConstants) (P₀ : SubjectLaw) (cut : CutoffData c)
    {u : ℝ} {n : ℕ} (hn : 2 ≤ n) (hu : 0 < u)
    (hh : 2 * criticalBandwidth c n ≤ c.x0 / 4) :
    midpointSurvivalFloor c P₀ *
        (u / Real.sqrt ((n : ℝ) * Real.log n)) *
        Real.log ((c.x0 / 4) / (2 * criticalBandwidth c n)) ≤
      ∫ t in (1 - c.x0 / 4)..(1 - 2 * criticalBandwidth c n),
        survival (midpointBaseline c P₀) true t * criticalDirection c cut u n t := by
  let h := criticalBandwidth c n
  let S := fun t : ℝ ↦ survival (midpointBaseline c P₀) true t
  let d := criticalDirection c cut u n
  let A := u / Real.sqrt ((n : ℝ) * Real.log n)
  have hhpos : 0 < h := criticalBandwidth_pos c hn
  have hx0 : 0 < c.x0 / 4 := div_pos c.x0_pos (by norm_num)
  have hz : 0 < (n : ℝ) * Real.log n := mul_pos
    (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))
  have hA : 0 < A := div_pos hu (Real.sqrt_pos.2 hz)
  have hord : 1 - c.x0 / 4 ≤ 1 - 2 * h := sub_le_sub_left hh 1
  have hsub : Set.Icc (1 - c.x0 / 4) (1 - 2 * h) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    constructor
    · linarith [ht.1, c.x0_le]
    · linarith [ht.2, hhpos]
  have hdcont := (criticalDirection_continuousOn c cut u hn).mono hsub
  have hscont : ContinuousOn S (Set.Icc (1 - c.x0 / 4) (1 - 2 * h)) :=
    (midpointBaseline_survival_continuous c P₀ true).continuousOn
  have hright : IntervalIntegrable (fun t ↦ S t * d t) volume
      (1 - c.x0 / 4) (1 - 2 * h) :=
    (hscont.mul hdcont).intervalIntegrable_of_Icc hord
  have hinvCont : ContinuousOn (fun t : ℝ ↦ (1 - t)⁻¹)
      (Set.Icc (1 - c.x0 / 4) (1 - 2 * h)) := by
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro t ht hzero
    change 1 - t = 0 at hzero
    linarith [ht.2, hhpos]
  have hleft : IntervalIntegrable
      (fun t ↦ midpointSurvivalFloor c P₀ * A * (1 - t)⁻¹) volume
      (1 - c.x0 / 4) (1 - 2 * h) :=
    (continuousOn_const.mul hinvCont).intervalIntegrable_of_Icc hord
  have hpoint : ∀ t ∈ Set.Icc (1 - c.x0 / 4) (1 - 2 * h),
      midpointSurvivalFloor c P₀ * A * (1 - t)⁻¹ ≤ S t * d t := by
    intro t ht
    have hx : 0 < 1 - t := by linarith [ht.2, hhpos]
    have hxupper : 1 - t ≤ c.x0 / 4 := by linarith [ht.1]
    have hscaled : 2 ≤ (1 - t) / h := by
      exact (le_div_iff₀ hhpos).2 (by linarith [ht.2])
    have hchi : cut.chi ((1 - t) / h) = 1 := cut.chi_one _ hscaled
    have hpsi : cut.psi (1 - t) = 1 :=
      cut.psi_one _ ⟨hx.le, hxupper⟩
    have hd : d t = A * (1 - t)⁻¹ := by
      dsimp [d, A, h]
      rw [criticalDirection, if_neg hx.ne', hchi, hpsi]
      field_simp [hx.ne']
    rw [hd]
    simpa only [S, mul_assoc] using
      mul_le_mul_of_nonneg_right
        (midpointSurvivalFloor_le c P₀ (t := t) (by linarith [ht.2]))
        (mul_nonneg hA.le (inv_nonneg.mpr hx.le))
  have hmono := intervalIntegral.integral_mono_on hord hleft hright hpoint
  have hinv : (∫ t in (1 - c.x0 / 4)..(1 - 2 * h), (1 - t)⁻¹) =
      Real.log ((c.x0 / 4) / (2 * h)) := by
    rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x⁻¹) 1]
    have htwoh : 0 < 2 * h := mul_pos (by norm_num) hhpos
    convert integral_inv_of_pos htwoh hx0 using 1 <;> ring
  calc
    midpointSurvivalFloor c P₀ * A * Real.log ((c.x0 / 4) / (2 * h)) =
        ∫ t in (1 - c.x0 / 4)..(1 - 2 * h),
          midpointSurvivalFloor c P₀ * A * (1 - t)⁻¹ := by
      rw [intervalIntegral.integral_const_mul, hinv]
    _ ≤ _ := hmono

/-- The full critical direction integral contains its positive logarithmic
core, up to the two fixed-width cutoff transition costs. -/
lemma criticalDirection_integral_log_lower
    (c : ClassConstants) (P₀ : SubjectLaw) (cut : CutoffData c)
    {u Cchi Cpsi : ℝ} {n : ℕ} (hn : 2 ≤ n) (hu : 0 < u)
    (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    (hh : 2 * criticalBandwidth c n ≤ c.x0 / 4) :
    (u / Real.sqrt ((n : ℝ) * Real.log n)) *
        (midpointSurvivalFloor c P₀ *
            Real.log ((c.x0 / 8) / criticalBandwidth c n) -
          Cchi * Cpsi * (Real.log 4 + Real.log 2)) ≤
      ∫ t in (0 : ℝ)..1,
        survival (midpointBaseline c P₀) true t *
          criticalDirection c cut u n t := by
  let h := criticalBandwidth c n
  let f := fun t : ℝ ↦ survival (midpointBaseline c P₀) true t *
    criticalDirection c cut u n t
  have hhpos : 0 < h := criticalBandwidth_pos c hn
  have hh1 : 2 * h ≤ 1 := by linarith [hh, c.x0_le]
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (midpointBaseline_survival_continuous c P₀ true).continuousOn.mul
      (criticalDirection_continuousOn c cut u hn)
  have hint : IntervalIntegrable f volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have hseg (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
      IntervalIntegrable f volume a b :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro x hx
      exact ⟨ha.trans hx.1, hx.2.trans hb⟩)
  have hleftzero : (∫ t in (0 : ℝ)..(1 - c.x0), f t) = 0 := by
    rw [show (∫ t in (0 : ℝ)..(1 - c.x0), f t) =
        ∫ _t in (0 : ℝ)..(1 - c.x0), (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) (1 - c.x0) := by
        have hord : (0 : ℝ) ≤ 1 - c.x0 := by linarith [c.x0_le]
        rw [Set.uIcc_of_le hord] at ht
        exact ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht'.1, ht'.2.trans (by linarith [c.x0_pos])⟩
      have hd : criticalDirection c cut u n t = 0 := by
        by_contra hne
        have hb := criticalDirection_ne_zero_imp_band c cut hn ht01 hne
        linarith [ht'.2, hb.2]
      simp [f, hd]
      ]
    simp
  have hrightzero : (∫ t in (1 - h)..1, f t) = 0 := by
    rw [show (∫ t in (1 - h)..1, f t) =
        ∫ _t in (1 - h)..1, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (1 - h) (1 : ℝ) := by
        simpa [Set.uIcc_of_le (by linarith : 1 - h ≤ (1 : ℝ))] using ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [hh1, ht'.1], ht'.2⟩
      have hd : criticalDirection c cut u n t = 0 :=
        criticalDirection_eq_zero_of_endpoint_band c cut (u := u) hn ht01
          (show 1 - t ≤ h by linarith [ht'.1])
      change survival (midpointBaseline c P₀) true t *
        criticalDirection c cut u n t = 0
      rw [hd, mul_zero]
      ]
    simp
  have houter := criticalDirection_integral_band_lower c P₀ cut (u := u) hn hCchi hCpsi
    hchi hpsi (div_pos c.x0_pos (by norm_num : (0 : ℝ) < 4))
    (by linarith [c.x0_pos] : c.x0 / 4 ≤ c.x0)
    (by linarith [c.x0_le] : c.x0 ≤ 1)
  have hinner := criticalDirection_integral_band_lower c P₀ cut (u := u) hn hCchi hCpsi
    hchi hpsi hhpos (by linarith : h ≤ 2 * h)
    (hh.trans (by have := c.x0_le; linarith) : 2 * h ≤ 1)
  have hcore := criticalDirection_integral_core_lower c P₀ cut hn hu hh
  have habs : |u| = u := abs_of_pos hu
  have houter' :
      -(u * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n) * Real.log 4) ≤
        ∫ t in (1 - c.x0)..(1 - c.x0 / 4), f t := by
    have hratio : c.x0 / (c.x0 / 4) = (4 : ℝ) := by
      field_simp [c.x0_pos.ne']
    rw [habs, hratio] at houter
    exact houter
  have hinner' :
      -(u * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n) * Real.log 2) ≤
        ∫ t in (1 - 2 * h)..(1 - h), f t := by
    have hratio : 2 * h / h = (2 : ℝ) := by field_simp [hhpos.ne']
    rw [habs, hratio] at hinner
    exact hinner
  have hcore' :
      midpointSurvivalFloor c P₀ *
          (u / Real.sqrt ((n : ℝ) * Real.log n)) *
          Real.log ((c.x0 / 8) / h) ≤
        ∫ t in (1 - c.x0 / 4)..(1 - 2 * h), f t := by
    convert hcore using 1 <;> dsimp only [h, f] <;> ring
  have hdecomp :
      (∫ t in (0 : ℝ)..1, f t) =
        (∫ t in (1 - c.x0)..(1 - c.x0 / 4), f t) +
        (∫ t in (1 - c.x0 / 4)..(1 - 2 * h), f t) +
        (∫ t in (1 - 2 * h)..(1 - h), f t) := by
    have h0x := hseg 0 (1 - c.x0) (by norm_num) (by linarith [c.x0_pos])
      (by linarith [c.x0_le])
    have hxo := hseg (1 - c.x0) (1 - c.x0 / 4)
      (by linarith [c.x0_le]) (by linarith [c.x0_pos]) (by linarith [c.x0_pos])
    have hoc := hseg (1 - c.x0 / 4) (1 - 2 * h)
      (by linarith [c.x0_le]) (by linarith [hhpos])
      (sub_le_sub_left hh 1)
    have hci := hseg (1 - 2 * h) (1 - h)
      (by linarith [hh1]) (by linarith [hhpos]) (by linarith [hhpos])
    have hi1 := hseg (1 - h) 1 (by linarith [hh1]) (by norm_num)
      (by linarith [hhpos])
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (((h0x.trans hxo).trans hoc).trans hci) hi1,
      hrightzero, add_zero,
      ← intervalIntegral.integral_add_adjacent_intervals ((h0x.trans hxo).trans hoc) hci,
      ← intervalIntegral.integral_add_adjacent_intervals (h0x.trans hxo) hoc,
      ← intervalIntegral.integral_add_adjacent_intervals h0x hxo,
      hleftzero, zero_add]
  rw [hdecomp]
  dsimp only [h] at houter' hinner' hcore' ⊢
  calc
    u / Real.sqrt ((n : ℝ) * Real.log n) *
          (midpointSurvivalFloor c P₀ *
              Real.log (c.x0 / 8 / criticalBandwidth c n) -
            Cchi * Cpsi * (Real.log 4 + Real.log 2)) =
        -(u * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n) * Real.log 4) +
          midpointSurvivalFloor c P₀ *
            (u / Real.sqrt ((n : ℝ) * Real.log n)) *
              Real.log (c.x0 / 8 / criticalBandwidth c n) +
          -(u * Cchi * Cpsi / Real.sqrt ((n : ℝ) * Real.log n) * Real.log 2) := by
            ring
    _ ≤ _ := add_le_add (add_le_add houter' hcore') hinner'

lemma log_nat_div_sqrt_mul_eq_sqrt_div {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / Real.sqrt ((n : ℝ) * Real.log n) =
      Real.sqrt (Real.log n / n) := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
  have hsqrtlog : Real.sqrt (Real.log n) ≠ 0 := (Real.sqrt_pos.2 hlog).ne'
  rw [Real.sqrt_mul hnpos.le, Real.sqrt_div hlog.le]
  have hsq := Real.sq_sqrt hlog.le
  field_simp [hsqrtn, hsqrtlog]
  nlinarith

/-- The reciprocal critical bandwidth has a logarithm diverging to infinity. -/
lemma tendsto_neg_log_criticalBandwidth_atTop (c : ClassConstants) :
    Filter.Tendsto (fun n : ℕ ↦ -Real.log (criticalBandwidth c n))
      Filter.atTop Filter.atTop := by
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hcast
  have hprod : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log n)
      Filter.atTop Filter.atTop := hcast.atTop_mul_atTop₀ hlog
  have hlogprod : Filter.Tendsto
      (fun n : ℕ ↦ Real.log ((n : ℝ) * Real.log n))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hprod
  have hden : 0 < 2 * c.beta + 2 := by nlinarith [c.beta_pos]
  have hdiv := hlogprod.atTop_div_const hden
  refine hdiv.congr' ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩] with n hn
  exact (neg_log_criticalBandwidth c hn).symm

/-- Critical directions achieve the frozen `sqrt(log n / n)` separation
rate with one positive coefficient and one sample threshold. -/
lemma exists_criticalDirection_integral_rate_lower
    (c : ClassConstants) (P₀ : SubjectLaw) (cut : CutoffData c) {u : ℝ}
    (hu : 0 < u) :
    ∃ delta : ℝ, ∃ N : ℕ, 0 < delta ∧ 3 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        delta * Real.sqrt (Real.log n / n) ≤
          ∫ t in (0 : ℝ)..1,
            survival (midpointBaseline c P₀) true t *
              criticalDirection c cut u n t := by
  rcases cut.exists_critical_abs_bounds c with
    ⟨Cchi, Cpsi, hCchi, hCpsi, hchi, hpsi⟩
  let s := midpointSurvivalFloor c P₀
  let B := Cchi * Cpsi * (Real.log 4 + Real.log 2)
  let D := 2 * c.beta + 2
  let delta := s * u / (2 * D)
  have hs : 0 < s := midpointSurvivalFloor_pos c P₀
  have hD : 0 < D := by dsimp [D]; nlinarith [c.beta_pos]
  have hdelta : 0 < delta := div_pos (mul_pos hs hu) (mul_pos (by norm_num) hD)
  have heventLog : ∀ᶠ n in Filter.atTop,
      (2 * (B - s * Real.log (c.x0 / 8)) / s) ≤
        -Real.log (criticalBandwidth c n) :=
    (tendsto_atTop.1 (tendsto_neg_log_criticalBandwidth_atTop c)) _
  have heventSmall : ∀ᶠ n in Filter.atTop,
      criticalBandwidth c n < c.x0 / 8 :=
    (tendsto_order.1 (criticalBandwidth_tendsto_zero c)).2 _
      (div_pos c.x0_pos (by norm_num))
  have heventNatLog : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log n := by
    exact (tendsto_atTop.1
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)) 1
  rcases Filter.eventually_atTop.1 (heventLog.and (heventSmall.and heventNatLog)) with
    ⟨N₀, hN₀⟩
  let N := max 3 N₀
  refine ⟨delta, N, hdelta, le_max_left _ _, ?_⟩
  intro n hn
  have hall := hN₀ n (le_trans (le_max_right _ _) hn)
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hbwpos : 0 < criticalBandwidth c n := criticalBandwidth_pos c hn2
  have hh : 2 * criticalBandwidth c n ≤ c.x0 / 4 := by
    linarith [hall.2.1]
  have hlogratio :
      Real.log ((c.x0 / 8) / criticalBandwidth c n) =
        Real.log (c.x0 / 8) - Real.log (criticalBandwidth c n) := by
    rw [Real.log_div (div_ne_zero c.x0_pos.ne' (by norm_num)) hbwpos.ne']
  have hbracket :
      s / 2 * (-Real.log (criticalBandwidth c n)) ≤
        s * Real.log ((c.x0 / 8) / criticalBandwidth c n) - B := by
    rw [hlogratio]
    have := hall.1
    apply (div_le_iff₀ hs).mp at this
    linarith
  have hfinite := criticalDirection_integral_log_lower c P₀ cut hn2 hu
    hCchi hCpsi hchi hpsi hh
  have hz : 0 < (n : ℝ) * Real.log n := mul_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn2))
  have hfactor : 0 ≤ u / Real.sqrt ((n : ℝ) * Real.log n) :=
    (div_pos hu (Real.sqrt_pos.2 hz)).le
  have hmain :
      (u / Real.sqrt ((n : ℝ) * Real.log n)) *
          (s / 2 * (-Real.log (criticalBandwidth c n))) ≤
        ∫ t in (0 : ℝ)..1,
          survival (midpointBaseline c P₀) true t *
            criticalDirection c cut u n t := by
    calc
      _ ≤ (u / Real.sqrt ((n : ℝ) * Real.log n)) *
          (s * Real.log ((c.x0 / 8) / criticalBandwidth c n) - B) :=
        mul_le_mul_of_nonneg_left hbracket hfactor
      _ ≤ _ := by simpa only [s, B] using hfinite
  have hlogz : Real.log n ≤ Real.log ((n : ℝ) * Real.log n) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact (show 0 < (n : ℝ) by positivity)
    · exact hz
    · nlinarith [hall.2.2]
  rw [neg_log_criticalBandwidth c hn2] at hmain
  have hscaled :
      (u / Real.sqrt ((n : ℝ) * Real.log n)) * (s / 2) *
          (Real.log n / (2 * c.beta + 2)) ≤
        ∫ t in (0 : ℝ)..1,
          survival (midpointBaseline c P₀) true t *
            criticalDirection c cut u n t := by
    calc
      _ ≤ (u / Real.sqrt ((n : ℝ) * Real.log n)) * (s / 2) *
          (Real.log ((n : ℝ) * Real.log n) / (2 * c.beta + 2)) := by
            gcongr
      _ ≤ _ := by convert hmain using 1 <;> ring
  calc
    delta * Real.sqrt (Real.log n / n) =
        (u / Real.sqrt ((n : ℝ) * Real.log n)) * (s / 2) *
          (Real.log n / (2 * c.beta + 2)) := by
      rw [← log_nat_div_sqrt_mul_eq_sqrt_div hn2]
      dsimp [delta, D]
      have hden : 2 * c.beta + 2 ≠ 0 := by nlinarith [c.beta_pos]
      have hsqrt : Real.sqrt ((n : ℝ) * Real.log n) ≠ 0 :=
        (Real.sqrt_pos.2 hz).ne'
      field_simp [hden, hsqrt]
      <;> ring
    _ ≤ _ := hscaled

#print axioms endpointDirection_integral_rate_lower
#print axioms criticalDirection_integral_log_lower
#print axioms exists_criticalDirection_integral_rate_lower

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
