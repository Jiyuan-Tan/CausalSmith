module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotBernstein
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualMoments

/-!
Deterministic pilot clipping and normalization error transfer, normalized histogram envelopes,
and absorption of the raw histogram thresholds into the public allowance.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/- The deterministic part of the pilot roadmap, including its normalization step (20). -/

/-- Clipping cannot increase error relative to a value inside the clipping interval. -/
-- @node: clip_error_le
lemma clip_error_le (lo hi z v : ℝ) (hv : v ∈ Set.Icc lo hi) :
    |clip lo hi z - v| ≤ |z - v| := by
  by_cases hzlo : z < lo
  · rw [clip, min_eq_right (hzlo.le.trans (hv.1.trans hv.2)), max_eq_left hzlo.le]
    rw [abs_of_nonpos (sub_nonpos.mpr hv.1),
      abs_of_nonpos (sub_nonpos.mpr (hzlo.le.trans hv.1))]
    linarith
  · by_cases hzhi : hi < z
    · rw [clip, min_eq_left hzhi.le, max_eq_right (hv.1.trans hv.2)]
      rw [abs_of_nonneg (sub_nonneg.mpr hv.2),
        abs_of_nonneg (sub_nonneg.mpr (hv.2.trans hzhi.le))]
      linarith
    · rw [clip, min_eq_right (le_of_not_gt hzhi), max_eq_right (le_of_not_gt hzlo)]

/-- Propensity clipping preserves a bound on the raw cell treatment fraction. -/
-- @node: pilotPi_error_le_of_raw
lemma pilotPi_error_le_of_raw {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x D : ℝ)
    (hx : x ∈ Set.Icc 0 1)
    (hraw : |(if cellCount train mx x = 0 then (1 / 2 : ℝ) else
      (armCellCount train mx true x : ℝ) / cellCount train mx x) - P.e x| ≤ D) :
    |pilotPi train mx a x - pi P a x| ≤ D := by
  have he : |propensityPilot train mx x - P.e x| ≤ D :=
    (clip_error_le _ _ _ _ (hModel.overlap x hx)).trans hraw
  cases a
  · simpa only [pilotPi, pi, armProbability, Bool.false_eq_true, ↓reduceIte,
      sub_sub_sub_cancel_left, abs_sub_comm] using he
  · exact he

/-- Clipping the raw outcome cell height preserves error relative to the model density. -/
-- @node: clippedDensityPilot_error_le_of_raw
lemma clippedDensityPilot_error_le_of_raw {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x y D : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hraw : |(if armCellCount train mx a x = 0 then (1 : ℝ) else
      (my : ℝ) * outcomeCellCount train mx my a x y / armCellCount train mx a x) -
      P.eta a x y| ≤ D) :
    |clippedDensityPilot train mx my a x y - P.eta a x y| ≤ D := by
  have he := hModel.density_envelope a x y hx hy
  exact (clip_error_le _ _ _ _ ⟨by linarith [he.1], by linarith [he.2]⟩).trans hraw

/-- A pointwise clipped-density error bounds the normalization integral's error. -/
-- @node: pilot_normalizer_error_le
lemma pilot_normalizer_error_le {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x D : ℝ) (hx : x ∈ Set.Icc 0 1)
    (herror : ∀ y ∈ Set.Icc 0 1,
      |clippedDensityPilot train mx my a x y - P.eta a x y| ≤ D) :
    |(∫ y, clippedDensityPilot train mx my a x y ∂unitVolume) - 1| ≤ D := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi := (clippedDensityPilot_integrable train mx my a x).sub
    (P.eta_integrable a x hx)
  rw [← P.eta_normalized a x hx, ← integral_sub
    (clippedDensityPilot_integrable train mx my a x) (P.eta_integrable a x hx)]
  calc
    _ ≤ ∫ y, |clippedDensityPilot train mx my a x y - P.eta a x y| ∂unitVolume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℝ, D ∂unitVolume := by
      apply integral_mono_ae hi.abs (integrable_const D)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact herror y hy
    _ = D := by simp

/-- Normalizing a clipped pilot inflates its uniform error by at most forty. -/
-- @node: densityPilot_error_le_forty
lemma densityPilot_error_le_forty {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x y D : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hD : 0 ≤ D)
    (herror : ∀ yp ∈ Set.Icc 0 1,
      |clippedDensityPilot train mx my a x yp - P.eta a x yp| ≤ D) :
    |densityPilot train mx my a x y - P.eta a x y| ≤ 40 * D := by
  let s := ∫ yp, clippedDensityPilot train mx my a x yp ∂unitVolume
  have hs := clippedDensityPilot_integral_mem_Icc train mx my a x
  have hspos : 0 < s := by dsimp [s]; linarith [hs.1]
  have hsnorm : |s - 1| ≤ D := pilot_normalizer_error_le P train mx my a x D hx herror
  have heta : |P.eta a x y| ≤ 4 := by
    have he := hModel.density_envelope a x y hx hy
    rw [abs_of_nonneg (by linarith [he.1])]
    exact he.2
  have hid : clippedDensityPilot train mx my a x y / s - P.eta a x y =
      ((clippedDensityPilot train mx my a x y - P.eta a x y) +
        P.eta a x y * (1 - s)) / s := by
    field_simp
    ring
  change |clippedDensityPilot train mx my a x y / s - P.eta a x y| ≤ _
  rw [hid, abs_div, abs_of_pos hspos]
  apply (div_le_iff₀ hspos).2
  have hprod : |P.eta a x y * (1 - s)| ≤ 4 * D := by
    rw [abs_mul, abs_sub_comm 1 s]
    exact mul_le_mul heta hsnorm (abs_nonneg _) (by norm_num)
  have hnum := (abs_add_le (clippedDensityPilot train mx my a x y - P.eta a x y)
    (P.eta a x y * (1 - s))).trans (add_le_add (herror y hy) hprod)
  have hslo : (1 / 8 : ℝ) ≤ s := hs.1
  nlinarith [mul_le_mul_of_nonneg_left hslo hD]

/-- The raw histogram error transfers to the normalized density with factor forty. -/
-- @node: densityPilot_error_le_of_raw
lemma densityPilot_error_le_of_raw {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x y D : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hD : 0 ≤ D)
    (hraw : ∀ yp ∈ Set.Icc 0 1,
      |(if armCellCount train mx a x = 0 then (1 : ℝ) else
        (my : ℝ) * outcomeCellCount train mx my a x yp / armCellCount train mx a x) -
        P.eta a x yp| ≤ D) :
    |densityPilot train mx my a x y - P.eta a x y| ≤ 40 * D := by
  apply densityPilot_error_le_forty P hModel train mx my a x y D hx hy hD
  intro yp hyp
  exact clippedDensityPilot_error_le_of_raw P hModel train mx my a x yp D hx hyp
    (hraw yp hyp)

/-- Pointwise bounds on both pilots control the supremum-based pilot error. -/
-- @node: pilotError_le_of_pointwise
lemma pilotError_le_of_pointwise {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my : ℕ) (D : ℝ)
    (hpi : ∀ a x, x ∈ Set.Icc 0 1 → |pilotPi train mx a x - pi P a x| ≤ D)
    (heta : ∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      |densityPilot train mx my a x y - P.eta a x y| ≤ D) :
    pilotError P train mx my ≤ D := by
  apply max_le
  · apply csSup_le
    · exact ⟨_, false, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
    · rintro r ⟨a, x, hx, rfl⟩
      exact hpi a x hx
  · apply csSup_le
    · exact ⟨_, false, 0, 0, ⟨by norm_num, by norm_num⟩,
        ⟨by norm_num, by norm_num⟩, rfl⟩
    · rintro r ⟨a, x, y, hx, hy, rfl⟩
      exact heta a x y hx hy

/-- The model and deterministic pilot envelopes give an unconditional error bound. -/
-- @node: pilotError_le_sixtyfour
lemma pilotError_le_sixtyfour {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) : pilotError P train mx my ≤ 64 := by
  apply pilotError_le_of_pointwise
  · intro a x hx
    have hp := pilotPi_mem_Icc train mx a x
    have ht := model_pi_mem_Icc P hModel a x hx
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2, ht.1, ht.2]
  · intro a x y hx hy
    have hp := densityPilot_mem_Icc train mx my a x y
    have ht := hModel.density_envelope a x y hx hy
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2, ht.1, ht.2]

/-- A large public allowance makes every trained realization good. -/
-- @node: goodPilot_of_large_allowance
lemma goodPilot_of_large_allowance {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hh : 64 ≤ hAllow C0 m mx my) : GoodPilot P train C0 mx my :=
  (pilotError_le_sixtyfour P hModel train mx my).trans hh

/-- The explicit pilot failure allowance is nonnegative at every resolution. -/
-- @node: zetaAllow_nonneg
lemma zetaAllow_nonneg (m mx my : ℕ) : 0 ≤ zetaAllow m mx my := by
  unfold zetaAllow
  split_ifs <;> positivity

/-- The factor forty from normalization is absorbed by the public pilot multiplier. -/
-- @node: normalized_pilot_threshold_le
lemma normalized_pilot_threshold_le (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) :
    40 * (10 * x + 10 * y + Real.sqrt (1920 * z) + 160 * z) ≤
      (2 : ℝ) ^ 16 * (x + y + Real.sqrt z + z) := by
  have hs : Real.sqrt (1920 * z) ≤ 44 * Real.sqrt z := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hz]
  have hs0 := Real.sqrt_nonneg z
  rw [show (2 : ℝ) ^ 16 = 65536 by norm_num]
  linarith

/-- The raw outcome histogram threshold in (19), with tau = 30 log m,
remains below the pilot allowance after normalization. -/
-- @node: density_histogram_threshold_le_hAllow
lemma density_histogram_threshold_le_hAllow (m mx my : ℕ) (hm : 3 ≤ m) :
    40 * (10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
      160 * ((mx : ℝ) * my * Real.log m / m)) ≤ hAllow (2 ^ 16) m mx my := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  rw [hAllow, if_neg (by omega)]
  exact normalized_pilot_threshold_le _ _ _ (by positivity) (by positivity) (by positivity)

/-- The propensity threshold in (18) is dominated by the normalized outcome threshold:
the outcome resolution is at least one. -/
-- @node: propensity_histogram_threshold_le_density
lemma propensity_histogram_threshold_le_density (m mx my : ℕ) (hm : 3 ≤ m)
    (hmy : 1 ≤ my) :
    10 * (mx : ℝ) ^ (-1 / 10 : ℝ) +
      Real.sqrt (240 * ((mx : ℝ) * Real.log m / m)) +
      80 * ((mx : ℝ) * Real.log m / m) ≤
    10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
      160 * ((mx : ℝ) * my * Real.log m / m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  have hmy1 : (1 : ℝ) ≤ my := by exact_mod_cast hmy
  have hz : 0 ≤ (mx : ℝ) * Real.log m / m := by positivity
  have hzz : (mx : ℝ) * Real.log m / m ≤ (mx : ℝ) * my * Real.log m / m := by
    calc
      _ ≤ ((mx : ℝ) * Real.log m / m) * my := le_mul_of_one_le_right hz hmy1
      _ = _ := by ring
  have hs : Real.sqrt (240 * ((mx : ℝ) * Real.log m / m)) ≤
      Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hy : 0 ≤ (my : ℝ)⁻¹ := by positivity
  linarith

/-- Raw pointwise histogram bounds (18)--(19) imply the good-pilot event;
clipping, normalization, and the public constant are handled deterministically here. -/
-- @node: goodPilot_of_raw_histogram_bounds
lemma goodPilot_of_raw_histogram_bounds {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (hm : 3 ≤ m) (hmy : 1 ≤ my)
    (hpi : ∀ x ∈ Set.Icc 0 1,
      |(if cellCount train mx x = 0 then (1 / 2 : ℝ) else
        (armCellCount train mx true x : ℝ) / cellCount train mx x) - P.e x| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) +
        Real.sqrt (240 * ((mx : ℝ) * Real.log m / m)) +
        80 * ((mx : ℝ) * Real.log m / m))
    (heta : ∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      |(if armCellCount train mx a x = 0 then (1 : ℝ) else
        (my : ℝ) * outcomeCellCount train mx my a x y / armCellCount train mx a x) -
        P.eta a x y| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
        Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
        160 * ((mx : ℝ) * my * Real.log m / m)) :
    GoodPilot P train (2 ^ 16) mx my := by
  let D := 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
    Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
    160 * ((mx : ℝ) * my * Real.log m / m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hallow : 40 * D ≤ hAllow (2 ^ 16) m mx my :=
    density_histogram_threshold_le_hAllow m mx my hm
  apply pilotError_le_of_pointwise
  · intro a x hx
    have hraw := (hpi x hx).trans
      (propensity_histogram_threshold_le_density m mx my hm hmy)
    exact (pilotPi_error_le_of_raw P hModel train mx a x D hx hraw).trans
      ((by linarith : D ≤ 40 * D).trans hallow)
  · intro a x y hx hy
    exact (densityPilot_error_le_of_raw P hModel train mx my a x y D hx hy hD
      (fun yp hyp => heta a x yp hx hyp)).trans hallow

end CausalSmith.Stat.DensityEffectRoughNull
