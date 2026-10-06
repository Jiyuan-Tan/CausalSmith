module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualSecondMoment

/-!
Exact observable corrected-mean identity and its public good-pilot norm allowance.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- The propensity component of the supremum error controls every unit-domain value. -/
-- @node: pilotPi_error_le_pilotError
lemma pilotPi_error_le_pilotError {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) :
    |pilotPi train mx a x - pi P a x| ≤ pilotError P train mx my := by
  have hb : BddAbove {r : ℝ | ∃ a x, x ∈ Set.Icc 0 1 ∧
      r = |pilotPi train mx a x - pi P a x|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨b, z, hz, rfl⟩
    have hp := pilotPi_mem_Icc train mx b z
    have ht := model_pi_mem_Icc P hModel b z hz
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2, ht.1, ht.2]
  exact (le_csSup hb ⟨a, x, hx, rfl⟩).trans (le_max_left _ _)

/-- The density component of the supremum error controls every unit-domain value. -/
-- @node: werr_abs_le_pilotError
lemma werr_abs_le_pilotError {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x y : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |werr P train mx my a x y| ≤ pilotError P train mx my := by
  have hb : BddAbove {r : ℝ | ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
      r = |densityPilot train mx my a x y - P.eta a x y|} := by
    refine ⟨64, ?_⟩
    rintro r ⟨b, z, v, hz, hv, rfl⟩
    have hp := densityPilot_mem_Icc train mx my b z v
    have ht := hModel.density_envelope b z v hz hv
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2, ht.1, ht.2]
  have he : |densityPilot train mx my a x y - P.eta a x y| ≤ pilotError P train mx my :=
    (le_csSup hb ⟨a, x, y, hx, hy, rfl⟩).trans (le_max_right _ _)
  simpa only [werr, abs_sub_comm] using he

/-- The good-pilot event forces its allowance to be nonnegative. -/
-- @node: goodPilot_allowance_nonneg
lemma goodPilot_allowance_nonneg {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) : 0 ≤ hAllow C0 m mx my := by
  exact (abs_nonneg _).trans
    ((pilotPi_error_le_pilotError P hModel train mx my false 0
      ⟨by norm_num, by norm_num⟩).trans hG)

/-- Pilot clipping converts the absolute propensity error into the relative error in (23). -/
-- @node: goodPilot_uerr_abs_le
lemma goodPilot_uerr_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : |uerr P train mx a x| ≤ 4 * hAllow C0 m mx my := by
  have hp := pilotPi_mem_Icc train mx a x
  have hpos : 0 < pilotPi train mx a x := by linarith [hp.1]
  have hh := goodPilot_allowance_nonneg P hModel train C0 mx my hG
  have he := (pilotPi_error_le_pilotError P hModel train mx my a x hx).trans hG
  rw [uerr, abs_div, abs_of_pos hpos, abs_sub_comm]
  apply (div_le_iff₀ hpos).2
  nlinarith [mul_le_mul_of_nonneg_left hp.1 hh]

/-- Global overlap bounds the multiplicative weight in (23), independently of training. -/
-- @node: one_add_uerr_abs_le
lemma one_add_uerr_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : |1 + uerr P train mx a x| ≤ 3 := by
  have hu := uerr_mem_Icc P hModel train mx a x hx
  apply abs_le.mpr
  constructor <;> linarith [hu.1, hu.2]

/-- The weighted density error inherits the good-pilot envelope in (23). -/
-- @node: goodPilot_verr_abs_le
lemma goodPilot_verr_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (x y : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |verr P train mx my a x y| ≤ 3 * hAllow C0 m mx my := by
  rw [verr, abs_mul]
  exact mul_le_mul (one_add_uerr_abs_le P hModel train mx a x hx)
    ((werr_abs_le_pilotError P hModel train mx my a x y hx hy).trans hG)
    (abs_nonneg _) (by norm_num)

/-- The exact polynomial cancellation (22) leaves a cubic relative-error term. -/
-- @node: corrected_mean_pointwise_identity
lemma corrected_mean_pointwise_identity {m : ℕ} (P : ObsLaw)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x y : ℝ) :
    densityPilot train mx my a x y + verr P train mx my a x y -
      uerr P train mx a x * verr P train mx my a x y +
      (uerr P train mx a x) ^ 2 * verr P train mx my a x y =
    P.eta a x y + (uerr P train mx a x) ^ 3 * werr P train mx my a x y := by
  dsimp [verr, werr]
  ring

/-- A uniform envelope on the unit domain bounds the concrete square-integral norm. -/
-- @node: l2Norm_le_of_abs_le
lemma l2Norm_le_of_abs_le (f : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hf : ∀ᵐ y ∂unitVolume, |f y| ≤ b) : l2Norm f ≤ b := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hs : ∀ᵐ y ∂unitVolume, ‖(f y) ^ 2‖ ≤ b ^ 2 := by
    filter_upwards [hf] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).2 hy
  have hi := norm_integral_le_of_norm_le_const hs
  have hle : l2Squared f ≤ b ^ 2 := by
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, l2Squared] using hi)
  exact (Real.sqrt_le_iff).2 ⟨hb, hle⟩

/-- The good density pilot error has conditional outcome L² norm at most h. -/
-- @node: goodPilot_werr_l2Norm_le
lemma goodPilot_werr_l2Norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : l2Norm (werr P train mx my a x) ≤ hAllow C0 m mx my := by
  apply l2Norm_le_of_abs_le _ _ (goodPilot_allowance_nonneg P hModel train C0 mx my hG)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact (werr_abs_le_pilotError P hModel train mx my a x y hx hy).trans hG

/-- The good weighted error has conditional outcome L² norm at most 3h. -/
-- @node: goodPilot_verr_l2Norm_le
lemma goodPilot_verr_l2Norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : l2Norm (verr P train mx my a x) ≤ 3 * hAllow C0 m mx my := by
  apply l2Norm_le_of_abs_le _ _
    (mul_nonneg (by norm_num) (goodPilot_allowance_nonneg P hModel train C0 mx my hG))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx hy

/-- The cubic remainder integrand has the fourth-order envelope used after (23). -/
-- @node: goodPilot_cubic_remainder_abs_le
lemma goodPilot_cubic_remainder_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (x y : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |(uerr P train mx a x) ^ 3 * werr P train mx my a x y| ≤
      64 * (hAllow C0 m mx my) ^ 4 := by
  have hh := goodPilot_allowance_nonneg P hModel train C0 mx my hG
  have hu := goodPilot_uerr_abs_le P hModel train C0 mx my hG a x hx
  have hw := (werr_abs_le_pilotError P hModel train mx my a x y hx hy).trans hG
  rw [abs_mul, abs_pow]
  calc
    _ ≤ (4 * hAllow C0 m mx my) ^ 3 * hAllow C0 m mx my :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu 3) hw (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Integrating the cubic term over X preserves its fourth-order envelope. -/
-- @node: goodPilot_integrated_cubic_remainder_abs_le
lemma goodPilot_integrated_cubic_remainder_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (y : ℝ)
    (hy : y ∈ Set.Icc 0 1) :
    |∫ x, (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume| ≤
      64 * (hAllow C0 m mx my) ^ 4 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hb : ∀ᵐ x ∂unitVolume,
      ‖(uerr P train mx a x) ^ 3 * werr P train mx my a x y‖ ≤
        64 * (hAllow C0 m mx my) ^ 4 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa only [Real.norm_eq_abs] using
      goodPilot_cubic_remainder_abs_le P hModel train C0 mx my hG a x y hx hy
  simpa [Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const hb

/-- The X-integrated cubic remainder has outcome L² norm at most 64h⁴. -/
-- @node: goodPilot_integrated_cubic_remainder_l2Norm_le
lemma goodPilot_integrated_cubic_remainder_l2Norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) :
    l2Norm (fun y => ∫ x,
      (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume) ≤
      64 * (hAllow C0 m mx my) ^ 4 := by
  apply l2Norm_le_of_abs_le _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_integrated_cubic_remainder_abs_le P hModel train C0 mx my hG a y hy

/-- A bounded outcome function has projection coefficient norm at most its envelope. -/
-- @node: coefficients_norm_le_of_abs_le
lemma coefficients_norm_le_of_abs_le (J : ℕ) (hJ : 0 < J) (f : ℝ → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hf : ∀ᵐ y ∂unitVolume, |f y| ≤ b) :
    ‖coefficients J f‖ ≤ b := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsqrt := Real.sq_sqrt hpos.le
  have hcoord (i : Fin J) : |coefficients J f i| ≤ Real.sqrt J * (b / J) := by
    have hbound : ∀ᵐ y ∂unitVolume.restrict (histogramCell J (i.val + 1)), ‖f y‖ ≤ b :=
      ae_restrict_of_ae (by simpa only [Real.norm_eq_abs] using hf)
    have hi := norm_integral_le_of_norm_le_const hbound
    have hc : |∫ y in histogramCell J (i.val + 1), f y ∂unitVolume| ≤ b / J := by
      calc
        _ ≤ b * unitVolume.real (histogramCell J (i.val + 1)) := by
          simpa [Real.norm_eq_abs] using hi
        _ ≤ b * (1 / J) := mul_le_mul_of_nonneg_left (histogramCell_mass_le J hJ i) hb
        _ = _ := by ring
    change |Real.sqrt J * (∫ y in histogramCell J (i.val + 1), f y ∂unitVolume)| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
  have hsq : ‖coefficients J f‖ ^ 2 ≤ b ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin J, b ^ 2 / J := by
        apply Finset.sum_le_sum
        intro i _
        have hc := (sq_le_sq₀ (abs_nonneg _) (by positivity :
          0 ≤ Real.sqrt J * (b / J))).2 (hcoord i)
        have he : (Real.sqrt J * (b / J)) ^ 2 = b ^ 2 / J := by
          rw [mul_pow, hsqrt, div_pow]
          field_simp
        simpa only [sq_abs, he] using hc
      _ = b ^ 2 := by simp; field_simp
  exact (sq_le_sq₀ (norm_nonneg _) hb).1 hsq

/-- The first projected remainder in the corrected-mean formula is at most 64h⁴. -/
-- @node: goodPilot_cubic_remainder_coefficients_norm_le
lemma goodPilot_cubic_remainder_coefficients_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my J : ℕ) (hJ : 0 < J)
    (hG : GoodPilot P train C0 mx my) (a : Bool) :
    ‖coefficients J (fun y => ∫ x,
      (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume)‖ ≤
      64 * (hAllow C0 m mx my) ^ 4 := by
  apply coefficients_norm_le_of_abs_le J hJ _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_integrated_cubic_remainder_abs_le P hModel train C0 mx my hG a y hy

/-- A positive-rank cell has a one-based index in the declared range. -/
-- @node: cell_index_mem
lemma cell_index_mem (k : ℕ) (hk : 0 < k) (x : ℝ) :
    1 ≤ cell k x ∧ cell k x ≤ k := by
  unfold cell
  constructor <;> omega

/-- A cell at an integer multiple of a positive rank refines a cell at that rank. -/
-- @node: cell_eq_of_refinement
lemma cell_eq_of_refinement (mx k : ℕ) (hmx : 0 < mx) (hk : 0 < k)
    (hdiv : mx ∣ k) (x xp : ℝ) (hc : cell k x = cell k xp) :
    cell mx x = cell mx xp := by
  obtain ⟨q, rfl⟩ := hdiv
  have hq : 0 < q := by nlinarith
  have hfloor (z : ℝ) : ⌊((mx * q : ℕ) : ℝ) * z⌋₊ / q = ⌊(mx : ℝ) * z⌋₊ := by
    rw [Nat.cast_mul]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_cast_floor_div_cancel (Nat.ne_of_gt hq) ((mx : ℝ) * z)
  by_cases hlast : cell (mx * q) x = mx * q
  · have hlastp : cell (mx * q) xp = mx * q := hc.symm.trans hlast
    have hcoarse (z : ℝ) (hz : cell (mx * q) z = mx * q) : cell mx z = mx := by
      have hf : mx * q - 1 ≤ ⌊((mx * q : ℕ) : ℝ) * z⌋₊ := by
        unfold cell at hz
        omega
      have hmul : (mx - 1) * q ≤ mx * q - 1 := by
        have hm : mx = mx - 1 + 1 := by omega
        have hprod : mx * q = (mx - 1) * q + q := by nlinarith
        omega
      have hle : mx - 1 ≤ ⌊((mx * q : ℕ) : ℝ) * z⌋₊ / q :=
        (Nat.le_div_iff_mul_le hq).2 (hmul.trans hf)
      rw [hfloor] at hle
      unfold cell
      omega
    rw [hcoarse x hlast, hcoarse xp hlastp]
  · have hf : ⌊((mx * q : ℕ) : ℝ) * x⌋₊ = ⌊((mx * q : ℕ) : ℝ) * xp⌋₊ := by
      unfold cell at hc hlast
      omega
    have hcoarse := congrArg (fun n : ℕ => n / q) hf
    rw [hfloor, hfloor] at hcoarse
    simp only [cell, hcoarse]

/-- Points in one histogram cell are separated by at most its width. -/
-- @node: same_cell_distance_le
lemma same_cell_distance_le (k : ℕ) (hk : 0 < k) (x xp : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (hc : cell k x = cell k xp) : |x - xp| ≤ 1 / (k : ℝ) := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hei : i.val + 1 = cell k x := by dsimp [i]; omega
  have hb := histogramCell_subset_bin k hk i ⟨hx, hei.symm⟩
  have hbp := histogramCell_subset_bin k hk i ⟨hxp, hc.symm.trans hei.symm⟩
  simp only [add_div] at hb hbp
  apply abs_le.mpr
  constructor <;> linarith [hb.1, hb.2, hbp.1, hbp.2]

/-- Equal covariate-cell labels give exactly the same clipped arm pilot. -/
-- @node: pilotPi_eq_of_cell_eq
lemma pilotPi_eq_of_cell_eq {m : ℕ} (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) (x xp : ℝ) (hc : cell mx x = cell mx xp) :
    pilotPi train mx a x = pilotPi train mx a xp := by
  simp only [pilotPi, armProbability, propensityPilot, cellCount, armCellCount, hc]
  rfl

/-- Normalization preserves the density pilot's constancy within a covariate cell. -/
-- @node: densityPilot_eq_of_cell_eq
lemma densityPilot_eq_of_cell_eq {m : ℕ} (train : Fin m → Omega) (mx my : ℕ)
    (a : Bool) (x xp y : ℝ) (hc : cell mx x = cell mx xp) :
    densityPilot train mx my a x y = densityPilot train mx my a xp y := by
  simp only [densityPilot, clippedDensityPilot, armCellCount, outcomeCellCount, hc]
  rfl

/-- The Hölder propensity condition holds for both arm probabilities. -/
-- @node: model_pi_holder
lemma model_pi_holder (P : ObsLaw) (hModel : Model P) (a : Bool) (x xp : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1) :
    |pi P a x - pi P a xp| ≤ 10 * |x - xp| ^ (1 / 10 : ℝ) := by
  have h := hModel.propensity_holder x hx xp hxp
  cases a
  · simpa [pi, armProbability, show 1 - P.e x - (1 - P.e xp) =
      -(P.e x - P.e xp) by ring, abs_sub_comm] using h
  · exact h

/-- Within a pilot cell, dividing by the clipped pilot costs at most four. -/
-- @node: uerr_same_cell_holder
lemma uerr_same_cell_holder {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x xp : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (hc : cell mx x = cell mx xp) :
    |uerr P train mx a x - uerr P train mx a xp| ≤
      40 * |x - xp| ^ (1 / 10 : ℝ) := by
  have hp := pilotPi_mem_Icc train mx a xp
  have hpos : 0 < pilotPi train mx a xp := by linarith [hp.1]
  have hh := model_pi_holder P hModel a x xp hx hxp
  have he : uerr P train mx a x - uerr P train mx a xp =
      (pi P a x - pi P a xp) / pilotPi train mx a xp := by
    rw [uerr, uerr, pilotPi_eq_of_cell_eq train mx a x xp hc]
    ring
  rw [he, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  have hnon : 0 ≤ |x - xp| ^ (1 / 10 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  nlinarith [mul_le_mul_of_nonneg_right hp.1 hnon]

/-- Within a pilot cell, the density-error oscillation is the model's oscillation. -/
-- @node: werr_same_cell_holder
lemma werr_same_cell_holder {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x xp y : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) (hc : cell mx x = cell mx xp) :
    |werr P train mx my a x y - werr P train mx my a xp y| ≤
      10 * |x - xp| ^ (1 / 10 : ℝ) := by
  have he : werr P train mx my a x y - werr P train mx my a xp y =
      P.eta a x y - P.eta a xp y := by
    rw [werr, werr, densityPilot_eq_of_cell_eq train mx my a x xp y hc]
    ring
  rw [he]
  exact hModel.density_covariate_holder a y hy x hx xp hxp

/-- The weighted error has the constant seventy in (24) when the pilot allowance is at most one. -/
-- @node: goodPilot_verr_same_cell_holder
lemma goodPilot_verr_same_cell_holder {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (x xp y : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hxp : xp ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hc : cell mx x = cell mx xp) :
    |verr P train mx my a x y - verr P train mx my a xp y| ≤
      70 * |x - xp| ^ (1 / 10 : ℝ) := by
  have hu := uerr_same_cell_holder P hModel train mx a x xp hx hxp hc
  have hw := werr_same_cell_holder P hModel train mx my a x xp y hx hxp hy hc
  have hwsize : |werr P train mx my a xp y| ≤ 1 :=
    ((werr_abs_le_pilotError P hModel train mx my a xp y hxp hy).trans hG).trans hh
  have hone := one_add_uerr_abs_le P hModel train mx a x hx
  have he : verr P train mx my a x y - verr P train mx my a xp y =
      (1 + uerr P train mx a x) *
        (werr P train mx my a x y - werr P train mx my a xp y) +
      (uerr P train mx a x - uerr P train mx a xp) * werr P train mx my a xp y := by
    dsimp [verr]; ring
  rw [he]
  calc
    _ ≤ |(1 + uerr P train mx a x) *
        (werr P train mx my a x y - werr P train mx my a xp y)| +
        |(uerr P train mx a x - uerr P train mx a xp) * werr P train mx my a xp y| :=
      abs_add_le _ _
    _ ≤ 3 * (10 * |x - xp| ^ (1 / 10 : ℝ)) +
        (40 * |x - xp| ^ (1 / 10 : ℝ)) * 1 := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hone hw (abs_nonneg _) (by norm_num))
        (mul_le_mul hu hwsize (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- Raising the cell-width bound to the Hölder exponent gives the resolution factor. -/
-- @node: same_cell_holder_scale_le
lemma same_cell_holder_scale_le (k : ℕ) (hk : 0 < k) (x xp : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (hc : cell k x = cell k xp) :
    |x - xp| ^ (1 / 10 : ℝ) ≤ (k : ℝ) ^ (-1 / 10 : ℝ) := by
  have h := Real.rpow_le_rpow (abs_nonneg (x - xp))
    (same_cell_distance_le k hk x xp hx hxp hc) (by norm_num : (0 : ℝ) ≤ 1 / 10)
  simpa only [one_div, ← Real.rpow_neg_eq_inv_rpow, neg_div] using h

/-- The scalar relative-error oscillation on every refined correction cell is at most 40k⁻¹ᐟ¹⁰. -/
-- @node: uerr_refined_cell_oscillation
lemma uerr_refined_cell_oscillation {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx k : ℕ) (hmx : 0 < mx) (hk : 0 < k)
    (hdiv : mx ∣ k) (a : Bool) (x xp : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (hc : cell k x = cell k xp) :
    |uerr P train mx a x - uerr P train mx a xp| ≤ 40 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
  exact (uerr_same_cell_holder P hModel train mx a x xp hx hxp
    (cell_eq_of_refinement mx k hmx hk hdiv x xp hc)).trans
    (mul_le_mul_of_nonneg_left (same_cell_holder_scale_le k hk x xp hx hxp hc) (by norm_num))

/-- The good-pilot weighted density error obeys the constant seventy on a refined cell. -/
-- @node: goodPilot_verr_refined_cell_oscillation
lemma goodPilot_verr_refined_cell_oscillation {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (x xp y : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hxp : xp ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hc : cell k x = cell k xp) :
    |verr P train mx my a x y - verr P train mx my a xp y| ≤
      70 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
  exact (goodPilot_verr_same_cell_holder P hModel train C0 mx my hG hh a x xp y hx hxp hy
    (cell_eq_of_refinement mx k hmx hk hdiv x xp hc)).trans
    (mul_le_mul_of_nonneg_left (same_cell_holder_scale_le k hk x xp hx hxp hc) (by norm_num))

/-- The pointwise refined-cell envelope gives exactly the Hilbert oscillation in (24). -/
-- @node: goodPilot_verr_refined_cell_l2Norm_le
lemma goodPilot_verr_refined_cell_l2Norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (x xp : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hxp : xp ∈ Set.Icc 0 1) (hc : cell k x = cell k xp) :
    l2Norm (fun y => verr P train mx my a x y - verr P train mx my a xp y) ≤
      70 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
  apply l2Norm_le_of_abs_le _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_verr_refined_cell_oscillation P hModel train C0 mx my k
    hmx hk hdiv hG hh a x xp y hx hxp hy hc

/-- Factoring the difference of squares and using |u| ≤ 4h yields the oscillation in (28). -/
-- @node: goodPilot_uerr_sq_refined_cell_oscillation
lemma goodPilot_uerr_sq_refined_cell_oscillation {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (x xp : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (hc : cell k x = cell k xp) :
    |(uerr P train mx a x) ^ 2 - (uerr P train mx a xp) ^ 2| ≤
      320 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 10 : ℝ) := by
  have hu := uerr_refined_cell_oscillation P hModel train mx k hmx hk hdiv a x xp hx hxp hc
  have hxsize := goodPilot_uerr_abs_le P hModel train C0 mx my hG a x hx
  have hxpsize := goodPilot_uerr_abs_le P hModel train C0 mx my hG a xp hxp
  have hsum : |uerr P train mx a x + uerr P train mx a xp| ≤ 8 * hAllow C0 m mx my :=
    (abs_add_le _ _).trans (by linarith)
  calc
    _ = |uerr P train mx a x - uerr P train mx a xp| *
        |uerr P train mx a x + uerr P train mx a xp| := by rw [sq_sub_sq, abs_mul, mul_comm]
    _ ≤ (40 * (k : ℝ) ^ (-1 / 10 : ℝ)) * (8 * hAllow C0 m mx my) :=
      mul_le_mul hu hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Genuine refinement restrictions of the corrected-mean identity. -/
def MeanRanks (mx my K L T J q : ℕ) (kt : ℕ → ℕ) : Prop :=
  Dyadic mx ∧ -- @realizes mx(positive dyadic covariate rank)
  Dyadic my ∧ -- @realizes my(positive dyadic outcome rank)
  Dyadic L ∧ -- @realizes L(positive dyadic initial outcome rank)
  Dyadic K ∧ -- @realizes K(positive dyadic initial correction rank)
  Dyadic q ∧ -- @realizes q(positive dyadic third-order rank)
  (∀ t, t ≤ T → Dyadic (kt t)) ∧ -- @realizes kt(positive dyadic band ranks)
  J = 2 ^ T * L ∧ -- @realizes J(final dyadic rank 2^T L)
  my ≤ L ∧ kt 0 = K ∧
  (∀ t, t ≤ T → mx ∣ kt t) ∧ mx ∣ q

/-- The three exact remainder terms, constructed from the analysis-only pilot errors. -/
def meanRemainder {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) : Hj J :=
  ∑ a : Bool, (if a then (1 : ℝ) else - 1) •
    (coefficients J (fun y => ∫ x,
      (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume) + 
    (∑ t ∈ Finset.range (T + 1), Qband L J t (coefficients J (fun y => ∫ x,
      uerr P train mx a x * verr P train mx my a x y -
      cellAverage (kt t) (uerr P train mx a) x * 
        cellAverage (kt t) (fun xp => verr P train mx my a xp y) x ∂unitVolume))) + 
    coefficients J (fun y => ∫ x,
      (cellAverage q (uerr P train mx a) x) ^ 2 * 
        cellAverage q (fun xp => verr P train mx my a xp y) x -
      (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume))


end CausalSmith.Stat.DensityEffectRoughNull
