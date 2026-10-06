module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CorrectedMean

/-! Application of cell centering to the pilot errors: the constants in (25) and (28).
The outcome approximation bounds realize (26); the cell bounds apply to any probability
measure supported on a single refined cell. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Integrating the pointwise outcome approximation proves the L² envelope in (26). -/
-- @node: model_outcomeProjection_l2Norm_le
lemma model_outcomeProjection_l2Norm_le (P : ObsLaw) (hModel : Model P)
    (d : ℕ) (hd : 0 < d) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    l2Norm (fun y => P.eta a x y - outcomeProjection d (P.eta a x) y) ≤
      10 / (d : ℝ) := by
  apply l2Norm_le_of_abs_le _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simpa only [abs_sub_comm] using model_outcomeProjection_error_le P hModel d hd a x y hx hy

/-- The same approximation controls final-rank coefficients without a dimension factor. -/
-- @node: model_outcomeProjection_coefficients_norm_le
lemma model_outcomeProjection_coefficients_norm_le (P : ObsLaw) (hModel : Model P)
    (d J : ℕ) (hd : 0 < d) (hJ : 0 < J) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) :
    ‖coefficients J (fun y => P.eta a x y - outcomeProjection d (P.eta a x) y)‖ ≤
      10 / (d : ℝ) := by
  apply coefficients_norm_le_of_abs_le J hJ _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simpa only [abs_sub_comm] using model_outcomeProjection_error_le P hModel d hd a x y hx hy

/-- Squaring the refined-cell scale gives the one-fifth power used by both remainders. -/
-- @node: refined_cell_scale_sq
lemma refined_cell_scale_sq (k : ℕ) (hk : 0 < k) :
    ((k : ℝ) ^ (-1 / 10 : ℝ)) ^ 2 = (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have hpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sq, ← Real.rpow_add hpos]
  congr 1
  norm_num

/-- The normalized-cell scalar covariance bound in (25) has constant 2800. -/
-- @node: goodPilot_cell_covariance_abs_le
lemma goodPilot_cell_covariance_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℕ)
    (hs : ∀ᵐ x ∂μ, x ∈ Set.Icc 0 1 ∧ cell k x = c)
    (hu : Integrable (uerr P train mx a) μ)
    (hv : Integrable (fun x => verr P train mx my a x y) μ)
    (huv : Integrable (fun x => uerr P train mx a x * verr P train mx my a x y) μ) :
    |(∫ x, uerr P train mx a x * verr P train mx my a x y ∂μ) -
      (∫ x, uerr P train mx a x ∂μ) * (∫ x, verr P train mx my a x y ∂μ)| ≤
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have ha : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ,
      |uerr P train mx a x - uerr P train mx a z| ≤ 40 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [hs] with x hx
    filter_upwards [hs] with z hz
    exact uerr_refined_cell_oscillation P hModel train mx k hmx hk hdiv a x z
      hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hb : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ,
      ‖verr P train mx my a x y - verr P train mx my a z y‖ ≤
        70 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [hs] with x hx
    filter_upwards [hs] with z hz
    simpa only [Real.norm_eq_abs] using
      goodPilot_verr_refined_cell_oscillation P hModel train C0 mx my k hmx hk hdiv
        hG hh a x z y hx.1 hz.1 hy (hx.2.trans hz.2.symm)
  have h := cell_covariance_norm_le_of_oscillation μ (uerr P train mx a)
    (fun x => verr P train mx my a x y) hu hv (by simpa only [smul_eq_mul] using huv)
    (40 * (k : ℝ) ^ (-1 / 10 : ℝ)) (70 * (k : ℝ) ^ (-1 / 10 : ℝ))
    (by positivity) ha hb
  have he : (40 * (k : ℝ) ^ (-1 / 10 : ℝ)) * (70 * (k : ℝ) ^ (-1 / 10 : ℝ)) =
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
    rw [← refined_cell_scale_sq k hk]
    ring
  simpa only [Real.norm_eq_abs, smul_eq_mul, he] using h

/-- On a normalized refined cell, the third-order remainder has the constant 27200 in (28). -/
-- @node: goodPilot_cell_squared_error_abs_le
lemma goodPilot_cell_squared_error_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℕ)
    (hs : ∀ᵐ x ∂μ, x ∈ Set.Icc 0 1 ∧ cell k x = c)
    (hu : Integrable (uerr P train mx a) μ)
    (hu2 : Integrable (fun x => (uerr P train mx a x) ^ 2) μ)
    (hv : Integrable (fun x => verr P train mx my a x y) μ)
    (hu2v : Integrable (fun x => (uerr P train mx a x) ^ 2 * verr P train mx my a x y) μ) :
    |(∫ x, (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂μ) -
      (∫ x, uerr P train mx a x ∂μ) ^ 2 * (∫ x, verr P train mx my a x y ∂μ)| ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have hh0 := goodPilot_allowance_nonneg P hModel train C0 mx my hG
  have ha : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ,
      |uerr P train mx a x - uerr P train mx a z| ≤ 40 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [hs] with x hx
    filter_upwards [hs] with z hz
    exact uerr_refined_cell_oscillation P hModel train mx k hmx hk hdiv a x z
      hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hd : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ,
      |(uerr P train mx a x) ^ 2 - (uerr P train mx a z) ^ 2| ≤
        320 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [hs] with x hx
    filter_upwards [hs] with z hz
    exact goodPilot_uerr_sq_refined_cell_oscillation P hModel train C0 mx my k
      hmx hk hdiv hG a x z hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hb : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ,
      ‖verr P train mx my a x y - verr P train mx my a z y‖ ≤
        70 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [hs] with x hx
    filter_upwards [hs] with z hz
    simpa only [Real.norm_eq_abs] using
      goodPilot_verr_refined_cell_oscillation P hModel train C0 mx my k hmx hk hdiv
        hG hh a x z y hx.1 hz.1 hy (hx.2.trans hz.2.symm)
  have hc : ‖∫ x, verr P train mx my a x y ∂μ‖ ≤ 3 * hAllow C0 m mx my := by
    have hpoint : ∀ᵐ x ∂μ, ‖verr P train mx my a x y‖ ≤ 3 * hAllow C0 m mx my := by
      filter_upwards [hs] with x hx
      simpa only [Real.norm_eq_abs] using
        goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx.1 hy
    simpa using norm_integral_le_of_norm_le_const hpoint
  have h := cell_squared_error_norm_le μ (uerr P train mx a)
    (fun x => verr P train mx my a x y) hu hu2 hv
    (by simpa only [smul_eq_mul] using hu2v)
    (40 * (k : ℝ) ^ (-1 / 10 : ℝ))
    (320 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 10 : ℝ))
    (70 * (k : ℝ) ^ (-1 / 10 : ℝ)) (3 * hAllow C0 m mx my)
    (by positivity) (by positivity) ha hd hb hc
  have he : (320 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 10 : ℝ)) *
      (70 * (k : ℝ) ^ (-1 / 10 : ℝ)) + (40 * (k : ℝ) ^ (-1 / 10 : ℝ)) ^ 2 *
      (3 * hAllow C0 m mx my) = 27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
    rw [← refined_cell_scale_sq k hk]
    ring
  simpa only [Real.norm_eq_abs, smul_eq_mul, he] using h

end CausalSmith.Stat.DensityEffectRoughNull
