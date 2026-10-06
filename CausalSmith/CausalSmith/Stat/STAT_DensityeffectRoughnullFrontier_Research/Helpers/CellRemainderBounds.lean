module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellMeanCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellCovariance

/-! Concrete correction-cell covariance and third-order remainder bounds in (25)--(28).
All envelopes and integrability witnesses follow from the model and the good-pilot event. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The product of the two cell oscillations gives the initial-band covariance envelope. -/
-- @node: goodPilot_correctionCell_covariance_abs_le
lemma goodPilot_correctionCell_covariance_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) (i : Fin k) :
    |(∫ x, uerr P train mx a x * verr P train mx my a x y ∂correctionCellLaw k i) -
      (∫ x, uerr P train mx a x ∂correctionCellLaw k i) *
        (∫ x, verr P train mx my a x y ∂correctionCellLaw k i)| ≤
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  let := correctionCellLaw_probability k hk i
  have hu := integrable_correctionCellLaw k i _ (integrable_uerr_covariate P hModel train mx a)
  have hv := integrable_correctionCellLaw k i _
    (goodPilot_integrable_verr_covariate P hModel train C0 mx my hG a y hy)
  have huv := integrable_correctionCellLaw k i _
    (goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 1)
  have ha : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      |uerr P train mx a x - uerr P train mx a z| ≤ 40 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    exact uerr_refined_cell_oscillation P hModel train mx k hmx hk hdiv a x z
      hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hb : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      ‖verr P train mx my a x y - verr P train mx my a z y‖ ≤
        70 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    simpa only [Real.norm_eq_abs] using goodPilot_verr_refined_cell_oscillation
      P hModel train C0 mx my k hmx hk hdiv hG hh a x z y hx.1 hz.1 hy
      (hx.2.trans hz.2.symm)
  have h := cell_covariance_norm_le_of_oscillation (correctionCellLaw k i)
    (uerr P train mx a) (fun x => verr P train mx my a x y) hu hv
    (by simpa only [pow_one, smul_eq_mul] using huv)
    (40 * (k : ℝ) ^ (-1 / 10 : ℝ)) (70 * (k : ℝ) ^ (-1 / 10 : ℝ))
    (by positivity) ha hb
  have he : (40 * (k : ℝ) ^ (-1 / 10 : ℝ)) * (70 * (k : ℝ) ^ (-1 / 10 : ℝ)) =
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
    calc
      _ = 2800 * ((k : ℝ) ^ (-1 / 10 : ℝ) * (k : ℝ) ^ (-1 / 10 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add (by exact_mod_cast hk)]; norm_num
  simpa only [Real.norm_eq_abs, smul_eq_mul, he] using h

/-- Contracting to the initial outcome band gives the first term of (27). -/
-- @node: goodPilot_initial_band_remainder_norm_le
lemma goodPilot_initial_band_remainder_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my K L T : ℕ)
    (hmx : 0 < mx) (hK : 0 < K) (hL : Dyadic L) (hdiv : mx ∣ K)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1) (a : Bool) :
    ‖Qband L (2 ^ T * L) 0 (coefficients (2 ^ T * L)
      (fun y => ∫ x, uerr P train mx a x * verr P train mx my a x y -
        cellAverage K (uerr P train mx a) x *
          cellAverage K (fun z => verr P train mx my a z y) x ∂unitVolume))‖ ≤
      2800 * (K : ℝ) ^ (-1 / 5 : ℝ) := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  exact ((band_projection_algebra L T hL).2.2 0 (Nat.zero_le T) _).trans
    (goodPilot_covariance_coefficients_norm_le P hModel train C0 mx my K (2 ^ T * L)
      hmx hK (by positivity) hdiv hG hh a)

/-- Covariance plus variance gives the constant 27200 in the third-order cell remainder. -/
-- @node: goodPilot_correctionCell_squared_remainder_abs_le
lemma goodPilot_correctionCell_squared_remainder_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) (i : Fin k) :
    |(∫ x, (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂correctionCellLaw k i) -
      (∫ x, uerr P train mx a x ∂correctionCellLaw k i) ^ 2 *
        (∫ x, verr P train mx my a x y ∂correctionCellLaw k i)| ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  let := correctionCellLaw_probability k hk i
  have hnonneg := goodPilot_allowance_nonneg P hModel train C0 mx my hG
  have hu := integrable_correctionCellLaw k i _ (integrable_uerr_covariate P hModel train mx a)
  have hu2 := integrable_correctionCellLaw k i _ (integrable_uerr_pow_covariate P hModel train mx a 2)
  have hv := integrable_correctionCellLaw k i _
    (goodPilot_integrable_verr_covariate P hModel train C0 mx my hG a y hy)
  have hu2v := integrable_correctionCellLaw k i _
    (goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 2)
  have ha : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      |uerr P train mx a x - uerr P train mx a z| ≤ 40 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    exact uerr_refined_cell_oscillation P hModel train mx k hmx hk hdiv a x z
      hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hd : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      |(uerr P train mx a x) ^ 2 - (uerr P train mx a z) ^ 2| ≤
        320 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    exact goodPilot_uerr_sq_refined_cell_oscillation P hModel train C0 mx my k
      hmx hk hdiv hG a x z hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hb : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      ‖verr P train mx my a x y - verr P train mx my a z y‖ ≤
        70 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    simpa only [Real.norm_eq_abs] using goodPilot_verr_refined_cell_oscillation
      P hModel train C0 mx my k hmx hk hdiv hG hh a x z y hx.1 hz.1 hy
      (hx.2.trans hz.2.symm)
  have hc : ‖∫ x, verr P train mx my a x y ∂correctionCellLaw k i‖ ≤ 3 * hAllow C0 m mx my := by
    have hbnd : ∀ᵐ x ∂correctionCellLaw k i, ‖verr P train mx my a x y‖ ≤ 3 * hAllow C0 m mx my := by
      filter_upwards [correctionCellLaw_support k i] with x hx
      simpa only [Real.norm_eq_abs] using goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx.1 hy
    simpa using norm_integral_le_of_norm_le_const hbnd
  have h := cell_squared_error_norm_le (correctionCellLaw k i) (uerr P train mx a)
    (fun x => verr P train mx my a x y) hu hu2 hv
    (by simpa only [smul_eq_mul] using hu2v)
    (40 * (k : ℝ) ^ (-1 / 10 : ℝ))
    (320 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 10 : ℝ))
    (70 * (k : ℝ) ^ (-1 / 10 : ℝ)) (3 * hAllow C0 m mx my)
    (by positivity) (by positivity) ha hd hb hc
  have he : (k : ℝ) ^ (-1 / 10 : ℝ) * (k : ℝ) ^ (-1 / 10 : ℝ) =
      (k : ℝ) ^ (-1 / 5 : ℝ) := by
    rw [← Real.rpow_add (by exact_mod_cast hk)]; norm_num
  simp only [Real.norm_eq_abs, smul_eq_mul] at h
  calc
    _ ≤ _ := h
    _ = 27200 * hAllow C0 m mx my *
        ((k : ℝ) ^ (-1 / 10 : ℝ) * (k : ℝ) ^ (-1 / 10 : ℝ)) := by ring
    _ = _ := by rw [he]

/-- Expressing (28) in the concrete cell-average notation preserves its envelope. -/
-- @node: goodPilot_cellAverage_squared_remainder_abs_le
lemma goodPilot_cellAverage_squared_remainder_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) (x : ℝ) :
    |cellAverage k (fun z => (uerr P train mx a z) ^ 2 * verr P train mx my a z y) x -
      (cellAverage k (uerr P train mx a) x) ^ 2 *
        cellAverage k (fun z => verr P train mx my a z y) x| ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hc : cell k x = i.val + 1 := by dsimp [i]; omega
  simp only [cellAverage_eq_correctionCellLaw k i _ x hc]
  exact goodPilot_correctionCell_squared_remainder_abs_le P hModel train C0 mx my k
    hmx hk hdiv hG hh a y hy i

/-- Uniform-design integration of (28) gives the third remainder with its paper constant. -/
-- @node: goodPilot_integrated_squared_remainder_abs_le
lemma goodPilot_integrated_squared_remainder_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    |∫ x, (cellAverage k (uerr P train mx a) x) ^ 2 *
        cellAverage k (fun z => verr P train mx my a z y) x -
        (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume| ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let f := fun x => (uerr P train mx a x) ^ 2 * verr P train mx my a x y
  let g := fun x => (cellAverage k (uerr P train mx a) x) ^ 2 *
    cellAverage k (fun z => verr P train mx my a z y) x
  have hf : Integrable f unitVolume :=
    goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 2
  have hg : Integrable g unitVolume :=
    goodPilot_integrable_cellAverage_sq_mul P hModel train C0 mx my k hk hG a y hy
  have hav : Integrable (cellAverage k f) unitVolume := integrable_cellAverage k hk f
  have he : (∫ x, g x - f x ∂unitVolume) =
      ∫ x, g x - cellAverage k f x ∂unitVolume := by
    rw [integral_sub hg hf, integral_sub hg hav, integral_cellAverage k hk f hf]
  change |∫ x, g x - f x ∂unitVolume| ≤ _
  rw [he]
  have hb : ∀ᵐ x ∂unitVolume, ‖g x - cellAverage k f x‖ ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_sub_comm] using
      goodPilot_cellAverage_squared_remainder_abs_le P hModel train C0 mx my k
        hmx hk hdiv hG hh a y hy x
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb

/-- Outcome projection gives the norm bound for the complete third arm remainder. -/
-- @node: goodPilot_squared_remainder_coefficients_norm_le
lemma goodPilot_squared_remainder_coefficients_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k J : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hJ : 0 < J) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1) (a : Bool) :
    ‖coefficients J (fun y => ∫ x, (cellAverage k (uerr P train mx a) x) ^ 2 *
      cellAverage k (fun z => verr P train mx my a z y) x -
        (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume)‖ ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have hnonneg := goodPilot_allowance_nonneg P hModel train C0 mx my hG
  apply coefficients_norm_le_of_abs_le J hJ _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_integrated_squared_remainder_abs_le P hModel train C0 mx my k
    hmx hk hdiv hG hh a y hy

end CausalSmith.Stat.DensityEffectRoughNull
