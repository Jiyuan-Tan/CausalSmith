module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CorrectedMean
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyProjection

/-!
Conditional-density approximation and weighted projection residual bounds for (26).
The concrete trained pilot is annihilated by every positive band above its outcome rank.
-/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Outcome smoothness bounds each conditional density's bin approximation by ten over rank. -/
-- @node: model_eta_projection_error_le
lemma model_eta_projection_error_le (P : ObsLaw) (hModel : Model P)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (d : ℕ) (hd : 0 < d) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    |outcomeProjection d (P.eta a x) y - P.eta a x y| ≤ 10 / (d : ℝ) := by
  have hind := cell_index_mem d hd y
  let i : Fin d := ⟨cell d y - 1, by omega⟩
  have hc : cell d y = i.val + 1 := by dsimp [i]; omega
  apply outcomeProjection_error_le d hd i _ (P.eta_integrable a x hx) y _ hc
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell d (i.val + 1))] with z hz
  have hdist := same_cell_distance_le d hd z y hz.1 hy (hz.2.trans hc.symm)
  exact (hModel.density_outcome_lipschitz a x hx z hz.1 y hy).trans
    (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 10))

/-- The conditional-density projection residual has outcome L² norm at most ten over rank. -/
-- @node: model_eta_projection_l2Norm_le
lemma model_eta_projection_l2Norm_le (P : ObsLaw) (hModel : Model P)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) (d : ℕ) (hd : 0 < d) :
    l2Norm (fun y => P.eta a x y - outcomeProjection d (P.eta a x) y) ≤
      10 / (d : ℝ) := by
  apply l2Norm_le_of_abs_le _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simpa only [abs_sub_comm] using model_eta_projection_error_le P hModel a x hx d hd y hy

/-- Projection of the conditional approximation residual at any final rank preserves its bound. -/
-- @node: model_eta_projection_residual_coefficients_norm_le
lemma model_eta_projection_residual_coefficients_norm_le (P : ObsLaw) (hModel : Model P)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (d J : ℕ) (hd : 0 < d) (hJ : 0 < J) :
    ‖coefficients J (fun y => P.eta a x y - outcomeProjection d (P.eta a x) y)‖ ≤
      10 / (d : ℝ) := by
  apply coefficients_norm_le_of_abs_le J hJ _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simpa only [abs_sub_comm] using model_eta_projection_error_le P hModel a x hx d hd y hy

/-- The relative-propensity weight multiplies the approximation envelope by at most three. -/
-- @node: weighted_eta_projection_residual_abs_le
lemma weighted_eta_projection_residual_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) (d : ℕ) (hd : 0 < d) (y : ℝ)
    (hy : y ∈ Set.Icc 0 1) :
    |(1 + uerr P train mx a x) *
      (P.eta a x y - outcomeProjection d (P.eta a x) y)| ≤ 30 / (d : ℝ) := by
  rw [abs_mul]
  have he : |P.eta a x y - outcomeProjection d (P.eta a x) y| ≤ 10 / (d : ℝ) := by
    simpa only [abs_sub_comm] using model_eta_projection_error_le P hModel a x hx d hd y hy
  calc
    _ ≤ 3 * (10 / (d : ℝ)) :=
      mul_le_mul (one_add_uerr_abs_le P hModel train mx a x hx) he
        (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Two weighted residuals differ by at most sixty over rank, without a covariate-distance loss. -/
-- @node: weighted_eta_projection_residual_oscillation_abs_le
lemma weighted_eta_projection_residual_oscillation_abs_le {m : ℕ}
    (P : ObsLaw) (hModel : Model P) (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) (x xp : ℝ) (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (d : ℕ) (hd : 0 < d) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    |(1 + uerr P train mx a x) * (P.eta a x y - outcomeProjection d (P.eta a x) y) -
      (1 + uerr P train mx a xp) * (P.eta a xp y - outcomeProjection d (P.eta a xp) y)| ≤
      60 / (d : ℝ) := by
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ 30 / (d : ℝ) + 30 / (d : ℝ) := add_le_add
      (weighted_eta_projection_residual_abs_le P hModel train mx a x hx d hd y hy)
      (weighted_eta_projection_residual_abs_le P hModel train mx a xp hxp d hd y hy)
    _ = _ := by ring

/-- The sixty-over-rank oscillation also holds in the outcome Hilbert norm. -/
-- @node: weighted_eta_projection_residual_oscillation_l2Norm_le
lemma weighted_eta_projection_residual_oscillation_l2Norm_le {m : ℕ}
    (P : ObsLaw) (hModel : Model P) (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) (x xp : ℝ) (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (d : ℕ) (hd : 0 < d) :
    l2Norm (fun y =>
      (1 + uerr P train mx a x) * (P.eta a x y - outcomeProjection d (P.eta a x) y) -
      (1 + uerr P train mx a xp) * (P.eta a xp y - outcomeProjection d (P.eta a xp) y)) ≤
      60 / (d : ℝ) := by
  apply l2Norm_le_of_abs_le _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact weighted_eta_projection_residual_oscillation_abs_le P hModel train mx a x xp hx hxp d hd y hy

/-- Every dyadic band contracts the coefficient form of the conditional approximation error. -/
-- @node: model_eta_projection_residual_band_norm_le
lemma model_eta_projection_residual_band_norm_le (P : ObsLaw) (hModel : Model P)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (d L T t : ℕ) (hd : 0 < d) (hL : Dyadic L) (ht : t ≤ T) :
    ‖Qband L (2 ^ T * L) t (coefficients (2 ^ T * L)
      (fun y => P.eta a x y - outcomeProjection d (P.eta a x) y))‖ ≤ 10 / (d : ℝ) := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  exact ((band_projection_algebra L T hL).2.2 t ht _).trans
    (model_eta_projection_residual_coefficients_norm_le P hModel a x hx d (2 ^ T * L)
      hd (by positivity))

/-- Band projection preserves the sixty-over-rank weighted residual oscillation. -/
-- @node: weighted_eta_projection_residual_band_oscillation_norm_le
lemma weighted_eta_projection_residual_band_oscillation_norm_le {m : ℕ}
    (P : ObsLaw) (hModel : Model P) (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) (x xp : ℝ) (hx : x ∈ Set.Icc 0 1) (hxp : xp ∈ Set.Icc 0 1)
    (d L T t : ℕ) (hd : 0 < d) (hL : Dyadic L) (ht : t ≤ T) :
    ‖Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (fun y =>
      (1 + uerr P train mx a x) * (P.eta a x y - outcomeProjection d (P.eta a x) y) -
      (1 + uerr P train mx a xp) * (P.eta a xp y - outcomeProjection d (P.eta a xp) y)))‖ ≤
      60 / (d : ℝ) := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  apply ((band_projection_algebra L T hL).2.2 t ht _).trans
  apply coefficients_norm_le_of_abs_le _ (by positivity) _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact weighted_eta_projection_residual_oscillation_abs_le P hModel train mx a x xp hx hxp d hd y hy


/-- Normalizing the clipped histogram preserves constancy on outcome cells. -/
-- @node: densityPilot_eq_of_outcome_cell_eq
lemma densityPilot_eq_of_outcome_cell_eq {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x y z : ℝ) (hc : cell my y = cell my z) :
    densityPilot train mx my a x y = densityPilot train mx my a x z := by
  simp only [densityPilot, clippedDensityPilot, outcomeCellCount, hc]

/-- Coefficients of a coarse histogram are its midpoint values times the common cell mass. -/
-- @node: coefficients_histogram_const_apply
lemma coefficients_histogram_const_apply (j J : ℕ) (hj : 0 < j) (hJ : 0 < J)
    (hjJ : j ∣ J) (f : ℝ → ℝ)
    (hf : ∀ y z, cell j y = cell j z → f y = f z) (i : Fin J) :
    coefficients J f i = Real.sqrt J * ((1 / (J : ℝ)) * f (midpoint J i)) := by
  have he : (∫ y in histogramCell J (i.val + 1), f y ∂unitVolume) =
      ∫ _y in histogramCell J (i.val + 1), f (midpoint J i) ∂unitVolume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell J (i.val + 1))] with y hy
    exact hf y _ (cell_eq_of_refinement j J hj hJ hjJ y _
      (hy.2.trans (cell_midpoint_self J i).symm))
  change Real.sqrt J * _ = _
  rw [he, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  rw [← measureReal_def, histogramCell_mass_eq J hJ i]

/-- Coarse-cell-constant coefficients are fixed by their coarse averaging matrix. -/
-- @node: coefficientProjection_fix_histogram_const
lemma coefficientProjection_fix_histogram_const (j J : ℕ) (hj : 0 < j) (hJ : 0 < J)
    (hjJ : j ∣ J) (f : ℝ → ℝ)
    (hf : ∀ y z, cell j y = cell j z → f y = f z) :
    coefficientProjection j J (coefficients J f) = coefficients J f := by
  classical
  obtain ⟨r, rfl⟩ := hjJ
  have hr : 0 < r := by nlinarith
  ext i
  change (j : ℝ) / (j * r : ℕ) *
    (∑ l : Fin (j * r), if cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i)
      then coefficients (j * r) f l else 0) = coefficients (j * r) f i
  have he : (∑ l : Fin (j * r),
      if cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i)
      then coefficients (j * r) f l else 0) =
      ∑ l ∈ Finset.univ.filter (fun l : Fin (j * r) =>
        cell j (midpoint (j * r) l) = cell j (midpoint (j * r) i)),
        coefficients (j * r) f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with h
    · rw [coefficients_histogram_const_apply j (j * r) hj hJ (dvd_mul_right j r) f hf l,
        coefficients_histogram_const_apply j (j * r) hj hJ (dvd_mul_right j r) f hf i,
        hf _ _ h]
    · rfl
  rw [he, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, Nat.cast_mul,
    midpoint_fiber_mass_mul j r hj hr i, one_mul]

/-- Any positive band kills a histogram whose rank divides its lower resolution. -/
-- @node: Qband_histogram_const_eq_zero
lemma Qband_histogram_const_eq_zero (j L T t : ℕ) (hj : 0 < j) (hL : 0 < L)
    (ht : 0 < t) (htT : t ≤ T) (hjd : j ∣ 2 ^ (t - 1) * L)
    (f : ℝ → ℝ) (hf : ∀ y z, cell j y = cell j z → f y = f z) :
    Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) f) = 0 := by
  have hlow := band_rank_dvd L (t - 1) T (by omega)
  have hjJ := dvd_trans hjd hlow
  have hfix := coefficientProjection_fix_histogram_const j (2 ^ T * L) hj
    (by positivity) hjJ f hf
  have hh := (coefficientProjection_nested_of_dvd j (2 ^ t * L) (2 ^ T * L)
    hj (by positivity) (by positivity)
    (dvd_trans hjd (band_rank_dvd L (t - 1) t (by omega)))
    (band_rank_dvd L t T htT) (coefficients (2 ^ T * L) f)).1
  have hl := (coefficientProjection_nested_of_dvd j (2 ^ (t - 1) * L) (2 ^ T * L)
    hj (by positivity) (by positivity) hjd hlow (coefficients (2 ^ T * L) f)).1
  rw [hfix] at hh hl
  simp only [Qband, if_neg (by omega : t ≠ 0), hh, hl, sub_self]

/-- The normalized trained density pilot is absent from every positive outcome band. -/
-- @node: densityPilot_high_band_eq_zero
lemma densityPilot_high_band_eq_zero {m : ℕ} (train : Fin m → Omega)
    (mx my L T t : ℕ) (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L)
    (ht : 0 < t) (htT : t ≤ T) (a : Bool) (x : ℝ) :
    Qband L (2 ^ T * L) t (coefficients (2 ^ T * L)
      (densityPilot train mx my a x)) = 0 := by
  obtain ⟨u, hu⟩ := hmy
  obtain ⟨v, hv⟩ := hL
  have huv : u ≤ v := by
    rw [hu, hv] at hmyL
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 hmyL
  have hdiv : my ∣ L := by
    rw [hu, hv]
    exact pow_dvd_pow 2 huv
  apply Qband_histogram_const_eq_zero my L T t
    (by rw [hu]; positivity) (by rw [hv]; positivity) ht htT
    (dvd_trans hdiv (dvd_mul_left L (2 ^ (t - 1))))
  exact densityPilot_eq_of_outcome_cell_eq train mx my a x


/-- Every outcome projection is constant within its own cells. -/
-- @node: outcomeProjection_eq_of_cell_eq
lemma outcomeProjection_eq_of_cell_eq (d : ℕ) (f : ℝ → ℝ) (y z : ℝ)
    (hc : cell d y = cell d z) : outcomeProjection d f y = outcomeProjection d f z := by
  simp only [outcomeProjection, hc]

/-- Outcome projection factors through the measurable countable cell label. -/
-- @node: measurable_outcomeProjection
@[fun_prop] lemma measurable_outcomeProjection (d : ℕ) (f : ℝ → ℝ) :
    Measurable (outcomeProjection d f) := by
  let g : ℕ → ℝ := fun c => (d : ℝ) * ∫ y in histogramCell d c, f y ∂unitVolume
  exact (measurable_of_countable g).comp (measurable_cell d)

/-- Removing any lower-rank histogram leaves a positive band unchanged. -/
-- @node: Qband_coefficients_sub_histogram_const
lemma Qband_coefficients_sub_histogram_const (j L T t : ℕ)
    (hj : 0 < j) (hL : 0 < L) (ht : 0 < t) (htT : t ≤ T)
    (hjd : j ∣ 2 ^ (t - 1) * L) (f g : ℝ → ℝ)
    (hf : Integrable f unitVolume) (hg : Integrable g unitVolume)
    (hgc : ∀ y z, cell j y = cell j z → g y = g z) :
    Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (fun y => f y - g y)) =
      Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) f) := by
  have he := coefficients_const_mul_sub (2 ^ T * L) 1 f g hf hg
  simp only [one_mul, one_smul] at he
  rw [he, Qband_sub, Qband_histogram_const_eq_zero j L T t hj hL ht htT hjd g hgc,
    sub_zero]

/-- The conditional density's high-band norm is at most ten over the lower band rank. -/
-- @node: model_eta_high_band_norm_le
lemma model_eta_high_band_norm_le (P : ObsLaw) (hModel : Model P)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) (L T t : ℕ)
    (hL : Dyadic L) (ht : 0 < t) (htT : t ≤ T) :
    ‖Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (P.eta a x))‖ ≤
      10 / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  let d := 2 ^ (t - 1) * L
  have hd : 0 < d := by dsimp [d]; positivity
  have hi : Integrable (outcomeProjection d (P.eta a x)) unitVolume := by
    let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
    apply Integrable.of_bound (by fun_prop) (10 / (d : ℝ) + 8)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |outcomeProjection d (P.eta a x) y - P.eta a x y| + |P.eta a x y| :=
        by simpa only [sub_add_cancel] using
          abs_add_le (outcomeProjection d (P.eta a x) y - P.eta a x y) (P.eta a x y)
      _ ≤ 10 / (d : ℝ) + 8 := add_le_add
        (model_eta_projection_error_le P hModel a x hx d hd y hy)
        (abs_le.mpr ⟨by linarith [(hModel.density_envelope a x y hx hy).1],
          by linarith [(hModel.density_envelope a x y hx hy).2]⟩)
  rw [← Qband_coefficients_sub_histogram_const d L T t hd hLpos ht htT
    (dvd_refl d) (P.eta a x) (outcomeProjection d (P.eta a x))
    (P.eta_integrable a x hx) hi (outcomeProjection_eq_of_cell_eq d (P.eta a x))]
  exact model_eta_projection_residual_band_norm_le P hModel a x hx d L T t hd hL htT

/-- Above the pilot outcome rank, the weighted-error band equals the weighted true-density band. -/
-- @node: verr_high_band_eq_weighted_eta
lemma verr_high_band_eq_weighted_eta {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my L T t : ℕ) (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L)
    (ht : 0 < t) (htT : t ≤ T) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (verr P train mx my a x)) =
      (1 + uerr P train mx a x) •
        Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (P.eta a x)) := by
  rw [show verr P train mx my a x = fun y =>
    (1 + uerr P train mx a x) * (P.eta a x y - densityPilot train mx my a x y) from rfl,
    coefficients_const_mul_sub _ _ _ _ (P.eta_integrable a x hx)
      (densityPilot_integrable train mx my a x), Qband_smul, Qband_sub,
    densityPilot_high_band_eq_zero train mx my L T t hmy hL hmyL ht htT a x, sub_zero]

/-- Clipping bounds the weighted-error high band by thirty over the lower band rank. -/
-- @node: verr_high_band_norm_le
lemma verr_high_band_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T t : ℕ)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    ‖Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (verr P train mx my a x))‖ ≤
      30 / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  rw [verr_high_band_eq_weighted_eta P train mx my L T t hmy hL hmyL ht htT a x hx,
    norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 3 * (10 / ((2 ^ (t - 1) * L : ℕ) : ℝ)) := mul_le_mul
      (one_add_uerr_abs_le P hModel train mx a x hx)
      (model_eta_high_band_norm_le P hModel a x hx L T t hL ht htT)
      (norm_nonneg _) (by norm_num)
    _ = 30 / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by push_cast; ring

/-- The actual weighted-error bands have the sixty-over-rank oscillation required by (26). -/
-- @node: verr_high_band_oscillation_norm_le
lemma verr_high_band_oscillation_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T t : ℕ)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) (x z : ℝ) (hx : x ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    ‖Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (verr P train mx my a x)) -
      Qband L (2 ^ T * L) t (coefficients (2 ^ T * L) (verr P train mx my a z))‖ ≤
      60 / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ 30 / ((2 ^ (t - 1) * L : ℕ) : ℝ) + 30 / ((2 ^ (t - 1) * L : ℕ) : ℝ) := add_le_add
      (verr_high_band_norm_le P hModel train mx my L T t hmy hL hmyL ht htT a x hx)
      (verr_high_band_norm_le P hModel train mx my L T t hmy hL hmyL ht htT a z hz)
    _ = _ := by ring

end CausalSmith.Stat.DensityEffectRoughNull
