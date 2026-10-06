module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellRemainderBounds
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ConditionalProjection
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellProjectionMeans

/-! High-band correction-cell covariance bounds combining (24)--(26).
The outcome-band oscillation is used before covariance estimation, preserving
its inverse-rank decay. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Joint integrability gives integrability of the conditional outcome coefficient vector. -/
-- @node: integrable_covariate_coefficients
lemma integrable_covariate_coefficients (J : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) :
    Integrable (fun x => coefficients J (f x)) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hw := integrable_joint_weighted_phiCoefficients J f hf
  apply hw.integral_prod_left.congr
  filter_upwards [hf.prod_right_ae] with x hx
  exact integral_weighted_phiCoefficients J (f x) hx

/-- A true high outcome band is integrable under the uniform covariate design. -/
-- @node: integrable_verr_high_band
lemma integrable_verr_high_band {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T t : ℕ)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) :
    Integrable (fun x => Qband L (2 ^ T * L) t
      (coefficients (2 ^ T * L) (verr P train mx my a x))) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let : MeasurableSpace (Hj (2 ^ T * L)) := borel _
  let : BorelSpace (Hj (2 ^ T * L)) := ⟨rfl⟩
  have hv : Integrable (Function.uncurry (verr P train mx my a))
      (unitVolume.prod unitVolume) := by
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  have hc := integrable_covariate_coefficients (2 ^ T * L) (verr P train mx my a) hv
  apply Integrable.of_bound
    ((measurable_Qband L (2 ^ T * L) t).comp_aemeasurable hc.aemeasurable).aestronglyMeasurable
    (30 / ((2 ^ (t - 1) * L : ℕ) : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact verr_high_band_norm_le P hModel train mx my L T t hmy hL hmyL ht htT a x hx

/-- On each refined correction cell, high-band covariance is bounded by 2400 k⁻¹ᐟ¹⁰/d. -/
-- @node: correctionCell_high_band_covariance_norm_le
lemma correctionCell_high_band_covariance_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my k L T t : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) (i : Fin k) :
    ‖(∫ x, uerr P train mx a x • Qband L (2 ^ T * L) t
        (coefficients (2 ^ T * L) (verr P train mx my a x)) ∂correctionCellLaw k i) -
      (∫ x, uerr P train mx a x ∂correctionCellLaw k i) •
        (∫ x, Qband L (2 ^ T * L) t
          (coefficients (2 ^ T * L) (verr P train mx my a x)) ∂correctionCellLaw k i)‖ ≤
      2400 * (k : ℝ) ^ (-1 / 10 : ℝ) / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  let := correctionCellLaw_probability k hk i
  let r := fun x => Qband L (2 ^ T * L) t
    (coefficients (2 ^ T * L) (verr P train mx my a x))
  have hu := integrable_correctionCellLaw k i _ (integrable_uerr_covariate P hModel train mx a)
  have hr : Integrable r (correctionCellLaw k i) :=
    (integrable_verr_high_band P hModel train mx my L T t hmy hL hmyL ht htT a).integrableOn
      |>.smul_measure (by simp)
  have hur : Integrable (fun x => uerr P train mx a x • r x) (correctionCellLaw k i) := by
    apply Integrable.of_bound (hu.aestronglyMeasurable.smul hr.aestronglyMeasurable)
      (2 * (30 / ((2 ^ (t - 1) * L : ℕ) : ℝ)))
    filter_upwards [correctionCellLaw_support k i] with x hx
    change ‖uerr P train mx a x • r x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    have hb : |uerr P train mx a x| ≤ 2 := by
      have h := uerr_mem_Icc P hModel train mx a x hx.1
      exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
    exact mul_le_mul hb
      (verr_high_band_norm_le P hModel train mx my L T t hmy hL hmyL ht htT a x hx.1)
      (norm_nonneg _) (by norm_num)
  have ha : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      |uerr P train mx a x - uerr P train mx a z| ≤ 40 * (k : ℝ) ^ (-1 / 10 : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    exact uerr_refined_cell_oscillation P hModel train mx k hmx hk hdiv a x z
      hx.1 hz.1 (hx.2.trans hz.2.symm)
  have hb : ∀ᵐ x ∂correctionCellLaw k i, ∀ᵐ z ∂correctionCellLaw k i,
      ‖r x - r z‖ ≤ 60 / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
    filter_upwards [correctionCellLaw_support k i] with x hx
    filter_upwards [correctionCellLaw_support k i] with z hz
    exact verr_high_band_oscillation_norm_le P hModel train mx my L T t
      hmy hL hmyL ht htT a x z hx.1 hz.1
  have h := cell_covariance_norm_le_of_oscillation (correctionCellLaw k i)
    (uerr P train mx a) r hu hr hur (40 * (k : ℝ) ^ (-1 / 10 : ℝ))
    (60 / ((2 ^ (t - 1) * L : ℕ) : ℝ)) (by positivity) ha hb
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The concrete high-band cell-average covariance has the same uniform envelope. -/
-- @node: cellAverage_high_band_covariance_norm_le
lemma cellAverage_high_band_covariance_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my k L T t : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) (x : ℝ) :
    ‖cellAverage k (fun z => uerr P train mx a z • Qband L (2 ^ T * L) t
        (coefficients (2 ^ T * L) (verr P train mx my a z))) x -
      cellAverage k (uerr P train mx a) x •
        cellAverage k (fun z => Qband L (2 ^ T * L) t
          (coefficients (2 ^ T * L) (verr P train mx my a z))) x‖ ≤
      2400 * (k : ℝ) ^ (-1 / 10 : ℝ) / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hc : cell k x = i.val + 1 := by dsimp [i]; omega
  simp only [cellAverage_eq_correctionCellLaw k i _ x hc]
  exact correctionCell_high_band_covariance_norm_le P hModel train mx my k L T t
    hmx hk hdiv hmy hL hmyL ht htT a i

/-- Integrating the high-band cell covariances preserves the constant 2400 and band decay. -/
-- @node: integrated_high_band_cell_covariance_norm_le
lemma integrated_high_band_cell_covariance_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my k L T t : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hmy : Dyadic my) (hL : Dyadic L) (hmyL : my ≤ L) (ht : 0 < t) (htT : t ≤ T)
    (a : Bool) :
    ‖∫ x, cellAverage k (fun z => uerr P train mx a z • Qband L (2 ^ T * L) t
        (coefficients (2 ^ T * L) (verr P train mx my a z))) x -
      cellAverage k (uerr P train mx a) x •
        cellAverage k (fun z => Qband L (2 ^ T * L) t
          (coefficients (2 ^ T * L) (verr P train mx my a z))) x ∂unitVolume‖ ≤
      2400 * (k : ℝ) ^ (-1 / 10 : ℝ) / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hb : ∀ᵐ x ∂unitVolume,
      ‖cellAverage k (fun z => uerr P train mx a z • Qband L (2 ^ T * L) t
          (coefficients (2 ^ T * L) (verr P train mx my a z))) x -
        cellAverage k (uerr P train mx a) x •
          cellAverage k (fun z => Qband L (2 ^ T * L) t
            (coefficients (2 ^ T * L) (verr P train mx my a z))) x‖ ≤
        2400 * (k : ℝ) ^ (-1 / 10 : ℝ) / ((2 ^ (t - 1) * L : ℕ) : ℝ) := by
    filter_upwards [] with x
    exact cellAverage_high_band_covariance_norm_le P hModel train mx my k L T t
      hmx hk hdiv hmy hL hmyL ht htT a x
  simpa using norm_integral_le_of_norm_le_const hb

end CausalSmith.Stat.DensityEffectRoughNull
