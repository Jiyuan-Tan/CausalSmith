module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellMeanCovariance

/-! Integrated polynomial cancellation (22) and the exact scalar correction assembly.
All integrability is derived from the model envelopes and pilot clipping, for every training
realization; no good-pilot event is required for these identities. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Conditional outcome densities are integrable as functions of the uniform covariate. -/
-- @node: integrable_eta_covariate
lemma integrable_eta_covariate (P : ObsLaw) (hModel : Model P)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    Integrable (fun x => P.eta a x y) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hmeas : Measurable (fun x => P.eta a x y) :=
    (P.eta_measurable a).comp (measurable_id.prodMk measurable_const)
  apply Integrable.of_bound hmeas.aestronglyMeasurable 4
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (P.eta_nonneg a x y hx hy)]
  exact (hModel.density_envelope a x y hx hy).2

/-- Pilot clipping also supplies covariate-slice integrability. -/
-- @node: integrable_densityPilot_covariate
@[fun_prop] lemma integrable_densityPilot_covariate {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (y : ℝ) :
    Integrable (fun x => densityPilot train mx my a x y) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 64
  filter_upwards [] with x
  have h := densityPilot_mem_Icc train mx my a x y
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
  exact h.2

/-- Clipping bounds every propensity-power times density-error slice, without a pilot event. -/
-- @node: integrable_uerr_pow_mul_werr_covariate
lemma integrable_uerr_pow_mul_werr_covariate {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (y : ℝ)
    (hy : y ∈ Set.Icc 0 1) (n : ℕ) :
    Integrable (fun x => (uerr P train mx a x) ^ n * werr P train mx my a x y)
      unitVolume := by
  have hw : Integrable (fun x => werr P train mx my a x y) unitVolume :=
    (integrable_eta_covariate P hModel a y hy).sub
      (integrable_densityPilot_covariate train mx my a y)
  have hb : ∀ᵐ x ∂unitVolume, ‖(uerr P train mx a x) ^ n‖ ≤ 2 ^ n := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (uerr_abs_le P hModel train mx a x hx) n
  simpa only [mul_comm] using hw.mul_bdd (by fun_prop) hb

/-- The weighted outcome residual and its propensity-power products are integrable. -/
-- @node: integrable_uerr_pow_mul_verr_covariate
lemma integrable_uerr_pow_mul_verr_covariate {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (y : ℝ)
    (hy : y ∈ Set.Icc 0 1) (n : ℕ) :
    Integrable (fun x => (uerr P train mx a x) ^ n * verr P train mx my a x y)
      unitVolume := by
  have h0 := integrable_uerr_pow_mul_werr_covariate P hModel train mx my a y hy n
  have h1 := integrable_uerr_pow_mul_werr_covariate P hModel train mx my a y hy (n + 1)
  apply (h0.add h1).congr
  filter_upwards [] with x
  dsimp [verr]
  rw [pow_succ]
  ring

/-- Design integration preserves the exact cubic cancellation (22). -/
-- @node: corrected_mean_integrated_identity
lemma corrected_mean_integrated_identity {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (y : ℝ)
    (hy : y ∈ Set.Icc 0 1) :
    (∫ x, densityPilot train mx my a x y ∂unitVolume) +
      (∫ x, verr P train mx my a x y ∂unitVolume) -
      (∫ x, uerr P train mx a x * verr P train mx my a x y ∂unitVolume) +
      (∫ x, (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume) =
    marginalDensity P a y +
      ∫ x, (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume := by
  have hp := integrable_densityPilot_covariate train mx my a y
  have he := integrable_eta_covariate P hModel a y hy
  have hv : Integrable (fun x => verr P train mx my a x y) unitVolume := by
    simpa using integrable_uerr_pow_mul_verr_covariate P hModel train mx my a y hy 0
  have huv : Integrable (fun x => uerr P train mx a x * verr P train mx my a x y)
      unitVolume := by
    simpa using integrable_uerr_pow_mul_verr_covariate P hModel train mx my a y hy 1
  have hu2v := integrable_uerr_pow_mul_verr_covariate P hModel train mx my a y hy 2
  have hu3w := integrable_uerr_pow_mul_werr_covariate P hModel train mx my a y hy 3
  have h := integral_congr_ae (μ := unitVolume) (Filter.Eventually.of_forall
    (fun x => corrected_mean_pointwise_identity P train mx my a x y))
  change _ = (∫ x, P.eta a x y ∂unitVolume) + _
  calc
    _ = ∫ x, densityPilot train mx my a x y + verr P train mx my a x y -
        uerr P train mx a x * verr P train mx my a x y +
        (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume := by
      integral_linearity
    _ = ∫ x, P.eta a x y +
        (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume := h
    _ = _ := by integral_linearity


/-- Squared cell means times another cell mean are integrable because they are cellwise constant. -/
-- @node: integrable_cellAverage_sq_mul
lemma integrable_cellAverage_sq_mul (k : ℕ) (hk : 0 < k) (g r : ℝ → ℝ) :
    Integrable (fun x => (cellAverage k g x) ^ 2 * cellAverage k r x) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply integrable_of_histogramCells k hk
  intro i
  apply (integrable_const ((∫ z, g z ∂correctionCellLaw k i) ^ 2 *
    (∫ z, r z ∂correctionCellLaw k i))).congr
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
  rw [cellAverage_eq_correctionCellLaw k i g x hx.2,
    cellAverage_eq_correctionCellLaw k i r x hx.2]

/-- Inserting the unaveraged products gives the scalar arm assembly from (21)--(22). -/
-- @node: corrected_mean_scalar_arm_identity
lemma corrected_mean_scalar_arm_identity {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    (∫ x, densityPilot train mx my a x y ∂unitVolume) +
      (∫ x, verr P train mx my a x y ∂unitVolume) -
      (∫ x, cellAverage k (uerr P train mx a) x *
        cellAverage k (fun z => verr P train mx my a z y) x ∂unitVolume) +
      (∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 *
        cellAverage q (fun z => verr P train mx my a z y) x ∂unitVolume) -
      marginalDensity P a y =
    (∫ x, (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume) +
      (∫ x, uerr P train mx a x * verr P train mx my a x y -
        cellAverage k (uerr P train mx a) x *
          cellAverage k (fun z => verr P train mx my a z y) x ∂unitVolume) +
      (∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 *
        cellAverage q (fun z => verr P train mx my a z y) x -
        (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume) := by
  have hcancel := corrected_mean_integrated_identity P hModel train mx my a y hy
  have huv : Integrable (fun x => uerr P train mx a x * verr P train mx my a x y)
      unitVolume := by
    simpa using integrable_uerr_pow_mul_verr_covariate P hModel train mx my a y hy 1
  have hu2v := integrable_uerr_pow_mul_verr_covariate P hModel train mx my a y hy 2
  rw [integral_sub huv (integrable_cellAverage_mul k hk _ _),
    integral_sub (integrable_cellAverage_sq_mul q hq _ _) hu2v]
  linarith only [hcancel]

end CausalSmith.Stat.DensityEffectRoughNull
