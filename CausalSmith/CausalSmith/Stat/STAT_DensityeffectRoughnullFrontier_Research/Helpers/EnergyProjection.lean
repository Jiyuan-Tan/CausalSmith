module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualSecondMoment

/-! Concrete histogram Pythagoras and the contrast approximation budget in (30). -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Reciprocal cell masses make the histogram representation an isometry. -/
-- @node: histogramFunction_squared_integral_eq
lemma histogramFunction_squared_integral_eq (J : ℕ) (hJ : 0 < J) (f : Hj J) :
    (∫ y, (histogramFunction f y) ^ 2 ∂unitVolume) = ‖f‖ ^ 2 := by
  classical
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hs (i : Fin J) : MeasurableSet {y | cell J y = i.val + 1} := by
    have hc : Measurable (cell J) := by
      unfold cell
      have hf : Measurable (fun x : ℝ => ⌊(J : ℝ) * x⌋₊) :=
        Nat.measurable_floor.comp (by fun_prop)
      fun_prop
    exact hc (measurableSet_singleton _)
  have hi (i : Fin J) : Integrable (fun y =>
      if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0) unitVolume := by
    have heq : (fun y => if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0) =
        {y | cell J y = i.val + 1}.indicator (fun _ => (J : ℝ) * (f i) ^ 2) := by
      funext y
      simp [Set.indicator]
    rw [heq]
    exact (integrable_const (μ := unitVolume) _).indicator (hs i)
  simp_rw [histogramFunction_sq]
  rw [integral_finsetSum _ (fun i _ => hi i), EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (∫ y, (if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0)
      ∂unitVolume) = unitVolume.real (histogramCell J (i.val + 1)) * ((J : ℝ) * (f i) ^ 2) := by
    have hcell : MeasurableSet (histogramCell J (i.val + 1)) :=
      measurableSet_Icc.inter (hs i)
    calc
      _ = ∫ y, (histogramCell J (i.val + 1)).indicator
          (fun _ => (J : ℝ) * (f i) ^ 2) y ∂unitVolume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        simp [Set.indicator, histogramCell, hy.1, hy.2]
      _ = _ := by
        rw [integral_indicator hcell, integral_const]
        simp [measureReal_def, smul_eq_mul]
  rw [heq]
  rw [histogramCell_mass_eq J hJ i]
  field_simp

/-- Projection coefficients represent the actual outcome bin average on the unit interval. -/
-- @node: histogramFunction_coefficients_eq_projection
lemma histogramFunction_coefficients_eq_projection (J : ℕ) (hJ : 0 < J)
    (f : ℝ → ℝ) (y : ℝ) :
    histogramFunction (coefficients J f) y = outcomeProjection J f y := by
  classical
  have hind : 1 ≤ cell J y ∧ cell J y ≤ J := by
    unfold cell
    constructor <;> omega
  let i : Fin J := ⟨cell J y - 1, by omega⟩
  have hc : cell J y = i.val + 1 := by dsimp [i]; omega
  have heq (l : Fin J) : cell J y = l.val + 1 ↔ l = i := by
    rw [hc]
    constructor
    · intro h; apply Fin.ext; omega
    · rintro rfl; rfl
  simp only [histogramFunction, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change Real.sqrt J * (Real.sqrt J * ∫ z in histogramCell J (i.val + 1), f z ∂unitVolume) = _
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg J)]
  simp only [outcomeProjection, hc]

/-- Orthogonality to the represented projection gives the exact energy decomposition. -/
-- @node: histogram_projection_energy_decomposition
lemma histogram_projection_energy_decomposition (J : ℕ) (hJ : 0 < J)
    (f : ℝ → ℝ) (hf : Integrable f unitVolume)
    (hfsq : Integrable (fun y => (f y) ^ 2) unitVolume) :
    l2Squared f = ‖coefficients J f‖ ^ 2 +
      l2Squared (fun y => f y - outcomeProjection J f y) := by
  let p := coefficients J f
  have hp := (histogramFunction_integrable J p).2
  have hfp := integrable_mul_histogramFunction J p f hf
  have hpair : (∫ y, f y * histogramFunction p y ∂unitVolume) = ‖p‖ ^ 2 := by
    rw [← inner_coefficients_eq_integral J p f hf]
    exact real_inner_self_eq_norm_sq p
  have hexpand : (fun y => (f y - outcomeProjection J f y) ^ 2) =
      fun y => (f y) ^ 2 - 2 * (f y * histogramFunction p y) + (histogramFunction p y) ^ 2 := by
    funext y
    rw [← histogramFunction_coefficients_eq_projection J hJ f y]
    dsimp [p]
    ring
  have hsub : Integrable (fun y => (f y) ^ 2 - 2 * (f y * histogramFunction p y)) unitVolume :=
    hfsq.sub (hfp.const_mul 2)
  unfold l2Squared
  rw [hexpand, integral_add hsub hp,
    integral_sub hfsq (hfp.const_mul 2), integral_const_mul, hpair,
    histogramFunction_squared_integral_eq J hJ p]
  change _ = ‖p‖ ^ 2 + _
  ring

/-- Joint measurability of the conditional density gives measurable marginal densities. -/
@[fun_prop] lemma measurable_marginalDensity (P : ObsLaw) (a : Bool) :
    Measurable (marginalDensity P a) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (P.eta_measurable a).stronglyMeasurable.integral_prod_left'.measurable

/-- Each fixed outcome slice is integrable on the covariate domain by the model envelope. -/
-- @node: model_eta_covariate_integrable
lemma model_eta_covariate_integrable (P : ObsLaw) (hModel : Model P)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    Integrable (fun x => P.eta a x y) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound ((P.eta_measurable a).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable 4
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  change ‖P.eta a x y‖ ≤ 4
  rw [Real.norm_eq_abs, abs_of_nonneg (P.eta_nonneg a x y hx hy)]
  exact (hModel.density_envelope a x y hx hy).2

/-- Integrating the conditional envelopes bounds each marginal by four. -/
-- @node: model_marginalDensity_abs_le
lemma model_marginalDensity_abs_le (P : ObsLaw) (hModel : Model P)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) : |marginalDensity P a y| ≤ 4 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hb : ∀ᵐ x ∂unitVolume, ‖P.eta a x y‖ ≤ 4 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (P.eta_nonneg a x y hx hy)]
    exact (hModel.density_envelope a x y hx hy).2
  have h := norm_integral_le_of_norm_le_const hb
  simpa [marginalDensity, Real.norm_eq_abs] using h

/-- The contrast is measurable and bounded, hence both it and its square are integrable. -/
-- @node: model_delta_integrable
lemma model_delta_integrable (P : ObsLaw) (hModel : Model P) :
    Integrable (delta P) unitVolume ∧ Integrable (fun y => (delta P y) ^ 2) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hm : Measurable (delta P) := by unfold delta; fun_prop
  have hb : ∀ᵐ y ∂unitVolume, |delta P y| ≤ 8 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    unfold delta
    exact (abs_sub _ _).trans (by linarith [model_marginalDensity_abs_le P hModel true y hy,
      model_marginalDensity_abs_le P hModel false y hy])
  constructor
  · exact Integrable.of_bound hm.aestronglyMeasurable 8
      (by simpa only [Real.norm_eq_abs] using hb)
  · have hs : Measurable (fun y => (delta P y) ^ 2) := by fun_prop
    apply Integrable.of_bound hs.aestronglyMeasurable 64
    filter_upwards [hb] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (delta P y), abs_nonneg (delta P y)]

/-- Averaging conditional Lipschitz inequalities preserves their constant ten. -/
-- @node: model_marginalDensity_lipschitz
lemma model_marginalDensity_lipschitz (P : ObsLaw) (hModel : Model P)
    (a : Bool) (y z : ℝ) (hy : y ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    |marginalDensity P a y - marginalDensity P a z| ≤ 10 * |y - z| := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  rw [marginalDensity, marginalDensity, ← integral_sub
    (model_eta_covariate_integrable P hModel a y hy)
    (model_eta_covariate_integrable P hModel a z hz)]
  have hb : ∀ᵐ x ∂unitVolume, ‖P.eta a x y - P.eta a x z‖ ≤ 10 * |y - z| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hModel.density_outcome_lipschitz a x hx y hy z hz
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- The difference of two ten-Lipschitz marginal densities is twenty-Lipschitz. -/
-- @node: model_delta_lipschitz
lemma model_delta_lipschitz (P : ObsLaw) (hModel : Model P)
    (y z : ℝ) (hy : y ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    |delta P y - delta P z| ≤ 20 * |y - z| := by
  have ht := model_marginalDensity_lipschitz P hModel true y z hy hz
  have hf := model_marginalDensity_lipschitz P hModel false y z hy hz
  calc
    _ = |(marginalDensity P true y - marginalDensity P true z) -
      (marginalDensity P false y - marginalDensity P false z)| := by unfold delta; congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-- The concrete contrast projection has pointwise error at most twenty divided by rank. -/
-- @node: model_delta_projection_error_le
lemma model_delta_projection_error_le (P : ObsLaw) (hModel : Model P)
    (J : ℕ) (hJ : 0 < J) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    |outcomeProjection J (delta P) y - delta P y| ≤ 20 / (J : ℝ) := by
  have hind : 1 ≤ cell J y ∧ cell J y ≤ J := by unfold cell; constructor <;> omega
  let i : Fin J := ⟨cell J y - 1, by omega⟩
  have hc : cell J y = i.val + 1 := by dsimp [i]; omega
  apply outcomeProjection_error_le J hJ i _ (model_delta_integrable P hModel).1 y _ hc
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell J (i.val + 1))] with z hz
  have hb := histogramCell_subset_bin J hJ i hz
  have hby := histogramCell_subset_bin J hJ i ⟨hy, hc⟩
  have hd : |z - y| ≤ 1 / (J : ℝ) := by
    simp only [add_div] at hb hby
    apply abs_le.mpr
    constructor <;> linarith [hb.1, hb.2, hby.1, hby.2]
  exact (model_delta_lipschitz P hModel z y hz.1 hy).trans
    (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 20))

/-- Squaring and integrating the contrast approximation gives exactly the remainder in (30). -/
-- @node: model_delta_projection_l2Squared_le
lemma model_delta_projection_l2Squared_le (P : ObsLaw) (hModel : Model P)
    (J : ℕ) (hJ : 0 < J) :
    l2Squared (fun y => delta P y - outcomeProjection J (delta P) y) ≤
      400 * (J : ℝ) ^ (-2 : ℤ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hb : ∀ᵐ y ∂unitVolume,
      (delta P y - outcomeProjection J (delta P) y) ^ 2 ≤ (20 / (J : ℝ)) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have h := model_delta_projection_error_le P hModel J hJ y hy
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    simpa only [← sq, sq_abs, sub_sq_comm] using hs
  have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => sq_nonneg _))
    (integrable_const ((20 / (J : ℝ)) ^ 2)) hb
  have heq : (20 / (J : ℝ)) ^ 2 = 400 * (J : ℝ) ^ (-2 : ℤ) := by
    simp [zpow_neg, div_pow]; ring
  simpa only [l2Squared, integral_const, probReal_univ, smul_eq_mul, one_mul, heq] using hi

/-- Pythagoras, positivity and the concrete approximation give both projection energy budgets. -/
-- @node: model_delta_projection_budgets
lemma model_delta_projection_budgets (P : ObsLaw) (hModel : Model P)
    (J : ℕ) (hJ : 0 < J) :
    ‖coefficients J (delta P)‖ ≤ Real.sqrt (Psi P) ∧
      |‖coefficients J (delta P)‖ ^ 2 - Psi P| ≤ 400 * (J : ℝ) ^ (-2 : ℤ) := by
  have heq := histogram_projection_energy_decomposition J hJ (delta P)
    (model_delta_integrable P hModel).1 (model_delta_integrable P hModel).2
  have hn : 0 ≤ l2Squared (fun y => delta P y - outcomeProjection J (delta P) y) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hPsi : 0 ≤ Psi P := integral_nonneg (fun _ => sq_nonneg _)
  constructor
  · apply (Real.le_sqrt (norm_nonneg _) hPsi).2
    change Psi P = _ at heq
    linarith
  · change Psi P = _ at heq
    rw [show ‖coefficients J (delta P)‖ ^ 2 - Psi P =
      -l2Squared (fun y => delta P y - outcomeProjection J (delta P) y) by linarith,
      abs_neg, abs_of_nonneg hn]
    exact model_delta_projection_l2Squared_le P hModel J hJ

end CausalSmith.Stat.DensityEffectRoughNull
