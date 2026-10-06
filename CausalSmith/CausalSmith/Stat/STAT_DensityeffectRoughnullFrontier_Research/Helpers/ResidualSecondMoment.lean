module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.HistogramGeometry
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualMoments

/-! Conditional histogram residual second moments, uniformly in the outcome rank. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Multiplication by a fixed histogram test preserves integrability. -/
-- @node: integrable_mul_histogramFunction
lemma integrable_mul_histogramFunction (J : ℕ) (f : Hj J) (g : ℝ → ℝ)
    (hg : Integrable g unitVolume) :
    Integrable (fun y => g y * histogramFunction f y) unitVolume := by
  apply hg.mul_bdd (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using histogramFunction_abs_le J f y)

/-- Multiplication by the square of a fixed histogram test preserves integrability. -/
-- @node: integrable_mul_histogramFunction_sq
lemma integrable_mul_histogramFunction_sq (J : ℕ) (f : Hj J) (g : ℝ → ℝ)
    (hg : Integrable g unitVolume) :
    Integrable (fun y => g y * (histogramFunction f y) ^ 2) unitVolume := by
  apply hg.mul_bdd (c := (∑ i : Fin J, |Real.sqrt J * f i|) ^ 2) (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := mul_self_le_mul_self (abs_nonneg _) (histogramFunction_abs_le J f y)
  simpa only [← sq, sq_abs] using h

/-- The coefficient pairing is the density-weighted integral of the histogram test. -/
-- @node: inner_coefficients_eq_integral
lemma inner_coefficients_eq_integral (J : ℕ) (f : Hj J) (g : ℝ → ℝ)
    (hg : Integrable g unitVolume) :
    inner ℝ (coefficients J g) f = ∫ y, g y * histogramFunction f y ∂unitVolume := by
  rw [← integral_weighted_phiCoefficients J g hg, PiLp.inner_apply]
  simp_rw [eval_integral_piLp (f := fun y => g y • phiCoefficients J y) (fun i => by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      weighted_phi_coordinate_integrable J g hg i)]
  simp only [PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ =>
    (weighted_phi_coordinate_integrable J g hg i).const_mul (f i))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← inner_phiCoefficients, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A normalized nonnegative density obeys the squared-integral inequality for histogram tests. -/
-- @node: density_histogram_integral_sq_le
lemma density_histogram_integral_sq_le (J : ℕ) (f : Hj J) (g : ℝ → ℝ)
    (hg : Integrable g unitVolume) (hn : ∫ y, g y ∂unitVolume = 1)
    (hpos : ∀ᵐ y ∂unitVolume, 0 ≤ g y) :
    (∫ y, g y * histogramFunction f y ∂unitVolume) ^ 2 ≤
      ∫ y, g y * (histogramFunction f y) ^ 2 ∂unitVolume := by
  let c := ∫ y, g y * histogramFunction f y ∂unitVolume
  have hi := integrable_mul_histogramFunction J f g hg
  have hs := integrable_mul_histogramFunction_sq J f g hg
  have hnon : 0 ≤ ∫ y, g y * (histogramFunction f y - c) ^ 2 ∂unitVolume := by
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with y hy
    exact mul_nonneg hy (sq_nonneg _)
  have heq : (∫ y, g y * (histogramFunction f y - c) ^ 2 ∂unitVolume) =
      (∫ y, g y * (histogramFunction f y) ^ 2 ∂unitVolume) - c ^ 2 := by
    have hfun : (fun y => g y * (histogramFunction f y - c) ^ 2) =
        fun y => g y * (histogramFunction f y) ^ 2 -
          (2 * c) * (g y * histogramFunction f y) + c ^ 2 * g y := by
      funext y
      ring
    rw [hfun]
    integral_linearity
    rw [hn]
    dsimp [c]
    ring
  rw [heq] at hnon
  exact sub_nonneg.mp hnon

/-- A bounded density weights histogram energy by at most its envelope. -/
-- @node: density_histogram_energy_le
lemma density_histogram_energy_le (J : ℕ) (hJ : 0 < J) (f : Hj J)
    (g : ℝ → ℝ) (hg : Integrable g unitVolume) (b : ℝ) (hb : 0 ≤ b)
    (henv : ∀ᵐ y ∂unitVolume, g y ≤ b) :
    (∫ y, g y * (histogramFunction f y) ^ 2 ∂unitVolume) ≤ b * ‖f‖ ^ 2 := by
  calc
    _ ≤ ∫ y, b * (histogramFunction f y) ^ 2 ∂unitVolume := by
      apply integral_mono_ae (integrable_mul_histogramFunction_sq J f g hg)
        ((histogramFunction_integrable J f).2.const_mul b)
      filter_upwards [henv] with y hy
      exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)
    _ = b * ∫ y, (histogramFunction f y) ^ 2 ∂unitVolume := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (histogramFunction_squared_integral_le J hJ f) hb

/-- The normalized pilot pairing has squared size at most sixty-four times test energy. -/
-- @node: pilotCoefficients_inner_sq_le
lemma pilotCoefficients_inner_sq_le {m : ℕ} (train : Fin m → Omega)
    (mx my J : ℕ) (hJ : 0 < J) (a : Bool) (x : ℝ) (f : Hj J) :
    (inner ℝ (pilotCoefficients train mx my J a x) f) ^ 2 ≤ 64 * ‖f‖ ^ 2 := by
  rw [pilotCoefficients, inner_coefficients_eq_integral J f _
    (densityPilot_integrable train mx my a x)]
  apply (density_histogram_integral_sq_le J f _
    (densityPilot_integrable train mx my a x) (densityPilot_normalized train mx my a x)
    (Filter.Eventually.of_forall (fun y => by
      linarith [(densityPilot_mem_Icc train mx my a x y).1]))).trans
  exact density_histogram_energy_le J hJ f _ (densityPilot_integrable train mx my a x)
    64 (by norm_num) (Filter.Eventually.of_forall (fun y =>
      (densityPilot_mem_Icc train mx my a x y).2))

/-- A density times a squared centered histogram test is integrable. -/
-- @node: integrable_density_centered_histogram_sq
lemma integrable_density_centered_histogram_sq (J : ℕ) (f : Hj J) (g : ℝ → ℝ)
    (hg : Integrable g unitVolume) (c : ℝ) :
    Integrable (fun y => g y * (histogramFunction f y - c) ^ 2) unitVolume := by
  apply hg.mul_bdd (c := ((∑ i : Fin J, |Real.sqrt J * f i|) + |c|) ^ 2) (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb : |histogramFunction f y - c| ≤ (∑ i : Fin J, |Real.sqrt J * f i|) + |c| :=
    (abs_sub _ _).trans (add_le_add (histogramFunction_abs_le J f y) (le_refl |c|))
  have h := mul_self_le_mul_self (abs_nonneg _) hb
  simpa only [← sq, sq_abs] using h

/-- Conditional outcome energy of a centered test is at most 136 times its norm squared. -/
-- @node: model_centered_histogram_energy_le
lemma model_centered_histogram_energy_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) (f : Hj J) :
    (∫ y, P.eta a x y * (histogramFunction f y -
      inner ℝ (pilotCoefficients train mx my J a x) f) ^ 2 ∂unitVolume) ≤ 136 * ‖f‖ ^ 2 := by
  let c := inner ℝ (pilotCoefficients train mx my J a x) f
  have hg := P.eta_integrable a x hx
  have hi := integrable_density_centered_histogram_sq J f _ hg c
  have hs := integrable_mul_histogramFunction_sq J f _ hg
  have henv : ∀ᵐ y ∂unitVolume, P.eta a x y ≤ 4 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact (hModel.density_envelope a x y hx hy).2
  have henergy := density_histogram_energy_le J hJ f _ hg 4 (by norm_num) henv
  have hgamma := pilotCoefficients_inner_sq_le train mx my J hJ a x f
  calc
    _ ≤ ∫ y, 2 * (P.eta a x y * (histogramFunction f y) ^ 2) +
        (2 * c ^ 2) * P.eta a x y ∂unitVolume := by
      apply integral_mono_ae hi ((hs.const_mul 2).add (hg.const_mul (2 * c ^ 2)))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have hn := P.eta_nonneg a x y hx hy
      have he : (histogramFunction f y - c) ^ 2 ≤
          2 * (histogramFunction f y) ^ 2 + 2 * c ^ 2 := by
        nlinarith [sq_nonneg (histogramFunction f y + c)]
      change P.eta a x y * (histogramFunction f y - c) ^ 2 ≤
        2 * (P.eta a x y * (histogramFunction f y) ^ 2) + (2 * c ^ 2) * P.eta a x y
      nlinarith [mul_le_mul_of_nonneg_left he hn]
    _ = 2 * (∫ y, P.eta a x y * (histogramFunction f y) ^ 2 ∂unitVolume) +
        2 * c ^ 2 := by
      integral_linearity
      rw [P.eta_normalized a x hx, mul_one]
    _ ≤ _ := by dsimp [c]; linarith

/-- Outcome integration removes the treatment indicator and exposes the inverse weight. -/
-- @node: armOutcomeMean_Vres_sq
lemma armOutcomeMean_Vres_sq {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my J : ℕ) (a : Bool) (x : ℝ) (f : Hj J) :
    armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x =
      (pi P a x / (pilotPi train mx a x) ^ 2) *
        ∫ y, P.eta a x y * (histogramFunction f y -
          inner ℝ (pilotCoefficients train mx my J a x) f) ^ 2 ∂unitVolume := by
  unfold armOutcomeMean
  simp only [Fintype.sum_bool]
  cases a <;> simp only [Vres, X, A, Y, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, zero_div, zero_smul, inner_zero_left,
    zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, smul_eq_mul,
    integral_zero, add_zero, zero_add, one_div, real_inner_smul_left, inner_sub_left,
    inner_phiCoefficients]
  all_goals
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [div_eq_mul_inv, inv_pow, mul_pow]
    ring

/-- Model overlap and pilot clipping bound the squared inverse-propensity multiplier by twelve. -/
-- @node: inverse_propensity_second_moment_multiplier
lemma inverse_propensity_second_moment_multiplier {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    pi P a x / (pilotPi train mx a x) ^ 2 ∈ Set.Icc 0 12 := by
  have hp := pilotPi_mem_Icc train mx a x
  have hpi := model_pi_mem_Icc P hModel a x hx
  have hpos : 0 < pilotPi train mx a x := by linarith [hp.1]
  constructor
  · exact div_nonneg (by linarith [hpi.1]) (sq_nonneg _)
  · apply (div_le_iff₀ (sq_pos_of_pos hpos)).2
    have hs : (1 / 4 : ℝ) ^ 2 ≤ (pilotPi train mx a x) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hpos.le).2 hp.1
    linarith [hpi.2]

/-- The observable outcome residual has a second moment uniform in the histogram rank. -/
-- @node: armOutcomeMean_Vres_sq_le
lemma armOutcomeMean_Vres_sq_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) (f : Hj J) :
    armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x ≤
      4096 * ‖f‖ ^ 2 := by
  rw [armOutcomeMean_Vres_sq]
  have hratio := inverse_propensity_second_moment_multiplier P hModel train mx a x hx
  have henergy := model_centered_histogram_energy_le P hModel train mx my J hJ a x hx f
  calc
    _ ≤ (pi P a x / (pilotPi train mx a x) ^ 2) * (136 * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy hratio.1
    _ ≤ 12 * (136 * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_right hratio.2 (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg ‖f‖]

/-- Bounded normalized pilots give the exact residual means and J-independent bounds,
including the second moment against every (possibly covariate-dependent) histogram test vector. -/
-- @node: lem:conditional-residual-moments
lemma conditional_residual_moments (P : ObsLaw) (hModel : Model P) (m mx my J : ℕ)
    (hmx : Dyadic mx) (hmy : Dyadic my) (hJ : Dyadic J)
    (train : Fin m → Omega) (ν : Measure (SampleSpace (13 * m)))
    (hSampling : SamplingLaw P (13 * m) ν) :
    (∀ a o, |Rres train mx a o| ≤ 3) ∧
    (∀ a x, x ∈ Set.Icc 0 1 → |uerr P train mx a x| ≤ 2) ∧
    (∀ a x, x ∈ Set.Icc 0 1 → l2Norm (verr P train mx my a x) ≤ 30) ∧
    (∀ a x, x ∈ Set.Icc 0 1 →
      armOutcomeMean P (Rres train mx a) x = uerr P train mx a x) ∧
    (∀ a x, x ∈ Set.Icc 0 1 →
      armOutcomeMean P (Vres train mx my J a) x =
        coefficients J (verr P train mx my a x)) ∧
    (∀ a x, x ∈ Set.Icc 0 1 → ∀ f : Hj J,
      armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x ≤
        4096 * ‖f‖ ^ 2) := by
  refine ⟨Rres_abs_le train mx, ?_, ?_, armOutcomeMean_Rres P train mx, ?_, ?_⟩
  · exact fun a x hx => uerr_abs_le P hModel train mx a x hx
  · exact fun a x hx => verr_l2Norm_le P hModel train mx my a x hx
  · exact fun a x hx => armOutcomeMean_Vres P train mx my J a x hx
  · obtain ⟨j, hj⟩ := hJ
    have hpos : 0 < J := by rw [hj]; positivity
    exact fun a x hx f => armOutcomeMean_Vres_sq_le P hModel train mx my J hpos a x hx f

end CausalSmith.Stat.DensityEffectRoughNull
