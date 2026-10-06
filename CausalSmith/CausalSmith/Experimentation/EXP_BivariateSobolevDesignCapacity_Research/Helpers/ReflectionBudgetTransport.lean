module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionFourier

/-! # Cube transport and the zero Fourier coefficient

Folding sends normalized Haar measure exactly to cube probability. This gives
representative-independent reflection and the centered zero-frequency identity.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Folding the independently reflected cube sample recovers its original point almost surely.](goal) -/
-- @node: fold_cubeReflection_ae
lemma fold_cubeReflection_ae (d : ℕ) :
    (fun z : Cube d × (Fin d → Bool) =>
      fold (fun j => reflectedCoordinate (z.1 j) (z.2 j))) =ᵐ[
        (cubeMeasure d).prod (PMF.uniformOfFintype (Fin d → Bool)).toMeasure] Prod.fst := by
  haveI : IsProbabilityMeasure (PMF.uniformOfFintype (Fin d → Bool)).toMeasure := inferInstance
  have hc := (measurePreserving_fst (μ := cubeMeasure d)
    (ν := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)).quasiMeasurePreserving.ae
      (cube_mem_ae d)
  filter_upwards [hc] with z hz
  funext j
  exact fold_lift_apply (n := 1) (fun _ => z.1) (fun _ => z.2) 0 j (hz j)

/-- [ Normalized Haar measure folds to unit-cube Lebesgue probability in every dimension.](goal) -/
-- @node: fold_measurePreserving
lemma fold_measurePreserving (d : ℕ) :
    MeasurePreserving (fold : Torus d → Cube d) (torusMeasure d) (cubeMeasure d) := by
  refine ⟨fold_measurable d, ?_⟩
  rw [← cubeReflection_map d, Measure.map_map (fold_measurable d)]
  · trans Measure.map Prod.fst ((cubeMeasure d).prod
        (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)
    · exact Measure.map_congr (fold_cubeReflection_ae d)
    · haveI : IsProbabilityMeasure (PMF.uniformOfFintype (Fin d → Bool)).toMeasure := inferInstance
      exact (measurePreserving_fst (μ := cubeMeasure d)
      (ν := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)).map_eq
  · unfold reflectedCoordinate
    apply measurable_pi_lambda
    intro j
    apply AddCircle.measurable_mk'.comp
    apply Measurable.ite
    · have hb : Measurable (fun z : Cube d × (Fin d → Bool) => z.2 j) :=
        (measurable_pi_apply j).comp measurable_snd
      exact hb (measurableSet_singleton true)
    · fun_prop
    · fun_prop

/-- Reflection preserves almost-everywhere equality of cube representatives. Under [the stated conditions](hyp:h), [the asserted mathematical result follows](goal). -/
-- @node: reflExt_congr_ae
lemma reflExt_congr_ae {d : ℕ} {m g : Cube d → ℝ}
    (h : m =ᵐ[cubeMeasure d] g) :
    reflExt m =ᵐ[torusMeasure d] reflExt g := by
  filter_upwards [(fold_measurePreserving d).quasiMeasurePreserving.ae h] with y hy
  simp only [reflExt, hy]

/-- The zero Fourier coefficient of a reflected centered outcome vanishes. [The asserted mathematical result follows](goal). -/
-- @node: Fhat_zero_of_centered
lemma Fhat_zero_of_centered {d : ℕ} (m : CenteredL2Fn d) : Fhat m.val 0 = 0 := by
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (cubeMeasure d) := by
    unfold cubeMeasure
    infer_instance
  have hi : Integrable (fun x => (m.val x : ℂ)) (cubeMeasure d) :=
    (m.property.2.1.integrable (by norm_num)).ofReal
  have ht := integral_map (fold_measurable d).aemeasurable (by
    rw [(fold_measurePreserving d).map_eq]
    exact hi.aestronglyMeasurable)
  rw [(fold_measurePreserving d).map_eq] at ht
  simp only [Fhat, ek, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul, reflExt]
  rw [← ht, integral_complex_ofReal, m.property.2.2]
  rfl

/-- Every cube L² representative reflects to a torus L² representative,
with no centering requirement. Under [the stated conditions](hyp:hg), [the asserted mathematical result follows](goal). -/
-- @node: reflExt_memLp_of_cube
lemma reflExt_memLp_of_cube {d : ℕ} {g : Cube d → ℝ}
    (hg : MemLp g 2 (cubeMeasure d)) : MemLp (reflExt g) 2 (torusMeasure d) := by
  exact hg.ofReal.comp_measurePreserving (fold_measurePreserving d)

/-- [ Parseval and folding identify the full Fourier mass with the cube second moment.](goal) Under [the stated conditions](hyp:hd,hg,hLp). -/
-- @node: cube_fourier_mass
lemma cube_fourier_mass {d : ℕ} (hd : 0 < d)
    (g : Cube d → ℝ) (hg : Measurable g) (hLp : MemLp g 2 (cubeMeasure d)) :
    (∫⁻ x, ENNReal.ofReal |g x| ^ 2 ∂cubeMeasure d) =
      ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat g k‖ ^ 2 := by
  have hp := commonShift_parseval_lintegral (n := 1) hd (reflExt g)
    (reflExt_memLp_of_cube hLp) (fun _ => 1) (fun _ => 0)
  have hz (k : Fin d → ℤ) : (UnitAddTorus.mFourier k) 0 = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
      fourier_eval_zero, Finset.prod_const_one]
  simp only [Fin.sum_univ_one, one_mul, zero_sub, hz,
    norm_one, ENNReal.ofReal_one, one_pow, mul_one, mFourierCoeff_reflExt] at hp
  have hn : MeasurePreserving (fun y : Torus d => -y) (torusMeasure d) (torusMeasure d) :=
    measurePreserving_pi (fun _ : Fin d => AddCircle.haarAddCircle)
      (fun _ : Fin d => AddCircle.haarAddCircle)
      (fun _ => Measure.measurePreserving_neg AddCircle.haarAddCircle)
  have hmeas : Measurable (fun y : Torus d => ENNReal.ofReal ‖reflExt g y‖ ^ 2) := by
    apply Measurable.pow_const
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.norm
    exact Complex.measurable_ofReal.comp (hg.comp (fold_measurable d))
  rw [hn.lintegral_comp hmeas] at hp
  rw [reflExt_sq_lintegral_eq d g hg] at hp
  exact hp

/-- [ Centered outcomes inherit the full cube Parseval identity.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: cube_second_moment_fourier_mass
lemma cube_second_moment_fourier_mass {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    (∫⁻ x, ENNReal.ofReal |m.val x| ^ 2 ∂cubeMeasure d) =
      ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 :=
  cube_fourier_mass hd m.val m.property.1 m.property.2.1

/-- [ The zero-smoothness endpoint is exactly cube L² energy under normalized Haar measure.](goal) Under [the stated conditions](hyp:hp,hg,hLp). -/
-- @node: componentFourierBudget_zero
lemma componentFourierBudget_zero {p : ℕ} (hp : 0 < p)
    (g : Cube p → ℝ) (hg : Measurable g) (hLp : MemLp g 2 (cubeMeasure p)) :
    componentFourierBudget p 0 g =
      ∫⁻ x, ENNReal.ofReal |g x| ^ 2 ∂cubeMeasure p := by
  rw [cube_fourier_mass hp g hg hLp]
  simp only [componentFourierBudget, Real.rpow_zero, one_mul,
    ENNReal.ofReal_pow (norm_nonneg _)]

/-- [ Nonnegative smoothness weights are at least one, so the pooled spectral budget
controls the full Fourier mass when the excluded coefficients vanish.](goal) Under [the stated conditions](hyp:hs,hzero,hsupport). -/
-- @node: fourier_mass_le_reflectedBudget
lemma fourier_mass_le_reflectedBudget {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (m : Cube d → ℝ) (hzero : Fhat m 0 = 0)
    (hsupport : ∀ k, 2 < (frequencySupport k).card → Fhat m k = 0) :
    (∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m k‖ ^ 2) ≤ reflectedBudget s m := by
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2
  · simp only [if_pos hk]
    rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0 ≤ frequencyComplexity k := by
      apply div_nonneg
      · exact Finset.sum_nonneg (fun j _ => sq_nonneg (k j : ℝ))
      · positivity
    have hw : 1 ≤ (1 + Real.pi ^ 2 * frequencyComplexity k) ^ s :=
      Real.one_le_rpow (by nlinarith [sq_nonneg Real.pi]) hs
    nlinarith [sq_nonneg ‖Fhat m k‖]
  · simp only [if_neg hk]
    have hz : Fhat m k = 0 := by
      by_cases hc : (frequencySupport k).card = 0
      · have hk0 : k = 0 := by
          funext j
          have he := Finset.card_eq_zero.mp hc
          have hj : j ∉ frequencySupport k := by rw [he]; simp
          simpa [frequencySupport] using hj
        simpa [hk0] using hzero
      · exact hsupport k (by omega)
    simp [hz]

/-- [ Once the pooled spectral estimate and its support statement are proved, Parseval
supplies the original-cube second-moment bound without a dimension factor.](goal) Under [the stated conditions](hyp:hd,hs,hsupport,hbudget). -/
-- @node: cube_second_moment_le_of_reflectedBudget
lemma cube_second_moment_le_of_reflectedBudget {d : ℕ} {s : ℝ}
    (hd : 0 < d) (hs : 0 ≤ s) (m : CenteredL2Fn d)
    (hsupport : ∀ k, 2 < (frequencySupport k).card → Fhat m.val k = 0)
    (hbudget : reflectedBudget s m.val ≤ 1) :
    (∫ x, |m.val x| ^ 2 ∂cubeMeasure d) ≤ 1 := by
  have hmass := (fourier_mass_le_reflectedBudget hs m.val
    (Fhat_zero_of_centered m) hsupport).trans hbudget
  rw [← cube_second_moment_fourier_mass hd m] at hmass
  have hi := m.property.2.1.integrable_norm_pow (by norm_num)
  simp only [Real.norm_eq_abs] at hi
  have he : ENNReal.ofReal (∫ x, |m.val x| ^ 2 ∂cubeMeasure d) =
      ∫⁻ x, ENNReal.ofReal |m.val x| ^ 2 ∂cubeMeasure d := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => sq_nonneg |m.val x|)]
    simp_rw [ENNReal.ofReal_pow (abs_nonneg _) 2]
  rw [← he, ← ENNReal.ofReal_one] at hmass
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hmass

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
