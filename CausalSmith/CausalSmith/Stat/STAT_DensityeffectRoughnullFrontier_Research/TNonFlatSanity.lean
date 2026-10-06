module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Example
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Model membership, exact identified contrasts and the zero first derivative of the non-flat
sinusoidal family.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Normalized conditional densities and the complementary treatment probabilities
recover the uniform covariate marginal. -/
-- @node: obsLaw_uniform_design
lemma obsLaw_uniform_design (P : ObsLaw) : UniformDesign P := by
  have : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hX : Measurable X := by unfold X; fun_prop
  have hA : Measurable A := by unfold A; fun_prop
  apply Measure.ext
  intro B hB
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply hX hB]
  have hsplit : X ⁻¹' B = {o | X o ∈ B ∧ A o = false} ∪
      {o | X o ∈ B ∧ A o = true} := by
    ext o
    cases ha : A o <;> simp [ha]
  rw [hsplit, measureReal_union]
  · have hr (a : Bool) := P.rectangles B Set.univ hB MeasurableSet.univ a
    simp only [Set.mem_univ, and_true, Measure.restrict_univ] at hr
    rw [hr false, hr true]
    have heq (a : Bool) :
        (∫ x in B, armProbability P.e a x * (∫ y, P.eta a x y ∂unitVolume) ∂unitVolume) =
        ∫ x in B, armProbability P.e a x ∂unitVolume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)] with x hx
      rw [P.eta_normalized a x hx, mul_one]
    rw [heq false, heq true]
    have he : IntegrableOn P.e B unitVolume := by
      apply Integrable.integrableOn
      apply Integrable.mono' (integrable_const (1 : ℝ)) P.e_measurable.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      simpa only [Real.norm_eq_abs, abs_le] using
        (show -1 ≤ P.e x ∧ P.e x ≤ 1 from ⟨by linarith [(P.e_range x hx).1], (P.e_range x hx).2⟩)
    simp only [armProbability, Bool.false_eq_true, if_false, if_true]
    rw [integral_sub (integrable_const (1 : ℝ)) he]
    simp
  · exact Set.disjoint_left.mpr (by intro o ho hp; simp_all)
  · exact (hB.preimage hX).inter (measurableSet_singleton true |>.preimage hA)

/-- Integrating over the covariate removes the conditional sine heterogeneity. -/
-- @node: example_marginal_density
lemma example_marginal_density (theta : ℝ) (a : Bool) (y : ℝ) :
    marginalDensity (exampleLaw theta) a y = baselineDensity y +
      (if a then exampleParameter theta * Real.sin (2 * Real.pi * y) else 0) := by
  have : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hs : Integrable (fun x : ℝ => Real.sin (2 * Real.pi * x)) unitVolume := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  change (∫ x, exampleDensity theta a x y ∂unitVolume) = _
  have hf : (fun x => exampleDensity theta a x y) = fun x =>
      (baselineDensity y + (if a then exampleParameter theta * Real.sin (2 * Real.pi * y) else 0)) +
      ((if a then (1 : ℝ) else -1) * Real.sin (2 * Real.pi * y) / 10) *
        Real.sin (2 * Real.pi * x) := by
    funext x
    unfold exampleDensity
    ring
  rw [hf, integral_add (integrable_const _) (hs.const_mul _), integral_const_mul,
    example_sin_integral]
  simp

/-- The totalized contrast is the sine perturbation, including outside the legal range. -/
-- @node: example_delta
lemma example_delta (theta y : ℝ) :
    delta (exampleLaw theta) y = exampleParameter theta * Real.sin (2 * Real.pi * y) := by
  rw [delta, example_marginal_density, example_marginal_density]
  simp

/-- The exact sine-square integral gives the totalized example energy. -/
-- @node: example_energy
lemma example_energy (theta : ℝ) :
    Psi (exampleLaw theta) = (exampleParameter theta) ^ 2 / 2 := by
  have hs : (∫ y, Real.sin (2 * Real.pi * y) ^ 2 ∂unitVolume) = 1 / 2 := by
    rw [unitVolume, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_comp_mul_left (fun y => Real.sin y ^ 2) (by positivity)]
    rw [integral_sin_sq]
    simp only [zero_mul, mul_one, Real.sin_zero, Real.sin_two_pi, Real.cos_zero,
      mul_zero, sub_zero, sub_self]
    simp only [smul_eq_mul]
    field_simp
    ring
  simp only [Psi, l2Squared, example_delta, mul_pow]
  rw [integral_const_mul, hs]
  ring

/-- On the unit interval, a Lipschitz modulus is bounded by the required Hölder modulus. -/
-- @node: example_holder_modulus
lemma example_holder_modulus {x xp : ℝ} (hx : x ∈ Set.Icc 0 1)
    (hp : xp ∈ Set.Icc 0 1) : |x - xp| ≤ |x - xp| ^ (1 / 10 : ℝ) := by
  have hle : |x - xp| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hp.1, hp.2]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg (x - xp)) hle (by norm_num : (0 : ℝ) ≤ 1 / 10)
    (by norm_num : (1 / 10 : ℝ) ≤ 1)

/-- The sine wave has a uniform Lipschitz constant eight. -/
-- @node: example_sine_lipschitz
lemma example_sine_lipschitz (x xp : ℝ) :
    |Real.sin (2 * Real.pi * x) - Real.sin (2 * Real.pi * xp)| ≤ 8 * |x - xp| := by
  calc
    _ ≤ |2 * Real.pi * x - 2 * Real.pi * xp| := Real.abs_sin_sub_sin_le _ _
    _ = (2 * Real.pi) * |x - xp| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (abs_nonneg _)

/-- The cosine wave has the same uniform Lipschitz constant eight. -/
-- @node: example_cosine_lipschitz
lemma example_cosine_lipschitz (x xp : ℝ) :
    |Real.cos (2 * Real.pi * x) - Real.cos (2 * Real.pi * xp)| ≤ 8 * |x - xp| := by
  calc
    _ ≤ |2 * Real.pi * x - 2 * Real.pi * xp| := Real.abs_cos_sub_cos_le _ _
    _ = (2 * Real.pi) * |x - xp| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (abs_nonneg _)

/-- Clipping preserves the legal perturbation and provides its global size bound. -/
-- @node: example_parameter_bound
lemma example_parameter_bound (theta : ℝ) : |exampleParameter theta| ≤ 1 / 20 := by
  rw [abs_le, exampleParameter]
  constructor
  · simpa only [neg_div] using le_max_left (-1 / 20 : ℝ) (min (1 / 20) theta)
  · exact max_le (by norm_num) (min_le_left _ _)

/-- All six fixed model conditions hold for the totalized sinusoidal construction. -/
-- @node: example_model
lemma example_model (theta : ℝ) : Model (exampleLaw theta) := by
  have he : (exampleLaw theta).e = examplePropensity := rfl
  have heta : (exampleLaw theta).eta = exampleDensity theta := rfl
  have hparam := example_parameter_bound theta
  refine ⟨obsLaw_uniform_design _, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [he]
    have hlo := Real.neg_one_le_sin (2 * Real.pi * x)
    have hhi := Real.sin_le_one (2 * Real.pi * x)
    constructor <;> dsimp [examplePropensity] <;> linarith
  · intro x hx xp hp
    rw [he]
    have hf : examplePropensity x - examplePropensity xp =
        (Real.sin (2 * Real.pi * x) - Real.sin (2 * Real.pi * xp)) / 10 := by
      unfold examplePropensity; ring
    rw [hf, abs_div]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    have hs := example_sine_lipschitz x xp
    have hh := example_holder_modulus hx hp
    have hn := abs_nonneg (x - xp)
    nlinarith
  · intro a x y hx hy
    rw [heta]
    have hc := Real.abs_cos_le_one (2 * Real.pi * y)
    have hxy : |Real.sin (2 * Real.pi * x) * Real.sin (2 * Real.pi * y)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hty : |exampleParameter theta * Real.sin (2 * Real.pi * y)| ≤ 1 / 20 := by
      rw [abs_mul]
      exact (mul_le_mul hparam (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq
        (by ring)
    rw [abs_le] at hc hxy hty
    cases a <;> constructor <;> dsimp [exampleDensity, baselineDensity] <;> nlinarith
  · intro a y hy x hx xp hp
    rw [heta]
    have hs := example_sine_lipschitz x xp
    have hh := example_holder_modulus hx hp
    have hn := abs_nonneg (x - xp)
    have hf : exampleDensity theta a x y - exampleDensity theta a xp y =
        (if a then (1 : ℝ) else -1) *
        (Real.sin (2 * Real.pi * x) - Real.sin (2 * Real.pi * xp)) *
        Real.sin (2 * Real.pi * y) / 10 := by
      unfold exampleDensity; ring
    rw [hf, abs_div, abs_mul, abs_mul]
    have ha : |(if a then (1 : ℝ) else -1)| = 1 := by cases a <;> norm_num
    rw [ha, one_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    have hb : |Real.sin (2 * Real.pi * x) - Real.sin (2 * Real.pi * xp)| *
        |Real.sin (2 * Real.pi * y)| ≤ 8 * |x - xp| :=
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using hs)
    nlinarith
  · intro a x hx y hy yp hp
    rw [heta]
    let c : ℝ := (if a then (1 : ℝ) else -1) * Real.sin (2 * Real.pi * x) / 10 +
      (if a then exampleParameter theta else 0)
    have hc : |c| ≤ 3 / 20 := by
      cases a <;> simp only [c, Bool.false_eq_true, if_false, if_true, one_mul, neg_mul,
        neg_div, add_zero]
      · simpa only [abs_neg, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)] using
          (show |Real.sin (2 * Real.pi * x)| / 10 ≤ 3 / 20 by
            linarith [Real.abs_sin_le_one (2 * Real.pi * x)])
      · calc
          _ ≤ |Real.sin (2 * Real.pi * x) / 10| + |exampleParameter theta| := abs_add_le _ _
          _ ≤ 3 / 20 := by
            rw [abs_div]
            norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
            linarith [Real.abs_sin_le_one (2 * Real.pi * x)]
    have hf : exampleDensity theta a x y - exampleDensity theta a x yp =
        (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * yp)) / 10 +
        c * (Real.sin (2 * Real.pi * y) - Real.sin (2 * Real.pi * yp)) := by
      cases a <;> dsimp [exampleDensity, baselineDensity, c] <;> ring
    rw [hf]
    calc
      _ ≤ |(Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * yp)) / 10| +
          |c * (Real.sin (2 * Real.pi * y) - Real.sin (2 * Real.pi * yp))| := abs_add_le _ _
      _ ≤ (8 * |y - yp|) / 10 + (3 / 20) * (8 * |y - yp|) := by
        rw [abs_div, abs_mul]
        norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
        gcongr
        · exact example_cosine_lipschitz _ _
        · exact example_sine_lipschitz _ _
      _ ≤ _ := by nlinarith [abs_nonneg (y - yp)]

/-- The perturbation is unchanged throughout the specified parameter interval. -/
-- @node: example_parameter_eq
lemma example_parameter_eq {theta : ℝ} (ht : theta ∈ Set.Icc (-1 / 20 : ℝ) (1 / 20)) :
    exampleParameter theta = theta := by
  rw [exampleParameter, min_eq_right ht.2, max_eq_right ht.1]

-- @node: prop:non-flat-sanity
/-- The sinusoidal family stays in the unchanged model, has the stated non-flat marginal,
contrast theta sin(2 pi y) and effect theta²/2, with zero derivative at equality. -/
theorem nonflat_example :
    (∀ theta ∈ Set.Icc (-1 / 20 : ℝ) (1 / 20), Model (exampleLaw theta) ∧
      (∀ y ∈ Set.Icc 0 1, marginalDensity (exampleLaw theta) false y = baselineDensity y) ∧
      (∀ y ∈ Set.Icc 0 1, delta (exampleLaw theta) y = theta * Real.sin (2 * Real.pi * y)) ∧
      Psi (exampleLaw theta) = theta ^ 2 / 2) ∧
    NullModel (exampleLaw 0) ∧ HasDerivAt (fun theta => Psi (exampleLaw theta)) 0 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (-1 / 20 : ℝ) (1 / 20) := by norm_num
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro theta ht
    refine ⟨example_model theta, ?_, ?_, ?_⟩
    · intro y hy
      simpa using example_marginal_density theta false y
    · intro y hy
      rw [example_delta, example_parameter_eq ht]
    · rw [example_energy, example_parameter_eq ht]
  · exact ⟨example_model 0, by
      intro y hy
      rw [example_delta, example_parameter_eq hzero, zero_mul]⟩
  · have hd : HasDerivAt (fun theta : ℝ => theta ^ 2 / 2) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 / 20 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 20)] with theta ht
    rw [example_energy, example_parameter_eq ⟨ht.1.le, ht.2.le⟩]

end CausalSmith.Stat.DensityEffectRoughNull
