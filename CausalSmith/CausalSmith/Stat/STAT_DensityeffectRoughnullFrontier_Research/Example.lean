module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Concrete nuisance-to-law constructor and the non-flat sinusoidal family.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Conditions needed to construct an observed law from nuisance versions. -/
def NuisanceValid (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ) : Prop :=
  Measurable e ∧ (∀ a, Measurable (fun z : ℝ × ℝ => eta a z.1 z.2)) ∧
  (∀ x ∈ Set.Icc 0 1, e x ∈ Set.Icc 0 1) ∧
  (∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → 0 ≤ eta a x y) ∧
  (∀ a x, x ∈ Set.Icc 0 1 → Integrable (eta a x) unitVolume) ∧
  (∀ a x, x ∈ Set.Icc 0 1 → ∫ y, eta a x y ∂unitVolume = 1)

/-- Uniform design times counting measure on treatment times uniform outcome. -/
def densityBase : Measure Omega := unitVolume.prod (Measure.count.prod unitVolume)
/-- Actual measure obtained by multiplying the conditional densities and assignment probability. -/
def nuisanceMeasure (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ) : Measure Omega :=
  densityBase.withDensity (fun o => ENNReal.ofReal (armProbability e (A o) (X o) * 
    eta (A o) (X o) (Y o)))

/-- The nuisance density is measurable on the ambient observation product. -/
-- @node: nuisance_density_measurable
@[fun_prop] lemma nuisance_density_measurable (e : ℝ → ℝ)
    (eta : Bool → ℝ → ℝ → ℝ) (hv : NuisanceValid e eta) :
    Measurable (fun o : Omega => ENNReal.ofReal
      (armProbability e (A o) (X o) * eta (A o) (X o) (Y o))) := by
  classical
  have hm : Measurable (fun o : Omega => (X o, Y o)) := by
    unfold X Y
    fun_prop
  have ha : Measurable (A : Omega → Bool) := by unfold A; fun_prop
  have he : Measurable (fun o : Omega => e (X o)) := hv.1.comp measurable_fst
  have heta : Measurable (fun o : Omega => eta (A o) (X o) (Y o)) := by
    have hi : Measurable (fun o : Omega =>
        if A o = true then eta true (X o) (Y o) else eta false (X o) (Y o)) :=
      ((hv.2.1 true).comp hm).ite (ha (measurableSet_singleton true))
        ((hv.2.1 false).comp hm)
    convert hi using 1
    funext o
    rcases o with ⟨x, a, y⟩
    cases a <;> rfl
  have hp : Measurable (fun o : Omega => armProbability e (A o) (X o)) := by
    unfold armProbability
    apply Measurable.ite (ha (measurableSet_singleton true)) he
      ((measurable_const : Measurable (fun _ : Omega => (1 : ℝ))).sub he)
  exact (hp.mul heta).ennreal_ofReal

/-- Nuisance arm probabilities are nonnegative on the design support. -/
-- @node: nuisance_arm_nonneg
lemma nuisance_arm_nonneg (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ)
    (hv : NuisanceValid e eta) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0 ≤ armProbability e a x := by
  have h := hv.2.2.1 x hx
  cases a <;> simp only [armProbability, Bool.false_eq_true, if_false, if_true]
  · linarith [h.2]
  · exact h.1

/-- Each conditional density integrates to one also as a nonnegative integral. -/
-- @node: nuisance_lintegral_normalized
lemma nuisance_lintegral_normalized (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ)
    (hv : NuisanceValid e eta) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (∫⁻ y, ENNReal.ofReal (eta a x y) ∂unitVolume) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hv.2.2.2.2.1 a x hx)]
  · rw [hv.2.2.2.2.2 a x hx]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hv.2.2.2.1 a x y hx hy

/-- Integrating the two conditional outcome densities leaves the assignment probabilities. -/
-- @node: nuisanceMeasure_probability
lemma nuisanceMeasure_probability (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ)
    (hv : NuisanceValid e eta) : IsProbabilityMeasure (nuisanceMeasure e eta) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hd := nuisance_density_measurable e eta hv
  constructor
  rw [nuisanceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    densityBase, lintegral_prod _ hd.aemeasurable]
  have hf : ∀ x ∈ Set.Icc 0 1, ∀ a : Bool,
      (∫⁻ y, ENNReal.ofReal (armProbability e a x * eta a x y) ∂unitVolume) =
        ENNReal.ofReal (armProbability e a x) := by
    intro x hx a
    simp_rw [ENNReal.ofReal_mul (nuisance_arm_nonneg e eta hv a x hx)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      nuisance_lintegral_normalized e eta hv a x hx, mul_one]
  calc
    _ = ∫⁻ x, (1 : ℝ≥0∞) ∂unitVolume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hdx : Measurable (fun ay : Bool × ℝ => ENNReal.ofReal
          (armProbability e (A (x, ay)) (X (x, ay)) *
            eta (A (x, ay)) (X (x, ay)) (Y (x, ay)))) :=
        hd.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_prod _ hdx.aemeasurable]
      dsimp only [X, A, Y]
      simp_rw [hf x hx]
      rw [lintegral_count, tsum_fintype]
      simp only [Fintype.sum_bool, armProbability, Bool.false_eq_true, if_false, if_true]
      rw [← ENNReal.ofReal_add (hv.2.2.1 x hx).1 (sub_nonneg.mpr (hv.2.2.1 x hx).2)]
      simp
    _ = 1 := by simp

/-- The constructed density preserves the design and outcome support of its base measure. -/
-- @node: nuisanceMeasure_support
lemma nuisanceMeasure_support (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ) :
    ∀ᵐ o ∂nuisanceMeasure e eta, X o ∈ Set.Icc 0 1 ∧ Y o ∈ Set.Icc 0 1 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply (withDensity_absolutelyContinuous densityBase _).ae_le
  have hx : ∀ᵐ x ∂unitVolume, x ∈ Set.Icc 0 1 := ae_restrict_mem measurableSet_Icc
  have hs : MeasurableSet {o : Omega | X o ∈ Set.Icc 0 1 ∧ Y o ∈ Set.Icc 0 1} := by
    exact (measurable_fst measurableSet_Icc).inter
      (measurable_snd.snd measurableSet_Icc)
  apply Measure.ae_prod_iff_ae_ae hs |>.mpr
  filter_upwards [hx] with x hx
  apply Measure.ae_prod_iff_ae_ae
    ((measurable_const measurableSet_Icc).inter (measurable_snd measurableSet_Icc)) |>.mpr
  exact Filter.Eventually.of_forall (fun a =>
    (ae_restrict_mem measurableSet_Icc).mono (fun y hy => ⟨hx, hy⟩))

/-- Tonelli on a covariate/arm/outcome rectangle gives the nuisance representation. -/
-- @node: nuisanceMeasure_rectangle
lemma nuisanceMeasure_rectangle (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ)
    (hv : NuisanceValid e eta) (B D : Set ℝ)
    (hB : MeasurableSet B) (hD : MeasurableSet D) (a : Bool) :
    (nuisanceMeasure e eta).real {o | X o ∈ B ∧ A o = a ∧ Y o ∈ D} =
      ∫ x in B, armProbability e a x * (∫ y in D, eta a x y ∂unitVolume) ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hd := nuisance_density_measurable e eta hv
  have hx : ∀ᵐ x ∂unitVolume.restrict B, x ∈ Set.Icc 0 1 :=
    (ae_restrict_mem measurableSet_Icc).filter_mono (ae_mono Measure.restrict_le_self)
  have hy : ∀ᵐ y ∂unitVolume.restrict D, y ∈ Set.Icc 0 1 :=
    (ae_restrict_mem measurableSet_Icc).filter_mono (ae_mono Measure.restrict_le_self)
  have hpi : Measurable (armProbability e a) := by
    cases a
    · change Measurable (fun x => 1 - e x)
      exact measurable_const.sub hv.1
    · exact hv.1
  have hm : Measurable (fun x => armProbability e a x *
      (∫ y in D, eta a x y ∂unitVolume)) := by
    exact hpi.mul (hv.2.1 a).stronglyMeasurable.integral_prod_right.measurable
  have hn : 0 ≤ᵐ[unitVolume.restrict B] (fun x => armProbability e a x *
      (∫ y in D, eta a x y ∂unitVolume)) := by
    filter_upwards [hx] with x hx
    apply mul_nonneg (nuisance_arm_nonneg e eta hv a x hx)
    exact integral_nonneg_of_ae (hy.mono (fun y hy => hv.2.2.2.1 a x y hx hy))
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  change ((densityBase.withDensity (fun o => ENNReal.ofReal
      (armProbability e (A o) (X o) * eta (A o) (X o) (Y o))))
      (B ×ˢ ({a} ×ˢ D))).toReal = _
  rw [withDensity_apply _ (hB.prod ((measurableSet_singleton a).prod hD)),
    densityBase, ← Measure.prod_restrict, ← Measure.prod_restrict,
    lintegral_prod _ hd.aemeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hx] with x hx
  have hdx : Measurable (fun ay : Bool × ℝ => ENNReal.ofReal
      (armProbability e (A (x, ay)) (X (x, ay)) *
        eta (A (x, ay)) (X (x, ay)) (Y (x, ay)))) :=
    hd.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hdx.aemeasurable]
  simp only [lintegral_singleton, Measure.count_singleton, mul_one, X, A, Y]
  simp_rw [ENNReal.ofReal_mul (nuisance_arm_nonneg e eta hv a x hx)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (hv.2.2.2.2.1 a x hx).integrableOn]
  exact hy.mono (fun y hy => hv.2.2.2.1 a x y hx hy)

/-- Normalization and rectangle representation of the explicit constructed measure. -/
-- @node: nuisanceMeasure_spec
lemma nuisanceMeasure_spec (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ)
    (hv : NuisanceValid e eta) :
    IsProbabilityMeasure (nuisanceMeasure e eta) ∧
    (∀ᵐ o ∂nuisanceMeasure e eta, X o ∈ Set.Icc 0 1 ∧ Y o ∈ Set.Icc 0 1) ∧
    (∀ (B D : Set ℝ), MeasurableSet B → MeasurableSet D → ∀ a,
      (nuisanceMeasure e eta).real {o | X o ∈ B ∧ A o = a ∧ Y o ∈ D} =
        ∫ x in B, armProbability e a x * (∫ y in D, eta a x y ∂unitVolume) ∂unitVolume) := by
  exact ⟨nuisanceMeasure_probability e eta hv, nuisanceMeasure_support e eta,
    nuisanceMeasure_rectangle e eta hv⟩

/-- Observed law constructed from normalized genuine nuisance functions. -/
def ObsLaw.ofNuisance (e : ℝ → ℝ) (eta : Bool → ℝ → ℝ → ℝ)
    (hv : NuisanceValid e eta) : ObsLaw where
  law := nuisanceMeasure e eta
  prob := (nuisanceMeasure_spec e eta hv).1
  e := e
  eta := eta
  e_measurable := hv.1
  eta_measurable := hv.2.1
  e_range := hv.2.2.1
  eta_nonneg := hv.2.2.2.1
  eta_integrable := hv.2.2.2.2.1
  eta_normalized := hv.2.2.2.2.2
  support := (nuisanceMeasure_spec e eta hv).2.1
  rectangles := (nuisanceMeasure_spec e eta hv).2.2

/-- Nonconstant example propensity. -/
def examplePropensity (x : ℝ) : ℝ := 1 / 2 + Real.sin (2 * Real.pi * x) / 10
    -- @realizes e(nonconstant sinusoidal example propensity)
/-- Non-flat common density at equality. -/
def baselineDensity (y : ℝ) : ℝ := 1 + Real.cos (2 * Real.pi * y) / 10
/-- Totalized perturbation, equal to theta throughout the stipulated parameter interval. -/
def exampleParameter (theta : ℝ) : ℝ := max (-1 / 20) (min (1 / 20) theta)
    -- @realizes tpert(perturbation in [-1/20,1/20])
/-- The two displayed conditional densities, unchanged on the legal parameter interval. -/
def exampleDensity (theta : ℝ) (a : Bool) (x y : ℝ) : ℝ :=
  baselineDensity y + (if a then (1 : ℝ) else - 1) * 
    Real.sin (2 * Real.pi * x) * Real.sin (2 * Real.pi * y) / 10 + 
    (if a then exampleParameter theta * Real.sin (2 * Real.pi * y) else 0)
/-- The sine perturbation has zero mean under the uniform design. -/
-- @node: example_sin_integral
lemma example_sin_integral :
    ∫ y, Real.sin (2 * Real.pi * y) ∂unitVolume = 0 := by
  rw [unitVolume, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left Real.sin (by positivity)]
  simp [integral_sin, Real.cos_two_pi]

/-- The cosine term leaves the baseline density normalized. -/
-- @node: example_cos_integral
lemma example_cos_integral :
    ∫ y, Real.cos (2 * Real.pi * y) ∂unitVolume = 0 := by
  rw [unitVolume, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left Real.cos (by positivity)]
  simp [integral_cos, Real.sin_two_pi]

/-- The displayed nuisances define probability laws for every totalized parameter. -/
-- @node: example_nuisance_valid
lemma example_nuisance_valid (theta : ℝ) :
    NuisanceValid examplePropensity (exampleDensity theta) := by
  have hsin : Integrable (fun y : ℝ => Real.sin (2 * Real.pi * y)) unitVolume := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hcos : Integrable (fun y : ℝ => Real.cos (2 * Real.pi * y)) unitVolume := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) unitVolume := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hparam : |exampleParameter theta| ≤ 1 / 20 := by
    rw [abs_le, exampleParameter]
    constructor
    · simpa only [neg_div] using le_max_left (-1 / 20 : ℝ) (min (1 / 20) theta)
    · exact max_le (by norm_num : (-1 / 20 : ℝ) ≤ 1 / 20)
        (min_le_left (1 / 20 : ℝ) theta)
  have hdint : ∀ a x, Integrable (exampleDensity theta a x) unitVolume := by
    intro a x
    apply ContinuousOn.integrableOn_Icc
    unfold exampleDensity baselineDensity
    cases a <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold examplePropensity
    fun_prop
  · intro a
    unfold exampleDensity baselineDensity
    cases a <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  · intro x hx
    have hs := Real.neg_one_le_sin (2 * Real.pi * x)
    have ht := Real.sin_le_one (2 * Real.pi * x)
    constructor <;> dsimp [examplePropensity] <;> linarith
  · intro a x y hx hy
    have hc := Real.neg_one_le_cos (2 * Real.pi * y)
    have hxy : |Real.sin (2 * Real.pi * x) * Real.sin (2 * Real.pi * y)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hty : |exampleParameter theta * Real.sin (2 * Real.pi * y)| ≤ 1 / 20 := by
      rw [abs_mul]
      exact (mul_le_mul hparam (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq
        (by ring)
    rw [abs_le] at hxy hty
    cases a <;> dsimp [exampleDensity, baselineDensity] <;> nlinarith
  · intro a x hx
    exact hdint a x
  · intro a x hx
    let c : ℝ := (if a then (1 : ℝ) else -1) * Real.sin (2 * Real.pi * x) / 10 +
      (if a then exampleParameter theta else 0)
    have hform : exampleDensity theta a x =
        fun y => 1 + Real.cos (2 * Real.pi * y) / 10 + c * Real.sin (2 * Real.pi * y) := by
      funext y
      cases a <;> dsimp [exampleDensity, baselineDensity, c] <;> ring
    rw [hform]
    dsimp only
    rw [integral_add (show Integrable (fun y => 1 + Real.cos (2 * Real.pi * y) / 10)
        unitVolume from hone.add (hcos.div_const 10)) (hsin.const_mul c),
      integral_add hone (hcos.div_const 10), integral_div, integral_const_mul,
      example_sin_integral, example_cos_integral]
    simp [unitVolume, integral_const]


-- @node: def:example
/-- Uniform covariate design and the sinusoidal conditional nuisance family. -/
def exampleLaw (theta : ℝ) : ObsLaw :=
  ObsLaw.ofNuisance examplePropensity (exampleDensity theta) (example_nuisance_valid theta)
    -- @realizes Pexample(sinusoidal observed probability law)

end CausalSmith.Stat.DensityEffectRoughNull
