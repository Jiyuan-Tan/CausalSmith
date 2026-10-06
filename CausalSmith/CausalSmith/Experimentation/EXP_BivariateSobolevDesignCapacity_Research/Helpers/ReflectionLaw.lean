module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CapacityHandle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Law of the reflected and shifted sample

This file proves that independent cube coordinates, independently reflected into the two
halves of the circle and then translated by a common Haar element, give an iid Haar sample
that is independent of the translating element.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ One fair reflection coin lifts a cube coordinate into the period-two circle. -/
-- @node: reflectedCoordinate
def reflectedCoordinate (x : ℝ) (b : Bool) : UnitAddCircle :=
  ((if b then (2 - x) / 2 else x / 2 : ℝ) : UnitAddCircle)

private lemma uniformBool_measure :
    (PMF.uniformOfFintype Bool).toMeasure =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac false + (2 : ℝ≥0∞)⁻¹ • Measure.dirac true := by
  apply Measure.ext_of_singleton
  intro b
  cases b <;> simp

private lemma uniformBoolFun_measure (m : ℕ) :
    (PMF.uniformOfFintype (Fin m → Bool)).toMeasure =
      Measure.pi (fun _ : Fin m => (PMF.uniformOfFintype Bool).toMeasure) := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hset : {b} = Set.univ.pi (fun i => {b i}) := by
    ext z
    simp [Set.mem_pi, funext_iff]
  rw [hset, Measure.pi_pi]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

private lemma map_half_restrict :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun x : ℝ => x / 2) =
      (2 : ℝ≥0∞) • volume.restrict (Ioc (0 : ℝ) (1 / 2)) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  have hpre : (fun x : ℝ => x / 2) ⁻¹' Ioc (0 : ℝ) (1 / 2) = Ioc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h
    · constructor <;> linarith [h.1, h.2]
    · constructor <;> linarith [h.1, h.2]
  rw [← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Ioc]
  have hmap : Measure.map (fun x : ℝ => x / 2) volume = (2 : ℝ≥0∞) • volume := by
    convert Real.map_volume_mul_right (a := (2 : ℝ)⁻¹) (by norm_num) using 1 <;>
      norm_num [div_eq_mul_inv]
  rw [hmap, Measure.restrict_smul]

private lemma map_one_sub_half_restrict :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun x : ℝ => (2 - x) / 2) =
      (2 : ℝ≥0∞) • volume.restrict (Ioc (1 / 2 : ℝ) 1) := by
  rw [← restrict_Ico_eq_restrict_Icc]
  have hpre : (fun x : ℝ => (2 - x) / 2) ⁻¹' Ioc (1 / 2 : ℝ) 1 = Ico 0 1 := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor <;> intro h
    · constructor <;> linarith [h.1, h.2]
    · constructor <;> linarith [h.1, h.2]
  rw [← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Ioc]
  have hlinear :
      Measure.map (fun x : ℝ => -(x / 2)) volume = (2 : ℝ≥0∞) • volume := by
    convert Real.map_volume_mul_left (a := -(2 : ℝ)⁻¹) (by norm_num) using 1 <;>
      norm_num [div_eq_mul_inv, mul_comm]
  calc
    (Measure.map (fun x : ℝ => (2 - x) / 2) volume).restrict (Ioc (1 / 2) 1) =
        (Measure.map (fun y : ℝ => 1 + y)
          (Measure.map (fun x : ℝ => -(x / 2)) volume)).restrict (Ioc (1 / 2) 1) := by
      congr 1
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      simp only [Function.comp_apply]
      ring
    _ = ((2 : ℝ≥0∞) • volume).restrict (Ioc (1 / 2) 1) := by
      rw [hlinear, Measure.map_smul, map_add_left_eq_self]
    _ = (2 : ℝ≥0∞) • volume.restrict (Ioc (1 / 2) 1) := by
      rw [Measure.restrict_smul]

private lemma reflectedCoordinate_map :
    ((volume.restrict (Icc (0 : ℝ) 1)).prod
      (PMF.uniformOfFintype Bool).toMeasure).map
        (fun z => reflectedCoordinate z.1 z.2) = AddCircle.haarAddCircle := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  have hmeas : Measurable (fun z : ℝ × Bool => reflectedCoordinate z.1 z.2) := by
    unfold reflectedCoordinate
    apply AddCircle.measurable_mk'.comp
    apply Measurable.ite
    · exact measurable_snd (measurableSet_singleton true)
    · fun_prop
    · fun_prop
  rw [uniformBool_measure, Measure.prod_add, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.map_add _ _ hmeas, Measure.map_smul,
    Measure.map_smul, Measure.prod_dirac, Measure.prod_dirac]
  have hfalse :
      Measure.map (fun z : ℝ × Bool => reflectedCoordinate z.1 z.2)
          (Measure.map (fun x : ℝ => (x, false)) ν) =
        Measure.map ((↑) : ℝ → UnitAddCircle)
          ((2 : ℝ≥0∞) • volume.restrict (Ioc (0 : ℝ) (1 / 2))) := by
    calc
      _ = Measure.map ((↑) : ℝ → UnitAddCircle)
          (Measure.map (fun x : ℝ => x / 2) ν) := by
        rw [Measure.map_map hmeas (by fun_prop),
          Measure.map_map AddCircle.measurable_mk' (by fun_prop)]
        congr 1
      _ = _ := by rw [map_half_restrict]
  have htrue :
      Measure.map (fun z : ℝ × Bool => reflectedCoordinate z.1 z.2)
          (Measure.map (fun x : ℝ => (x, true)) ν) =
        Measure.map ((↑) : ℝ → UnitAddCircle)
          ((2 : ℝ≥0∞) • volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
    calc
      _ = Measure.map ((↑) : ℝ → UnitAddCircle)
          (Measure.map (fun x : ℝ => (2 - x) / 2) ν) := by
        rw [Measure.map_map hmeas (by fun_prop),
          Measure.map_map AddCircle.measurable_mk' (by fun_prop)]
        congr 1
      _ = _ := by rw [map_one_sub_half_restrict]
  rw [hfalse, htrue, Measure.map_smul, Measure.map_smul,
    smul_smul, smul_smul]
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [htwo, one_smul, one_smul]
  rw [← Measure.map_add _ _ AddCircle.measurable_mk']
  have hunion : Ioc (0 : ℝ) (1 / 2) ∪ Ioc (1 / 2 : ℝ) 1 = Ioc 0 1 := by
    ext x
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
    · intro h
      by_cases hx : x ≤ 1 / 2
      · exact Or.inl ⟨h.1, hx⟩
      · exact Or.inr ⟨lt_of_not_ge hx, h.2⟩
  rw [← Measure.restrict_union (by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1) measurableSet_Ioc, hunion]
  simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one,
    one_smul] using (AddCircle.measurePreserving_mk 1 0).map_eq

/-- Independent fair coordinate reflections send cube probability to normalized Haar measure.](goal) This uses [the stated conclusion](goal). -/
-- @node: cubeReflection_map
lemma cubeReflection_map (d : ℕ) :
    ((cubeMeasure d).prod (PMF.uniformOfFintype (Fin d → Bool)).toMeasure).map
        (fun z j => reflectedCoordinate (z.1 j) (z.2 j)) = torusMeasure d := by
  rw [cubeMeasure, uniformBoolFun_measure]
  have hscalar : MeasurePreserving (fun z : ℝ × Bool => reflectedCoordinate z.1 z.2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod
        (PMF.uniformOfFintype Bool).toMeasure) AddCircle.haarAddCircle :=
    ⟨by
      unfold reflectedCoordinate
      apply AddCircle.measurable_mk'.comp
      apply Measurable.ite
      · exact measurable_snd (measurableSet_singleton true)
      · fun_prop
      · fun_prop,
    reflectedCoordinate_map⟩
  have hunzip := (measurePreserving_arrowProdEquivProdArrow ℝ Bool (Fin d)
    (fun _ => volume.restrict (Icc (0 : ℝ) 1))
    (fun _ => (PMF.uniformOfFintype Bool).toMeasure)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ Bool (Fin d))
  have hpi := measurePreserving_pi
    (fun _ : Fin d => (volume.restrict (Icc (0 : ℝ) 1)).prod
      (PMF.uniformOfFintype Bool).toMeasure)
    (fun _ : Fin d => AddCircle.haarAddCircle) (fun _ => hscalar)
  have h := hpi.comp hunzip
  change _ = Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
  convert h.map_eq using 1
  congr 1

private lemma reflectionLaw_pi (n d : ℕ) :
    reflectionLaw n d = Measure.pi (fun _ : Fin n =>
      (PMF.uniformOfFintype (Fin d → Bool)).toMeasure) := by
  unfold reflectionLaw
  apply Measure.ext_of_singleton
  intro η
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hset : {η} = Set.univ.pi (fun i => {η i}) := by
    ext z
    simp [Set.mem_pi, funext_iff]
  rw [hset, Measure.pi_pi]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

private lemma reflectedSample_map (n d : ℕ) :
    ((covLaw n d).prod (reflectionLaw n d)).map
        (fun z => lift z.1 z.2) = Measure.pi (fun _ : Fin n => torusMeasure d) := by
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (cubeMeasure d) := by
    unfold cubeMeasure
    infer_instance
  rw [covLaw, reflectionLaw_pi]
  have hunit : MeasurePreserving
      (fun z : Cube d × (Fin d → Bool) => fun j => reflectedCoordinate (z.1 j) (z.2 j))
      ((cubeMeasure d).prod (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)
      (torusMeasure d) := by
    refine ⟨?_, ?_⟩
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
    · exact cubeReflection_map d
  have hunzip := (measurePreserving_arrowProdEquivProdArrow (Cube d) (Fin d → Bool) (Fin n)
    (fun _ => cubeMeasure d)
    (fun _ => (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow (Cube d) (Fin d → Bool) (Fin n))
  have hpi := measurePreserving_pi
    (fun _ : Fin n => (cubeMeasure d).prod
      (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)
    (fun _ : Fin n => torusMeasure d) (fun _ => hunit)
  have h := hpi.comp hunzip
  convert h.map_eq using 1
  congr 1

private lemma reflectedSample_of_uniform
    {n d : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Covariates n d) (hX : UniformDraw μ X) :
    (μ.prod (reflectionLaw n d)).map (fun z => lift (X z.1) z.2) =
      Measure.pi (fun _ : Fin n => torusMeasure d) := by
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (cubeMeasure d) := by
    unfold cubeMeasure
    infer_instance
  haveI : IsProbabilityMeasure (covLaw n d) := by
    unfold covLaw
    infer_instance
  haveI : IsProbabilityMeasure μ := ⟨by
    have hmass := congrArg (fun ρ : Measure (Covariates n d) => ρ Set.univ) hX.2
    simpa [Measure.map_apply_of_aemeasurable hX.1.aemeasurable] using hmass⟩
  have hlift : Measurable (fun z : Covariates n d × ReflectionCoins n d => lift z.1 z.2) := by
    unfold lift
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    apply AddCircle.measurable_mk'.comp
    apply Measurable.ite
    · have hi : Measurable (fun z : Covariates n d × ReflectionCoins n d => z.2 i) :=
          (measurable_pi_apply i).comp measurable_snd
      have hb : Measurable (fun z : Covariates n d × ReflectionCoins n d => z.2 i j) :=
        (measurable_pi_apply j).comp hi
      exact hb (measurableSet_singleton true)
    · fun_prop
    · fun_prop
  have hpair : Measurable (Prod.map X id : Ω × ReflectionCoins n d →
      Covariates n d × ReflectionCoins n d) := hX.1.prodMap measurable_id
  calc
    _ = Measure.map (fun z => lift z.1 z.2)
        (Measure.map (Prod.map X id) (μ.prod (reflectionLaw n d))) := by
      rw [Measure.map_map hlift hpair]
      rfl
    _ = Measure.map (fun z => lift z.1 z.2)
        ((μ.map X).prod ((reflectionLaw n d).map id)) := by
      rw [Measure.map_prod_map μ (reflectionLaw n d) hX.1 measurable_id]
    _ = _ := by
      rw [Measure.map_id, hX.2, reflectedSample_map]

private lemma commonShift_preserving (n d : ℕ) :
    MeasurePreserving
      (fun z : (Fin n → Torus d) × Torus d => (fun i => z.1 i + z.2, z.2))
      ((Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d))
      ((Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d)) := by
  let ν := Measure.pi (fun _ : Fin n => torusMeasure d)
  let τ := torusMeasure d
  have htranslate (T : Torus d) :
      Measure.map (fun w : Fin n → Torus d => fun i => w i + T) ν = ν := by
    have hcoord (i : Fin n) : MeasurePreserving (fun y : Torus d => y + T)
        (torusMeasure d) (torusMeasure d) :=
      ⟨by fun_prop, map_add_right_eq_self (torusMeasure d) T⟩
    exact (measurePreserving_pi (fun _ : Fin n => torusMeasure d)
      (fun _ : Fin n => torusMeasure d) hcoord).map_eq
  have hswap₁ : MeasurePreserving Prod.swap (ν.prod τ) (τ.prod ν) :=
    Measure.measurePreserving_swap
  have hskew : MeasurePreserving
      (fun z : Torus d × (Fin n → Torus d) => (z.1, fun i => z.2 i + z.1))
      (τ.prod ν) (τ.prod ν) :=
    MeasurePreserving.skew_product (MeasurePreserving.id τ) (by fun_prop)
      (Filter.Eventually.of_forall htranslate)
  have hswap₂ : MeasurePreserving Prod.swap (τ.prod ν) (ν.prod τ) :=
    Measure.measurePreserving_swap
  have h := hswap₂.comp (hskew.comp hswap₁)
  convert h using 1
  funext z
  rfl

/-- Independent cube coordinates with independent fair reflections, followed by a common
Haar shift, have the iid Haar product law and remain independent of that common shift. This uses [the hX hypothesis](hyp:hX), [the stated conclusion](goal). -/
theorem reflectionLaw_map_shiftedSample
    (n d : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Covariates n d) (hX : UniformDraw μ X) :
    (μ.prod ((reflectionLaw n d).prod (torusMeasure d))).map
        (fun ω => (shiftedSample (X ω.1) ω.2.1 ω.2.2, ω.2.2)) =
      (Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d) := by
  let ν := Measure.pi (fun _ : Fin n => torusMeasure d)
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (cubeMeasure d) := by
    unfold cubeMeasure
    infer_instance
  haveI : IsProbabilityMeasure (covLaw n d) := by
    unfold covLaw
    infer_instance
  haveI : IsProbabilityMeasure μ := ⟨by
    have hmass := congrArg (fun ρ : Measure (Covariates n d) => ρ Set.univ) hX.2
    simpa [Measure.map_apply_of_aemeasurable hX.1.aemeasurable] using hmass⟩
  have hreflect : MeasurePreserving (fun z : Ω × ReflectionCoins n d => lift (X z.1) z.2)
      (μ.prod (reflectionLaw n d)) ν := by
    refine ⟨?_, reflectedSample_of_uniform μ X hX⟩
    unfold lift
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    apply AddCircle.measurable_mk'.comp
    apply Measurable.ite
    · have hi : Measurable (fun z : Ω × ReflectionCoins n d => z.2 i) :=
          (measurable_pi_apply i).comp measurable_snd
      have hb : Measurable (fun z : Ω × ReflectionCoins n d => z.2 i j) :=
        (measurable_pi_apply j).comp hi
      exact hb (measurableSet_singleton true)
    · have hXi : Measurable (fun z : Ω × ReflectionCoins n d => X z.1 i) :=
          (measurable_pi_apply i).comp (hX.1.comp measurable_fst)
      have hXij : Measurable (fun z : Ω × ReflectionCoins n d => X z.1 i j) :=
        (measurable_pi_apply j).comp hXi
      exact (measurable_const.sub hXij).div_const 2
    · have hXi : Measurable (fun z : Ω × ReflectionCoins n d => X z.1 i) :=
          (measurable_pi_apply i).comp (hX.1.comp measurable_fst)
      exact ((measurable_pi_apply j).comp hXi).div_const 2
  have hgrouped := hreflect.prod (MeasurePreserving.id (torusMeasure d))
  have hassoc := (measurePreserving_prodAssoc μ (reflectionLaw n d) (torusMeasure d)).symm
    (MeasurableEquiv.prodAssoc)
  have hseed := hgrouped.comp hassoc
  have h := (commonShift_preserving n d).comp hseed
  change _ = ν.prod (torusMeasure d)
  convert h.map_eq using 1
  congr 1

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
