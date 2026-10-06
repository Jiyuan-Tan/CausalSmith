module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionLaw

/-! # Reflection transport for the Fourier identity

The reflected outcome is rewritten on the torus and the original seed integral is transported
to independent Haar sample and shift coordinates. This isolates the remaining Parseval argument.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Folding a lifted coordinate recovers its original value on the closed unit interval.](goal) Under [the stated conditions](hyp:hx). -/
-- @node: fold_lift_apply
lemma fold_lift_apply {n d : ℕ} (x : Covariates n d) (η : ReflectionCoins n d)
    (i : Fin n) (j : Fin d) (hx : x i j ∈ Icc (0 : ℝ) 1) :
    fold (lift x η i) j = x i j := by
  unfold fold lift
  cases η i j
  · rw [AddCircle.equivIco_coe_of_mem]
    · simp only [Bool.false_eq_true, if_false]
      rw [min_eq_left]
      · ring
      · linarith [hx.2]
    · simp only [Bool.false_eq_true, if_false]
      constructor <;> linarith [hx.1, hx.2]
  · by_cases hzero : x i j = 0
    · simp [hzero, AddCircle.coe_equivIco_mk_apply]
    · rw [AddCircle.equivIco_coe_of_mem]
      · simp only [if_true]
        rw [min_eq_right]
        · ring
        · norm_num [div_eq_mul_inv]
          linarith [hx.2]
      · simp only [if_true]
        constructor
        · norm_num [div_eq_mul_inv]
          linarith [hx.2]
        · norm_num [div_eq_mul_inv]
          have hpos : 0 < x i j := lt_of_le_of_ne hx.1 (Ne.symm hzero)
          linarith

/-- Cube probability is supported on the closed unit cube. [The asserted mathematical result follows](goal). -/
-- @node: cube_mem_ae
lemma cube_mem_ae (d : ℕ) :
    ∀ᵐ x ∂cubeMeasure d, ∀ j, x j ∈ Icc (0 : ℝ) 1 := by
  unfold cubeMeasure
  apply Measure.ae_pi_le_pi
  apply Filter.eventually_pi
  intro j
  exact ae_restrict_mem measurableSet_Icc

private lemma covariates_mem_ae (n d : ℕ) :
    ∀ᵐ x ∂covLaw n d, ∀ i j, x i j ∈ Icc (0 : ℝ) 1 := by
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (cubeMeasure d) := by
    unfold cubeMeasure
    infer_instance
  unfold covLaw
  apply Measure.ae_pi_le_pi
  have h : ∀ᶠ x in Filter.pi (fun _ : Fin n => ae (cubeMeasure d)),
      ∀ i, (∀ j, x i j ∈ Icc (0 : ℝ) 1) :=
    Filter.eventually_pi (fun _ => cube_mem_ae d)
  exact h

private lemma sampled_covariates_mem_ae
    {n d : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Covariates n d) (hX : UniformDraw μ X) :
    ∀ᵐ ω ∂μ, ∀ i j, X ω i j ∈ Icc (0 : ℝ) 1 := by
  exact (⟨hX.1, hX.2⟩ : MeasurePreserving X μ (covLaw n d)).quasiMeasurePreserving.ae
    (covariates_mem_ae n d)

private lemma reflExt_lift_eq
    {n d : ℕ} (m : Cube d → ℝ) (x : Covariates n d) (η : ReflectionCoins n d)
    (hx : ∀ i j, x i j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (reflExt m (lift x η i)).re = m (x i) := by
  unfold reflExt
  simp only [Complex.ofReal_re]
  congr 1
  funext j
  exact fold_lift_apply x η i j (hx i j)

/-- The period-two folding map is Borel measurable, including at its endpoints. This uses [the stated conclusion](goal). -/
-- @node: fold_measurable
@[fun_prop] lemma fold_measurable (d : ℕ) : Measurable (fold : Torus d → Cube d) := by
  unfold fold
  apply measurable_pi_lambda
  intro j
  exact (measurable_const.mul
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply j)).subtype_val)
    |>.min (measurable_const.sub (measurable_const.mul
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp
        (measurable_pi_apply j)).subtype_val))

private lemma reflExt_re_measurable {d : ℕ} (m : Cube d → ℝ) (hm : Measurable m) :
    Measurable (fun y : Torus d => (reflExt m y).re) := by
  change Measurable (m ∘ fold)
  exact hm.comp (fold_measurable d)

/-- The joint law of the shifted sample, common shift, and original outcome values can be
written entirely in independent Haar coordinates. The original value at unit `i` becomes the
even reflected extension evaluated at `W i - T`. This uses [the hX hypothesis](hyp:hX), [the hm hypothesis](hyp:hm), [the stated conclusion](goal). -/
theorem reflection_enriched_map
    (n d : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Covariates n d) (hX : UniformDraw μ X)
    (m : Cube d → ℝ) (hm : Measurable m) :
    (μ.prod ((reflectionLaw n d).prod (torusMeasure d))).map
        (fun ω => ((shiftedSample (X ω.1) ω.2.1 ω.2.2, ω.2.2),
          fun i => m (X ω.1 i))) =
      ((Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d)).map
        (fun wt => (wt, fun i => (reflExt m (wt.1 i - wt.2)).re)) := by
  haveI : IsProbabilityMeasure (reflectionLaw n d) := by
    unfold reflectionLaw
    infer_instance
  haveI : IsProbabilityMeasure ((reflectionLaw n d).prod (torusMeasure d)) :=
    inferInstance
  let f : Ω × (ReflectionCoins n d × Torus d) →
      (Fin n → Torus d) × Torus d :=
    fun ω => (shiftedSample (X ω.1) ω.2.1 ω.2.2, ω.2.2)
  let g : ((Fin n → Torus d) × Torus d) →
      ((Fin n → Torus d) × Torus d) × (Fin n → ℝ) :=
    fun wt => (wt, fun i => (reflExt m (wt.1 i - wt.2)).re)
  have hf : Measurable f := by
    dsimp [f, shiftedSample, lift]
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      change Measurable (fun ω : Ω × (ReflectionCoins n d × Torus d) =>
        lift (X ω.1) ω.2.1 i + ω.2.2)
      have hlift : Measurable (fun ω : Ω × (ReflectionCoins n d × Torus d) =>
          lift (X ω.1) ω.2.1 i) := by
        unfold lift
        apply measurable_pi_lambda
        intro j
        apply AddCircle.measurable_mk'.comp
        apply Measurable.ite
        · have hi : Measurable
              (fun ω : Ω × (ReflectionCoins n d × Torus d) => ω.2.1 i) :=
              (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
          exact ((measurable_pi_apply j).comp hi) (measurableSet_singleton true)
        · have hXi : Measurable
              (fun ω : Ω × (ReflectionCoins n d × Torus d) => X ω.1 i) :=
              (measurable_pi_apply i).comp (hX.1.comp measurable_fst)
          have hXij : Measurable
              (fun ω : Ω × (ReflectionCoins n d × Torus d) => X ω.1 i j) :=
            (measurable_pi_apply j).comp hXi
          exact (measurable_const.sub hXij).div_const 2
        · have hXi : Measurable
              (fun ω : Ω × (ReflectionCoins n d × Torus d) => X ω.1 i) :=
              (measurable_pi_apply i).comp (hX.1.comp measurable_fst)
          exact ((measurable_pi_apply j).comp hXi).div_const 2
      exact hlift.add (measurable_snd.comp measurable_snd)
    · exact measurable_snd.comp measurable_snd
  have hg : Measurable g := by
    apply Measurable.prodMk measurable_id
    apply measurable_pi_lambda
    intro i
    apply (reflExt_re_measurable m hm).comp
    exact ((measurable_pi_apply i).comp measurable_fst).sub measurable_snd
  rw [← reflectionLaw_map_shiftedSample n d Ω μ X hX]
  rw [Measure.map_map hg hf]
  apply Measure.map_congr
  have hcube := (measurePreserving_fst (μ := μ)
    (ν := (reflectionLaw n d).prod (torusMeasure d))).quasiMeasurePreserving.ae
      (sampled_covariates_mem_ae μ X hX)
  filter_upwards [hcube] with ω hω
  change ((f ω, fun i => m (X ω.1 i))) = g (f ω)
  apply Prod.ext
  · rfl
  · funext i
    dsimp [f, g]
    rw [show shiftedSample (X ω.1) ω.2.1 ω.2.2 i - ω.2.2 =
      lift (X ω.1) ω.2.1 i by simp [shiftedSample]]
    exact (reflExt_lift_eq m (X ω.1) ω.2.1 hω i).symm

/-- Every nonnegative measurable functional of the shifted sample, common shift, and original
outcome vector can be averaged instead over independent Haar coordinates, with outcomes recovered
by folding `W i - T`. This uses [the hX hypothesis](hyp:hX), [the hm hypothesis](hyp:hm), [the Φ hypothesis](hyp:Φ), [the hΦ hypothesis](hyp:hΦ), [the stated conclusion](goal). -/
theorem reflection_lintegral_transport
    (n d : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Covariates n d) (hX : UniformDraw μ X)
    (m : Cube d → ℝ) (hm : Measurable m)
    (Φ : (((Fin n → Torus d) × Torus d) × (Fin n → ℝ)) → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ ω, Φ ((shiftedSample (X ω.1) ω.2.1 ω.2.2, ω.2.2),
      fun i => m (X ω.1 i))
      ∂μ.prod ((reflectionLaw n d).prod (torusMeasure d))) =
    ∫⁻ wt, Φ (wt, fun i => (reflExt m (wt.1 i - wt.2)).re)
      ∂(Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d) := by
  let source : Ω × (ReflectionCoins n d × Torus d) →
      (((Fin n → Torus d) × Torus d) × (Fin n → ℝ)) :=
    fun ω => ((shiftedSample (X ω.1) ω.2.1 ω.2.2, ω.2.2), fun i => m (X ω.1 i))
  let target : ((Fin n → Torus d) × Torus d) →
      (((Fin n → Torus d) × Torus d) × (Fin n → ℝ)) :=
    fun wt => (wt, fun i => (reflExt m (wt.1 i - wt.2)).re)
  have hsource : Measurable source := by
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · apply measurable_pi_lambda
        intro i
        change Measurable (fun ω : Ω × (ReflectionCoins n d × Torus d) =>
          lift (X ω.1) ω.2.1 i + ω.2.2)
        have hlift : Measurable (fun ω : Ω × (ReflectionCoins n d × Torus d) =>
            lift (X ω.1) ω.2.1 i) := by
          unfold lift
          apply measurable_pi_lambda
          intro j
          apply AddCircle.measurable_mk'.comp
          apply Measurable.ite
          · have hi : Measurable
                (fun ω : Ω × (ReflectionCoins n d × Torus d) => ω.2.1 i) :=
                (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
            exact ((measurable_pi_apply j).comp hi) (measurableSet_singleton true)
          · have hXi : Measurable
                (fun ω : Ω × (ReflectionCoins n d × Torus d) => X ω.1 i) :=
                (measurable_pi_apply i).comp (hX.1.comp measurable_fst)
            have hXij : Measurable
                (fun ω : Ω × (ReflectionCoins n d × Torus d) => X ω.1 i j) :=
              (measurable_pi_apply j).comp hXi
            exact (measurable_const.sub hXij).div_const 2
          · have hXi : Measurable
                (fun ω : Ω × (ReflectionCoins n d × Torus d) => X ω.1 i) :=
                (measurable_pi_apply i).comp (hX.1.comp measurable_fst)
            exact ((measurable_pi_apply j).comp hXi).div_const 2
        exact hlift.add (measurable_snd.comp measurable_snd)
      · exact measurable_snd.comp measurable_snd
    · apply measurable_pi_lambda
      intro i
      exact hm.comp ((measurable_pi_apply i).comp (hX.1.comp measurable_fst))
  have htarget : Measurable target := by
    apply Measurable.prodMk measurable_id
    apply measurable_pi_lambda
    intro i
    exact (reflExt_re_measurable m hm).comp
      (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd)
  rw [← lintegral_map hΦ hsource, reflection_enriched_map n d Ω μ X hX m hm,
    lintegral_map hΦ htarget]

private def reflectShiftEquiv {d : ℕ} (w : Torus d) : Torus d ≃ᵐ Torus d :=
  (MeasurableEquiv.neg (Torus d)).trans (MeasurableEquiv.addLeft w)

private lemma reflectShiftEquiv_apply {d : ℕ} (w t : Torus d) :
    reflectShiftEquiv w t = w - t := by
  simp [reflectShiftEquiv, sub_eq_add_neg]

private lemma reflectShiftEquiv_preserving {d : ℕ} (w : Torus d) :
    MeasurePreserving (reflectShiftEquiv w) (torusMeasure d) (torusMeasure d) := by
  have h := measurePreserving_pi
    (fun _ : Fin d => AddCircle.haarAddCircle)
    (fun _ : Fin d => AddCircle.haarAddCircle)
    (fun i => Measure.measurePreserving_sub_left AddCircle.haarAddCircle (w i))
  convert h using 1
  ext t i
  simp [reflectShiftEquiv, sub_eq_add_neg]

/-- Folding normalized Haar measure has the same squared-integral normalization as the unit cube.
This is obtained from the reflected sampling law, including its endpoint convention. This uses [the hm hypothesis](hyp:hm), [the stated conclusion](goal). -/
theorem reflExt_sq_lintegral_eq (d : ℕ) (m : Cube d → ℝ) (hm : Measurable m) :
    (∫⁻ y, ENNReal.ofReal ‖reflExt m y‖ ^ 2 ∂torusMeasure d) =
      ∫⁻ x, ENNReal.ofReal |m x| ^ 2 ∂cubeMeasure d := by
  let Φ : (((Fin 1 → Torus d) × Torus d) × (Fin 1 → ℝ)) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal |p.2 0| ^ 2
  have hΦ : Measurable Φ := by
    fun_prop
  have hId : UniformDraw (covLaw 1 d) (id : Covariates 1 d → Covariates 1 d) := by
    refine ⟨measurable_id, ?_⟩
    simp
  have ht := reflection_lintegral_transport 1 d (Covariates 1 d) (covLaw 1 d)
    id hId m hm Φ hΦ
  dsimp [Φ] at ht
  haveI : IsProbabilityMeasure (reflectionLaw 1 d) := by
    unfold reflectionLaw
    infer_instance
  haveI : IsProbabilityMeasure ((reflectionLaw 1 d).prod (torusMeasure d)) := inferInstance
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (cubeMeasure d) := by
    unfold cubeMeasure
    infer_instance
  have hleft :
      (∫⁻ (ω : Covariates 1 d × (ReflectionCoins 1 d × Torus d)),
        ENNReal.ofReal |m (ω.1 0)| ^ 2
        ∂(covLaw 1 d).prod ((reflectionLaw 1 d).prod (torusMeasure d))) =
      ∫⁻ x, ENNReal.ofReal |m x| ^ 2 ∂cubeMeasure d := by
    rw [lintegral_prod]
    · simp only [lintegral_const, measure_univ, mul_one]
      simpa only [covLaw, Function.comp_apply] using
        (measurePreserving_eval (fun _ : Fin 1 => cubeMeasure d) 0).lintegral_comp
          ((ENNReal.measurable_ofReal.comp hm.abs).pow_const 2)
    · fun_prop
  have hq : Measurable (fun y : Torus d => ENNReal.ofReal |(reflExt m y).re| ^ 2) :=
    ((ENNReal.measurable_ofReal.comp (reflExt_re_measurable m hm).abs).pow_const 2)
  have hinner (w : Fin 1 → Torus d) :
      (∫⁻ t, ENNReal.ofReal |(reflExt m (w 0 - t)).re| ^ 2 ∂torusMeasure d) =
      ∫⁻ y, ENNReal.ofReal |(reflExt m y).re| ^ 2 ∂torusMeasure d := by
    convert (reflectShiftEquiv_preserving (w 0)).lintegral_comp hq using 1
    apply lintegral_congr
    intro t
    rw [reflectShiftEquiv_apply]
  have hright :
      (∫⁻ (wt : (Fin 1 → Torus d) × Torus d),
        ENNReal.ofReal |(reflExt m (wt.1 0 - wt.2)).re| ^ 2
        ∂(Measure.pi fun _ : Fin 1 => torusMeasure d).prod (torusMeasure d)) =
      ∫⁻ y, ENNReal.ofReal |(reflExt m y).re| ^ 2 ∂torusMeasure d := by
    rw [lintegral_prod]
    · simp_rw [hinner]
      simp
    · exact (hq.comp
        (((measurable_pi_apply 0).comp measurable_fst).sub measurable_snd)).aemeasurable
  rw [hleft, hright] at ht
  calc
    (∫⁻ y, ENNReal.ofReal ‖reflExt m y‖ ^ 2 ∂torusMeasure d) =
        ∫⁻ y, ENNReal.ofReal |(reflExt m y).re| ^ 2 ∂torusMeasure d := by
      apply lintegral_congr
      intro y
      simp [reflExt]
    _ = _ := ht.symm

/-- The even reflected extension of a cube `L²` representative is `L²` for normalized Haar
measure on the torus. This uses [the stated conclusion](goal). -/
theorem reflExt_memLp {d : ℕ} (m : CenteredL2Fn d) :
    MemLp (reflExt m.val) 2 (torusMeasure d) := by
  have hmeas : Measurable (reflExt m.val) :=
    Complex.measurable_ofReal.comp (m.property.1.comp (fold_measurable d))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).2
  have hs := reflExt_sq_lintegral_eq d m.val m.property.1
  have hc := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) (f := m.val) (μ := cubeMeasure d) (by norm_num) (by norm_num)).1
      m.property.2.1.2
  norm_num at hc ⊢
  simp_rw [← ofReal_norm] at ⊢
  simp_rw [Real.enorm_eq_ofReal_abs] at hc
  exact hs ▸ hc

private lemma torusCharacter_reflect {d : ℕ} (k : Fin d → ℤ) (w y : Torus d) :
    UnitAddTorus.mFourier (-k) (w - y) =
      UnitAddTorus.mFourier (-k) w * UnitAddTorus.mFourier k y := by
  unfold UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk]
  have hcoord : ∀ i : Fin d, fourier (-k i) (w i - y i) =
      fourier (-k i) (w i) * fourier (k i) (y i) := by
    intro i
    simp only [fourier_apply]
    rw [show (-k i) • (w i - y i) = (-k i) • w i + k i • y i by
      simp [sub_eq_add_neg]]
    rw [AddCircle.toCircle_add]
    rfl
  simp_rw [Pi.sub_apply, Pi.neg_apply, hcoord]
  exact Finset.prod_mul_distrib

private lemma fourierCoeff_reflectTranslate {d : ℕ} (f : Torus d → ℂ)
    (w : Torus d) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t => f (w - t)) k =
      UnitAddTorus.mFourier (-k) w * UnitAddTorus.mFourierCoeff f (-k) := by
  unfold UnitAddTorus.mFourierCoeff
  have hchange := (reflectShiftEquiv_preserving w).integral_comp'
    (fun t => UnitAddTorus.mFourier (-k) t • f (w - t))
  calc
    (∫ t, UnitAddTorus.mFourier (-k) t • f (w - t) ∂torusMeasure d) =
        ∫ y, UnitAddTorus.mFourier (-k) (reflectShiftEquiv w y) •
          f (w - reflectShiftEquiv w y) ∂torusMeasure d := hchange.symm
    _ = UnitAddTorus.mFourier (-k) w *
        ∫ y, UnitAddTorus.mFourier k y * f y ∂torusMeasure d := by
      simp_rw [reflectShiftEquiv_apply, sub_sub_cancel, smul_eq_mul,
        torusCharacter_reflect]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = _ := by
      simp only [neg_neg, smul_eq_mul]
      congr 1

/-- The paper's reflected coefficient is Mathlib's normalized torus Fourier coefficient. This uses [the stated conclusion](goal). -/
theorem mFourierCoeff_reflExt {d : ℕ} (m : Cube d → ℝ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (reflExt m) k = Fhat m k := by
  unfold UnitAddTorus.mFourierCoeff Fhat ek
  simp only [smul_eq_mul]
  change (∫ y, UnitAddTorus.mFourier (-k) y * reflExt m y ∂torusMeasure d) = _
  rfl

private lemma shiftCombination_memLp {n d : ℕ} (f : Torus d → ℂ)
    (hf : MemLp f 2 (torusMeasure d)) (a : Fin n → ℂ) (w : Fin n → Torus d) :
    MemLp (fun t => ∑ i, a i * f (w i - t)) 2 (torusMeasure d) := by
  apply memLp_finsetSum
  intro i hi
  have ht : MemLp (fun t => f (w i - t)) 2 (torusMeasure d) := by
    convert hf.comp_measurePreserving (reflectShiftEquiv_preserving (w i)) using 1
    funext t
    rw [Function.comp_apply, reflectShiftEquiv_apply]
  convert ht.const_smul (a i) using 1
  ext t
  simp [Pi.smul_apply]

private lemma fourierCoeff_shiftCombination {n d : ℕ} (f : Torus d → ℂ)
    (hf : MemLp f 2 (torusMeasure d)) (a : Fin n → ℂ) (w : Fin n → Torus d)
    (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t => ∑ i, a i * f (w i - t)) k =
      UnitAddTorus.mFourierCoeff f (-k) *
        ∑ i, a i * UnitAddTorus.mFourier (-k) (w i) := by
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [show ∀ i t, UnitAddTorus.mFourier (-k) t *
        (a i * f (w i - t)) = a i *
          (UnitAddTorus.mFourier (-k) t • f (w i - t)) by
        intro i t
        simp only [smul_eq_mul]
        ring]
    simp_rw [integral_const_mul]
    change (∑ i, a i * UnitAddTorus.mFourierCoeff
      (fun t => f (w i - t)) k) =
      ∑ i, UnitAddTorus.mFourierCoeff f (-k) *
        (a i * UnitAddTorus.mFourier (-k) (w i))
    simp_rw [fourierCoeff_reflectTranslate f (w := w _) (k := k)]
    simp only [mul_comm, mul_left_comm]
  · intro i hi
    change Integrable (fun t => UnitAddTorus.mFourier (-k) t *
      (a i * f (w i - t))) (torusMeasure d)
    have ht : MemLp (fun t => f (w i - t)) 2 (torusMeasure d) := by
      convert hf.comp_measurePreserving (reflectShiftEquiv_preserving (w i)) using 1
      funext t
      rw [Function.comp_apply, reflectShiftEquiv_apply]
    have hprod := ((ht.const_smul (a i)).integrable (by norm_num)).bdd_mul
        (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by
          simpa using (UnitAddTorus.mFourier (-k)).norm_coe_le_norm t)
    simpa only [Pi.smul_apply, smul_eq_mul] using hprod

/-- Parseval for a finite complex linear combination of translates by a common Haar shift.
The coefficient phase is indexed in the same direction as the Fourier character after reindexing
the intermediate formula by `k ↦ -k`. This uses [the hd hypothesis](hyp:hd), [the hf hypothesis](hyp:hf), [the stated conclusion](goal). -/
theorem commonShift_parseval {n d : ℕ} (hd : 0 < d) (f : Torus d → ℂ)
    (hf : MemLp f 2 (torusMeasure d)) (a : Fin n → ℂ) (w : Fin n → Torus d) :
    HasSum (fun k : Fin d → ℤ =>
      ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 *
        ‖∑ i, a i * UnitAddTorus.mFourier k (w i)‖ ^ 2)
      (∫ t, ‖∑ i, a i * f (w i - t)‖ ^ 2 ∂torusMeasure d) := by
  let g : Torus d → ℂ := fun t => ∑ i, a i * f (w i - t)
  have hg := shiftCombination_memLp f hf a w
  have hp := (torusParseval d hd (hg.toLp g)).2.2.1
  have hint : (∫ t, ‖(hg.toLp g) t‖ ^ 2 ∂torusMeasure d) =
      ∫ t, ‖g t‖ ^ 2 ∂torusMeasure d := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with t ht
    rw [ht]
  rw [hint] at hp
  have hneg : HasSum (fun k : Fin d → ℤ =>
      ‖UnitAddTorus.mFourierCoeff f (-k)‖ ^ 2 *
        ‖∑ i, a i * UnitAddTorus.mFourier (-k) (w i)‖ ^ 2)
      (∫ t, ‖g t‖ ^ 2 ∂torusMeasure d) := by
    refine HasSum.congr_fun hp (fun k => ?_)
    have hc : UnitAddTorus.mFourierCoeff (hg.toLp g) k =
        UnitAddTorus.mFourierCoeff g k := by
      unfold UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with t ht
      rw [ht]
    rw [hc, fourierCoeff_shiftCombination f hf a w k, norm_mul, mul_pow]
  apply (Equiv.hasSum_iff (Equiv.neg (Fin d → ℤ))).mp
  convert hneg using 1
  funext k
  rfl

/-- The common-shift Parseval identity in the nonnegative extended-real form used by kernel
averages. This uses [the hd hypothesis](hyp:hd), [the hf hypothesis](hyp:hf), [the stated conclusion](goal). -/
theorem commonShift_parseval_lintegral {n d : ℕ} (hd : 0 < d)
    (f : Torus d → ℂ) (hf : MemLp f 2 (torusMeasure d))
    (a : Fin n → ℂ) (w : Fin n → Torus d) :
    (∫⁻ t, ENNReal.ofReal ‖∑ i, a i * f (w i - t)‖ ^ 2 ∂torusMeasure d) =
      ∑' k : Fin d → ℤ, ENNReal.ofReal ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 *
        ENNReal.ofReal ‖∑ i, a i * UnitAddTorus.mFourier k (w i)‖ ^ 2 := by
  let g : Torus d → ℂ := fun t => ∑ i, a i * f (w i - t)
  let q : (Fin d → ℤ) → ℝ := fun k =>
    ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 *
      ‖∑ i, a i * UnitAddTorus.mFourier k (w i)‖ ^ 2
  have hg := shiftCombination_memLp f hf a w
  have hs : HasSum q (∫ t, ‖g t‖ ^ 2 ∂torusMeasure d) :=
    commonShift_parseval hd f hf a w
  simp_rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [← ofReal_integral_eq_lintegral_ofReal (hg.integrable_norm_pow (by norm_num))
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs.summable]
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (sq_nonneg _)]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
