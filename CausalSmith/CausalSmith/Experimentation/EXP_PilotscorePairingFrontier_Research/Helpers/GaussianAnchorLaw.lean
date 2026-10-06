module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BernoulliHypercube
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BindIntegral
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Geometry
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Gaussian anchor laws

This file constructs the unit law used at the unbounded-outcome anchor endpoint.
The covariate is uniform on the unit cube and, conditional on it, the two potential
outcomes are independent Gaussians with the same prescribed mean and variance.
-/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {d : ℕ} {β cX CX : ℝ}

/-- Given [a conditional mean](hyp:g), [a variance](hyp:v), and [a covariate
point](hyp:x), [the conditional unit law records that point and draws two independent
Gaussians with the prescribed common mean and variance](goal). -/
noncomputable def gaussianAnchorFiber (g : XSpace d → ℝ) (v : NNReal) (x : XSpace d) :
    Measure (UnitRecord d) :=
  (Measure.dirac x).prod
    ((gaussianReal (g x) v).prod (gaussianReal (g x) v))

/-- Given [a conditional mean](hyp:g) and [a variance](hyp:v), [the Gaussian anchor
law mixes the conditional Gaussian unit laws over uniform cube covariates](goal). -/
noncomputable def gaussianAnchorLaw (g : XSpace d → ℝ) (v : NNReal) :
    Measure (UnitRecord d) :=
  (cubeMeasure d).bind (gaussianAnchorFiber g v)

/-- For [a measurable conditional mean](hyp:g,hg) and [a variance](hyp:v), [the
Gaussian anchor fiber varies measurably with the covariate](goal). -/
@[fun_prop]
lemma measurable_gaussianAnchorFiber (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) : Measurable (gaussianAnchorFiber g v) := by
  let G : XSpace d → ProbabilityMeasure ℝ :=
    fun x => ⟨gaussianReal (g x) v, inferInstance⟩
  have hG : Measurable G := by
    apply Measurable.subtype_mk
    exact measurable_gaussianReal.comp (hg.prodMk measurable_const)
  let GG : XSpace d → ProbabilityMeasure (ℝ × ℝ) :=
    fun x => ⟨(G x).toMeasure.prod (G x).toMeasure, inferInstance⟩
  have hGG : Measurable GG := by
    apply Measurable.subtype_mk
    exact ProbabilityMeasure.measurable_fun_prod.comp (hG.prodMk hG)
  let D : XSpace d → ProbabilityMeasure (XSpace d) :=
    fun x => ⟨Measure.dirac x, inferInstance⟩
  have hD : Measurable D := by
    apply Measurable.subtype_mk
    exact Measure.measurable_dirac
  change Measurable fun x => (D x).toMeasure.prod (GG x).toMeasure
  exact ProbabilityMeasure.measurable_fun_prod.comp (hD.prodMk hGG)

/-- For [a conditional mean](hyp:g), [a variance](hyp:v), and [a covariate
point](hyp:x), [the corresponding Gaussian anchor fiber is a probability measure](goal). -/
lemma gaussianAnchorFiber_isProbabilityMeasure (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) : IsProbabilityMeasure (gaussianAnchorFiber g v x) := by
  unfold gaussianAnchorFiber
  infer_instance

/-- For [a conditional mean](hyp:g), [a variance](hyp:v), and [measurability of the
mean](hyp:hg), [the Gaussian anchor law is a probability measure](goal). -/
lemma gaussianAnchorLaw_isProbabilityMeasure (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) : IsProbabilityMeasure (gaussianAnchorLaw g v) := by
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  unfold gaussianAnchorLaw
  exact MeasureTheory.isProbabilityMeasure_bind
    (measurable_gaussianAnchorFiber g v hg).aemeasurable
    (Filter.Eventually.of_forall (gaussianAnchorFiber_isProbabilityMeasure g v))

/-- For [a conditional mean](hyp:g), [a variance](hyp:v), and [a covariate
point](hyp:x), [pushing its Gaussian anchor fiber onto the recorded covariate gives
the point mass at that point](goal). -/
lemma gaussianAnchorFiber_map_fst (g : XSpace d → ℝ) (v : NNReal) (x : XSpace d) :
    (gaussianAnchorFiber g v x).map Prod.fst = Measure.dirac x := by
  unfold gaussianAnchorFiber
  rw [Measure.map_fst_prod]
  simp

/-- For [a conditional mean](hyp:g), [a variance](hyp:v), and [measurability of the
mean](hyp:hg), [the covariate marginal of the Gaussian anchor law is uniform cube
measure](goal). -/
lemma gaussianAnchorLaw_map_fst (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) :
    (gaussianAnchorLaw g v).map Prod.fst = cubeMeasure d := by
  unfold gaussianAnchorLaw
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.bind_apply (measurable_fst hs)
      (measurable_gaussianAnchorFiber g v hg).aemeasurable]
  have hpoint : ∀ x, gaussianAnchorFiber g v x (Prod.fst ⁻¹' s) = s.indicator 1 x := by
    intro x
    have hm := congrArg (fun μ : Measure (XSpace d) => μ s)
      (gaussianAnchorFiber_map_fst g v x)
    rw [Measure.map_apply measurable_fst hs, Measure.dirac_apply' _ hs] at hm
    simpa [Set.indicator_apply] using hm
  simp_rw [hpoint, lintegral_indicator hs]
  simp

private lemma gaussian_second_moment (a : ℝ) (v : NNReal) :
    (∫ y, y ^ 2 ∂gaussianReal a v) = (v : ℝ) + a ^ 2 := by
  have hmem : MemLp (fun y : ℝ => y) 2 (gaussianReal a v) := by
    change MemLp id 2 (gaussianReal a v)
    exact memLp_id_gaussianReal' 2 (by simp)
  have hvar := variance_eq_sub hmem
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at hvar
  change (v : ℝ) = (∫ y, y ^ 2 ∂gaussianReal a v) - a ^ 2 at hvar
  linarith

private lemma gaussianAnchorFiber_memLp_y0 (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    MemLp (fun u : UnitRecord d => u.2.1) 2 (gaussianAnchorFiber g v x) := by
  have hgauss : MemLp (fun y : ℝ => y) 2 (gaussianReal (g x) v) := by
    change MemLp id 2 (gaussianReal (g x) v)
    exact memLp_id_gaussianReal' 2 (by simp)
  have hpair : MemLp (fun ys : ℝ × ℝ => ys.1) 2
      ((gaussianReal (g x) v).prod (gaussianReal (g x) v)) :=
    hgauss.comp_fst (gaussianReal (g x) v)
  simpa [gaussianAnchorFiber] using hpair.comp_snd (Measure.dirac x)

private lemma gaussianAnchorFiber_memLp_y1 (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    MemLp (fun u : UnitRecord d => u.2.2) 2 (gaussianAnchorFiber g v x) := by
  have hgauss : MemLp (fun y : ℝ => y) 2 (gaussianReal (g x) v) := by
    change MemLp id 2 (gaussianReal (g x) v)
    exact memLp_id_gaussianReal' 2 (by simp)
  have hpair : MemLp (fun ys : ℝ × ℝ => ys.2) 2
      ((gaussianReal (g x) v).prod (gaussianReal (g x) v)) :=
    hgauss.comp_snd (gaussianReal (g x) v)
  simpa [gaussianAnchorFiber] using hpair.comp_snd (Measure.dirac x)

private lemma gaussianAnchorFiber_integral_y0 (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    (∫ u, u.2.1 ∂gaussianAnchorFiber g v x) = g x := by
  unfold gaussianAnchorFiber
  calc
    (∫ u : XSpace d × (ℝ × ℝ), u.2.1 ∂
        (Measure.dirac x).prod ((gaussianReal (g x) v).prod (gaussianReal (g x) v))) =
        ∫ ys : ℝ × ℝ, ys.1 ∂(gaussianReal (g x) v).prod (gaussianReal (g x) v) := by
      simpa using (integral_fun_snd (μ := Measure.dirac x)
        (ν := (gaussianReal (g x) v).prod (gaussianReal (g x) v))
        (fun ys : ℝ × ℝ => ys.1))
    _ = ∫ y : ℝ, y ∂gaussianReal (g x) v := by
      simpa using (integral_fun_fst (μ := gaussianReal (g x) v)
        (ν := gaussianReal (g x) v) (fun y : ℝ => y))
    _ = g x := integral_id_gaussianReal

private lemma gaussianAnchorFiber_integral_y1 (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    (∫ u, u.2.2 ∂gaussianAnchorFiber g v x) = g x := by
  unfold gaussianAnchorFiber
  calc
    (∫ u : XSpace d × (ℝ × ℝ), u.2.2 ∂
        (Measure.dirac x).prod ((gaussianReal (g x) v).prod (gaussianReal (g x) v))) =
        ∫ ys : ℝ × ℝ, ys.2 ∂(gaussianReal (g x) v).prod (gaussianReal (g x) v) := by
      simpa using (integral_fun_snd (μ := Measure.dirac x)
        (ν := (gaussianReal (g x) v).prod (gaussianReal (g x) v))
        (fun ys : ℝ × ℝ => ys.2))
    _ = ∫ y : ℝ, y ∂gaussianReal (g x) v := by
      simpa using (integral_fun_snd (μ := gaussianReal (g x) v)
        (ν := gaussianReal (g x) v) (fun y : ℝ => y))
    _ = g x := integral_id_gaussianReal

private lemma gaussianAnchorFiber_integral_sq_y0 (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    (∫ u, u.2.1 ^ 2 ∂gaussianAnchorFiber g v x) = (v : ℝ) + (g x) ^ 2 := by
  unfold gaussianAnchorFiber
  calc
    (∫ u : XSpace d × (ℝ × ℝ), u.2.1 ^ 2 ∂
        (Measure.dirac x).prod ((gaussianReal (g x) v).prod (gaussianReal (g x) v))) =
        ∫ ys : ℝ × ℝ, ys.1 ^ 2 ∂(gaussianReal (g x) v).prod (gaussianReal (g x) v) := by
      simpa using (integral_fun_snd (μ := Measure.dirac x)
        (ν := (gaussianReal (g x) v).prod (gaussianReal (g x) v))
        (fun ys : ℝ × ℝ => ys.1 ^ 2))
    _ = ∫ y : ℝ, y ^ 2 ∂gaussianReal (g x) v := by
      simpa using (integral_fun_fst (μ := gaussianReal (g x) v)
        (ν := gaussianReal (g x) v) (fun y : ℝ => y ^ 2))
    _ = (v : ℝ) + (g x) ^ 2 := gaussian_second_moment (g x) v

private lemma gaussianAnchorFiber_integral_sq_y1 (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    (∫ u, u.2.2 ^ 2 ∂gaussianAnchorFiber g v x) = (v : ℝ) + (g x) ^ 2 := by
  unfold gaussianAnchorFiber
  calc
    (∫ u : XSpace d × (ℝ × ℝ), u.2.2 ^ 2 ∂
        (Measure.dirac x).prod ((gaussianReal (g x) v).prod (gaussianReal (g x) v))) =
        ∫ ys : ℝ × ℝ, ys.2 ^ 2 ∂(gaussianReal (g x) v).prod (gaussianReal (g x) v) := by
      simpa using (integral_fun_snd (μ := Measure.dirac x)
        (ν := (gaussianReal (g x) v).prod (gaussianReal (g x) v))
        (fun ys : ℝ × ℝ => ys.2 ^ 2))
    _ = ∫ y : ℝ, y ^ 2 ∂gaussianReal (g x) v := by
      simpa using (integral_fun_snd (μ := gaussianReal (g x) v)
        (ν := gaussianReal (g x) v) (fun y : ℝ => y ^ 2))
    _ = (v : ℝ) + (g x) ^ 2 := gaussian_second_moment (g x) v

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the control outcome under the Gaussian
anchor law belongs to `L²`](goal). -/
lemma gaussianAnchorLaw_memLp_y0 (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    MemLp (fun u : UnitRecord d => u.2.1) 2 (gaussianAnchorLaw g v) := by
  let K : Kernel (XSpace d) (UnitRecord d) :=
    ⟨gaussianAnchorFiber g v, measurable_gaussianAnchorFiber g v hg⟩
  have heq : gaussianAnchorLaw g v = K ∘ₘ cubeMeasure d := rfl
  have hm : AEStronglyMeasurable (fun u : UnitRecord d => u.2.1 ^ 2)
      (gaussianAnchorLaw g v) := by fun_prop
  have hi : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) (gaussianAnchorLaw g v) := by
    rw [heq, Measure.integrable_comp_iff (by simpa [heq] using hm)]
    constructor
    · exact Filter.Eventually.of_forall fun x =>
        (gaussianAnchorFiber_memLp_y0 g v x).integrable_sq
    · have hconst : Integrable (fun _ : XSpace d => (v : ℝ)) (cubeMeasure d) := by
        letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
        fun_prop
      have hfun : (fun x => ∫ u, ‖u.2.1 ^ 2‖ ∂gaussianAnchorFiber g v x) =
          fun x => (v : ℝ) + (g x) ^ 2 := by
        funext x
        rw [← gaussianAnchorFiber_integral_sq_y0 g v x]
        apply integral_congr_ae
        filter_upwards [] with u
        rw [Real.norm_of_nonneg (sq_nonneg _)]
      change Integrable (fun x => ∫ u, ‖u.2.1 ^ 2‖ ∂gaussianAnchorFiber g v x)
        (cubeMeasure d)
      rw [hfun]
      exact hconst.add hg2
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hi

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the treated outcome under the Gaussian
anchor law belongs to `L²`](goal). -/
lemma gaussianAnchorLaw_memLp_y1 (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    MemLp (fun u : UnitRecord d => u.2.2) 2 (gaussianAnchorLaw g v) := by
  let K : Kernel (XSpace d) (UnitRecord d) :=
    ⟨gaussianAnchorFiber g v, measurable_gaussianAnchorFiber g v hg⟩
  have heq : gaussianAnchorLaw g v = K ∘ₘ cubeMeasure d := rfl
  have hm : AEStronglyMeasurable (fun u : UnitRecord d => u.2.2 ^ 2)
      (gaussianAnchorLaw g v) := by fun_prop
  have hi : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) (gaussianAnchorLaw g v) := by
    rw [heq, Measure.integrable_comp_iff (by simpa [heq] using hm)]
    constructor
    · exact Filter.Eventually.of_forall fun x =>
        (gaussianAnchorFiber_memLp_y1 g v x).integrable_sq
    · have hconst : Integrable (fun _ : XSpace d => (v : ℝ)) (cubeMeasure d) := by
        letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
        fun_prop
      have hfun : (fun x => ∫ u, ‖u.2.2 ^ 2‖ ∂gaussianAnchorFiber g v x) =
          fun x => (v : ℝ) + (g x) ^ 2 := by
        funext x
        rw [← gaussianAnchorFiber_integral_sq_y1 g v x]
        apply integral_congr_ae
        filter_upwards [] with u
        rw [Real.norm_of_nonneg (sq_nonneg _)]
      change Integrable (fun x => ∫ u, ‖u.2.2 ^ 2‖ ∂gaussianAnchorFiber g v x)
        (cubeMeasure d)
      rw [hfun]
      exact hconst.add hg2
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hi

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the control outcome has a finite second
moment under the Gaussian anchor law](goal). -/
lemma gaussianAnchorLaw_secondMoment0 (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    Integrable (fun u : UnitRecord d => u.2.1 ^ 2) (gaussianAnchorLaw g v) :=
  (gaussianAnchorLaw_memLp_y0 g v hg hg2).integrable_sq

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the treated outcome has a finite second
moment under the Gaussian anchor law](goal). -/
lemma gaussianAnchorLaw_secondMoment1 (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    Integrable (fun u : UnitRecord d => u.2.2 ^ 2) (gaussianAnchorLaw g v) :=
  (gaussianAnchorLaw_memLp_y1 g v hg hg2).integrable_sq

private lemma gaussian_setIntegral_bind_recording {X Y : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x)
    (f : Y → ℝ) (hf : Integrable f (μ.bind κ))
    (B : Set X) (hB : MeasurableSet B) :
    (∫ y in base ⁻¹' B, f y ∂μ.bind κ) =
      ∫ x in B, (∫ y, f y ∂κ x) ∂μ := by
  rw [← integral_indicator (hB.preimage hb)]
  rw [Causalean.Mathlib.MeasureTheory.integral_bind hκ
    (hf.indicator (hB.preimage hb))]
  rw [← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  have hbase : ∀ᵐ y ∂κ x, base y = x := by
    apply ae_of_ae_map (μ := κ x) (p := fun z => z = x) hb.aemeasurable
    rw [hx]
    simp
  calc
    (∫ y, (base ⁻¹' B).indicator f y ∂κ x) =
        ∫ y, B.indicator (fun _ => f y) x ∂κ x := by
      apply integral_congr_ae
      filter_upwards [hbase] with y hy
      by_cases hxB : x ∈ B
      · have hyB : y ∈ base ⁻¹' B := by
          change base y ∈ B
          rw [hy]
          exact hxB
        rw [Set.indicator_of_mem hyB, Set.indicator_of_mem hxB]
      · have hyB : y ∉ base ⁻¹' B := by
          intro h
          exact hxB (hy ▸ h)
        rw [Set.indicator_of_notMem hyB, Set.indicator_of_notMem hxB]
    _ = B.indicator (fun x => ∫ y, f y ∂κ x) x := by
      by_cases hxB : x ∈ B <;> simp [Set.indicator, hxB]

private lemma gaussian_condExp_bind_recording {X Y : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    [IsFiniteMeasure (μ.bind κ)]
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x)
    (f : Y → ℝ) (hf : Integrable f (μ.bind κ))
    (g : X → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun y => g (base y)) (μ.bind κ))
    (hmean : ∀ᵐ x ∂μ, (∫ y, f y ∂κ x) = g x) :
    (μ.bind κ)[f | MeasurableSpace.comap base inferInstance] =ᵐ[μ.bind κ]
      fun y => g (base y) := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hb.comap_le hf
  · intro s _ _
    exact hgi.integrableOn
  · intro s hs _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [gaussian_setIntegral_bind_recording μ κ base hκ hb hr _ hgi B hB,
      gaussian_setIntegral_bind_recording μ κ base hκ hb hr _ hf B hB]
    apply setIntegral_congr_ae hB
    filter_upwards [hr, hmean] with x hx hmx hxB
    rw [← integral_map_of_stronglyMeasurable hb hg.stronglyMeasurable, hx,
      integral_dirac]
    exact hmx.symm
  · exact (hg.comp (comap_measurable base)).stronglyMeasurable.aestronglyMeasurable

private lemma gaussianAnchorLaw_integrable_score (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    Integrable (fun u : UnitRecord d => g u.1) (gaussianAnchorLaw g v) := by
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  have hmem : MemLp g 2 (cubeMeasure d) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2
  have _hint : Integrable g (cubeMeasure d) := hmem.integrable one_le_two
  have hmap : Integrable g ((gaussianAnchorLaw g v).map Prod.fst) := by
    rwa [gaussianAnchorLaw_map_fst g v hg]
  change Integrable (g ∘ Prod.fst) (gaussianAnchorLaw g v)
  exact hmap.comp_measurable measurable_fst

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the control regression equals the
common conditional mean almost everywhere](goal). -/
lemma gaussianAnchorLaw_regression0 (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    regression0 (gaussianAnchorLaw g v) =ᵐ[gaussianAnchorLaw g v] fun u => g u.1 := by
  letI : IsProbabilityMeasure (gaussianAnchorLaw g v) :=
    gaussianAnchorLaw_isProbabilityMeasure g v hg
  unfold regression0 gaussianAnchorLaw
  letI : IsFiniteMeasure ((cubeMeasure d).bind (gaussianAnchorFiber g v)) := by
    rw [← gaussianAnchorLaw]
    infer_instance
  apply gaussian_condExp_bind_recording (cubeMeasure d) (gaussianAnchorFiber g v) Prod.fst
    (measurable_gaussianAnchorFiber g v hg) measurable_fst
  · exact Filter.Eventually.of_forall (gaussianAnchorFiber_map_fst g v)
  · exact (gaussianAnchorLaw_memLp_y0 g v hg hg2).integrable one_le_two
  · exact hg
  · exact gaussianAnchorLaw_integrable_score g v hg hg2
  · exact Filter.Eventually.of_forall (gaussianAnchorFiber_integral_y0 g v)

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the treated regression equals the
common conditional mean almost everywhere](goal). -/
lemma gaussianAnchorLaw_regression1 (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    regression1 (gaussianAnchorLaw g v) =ᵐ[gaussianAnchorLaw g v] fun u => g u.1 := by
  letI : IsProbabilityMeasure (gaussianAnchorLaw g v) :=
    gaussianAnchorLaw_isProbabilityMeasure g v hg
  unfold regression1 gaussianAnchorLaw
  letI : IsFiniteMeasure ((cubeMeasure d).bind (gaussianAnchorFiber g v)) := by
    rw [← gaussianAnchorLaw]
    infer_instance
  apply gaussian_condExp_bind_recording (cubeMeasure d) (gaussianAnchorFiber g v) Prod.fst
    (measurable_gaussianAnchorFiber g v hg) measurable_fst
  · exact Filter.Eventually.of_forall (gaussianAnchorFiber_map_fst g v)
  · exact (gaussianAnchorLaw_memLp_y1 g v hg hg2).integrable one_le_two
  · exact hg
  · exact gaussianAnchorLaw_integrable_score g v hg hg2
  · exact Filter.Eventually.of_forall (gaussianAnchorFiber_integral_y1 g v)

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), and [a
square-integrable mean on the cube](hyp:hg2), [the common Gaussian conditional mean
is a half-sum regression version](goal). -/
lemma gaussianAnchorLaw_isHalfSumVersion (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d)) :
    IsHalfSumVersion (gaussianAnchorLaw g v) g := by
  filter_upwards [gaussianAnchorLaw_regression0 g v hg hg2,
    gaussianAnchorLaw_regression1 g v hg hg2] with u h0 h1
  rw [h0, h1]
  ring

private lemma gaussian_cubeMeasure_ae_mem (d : ℕ) :
    ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
  unfold cubeMeasure
  exact ae_restrict_mem (by unfold cube; measurability)

/-- A [measurable score](hyp:g,hg) with [nonnegative exponent](hyp:β,hβ) and [the
radius-one Hölder property](hyp:hholder) [is square-integrable under uniform cube
measure](goal). -/
lemma holderScore_integrable_sq_cube (g : XSpace d → ℝ) (β : ℝ)
    (hg : Measurable g) (hβ : 0 ≤ β) (hholder : HolderScore g 1 β) :
    Integrable (fun x => (g x) ^ 2) (cubeMeasure d) := by
  let z : XSpace d := 0
  have hz : z ∈ cube d := by
    intro i
    simp [z]
  let C : ℝ := |g z| + (d : ℝ) ^ (β / 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound (x : XSpace d) (hx : x ∈ cube d) : |g x| ≤ C := by
    have hosc := holder_score_cube_oscillation g (L := 1) (β := β)
      (by norm_num) hβ hholder x z hx hz
    simp only [one_mul] at hosc
    calc
      |g x| = |(g x - g z) + g z| := by ring_nf
      _ ≤ |g x - g z| + |g z| := abs_add_le _ _
      _ ≤ (d : ℝ) ^ (β / 2) + |g z| := add_le_add hosc le_rfl
      _ = C := by dsimp [C]; ring
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  refine (integrable_const (C ^ 2)).mono' (by fun_prop) ?_
  filter_upwards [gaussian_cubeMeasure_ae_mem d] with x hx
  have hs := (sq_le_sq₀ (abs_nonneg (g x)) hC).2 (hbound x hx)
  simpa [sq_abs] using hs

/-- Given [a measurable conditional mean](hyp:g,hg), [a variance](hyp:v), [a lower
density bound at most one](hyp:hcX), and [an upper density bound at least one](hyp:hCX),
[the Gaussian anchor law satisfies the required covariate-density condition](goal). -/
lemma gaussianAnchorLaw_covariateDensity (g : XSpace d → ℝ) (v : NNReal)
    (hg : Measurable g) (hcX : cX ≤ 1) (hCX : 1 ≤ CX) :
    CovariateDensity (gaussianAnchorLaw g v) cX CX := by
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  refine ⟨gaussianAnchorLaw_isProbabilityMeasure g v hg, ?_, ?_⟩
  · rw [gaussianAnchorLaw_map_fst g v hg]
  · rw [gaussianAnchorLaw_map_fst g v hg]
    filter_upwards [Measure.rnDeriv_self (cubeMeasure d)] with x hx
    rw [hx]
    simpa using And.intro hcX hCX

/-- Given [a conditional mean and finite variance](hyp:g,v), [nondegenerate
variance](hyp:hv), [measurability of the mean](hyp:hg), [valid anchor
parameters](hyp:hpars), and [the radius-one Hölder property](hyp:hholder), [the
canonical anchor-class witness for the Gaussian law uses the supplied mean itself
as its score version](goal). -/
noncomputable def gaussianAnchorClass (g : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (hg : Measurable g)
    (hpars : ValidAnchorParameters d β cX CX) (hholder : HolderScore g 1 β) :
    AnchorClass (gaussianAnchorLaw g v) β cX CX := by
  have _hvpos : 0 < v := pos_iff_ne_zero.mpr hv
  have hg2 : Integrable (fun x => (g x) ^ 2) (cubeMeasure d) :=
    holderScore_integrable_sq_cube g β hg (le_of_lt hpars.2.1) hholder
  refine ⟨hpars,
    gaussianAnchorLaw_covariateDensity g v hg hpars.2.2.2.2.1 hpars.2.2.2.2.2,
    gaussianAnchorLaw_secondMoment0 g v hg hg2,
    gaussianAnchorLaw_secondMoment1 g v hg hg2, ?_⟩
  exact ⟨g, gaussianAnchorLaw_isHalfSumVersion g v hg hg2, hholder⟩

/-- Given [a conditional mean and finite variance](hyp:g,v), [nondegenerate
variance](hyp:hv), [measurability of the mean](hyp:hg), [valid anchor
parameters](hyp:hpars), and [the radius-one Hölder property](hyp:hholder), [the
Gaussian anchor law is an admissible member of the anchor class](goal). -/
-- keep: public constructor packaging a Gaussian anchor law as an AnchorClass member
lemma gaussianAnchorLaw_anchorClass (g : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (hg : Measurable g)
    (hpars : ValidAnchorParameters d β cX CX) (hholder : HolderScore g 1 β) :
    AnchorClass (gaussianAnchorLaw g v) β cX CX :=
  gaussianAnchorClass g v hv hg hpars hholder

end CausalSmith.Experimentation.PilotscorePairingFrontier
