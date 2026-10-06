module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Causalean.Mathlib.InformationTheory.KLBind
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Mathlib.MeasureTheory.IntegralBind
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Bernoulli hypercube witnesses

This file supplies the probability, support, regression, covariate-marginal, and
information-theoretic facts for the Bernoulli potential-outcome witnesses used by
the pilot-score pairing lower bound.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

private lemma bernoulliOutcomeLaw_eq_bernoulliLaw (p : ℝ) :
    bernoulliOutcomeLaw p = Causalean.Mathlib.Probability.bernoulliLaw p := by
  simp only [bernoulliOutcomeLaw, Causalean.Mathlib.Probability.bernoulliLaw]
  ac_rfl

/-- Lebesgue measure restricted to the finite unit cube has total mass one. -/
lemma cubeMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (cubeMeasure d) := by
  constructor
  have hcube : MeasurableSet (cube d) := by
    unfold cube
    measurability
  rw [cubeMeasure, Measure.restrict_apply_univ]
  · rw [show cube d = Set.univ.pi fun _ : Fin d => Icc (0 : ℝ) 1 by
      ext x
      constructor
      · intro hx i _
        exact hx i
      · intro hx i
        exact hx i (Set.mem_univ i)]
    rw [Measure.pi_pi]
    simp [Real.volume_Icc]

private lemma cubeMeasure_ae_mem (d : ℕ) :
    ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
  unfold cubeMeasure
  exact ae_restrict_mem (by unfold cube; measurability)

private lemma setIntegral_bind_recording {X Y : Type*} [MeasurableSpace X]
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

private lemma condExp_bind_recording {X Y : Type*} [MeasurableSpace X]
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
    rw [setIntegral_bind_recording μ κ base hκ hb hr _ hgi B hB,
      setIntegral_bind_recording μ κ base hκ hb hr _ hf B hB]
    apply setIntegral_congr_ae hB
    filter_upwards [hr, hmean] with x hx hmx hxB
    rw [← integral_map_of_stronglyMeasurable hb hg.stronglyMeasurable, hx,
      integral_dirac]
    exact hmx.symm
  · exact (hg.comp (comap_measurable base)).stronglyMeasurable.aestronglyMeasurable

private noncomputable def bernoulliUnitFiber (g : XSpace d → ℝ) (x : XSpace d) :
    Measure (UnitRecord d) :=
  let q0 := ENNReal.ofReal (1 - g x)
  let q1 := ENNReal.ofReal (g x)
  (q0 * q0) • Measure.dirac (x, (0 : ℝ), (0 : ℝ)) +
    (q0 * q1) • Measure.dirac (x, (0 : ℝ), (1 : ℝ)) +
    (q1 * q0) • Measure.dirac (x, (1 : ℝ), (0 : ℝ)) +
    (q1 * q1) • Measure.dirac (x, (1 : ℝ), (1 : ℝ))

private lemma measurable_bernoulliUnitFiber (g : XSpace d → ℝ) (hg : Measurable g) :
    Measurable (bernoulliUnitFiber g) := by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [bernoulliUnitFiber, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  fun_prop

private lemma bernoulliUnitFiber_eq (g : XSpace d → ℝ) (x : XSpace d) :
    bernoulliUnitFiber g x =
      ((bernoulliOutcomeLaw (g x)).prod (bernoulliOutcomeLaw (g x))).map
        fun ys => (x, ys.1, ys.2) := by
  unfold bernoulliUnitFiber bernoulliOutcomeLaw
  rw [← Measure.dirac_prod]
  simp only [Measure.prod_add, Measure.add_prod, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.dirac_prod_dirac]
  simp only [smul_add, smul_smul]
  module

private lemma bernoulliUnitLaw_eq_bind_fiber (g : XSpace d → ℝ) :
    bernoulliUnitLaw g = (cubeMeasure d).bind (bernoulliUnitFiber g) := by
  unfold bernoulliUnitLaw bernoulliUnitFiber
  congr 1
  funext x
  exact (bernoulliUnitFiber_eq g x).symm

/-- A measurable score valued in `[0,1]` on the cube induces a probability law. -/
lemma bernoulliUnitLaw_isProbabilityMeasure (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    IsProbabilityMeasure (bernoulliUnitLaw g) := by
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  rw [bernoulliUnitLaw_eq_bind_fiber]
  apply MeasureTheory.isProbabilityMeasure_bind
    (measurable_bernoulliUnitFiber g hg).aemeasurable
  filter_upwards [cubeMeasure_ae_mem d] with x hx
  have hp := hrange x hx
  rw [bernoulliUnitFiber_eq, bernoulliOutcomeLaw_eq_bernoulliLaw]
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw (g x)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp.1 hp.2
  have hf : AEMeasurable (fun ys : ℝ × ℝ => (x, ys.1, ys.2))
      ((Causalean.Mathlib.Probability.bernoulliLaw (g x)).prod
        (Causalean.Mathlib.Probability.bernoulliLaw (g x))) :=
    (by fun_prop : Measurable fun ys : ℝ × ℝ => (x, ys.1, ys.2)).aemeasurable
  exact Measure.isProbabilityMeasure_map hf

private lemma bernoulliUnitFiber_map_fst (g : XSpace d → ℝ) (x : XSpace d)
    (hp0 : 0 ≤ g x) (hp1 : g x ≤ 1) :
    (bernoulliUnitFiber g x).map Prod.fst = Measure.dirac x := by
  rw [bernoulliUnitFiber_eq, bernoulliOutcomeLaw_eq_bernoulliLaw]
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw (g x)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp0 hp1
  rw [Measure.map_map]
  · have hc := Measure.map_const
      ((Causalean.Mathlib.Probability.bernoulliLaw (g x)).prod
        (Causalean.Mathlib.Probability.bernoulliLaw (g x))) x
    rw [measure_univ, one_smul] at hc
    rw [show Prod.fst ∘ (fun ys : ℝ × ℝ => (x, ys.1, ys.2)) =
        (fun _ : ℝ × ℝ => x) by
      funext ys
      rfl]
    exact hc
  · fun_prop
  · fun_prop

private lemma bernoulliUnitFiber_integral_y0 (g : XSpace d → ℝ) (x : XSpace d)
    (hp0 : 0 ≤ g x) (hp1 : g x ≤ 1) :
    ∫ u, u.2.1 ∂bernoulliUnitFiber g x = g x := by
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw (g x)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp0 hp1
  rw [bernoulliUnitFiber_eq, bernoulliOutcomeLaw_eq_bernoulliLaw]
  rw [integral_map (by fun_prop)]
  change (∫ ys : ℝ × ℝ, ys.1 ∂
    (Causalean.Mathlib.Probability.bernoulliLaw (g x)).prod
      (Causalean.Mathlib.Probability.bernoulliLaw (g x))) = g x
  rw [integral_fun_fst (μ := Causalean.Mathlib.Probability.bernoulliLaw (g x))
    (ν := Causalean.Mathlib.Probability.bernoulliLaw (g x)) (fun y : ℝ => y)]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  simpa using Causalean.Mathlib.Probability.bernoulliLaw_integral hp0 hp1 id
  all_goals fun_prop

private lemma bernoulliUnitFiber_integral_y1 (g : XSpace d → ℝ) (x : XSpace d)
    (hp0 : 0 ≤ g x) (hp1 : g x ≤ 1) :
    ∫ u, u.2.2 ∂bernoulliUnitFiber g x = g x := by
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw (g x)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp0 hp1
  rw [bernoulliUnitFiber_eq, bernoulliOutcomeLaw_eq_bernoulliLaw]
  rw [integral_map (by fun_prop)]
  change (∫ ys : ℝ × ℝ, ys.2 ∂
    (Causalean.Mathlib.Probability.bernoulliLaw (g x)).prod
      (Causalean.Mathlib.Probability.bernoulliLaw (g x))) = g x
  rw [integral_fun_snd (μ := Causalean.Mathlib.Probability.bernoulliLaw (g x))
    (ν := Causalean.Mathlib.Probability.bernoulliLaw (g x)) (fun y : ℝ => y)]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  simpa using Causalean.Mathlib.Probability.bernoulliLaw_integral hp0 hp1 id
  all_goals fun_prop

/-- The covariate marginal of the Bernoulli unit law is uniform cube measure. -/
lemma bernoulliUnitLaw_map_fst (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    (bernoulliUnitLaw g).map Prod.fst = cubeMeasure d := by
  rw [bernoulliUnitLaw_eq_bind_fiber]
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.bind_apply (measurable_fst hs) (measurable_bernoulliUnitFiber g hg).aemeasurable]
  have hpoint : ∀ᵐ x ∂cubeMeasure d,
      bernoulliUnitFiber g x (Prod.fst ⁻¹' s) = s.indicator 1 x := by
    filter_upwards [cubeMeasure_ae_mem d] with x hx
    have hp := hrange x hx
    have hm := congrArg (fun μ : Measure (XSpace d) => μ s)
      (bernoulliUnitFiber_map_fst g x hp.1 hp.2)
    rw [Measure.map_apply measurable_fst hs, Measure.dirac_apply' _ hs] at hm
    simpa [Set.indicator_apply] using hm
  rw [lintegral_congr_ae hpoint, lintegral_indicator hs]
  simp

/-- Both potential outcomes of a Bernoulli unit lie in `[0,1]` almost surely. -/
lemma bernoulliUnitLaw_boundedOutcomes (g : XSpace d → ℝ) (hg : Measurable g) :
    BoundedOutcomes (bernoulliUnitLaw g) := by
  rw [bernoulliUnitLaw_eq_bind_fiber]
  let bad : Set (UnitRecord d) :=
    {u | ¬(u.2.1 ∈ Icc (0 : ℝ) 1 ∧ u.2.2 ∈ Icc (0 : ℝ) 1)}
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    measurability
  have hzero (x : XSpace d) : bernoulliUnitFiber g x bad = 0 := by
    simp only [bernoulliUnitFiber, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hbad, smul_eq_mul]
    simp [bad]
  change ((cubeMeasure d).bind (bernoulliUnitFiber g)) bad = 0
  rw [Measure.bind_apply hbad (measurable_bernoulliUnitFiber g hg).aemeasurable]
  simp [hzero]

private lemma bernoulliUnitLaw_integrable_y0 (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (fun u : UnitRecord d => u.2.1) (bernoulliUnitLaw g) := by
  letI : IsProbabilityMeasure (bernoulliUnitLaw g) :=
    bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [bernoulliUnitLaw_boundedOutcomes g hg] with u hu
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩

private lemma bernoulliUnitLaw_integrable_y1 (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (fun u : UnitRecord d => u.2.2) (bernoulliUnitLaw g) := by
  letI : IsProbabilityMeasure (bernoulliUnitLaw g) :=
    bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [bernoulliUnitLaw_boundedOutcomes g hg] with u hu
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩

private lemma bernoulliUnitLaw_integrable_score (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (fun u : UnitRecord d => g u.1) (bernoulliUnitLaw g) := by
  letI : IsProbabilityMeasure (bernoulliUnitLaw g) :=
    bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  refine (integrable_const (1 : ℝ)).mono'
    (hg.comp measurable_fst).aestronglyMeasurable ?_
  have hcube : ∀ᵐ u ∂bernoulliUnitLaw g, u.1 ∈ cube d := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [bernoulliUnitLaw_map_fst g hg hrange]
    exact cubeMeasure_ae_mem d
  filter_upwards [hcube] with u hu
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [(hrange u.1 hu).1], (hrange u.1 hu).2⟩

/-- The control regression of a Bernoulli unit law is its score. -/
lemma bernoulliUnitLaw_regression0 (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    regression0 (bernoulliUnitLaw g) =ᵐ[bernoulliUnitLaw g] fun u => g u.1 := by
  letI : IsProbabilityMeasure (bernoulliUnitLaw g) :=
    bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  unfold regression0
  rw [bernoulliUnitLaw_eq_bind_fiber]
  letI : IsFiniteMeasure ((cubeMeasure d).bind (bernoulliUnitFiber g)) := by
    rw [← bernoulliUnitLaw_eq_bind_fiber]
    infer_instance
  apply condExp_bind_recording (cubeMeasure d) (bernoulliUnitFiber g) Prod.fst
    (measurable_bernoulliUnitFiber g hg) measurable_fst
  · filter_upwards [cubeMeasure_ae_mem d] with x hx
    exact bernoulliUnitFiber_map_fst g x (hrange x hx).1 (hrange x hx).2
  · simpa [bernoulliUnitLaw_eq_bind_fiber] using
      bernoulliUnitLaw_integrable_y0 g hg hrange
  · exact hg
  · simpa [bernoulliUnitLaw_eq_bind_fiber] using
      bernoulliUnitLaw_integrable_score g hg hrange
  · filter_upwards [cubeMeasure_ae_mem d] with x hx
    exact bernoulliUnitFiber_integral_y0 g x (hrange x hx).1 (hrange x hx).2

/-- The treated regression of a Bernoulli unit law is its score. -/
lemma bernoulliUnitLaw_regression1 (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    regression1 (bernoulliUnitLaw g) =ᵐ[bernoulliUnitLaw g] fun u => g u.1 := by
  letI : IsProbabilityMeasure (bernoulliUnitLaw g) :=
    bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  unfold regression1
  rw [bernoulliUnitLaw_eq_bind_fiber]
  letI : IsFiniteMeasure ((cubeMeasure d).bind (bernoulliUnitFiber g)) := by
    rw [← bernoulliUnitLaw_eq_bind_fiber]
    infer_instance
  apply condExp_bind_recording (cubeMeasure d) (bernoulliUnitFiber g) Prod.fst
    (measurable_bernoulliUnitFiber g hg) measurable_fst
  · filter_upwards [cubeMeasure_ae_mem d] with x hx
    exact bernoulliUnitFiber_map_fst g x (hrange x hx).1 (hrange x hx).2
  · simpa [bernoulliUnitLaw_eq_bind_fiber] using
      bernoulliUnitLaw_integrable_y1 g hg hrange
  · exact hg
  · simpa [bernoulliUnitLaw_eq_bind_fiber] using
      bernoulliUnitLaw_integrable_score g hg hrange
  · filter_upwards [cubeMeasure_ae_mem d] with x hx
    exact bernoulliUnitFiber_integral_y1 g x (hrange x hx).1 (hrange x hx).2

/-- The score is a half-sum version because both Bernoulli regressions equal it. -/
lemma bernoulliUnitLaw_isHalfSumVersion (g : XSpace d → ℝ)
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1) :
    IsHalfSumVersion (bernoulliUnitLaw g) g := by
  filter_upwards [bernoulliUnitLaw_regression0 g hg hrange,
    bernoulliUnitLaw_regression1 g hg hrange] with u h0 h1
  rw [h0, h1]
  ring

private lemma fairCoin_isProbabilityMeasure : IsProbabilityMeasure fairCoin := by
  constructor
  simpa [fairCoin] using ENNReal.inv_two_add_inv_two

private lemma observedPilot_measurable :
    Measurable (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) := by
  unfold observedPilot
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.ite
  · exact measurable_snd (measurableSet_singleton true)
  · fun_prop
  · fun_prop

private lemma pilotUnitLaw_isProbabilityMeasure (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P) : IsProbabilityMeasure (pilotUnitLaw P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure fairCoin := fairCoin_isProbabilityMeasure
  unfold pilotUnitLaw
  apply Measure.isProbabilityMeasure_map
  exact observedPilot_measurable.aemeasurable

/-- Observing one randomized pilot response cannot increase unit-law KL divergence. -/
lemma pilotUnitLaw_klDiv_le (P Q : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P) (hQ : IsProbabilityMeasure Q) :
    InformationTheory.klDiv (pilotUnitLaw P) (pilotUnitLaw Q) ≤
      InformationTheory.klDiv P Q := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure fairCoin := fairCoin_isProbabilityMeasure
  have hm : Measurable (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) :=
    observedPilot_measurable
  calc
    InformationTheory.klDiv (pilotUnitLaw P) (pilotUnitLaw Q) =
        InformationTheory.klDiv ((P.prod fairCoin).map
          (fun ua => observedPilot ua.1 ua.2))
          ((Q.prod fairCoin).map (fun ua => observedPilot ua.1 ua.2)) := by
      rfl
    _ ≤ InformationTheory.klDiv (P.prod fairCoin) (Q.prod fairCoin) :=
      InformationTheory.klDiv_map_le _ _ hm
    _ = InformationTheory.klDiv P Q := by
      simpa only [Measure.compProd_const] using
        (InformationTheory.klDiv_compProd_left P Q
          (ProbabilityTheory.Kernel.const (UnitRecord d) fairCoin))

private lemma bernoulliUnitFiber_klDiv_le (g g' : XSpace d → ℝ) (x : XSpace d)
    (hglo : 1 / 4 ≤ g x) (hghi : g x ≤ 3 / 4)
    (hg'lo : 1 / 4 ≤ g' x) (hg'hi : g' x ≤ 3 / 4) :
    InformationTheory.klDiv (bernoulliUnitFiber g x) (bernoulliUnitFiber g' x) ≤
      ENNReal.ofReal (8 * (g x - g' x) ^ 2) := by
  let μ := Causalean.Mathlib.Probability.bernoulliLaw (g x)
  let ν := Causalean.Mathlib.Probability.bernoulliLaw (g' x)
  letI : IsProbabilityMeasure μ :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  letI : IsProbabilityMeasure ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  have hac : μ ≪ ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
      (by linarith) (by linarith)
  have hint : Integrable (llr μ ν) μ :=
    Causalean.Mathlib.Probability.bernoulliLaw_llr_integrable
  have hprod := Causalean.Mathlib.InformationTheory.ProductKL.klDiv_prod_toReal_add
    μ ν μ ν hac hac hint hint
  have hbern := Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
    hglo hghi hg'lo hg'hi
  have hbern_fin : InformationTheory.klDiv μ ν ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac hint
  have hprod_fin : InformationTheory.klDiv (μ.prod μ) (ν.prod ν) ≠ ⊤ := by
    exact InformationTheory.klDiv_ne_top_iff.mpr
      ⟨hac.prod hac,
        Causalean.Mathlib.InformationTheory.ProductKL.llr_prod_integrable
          μ ν μ ν hac hac hint hint⟩
  rw [bernoulliUnitFiber_eq, bernoulliUnitFiber_eq,
    bernoulliOutcomeLaw_eq_bernoulliLaw, bernoulliOutcomeLaw_eq_bernoulliLaw]
  have hemb : MeasurableEmbedding (fun ys : ℝ × ℝ => (x, ys.1, ys.2)) := by
    simpa only using (measurableEmbedding_prodMk_left x)
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding hemb]
  rw [← ENNReal.ofReal_toReal hprod_fin]
  apply ENNReal.ofReal_le_ofReal
  rw [hprod]
  have hreal : (InformationTheory.klDiv μ ν).toReal ≤ 4 * (g x - g' x) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbern
  linarith

/-- A one-unit KL budget lifts through pilot observation and an iid pilot product. -/
lemma bernoulliPilotProduct_klDiv_le_of_unit
    (m : ℕ) (g g' : XSpace d → ℝ)
    (hg : Measurable g) (hg' : Measurable g')
    (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1)
    (hrange' : ∀ x ∈ cube d, 0 ≤ g' x ∧ g' x ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hunit : InformationTheory.klDiv (bernoulliUnitLaw g)
      (bernoulliUnitLaw g') ≤ ENNReal.ofReal B) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw g))
      (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw g')) ≤
        ENNReal.ofReal ((m : ℝ) * B) := by
  let P := pilotUnitLaw (bernoulliUnitLaw g)
  let Q := pilotUnitLaw (bernoulliUnitLaw g')
  letI : IsProbabilityMeasure (bernoulliUnitLaw g) :=
    bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  letI : IsProbabilityMeasure (bernoulliUnitLaw g') :=
    bernoulliUnitLaw_isProbabilityMeasure g' hg' hrange'
  letI : IsProbabilityMeasure P :=
    pilotUnitLaw_isProbabilityMeasure _ inferInstance
  letI : IsProbabilityMeasure Q :=
    pilotUnitLaw_isProbabilityMeasure _ inferInstance
  have hone : InformationTheory.klDiv P Q ≤ ENNReal.ofReal B :=
    (pilotUnitLaw_klDiv_le _ _ inferInstance inferInstance).trans hunit
  have hone_fin : InformationTheory.klDiv P Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hone
  obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp hone_fin
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization m P Q hac hint
  rw [← ENNReal.ofReal_toReal ht.1]
  apply ENNReal.ofReal_le_ofReal
  calc
    (InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => P)
      (Measure.pi fun _ : Fin m => Q)).toReal
        ≤ (m : ℝ) * (InformationTheory.klDiv P Q).toReal := ht.2.2
    _ ≤ (m : ℝ) * B := by
      gcongr
      exact ENNReal.toReal_le_of_le_ofReal hB hone

end CausalSmith.Experimentation.PilotscorePairingFrontier
