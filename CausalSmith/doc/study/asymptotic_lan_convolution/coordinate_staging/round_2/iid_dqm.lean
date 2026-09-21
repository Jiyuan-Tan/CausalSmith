/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Estimation.Efficiency.AsymptoticLanConvolution.TriangularArray
import Causalean.Estimation.Efficiency.AsymptoticLanConvolution.LogTaylor
import Causalean.Stat.CLT.GaussianLimit
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Probability.Independence.InfinitePi

/-!
# Dominated i.i.d. quadratic-mean differentiability

This module defines dominated finite-dimensional i.i.d. models, quadratic-mean differentiability,
their score information, and the product-likelihood ingredients for local asymptotic normality.
The closing LAN theorem and remaining triangular-array argument are in `IIDDQMLAN`.
-/

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory Topology
open scoped RealInnerProductSpace

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- A dominated finite-dimensional i.i.d. model is a probability law `law θ` for every parameter
`θ`, together with one common dominating measure.  The base parameter is `0`. -/
structure DominatedIIDModel (X H : Type*) [MeasurableSpace X] where
  /-- Observation law at parameter `θ`. -/
  law : H → Measure X
  /-- Every observation law has total mass one. -/
  probability : ∀ θ, IsProbabilityMeasure (law θ)
  /-- Common dominating measure used to state DQM. -/
  dominating : Measure X
  /-- The dominating measure is sigma-finite, so its Radon--Nikodym densities represent the
  model laws. -/
  dominating_sigmaFinite : SigmaFinite dominating
  /-- Every model law is absolutely continuous with respect to the dominating measure. -/
  absolutelyContinuous : ∀ θ, law θ ≪ dominating

namespace DominatedIIDModel

/-- The square root of the density of `law θ` with respect to the model's dominating measure. -/
noncomputable def sqrtDensity (M : DominatedIIDModel X H) (θ : H) (x : X) : ℝ :=
  Real.sqrt ((M.law θ).rnDeriv M.dominating x).toReal

/-- The `n`-observation i.i.d. law is the finite product of the one-observation law. -/
noncomputable def iidLaw (M : DominatedIIDModel X H) (θ : H) (n : ℕ) :
    Measure (Fin n → X) :=
  Measure.pi (fun _ : Fin n => M.law θ)

end DominatedIIDModel

/-- Quadratic-mean differentiability at the base parameter `0` with score `score`.  The squared
`L²` error in the first-order square-root-density expansion is little-o of `‖h‖²`, and the score
is measurable and square-integrable under the base law. -/
structure IIDQuadraticMeanDifferentiable (M : DominatedIIDModel X H) where
  /-- Vector score at the base parameter. -/
  score : X → H
  /-- Measurability of the score. -/
  score_measurable : Measurable score
  /-- Square integrability of the score under the base observation law. -/
  score_squareIntegrable : Integrable (fun x => ‖score x‖ ^ 2) (M.law 0)
  /-- The defining quadratic-mean expansion of the square-root densities. -/
  expansion :
    (fun h => ∫ x,
      (M.sqrtDensity h x - M.sqrtDensity 0 x -
        (1 / 2 : ℝ) * inner ℝ h (score x) * M.sqrtDensity 0 x) ^ 2 ∂M.dominating)
      =o[𝓝 0] fun h : H => ‖h‖ ^ 2

namespace IIDQuadraticMeanDifferentiable

variable {M : DominatedIIDModel X H}

/-- Fisher information is the bilinear second moment of the DQM score. -/
noncomputable def information (M : DominatedIIDModel X H)
    (qmd : IIDQuadraticMeanDifferentiable M) : LinearMap.BilinForm ℝ H :=
  LinearMap.mk₂ ℝ
    (fun h g => inner ℝ
      (Causalean.Stat.secondMomentLM qmd.score_measurable qmd.score_squareIntegrable h) g)
    (by intros; rw [map_add, inner_add_left])
    (by intros; rw [map_smul, inner_smul_left]; simp)
    (by intros; rw [inner_add_right])
    (by intros; simp only [inner_smul_right, smul_eq_mul])

/-- Evaluating the Fisher-information form gives the second moment of the two scalar score
projections. -/
theorem information_apply (qmd : IIDQuadraticMeanDifferentiable M) (h g : H) :
    qmd.information M h g =
      ∫ x, inner ℝ h (qmd.score x) * inner ℝ g (qmd.score x) ∂M.law 0 := by
  rw [information]
  exact Causalean.Stat.secondMomentLM_inner
    qmd.score_measurable qmd.score_squareIntegrable h g

/-- The normalized score sum on the canonical `n`-fold product sample. -/
noncomputable def centralSequence (qmd : IIDQuadraticMeanDifferentiable M)
    (n : ℕ) (x : Fin n → X) : H :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i, qmd.score (x i)

/-- DQM forces the score to have mean zero under the base law.  This is the normalization
identity obtained by differentiating the total mass of the model. -/
theorem score_integral_eq_zero (qmd : IIDQuadraticMeanDifferentiable M) :
    ∫ x, qmd.score x ∂M.law 0 = 0 := by
  -- Proof plan: expand equality of the two density masses along `t • h`, divide the
  -- square-root-density identity by `t`, use the DQM `L²` remainder and Cauchy--Schwarz,
  -- then separate vectors by inner products.
  letI : SigmaFinite M.dominating := M.dominating_sigmaFinite
  have hsqrt_sq (θ : H) :
      ∫ x, M.sqrtDensity θ x ^ 2 ∂M.dominating = 1 := by
    let _ : IsProbabilityMeasure (M.law θ) := M.probability θ
    have hpoint : (fun x => M.sqrtDensity θ x ^ 2) =ᵐ[M.dominating]
        fun x => ((M.law θ).rnDeriv M.dominating x).toReal := by
      filter_upwards [] with x
      exact Real.sq_sqrt ENNReal.toReal_nonneg
    rw [integral_congr_ae hpoint, Measure.integral_toReal_rnDeriv
      (M.absolutelyContinuous θ)]
    simp
  have hp_mem (θ : H) : MemLp (M.sqrtDensity θ) 2 M.dominating := by
    have hpmeas : Measurable (M.sqrtDensity θ) := by
      unfold DominatedIIDModel.sqrtDensity
      exact Real.continuous_sqrt.measurable.comp
        (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
    apply (memLp_two_iff_integrable_sq_norm hpmeas.aestronglyMeasurable).2
    let _ : IsProbabilityMeasure (M.law θ) := M.probability θ
    refine (Measure.integrable_toReal_rnDeriv (μ := M.law θ) (ν := M.dominating)).congr ?_
    filter_upwards [] with x
    simp only [DominatedIIDModel.sqrtDensity, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]
  have hproj_int (h : H) :
      Integrable (fun x => inner ℝ h (qmd.score x) ^ 2) (M.law 0) := by
    refine Integrable.mono' (qmd.score_squareIntegrable.const_mul (‖h‖ ^ 2))
      ((qmd.score_measurable.const_inner (c := h)).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simp only [norm_pow, Real.norm_eq_abs]
    calc
      |inner ℝ h (qmd.score x)| ^ 2
          ≤ (‖h‖ * ‖qmd.score x‖) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (abs_real_inner_le_norm h (qmd.score x))
      _ = ‖h‖ ^ 2 * ‖qmd.score x‖ ^ 2 := by ring
  let aRaw (h : H) (x : X) : ℝ :=
    (1 / 2 : ℝ) * inner ℝ h (qmd.score x) * M.sqrtDensity 0 x
  have ha_mem (h : H) : MemLp (aRaw h) 2 M.dominating := by
    have hpmeas : Measurable (M.sqrtDensity 0) := by
      unfold DominatedIIDModel.sqrtDensity
      exact Real.continuous_sqrt.measurable.comp
        (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
    have hameas : Measurable (aRaw h) := by
      unfold aRaw
      exact (qmd.score_measurable.const_inner (c := h)).const_mul (1 / 2) |>.mul hpmeas
    apply (memLp_two_iff_integrable_sq_norm hameas.aestronglyMeasurable).2
    let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
    have hw := (integrable_toReal_rnDeriv_mul_iff
      (M.absolutelyContinuous 0)).2 (hproj_int h)
    refine (hw.const_mul ((1 / 2 : ℝ) ^ 2)).congr ?_
    filter_upwards [] with x
    simp only [aRaw, DominatedIIDModel.sqrtDensity, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num [mul_pow, sq_abs, Real.sq_sqrt ENNReal.toReal_nonneg] <;> ring
  let p (θ : H) : Lp ℝ 2 M.dominating := (hp_mem θ).toLp (M.sqrtDensity θ)
  let a (h : H) : Lp ℝ 2 M.dominating := (ha_mem h).toLp (aRaw h)
  have hnorm_sq_toLp (f : X → ℝ) (hf : MemLp f 2 M.dominating) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂M.dominating := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hnormp (θ : H) : ‖p θ‖ ^ 2 = 1 := by
    change ‖(hp_mem θ).toLp (M.sqrtDensity θ)‖ ^ 2 = 1
    rw [hnorm_sq_toLp]
    exact hsqrt_sq θ
  let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
  have hscore_int : Integrable qmd.score (M.law 0) :=
    ((memLp_two_iff_integrable_sq_norm qmd.score_measurable.aestronglyMeasurable).2
      qmd.score_squareIntegrable).integrable (by norm_num)
  have hinner (h : H) :
      inner ℝ (p 0) (a h) = (1 / 2 : ℝ) * inner ℝ h (∫ x, qmd.score x ∂M.law 0) := by
    change inner ℝ ((hp_mem 0).toLp (M.sqrtDensity 0))
      ((ha_mem h).toLp (aRaw h)) = _
    rw [L2.inner_def]
    have hae := (hp_mem 0).coeFn_toLp.and (ha_mem h).coeFn_toLp
    have hi : (∫ x, inner ℝ (((hp_mem 0).toLp (M.sqrtDensity 0)) x)
          (((ha_mem h).toLp (aRaw h)) x) ∂M.dominating) =
        ∫ x, M.sqrtDensity 0 x * aRaw h x ∂M.dominating := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      simp only [hx.1, hx.2, Real.inner_apply]
    rw [hi]
    calc
      (∫ x, M.sqrtDensity 0 x * aRaw h x ∂M.dominating) =
          (1 / 2 : ℝ) * ∫ x, ((M.law 0).rnDeriv M.dominating x).toReal *
            inner ℝ h (qmd.score x) ∂M.dominating := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [aRaw, DominatedIIDModel.sqrtDensity]
        ring_nf
        rw [Real.sq_sqrt ENNReal.toReal_nonneg]
        ring
      _ = (1 / 2 : ℝ) * ∫ x, inner ℝ h (qmd.score x) ∂M.law 0 := by
        congr 1
        simpa only [smul_eq_mul] using
          (integral_rnDeriv_smul (f := fun x => inner ℝ h (qmd.score x))
            (M.absolutelyContinuous 0))
      _ = (1 / 2 : ℝ) * inner ℝ h (∫ x, qmd.score x ∂M.law 0) := by
        rw [integral_inner hscore_int h]
  have hderiv (h : H) : HasDerivAt (fun t : ℝ => p (t • h)) (a h) 0 := by
    let rRaw (t : ℝ) (x : X) : ℝ :=
      M.sqrtDensity (t • h) x - M.sqrtDensity 0 x - t * aRaw h x
    have hr_mem (t : ℝ) : MemLp (rRaw t) 2 M.dominating := by
      have := ((hp_mem (t • h)).sub (hp_mem 0)).sub ((ha_mem h).const_smul t)
      change MemLp (M.sqrtDensity (t • h) - M.sqrtDensity 0 - t • aRaw h)
        2 M.dominating
      exact this
    have hr_eq (t : ℝ) :
        p (t • h) - p 0 - t • a h = (hr_mem t).toLp (rRaw t) := by
      change (hp_mem (t • h)).toLp (M.sqrtDensity (t • h)) -
          (hp_mem 0).toLp (M.sqrtDensity 0) - t • (ha_mem h).toLp (aRaw h) = _
      rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
      apply MemLp.toLp_congr
      exact ae_of_all _ fun x => rfl
    have hr_norm_sq (t : ℝ) :
        ‖p (t • h) - p 0 - t • a h‖ ^ 2 =
          ∫ x, rRaw t x ^ 2 ∂M.dominating := by
      rw [hr_eq, hnorm_sq_toLp]
    have he : (fun t : ℝ => ∫ x, rRaw t x ^ 2 ∂M.dominating) =o[𝓝 0]
        fun t : ℝ => ‖t • h‖ ^ 2 := by
      have ht : Tendsto (fun t : ℝ => t • h) (𝓝 0) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa only [norm_smul, zero_mul] using tendsto_norm_zero.mul_const ‖h‖
      have hc := qmd.expansion.comp_tendsto ht
      refine hc.congr (fun t => ?_) (fun _ => rfl)
      simp only [Function.comp_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      simp only [rRaw, aRaw, inner_smul_left, starRingEnd_apply, star_trivial]
      ring
    have hs := he.sqrt (Filter.Eventually.of_forall fun t : ℝ => sq_nonneg ‖t • h‖)
    have hsnorm : (fun t : ℝ => ‖p (t • h) - p 0 - t • a h‖) =o[𝓝 0]
        fun t : ℝ => ‖t • h‖ := by
      refine hs.congr (fun t => ?_) (fun t => ?_)
      · rw [← hr_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      · rw [Real.sqrt_sq (norm_nonneg _)]
    have hbig : (fun t : ℝ => ‖t • h‖) =O[𝓝 0] fun t : ℝ => t := by
      apply Asymptotics.IsBigO.of_bound ‖h‖
      filter_upwards [] with t
      simp only [Real.norm_eq_abs, norm_smul]
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact le_of_eq (mul_comm _ _)
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, zero_smul]
    exact (Asymptotics.isLittleO_norm_left.mp (hsnorm.trans_isBigO hbig))
  have horth (h : H) : inner ℝ h (∫ x, qmd.score x ∂M.law 0) = 0 := by
    have hd := (hderiv h).norm_sq
    have hc : HasDerivAt (fun t : ℝ => ‖p (t • h)‖ ^ 2) 0 0 :=
      (hasDerivAt_const (x := 0) (1 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => hnormp (t • h))
    have hu := hd.unique hc
    simp only [zero_smul] at hu
    rw [hinner] at hu
    linarith
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  exact horth (∫ x, qmd.score x ∂M.law 0)

/-- The score second-moment form is symmetric and nonnegative. -/
theorem information_isSymm_nonnegative (qmd : IIDQuadraticMeanDifferentiable M) :
    (qmd.information M).IsSymm ∧ ∀ h, 0 ≤ qmd.information M h h := by
  -- Rewrite with `information_apply`; symmetry is commutativity of multiplication and
  -- nonnegativity is the integral of a square.
  constructor
  · refine ⟨fun h g => ?_⟩
    rw [information_apply, information_apply]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  · intro h
    rw [information_apply]
    exact integral_nonneg fun x => mul_self_nonneg _

/-- Every finite product law of a dominated i.i.d. probability model is a probability measure. -/
theorem iidLaw_probability (M : DominatedIIDModel X H) (θ : H) (n : ℕ) :
    IsProbabilityMeasure (M.iidLaw θ n) := by
  -- Install `M.probability θ` for each `Fin n` coordinate and use the `Measure.pi` instance.
  let _ : ∀ _ : Fin n, IsProbabilityMeasure (M.law θ) := fun _ => M.probability θ
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => M.law θ))
  exact inferInstance

private theorem rnDeriv_prod_measure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) (κ η : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] [IsFiniteMeasure η] :
    (μ.prod κ).rnDeriv (ν.prod η) =ᵐ[ν.prod η]
      fun p => μ.rnDeriv ν p.1 * κ.rnDeriv η p.2 := by
  let ξ := μ + ν
  let ζ := κ + η
  have hμξ : μ ≪ ξ := Measure.AbsolutelyContinuous.rfl.add_right _
  have hνξ : ν ≪ ξ := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hκζ : κ ≪ ζ := Measure.AbsolutelyContinuous.rfl.add_right _
  have hηζ : η ≪ ζ := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hdens (a b : Measure A) (c d : Measure B)
      [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure c] [IsFiniteMeasure d]
      (hab : a ≪ b) (hcd : c ≪ d) :
      (a.prod c).rnDeriv (b.prod d) =ᵐ[b.prod d]
        fun p => a.rnDeriv b p.1 * c.rnDeriv d p.2 := by
    have ha := Measure.withDensity_rnDeriv_eq a b hab
    have hc := Measure.withDensity_rnDeriv_eq c d hcd
    have hprod : a.prod c =
        (b.withDensity (a.rnDeriv b)).prod (d.withDensity (c.rnDeriv d)) := by
      rw [ha, hc]
    rw [hprod, prod_withDensity (Measure.measurable_rnDeriv a b)
      (Measure.measurable_rnDeriv c d)]
    exact Measure.rnDeriv_withDensity (b.prod d)
      (((Measure.measurable_rnDeriv a b).comp measurable_fst).mul
        ((Measure.measurable_rnDeriv c d).comp measurable_snd))
  have hp := hdens μ ξ κ ζ hμξ hκζ
  have hq := hdens ν ξ η ζ hνξ hηζ
  have hbase : ν.prod η ≪ ξ.prod ζ := hνξ.prod hηζ
  have hratio := Measure.rnDeriv_eq_div
    (hμξ.prod hκζ) (hνξ.prod hηζ)
  have hcoord₁ := Measure.rnDeriv_eq_div hμξ hνξ
  have hcoord₂ := Measure.rnDeriv_eq_div hκζ hηζ
  have hc₁ := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := η)).ae_eq_comp hcoord₁
  have hc₂ := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := η)).ae_eq_comp hcoord₂
  have hcpos := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := η)).tendsto_ae
    (Measure.rnDeriv_pos hνξ)
  have hctop := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := η)).tendsto_ae
    (hνξ (Measure.rnDeriv_lt_top ν ξ))
  filter_upwards [hratio, hbase hp, hbase hq, hc₁, hc₂, hcpos, hctop]
    with p hr hp hq hc1 hc2 hcpos hctop
  simp only [Function.comp_apply, Set.mem_preimage, Set.mem_ofPred_eq] at hc1 hc2 hcpos hctop
  rw [hr, hp, hq, hc1, hc2, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hcpos.ne') (Or.inl hctop.ne)]
  ac_rfl

private theorem rnDeriv_pi_const {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∀ n : ℕ, (Measure.pi (fun _ : Fin n => μ)).rnDeriv
      (Measure.pi (fun _ : Fin n => ν)) =ᵐ[Measure.pi (fun _ : Fin n => ν)]
      fun x => ∏ i, μ.rnDeriv ν (x i) := by
  intro n
  induction n with
  | zero =>
      let _ : ∀ _ : Fin 0, IsFiniteMeasure μ := fun _ => inferInstance
      let _ : ∀ _ : Fin 0, IsFiniteMeasure ν := fun _ => inferInstance
      have heq : Measure.pi (fun _ : Fin 0 => μ) = Measure.pi (fun _ : Fin 0 => ν) := by
        rw [Measure.pi_of_empty, Measure.pi_of_empty]
      rw [heq]
      simpa using (Measure.rnDeriv_self (Measure.pi (fun _ : Fin 0 => ν)))
  | succ n ih =>
      let _ : ∀ _ : Fin n, IsFiniteMeasure μ := fun _ => inferInstance
      let _ : ∀ _ : Fin n, IsFiniteMeasure ν := fun _ => inferInstance
      let _ : ∀ _ : Fin (n + 1), IsFiniteMeasure μ := fun _ => inferInstance
      let _ : ∀ _ : Fin (n + 1), IsFiniteMeasure ν := fun _ => inferInstance
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      have hμ := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
      have hν := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
      have hb := rnDeriv_prod_measure μ ν
        (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
      have hitail := (Measure.quasiMeasurePreserving_snd
        (μ := ν) (ν := Measure.pi (fun _ : Fin n => ν))).ae_eq_comp ih
      have hprod : (μ.prod (Measure.pi (fun _ : Fin n => μ))).rnDeriv
          (ν.prod (Measure.pi (fun _ : Fin n => ν))) =ᵐ[
            ν.prod (Measure.pi (fun _ : Fin n => ν))]
          fun p => μ.rnDeriv ν p.1 * ∏ i, μ.rnDeriv ν (p.2 i) := by
        filter_upwards [hb, hitail] with p hp ht
        simp only [Function.comp_apply] at ht
        rw [hp, ht]
      have hpull := hν.quasiMeasurePreserving.ae_eq_comp hprod
      have hmap := e.measurableEmbedding.rnDeriv_map
        (Measure.pi (fun _ : Fin (n + 1) => μ))
        (Measure.pi (fun _ : Fin (n + 1) => ν))
      filter_upwards [hmap, hpull] with x hm hp
      simp only [Function.comp_apply] at hp
      rw [← hm, hμ.map_eq, hν.map_eq, hp, Fin.prod_univ_succ]
      congr 1

/-- The Radon--Nikodym derivative of a finite i.i.d. product law is the product of the
one-observation Radon--Nikodym derivatives (of their absolutely continuous parts).  No
one-observation absolute-continuity assumption is needed. -/
theorem iidLaw_rnDeriv_eq_prod (M : DominatedIIDModel X H) (θ : H) (n : ℕ) :
    (M.iidLaw θ n).rnDeriv (M.iidLaw 0 n) =ᵐ[M.iidLaw 0 n]
      fun x => ∏ i, (M.law θ).rnDeriv (M.law 0) (x i) := by
  -- Induct over `Fin n`, using the binary product Radon--Nikodym formula.  Probability
  -- measures supply every sigma-finiteness instance required by the product theorem.
  let _ : IsProbabilityMeasure (M.law θ) := M.probability θ
  let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
  exact rnDeriv_pi_const (M.law θ) (M.law 0) n

/-- The canonical local experiment of an i.i.d. model uses the base product law at parameter zero
and the local product law at parameter `(sqrt n)⁻¹ • h`. -/
noncomputable def localExperiment (M : DominatedIIDModel X H) :
    LocalExperiment (fun n => Fin n → X) H where
  baseLaw n := M.iidLaw 0 n
  localLaw n h := M.iidLaw ((Real.sqrt (n : ℝ))⁻¹ • h) n
  base_probability n := iidLaw_probability M 0 n
  local_probability n h := iidLaw_probability M ((Real.sqrt (n : ℝ))⁻¹ • h) n
  local_zero n := by simp

/-- Twice the relative square-root likelihood increment for one observation at local
parameter `h / sqrt n`.  It is set to zero on the zero set of the base square-root density;
the local mass of that set is controlled separately. -/
noncomputable def sqrtLikelihoodIncrement (qmd : IIDQuadraticMeanDifferentiable M)
    (n : ℕ) (h : H) (x : X) : ℝ :=
  if M.sqrtDensity 0 x = 0 then 0 else
    2 * (M.sqrtDensity ((Real.sqrt (n : ℝ))⁻¹ • h) x / M.sqrtDensity 0 x - 1)

private noncomputable def dqmRemainder (qmd : IIDQuadraticMeanDifferentiable M)
    (u : H) (x : X) : ℝ :=
  M.sqrtDensity u x - M.sqrtDensity 0 x -
    (1 / 2 : ℝ) * inner ℝ u (qmd.score x) * M.sqrtDensity 0 x

private theorem dqmRemainder_sq_integrable (qmd : IIDQuadraticMeanDifferentiable M)
    (u : H) : Integrable (fun x => qmd.dqmRemainder u x ^ 2) M.dominating := by
  letI : SigmaFinite M.dominating := M.dominating_sigmaFinite
  have hp_mem (v : H) : MemLp (M.sqrtDensity v) 2 M.dominating := by
    have hpmeas : Measurable (M.sqrtDensity v) := by
      unfold DominatedIIDModel.sqrtDensity
      exact Real.continuous_sqrt.measurable.comp
        (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
    apply (memLp_two_iff_integrable_sq_norm hpmeas.aestronglyMeasurable).2
    let _ : IsProbabilityMeasure (M.law v) := M.probability v
    refine (Measure.integrable_toReal_rnDeriv (μ := M.law v) (ν := M.dominating)).congr ?_
    filter_upwards [] with x
    simp only [DominatedIIDModel.sqrtDensity, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]
  have hproj_int : Integrable (fun x => inner ℝ u (qmd.score x) ^ 2) (M.law 0) := by
    refine Integrable.mono' (qmd.score_squareIntegrable.const_mul (‖u‖ ^ 2))
      ((qmd.score_measurable.const_inner (c := u)).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simp only [norm_pow, Real.norm_eq_abs]
    calc
      |inner ℝ u (qmd.score x)| ^ 2
          ≤ (‖u‖ * ‖qmd.score x‖) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (abs_real_inner_le_norm u (qmd.score x))
      _ = ‖u‖ ^ 2 * ‖qmd.score x‖ ^ 2 := by ring
  let aRaw (x : X) : ℝ :=
    (1 / 2 : ℝ) * inner ℝ u (qmd.score x) * M.sqrtDensity 0 x
  have ha_mem : MemLp aRaw 2 M.dominating := by
    have hpmeas : Measurable (M.sqrtDensity 0) := by
      unfold DominatedIIDModel.sqrtDensity
      exact Real.continuous_sqrt.measurable.comp
        (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
    have hameas : Measurable aRaw := by
      unfold aRaw
      exact (qmd.score_measurable.const_inner (c := u)).const_mul (1 / 2) |>.mul hpmeas
    apply (memLp_two_iff_integrable_sq_norm hameas.aestronglyMeasurable).2
    let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
    have hw := (integrable_toReal_rnDeriv_mul_iff
      (M.absolutelyContinuous 0)).2 hproj_int
    refine (hw.const_mul ((1 / 2 : ℝ) ^ 2)).congr ?_
    filter_upwards [] with x
    simp only [aRaw, DominatedIIDModel.sqrtDensity, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num [mul_pow, sq_abs, Real.sq_sqrt ENNReal.toReal_nonneg] <;> ring
  have hr_mem : MemLp (qmd.dqmRemainder u) 2 M.dominating := by
    have hm := ((hp_mem u).sub (hp_mem 0)).sub ha_mem
    have hae : (M.sqrtDensity u - M.sqrtDensity 0 - aRaw) =ᵐ[M.dominating]
        qmd.dqmRemainder u := ae_of_all _ fun x => by
      simp only [dqmRemainder, aRaw, Pi.sub_apply]
    refine ⟨hm.1.congr hae, ?_⟩
    rw [← eLpNorm_congr_ae hae]
    exact hm.2
  have hi := (memLp_two_iff_integrable_sq_norm hr_mem.1).1 hr_mem
  exact hi.congr (ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs, sq_abs])

private theorem scaledDqmRemainder_tendsto (qmd : IIDQuadraticMeanDifferentiable M) (h : H) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating)
      atTop (𝓝 0) := by
  by_cases hh : h = 0
  · subst h
    simp [dqmRemainder]
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have htheta : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ • h) atTop (𝓝 0) := by
    simpa only [zero_smul] using hinv.smul_const h
  have hexp : (fun u : H => ∫ x, qmd.dqmRemainder u x ^ 2 ∂M.dominating)
      =o[𝓝 0] fun u : H => ‖u‖ ^ 2 := by
    simpa only [dqmRemainder] using qmd.expansion
  have hratio := hexp.tendsto_div_nhds_zero.comp htheta
  have hscaled := (tendsto_const_nhds.mul hratio : Tendsto
    (fun n : ℕ => ‖h‖ ^ 2 *
      ((∫ x, qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating) /
        ‖(Real.sqrt (n : ℝ))⁻¹ • h‖ ^ 2)) atTop (𝓝 (‖h‖ ^ 2 * 0)))
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
    have hnorm : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    field_simp
    rw [Real.sq_sqrt hnR.le]
    ring)

/-- DQM makes the one-observation square-root likelihood increment equal to the projected
score divided by `sqrt n`, with squared error `o(1/n)` under the base law. -/
theorem sqrtLikelihoodIncrement_L2 (qmd : IIDQuadraticMeanDifferentiable M) (h : H) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      (qmd.sqrtLikelihoodIncrement n h x -
        (Real.sqrt (n : ℝ))⁻¹ * inner ℝ h (qmd.score x)) ^ 2 ∂M.law 0)
      atTop (𝓝 0) := by
  -- Restrict the dominating-measure DQM remainder to the support of the base density,
  -- cancel that density against `d(M.law 0)`, and compose the little-o estimate with
  -- `n ↦ h / sqrt n`.  Handle the harmless `n = 0` row separately.
  letI : SigmaFinite M.dominating := M.dominating_sigmaFinite
  let _ : IsProbabilityMeasure (M.law 0) := M.probability 0
  let err (n : ℕ) (x : X) : ℝ := qmd.sqrtLikelihoodIncrement n h x -
    (Real.sqrt (n : ℝ))⁻¹ * inner ℝ h (qmd.score x)
  have hpoint (n : ℕ) (x : X) :
      ((M.law 0).rnDeriv M.dominating x).toReal * err n x ^ 2 ≤
        4 * qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 := by
    rw [← Real.sq_sqrt ENNReal.toReal_nonneg]
    change M.sqrtDensity 0 x ^ 2 * err n x ^ 2 ≤ _
    by_cases hp : M.sqrtDensity 0 x = 0
    · simp [hp, sq_nonneg]
    ·
      simp only [err, sqrtLikelihoodIncrement, hp, if_false, dqmRemainder,
        inner_smul_left, starRingEnd_apply, star_trivial]
      field_simp
      ring
      exact le_rfl
  have hupper (n : ℕ) :
      ∫ x, err n x ^ 2 ∂M.law 0 ≤
        4 * ∫ x, qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating := by
    rw [← integral_toReal_rnDeriv_mul (M.absolutelyContinuous 0)]
    have hg : Integrable (fun x =>
        4 * qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2) M.dominating :=
      (qmd.dqmRemainder_sq_integrable _).const_mul 4
    have hf : Integrable (fun x =>
        ((M.law 0).rnDeriv M.dominating x).toReal * err n x ^ 2) M.dominating := by
      have hsqrt_meas (u : H) : Measurable (M.sqrtDensity u) := by
        unfold DominatedIIDModel.sqrtDensity
        exact Real.continuous_sqrt.measurable.comp
          (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
      have hzero : MeasurableSet {x | M.sqrtDensity 0 x = 0} :=
        (hsqrt_meas 0) (measurableSet_singleton 0)
      have hinc : Measurable (qmd.sqrtLikelihoodIncrement n h) := by
        unfold sqrtLikelihoodIncrement
        apply Measurable.ite hzero measurable_const
        exact (((hsqrt_meas _).div (hsqrt_meas 0)).sub_const 1).const_mul 2
      have herr : Measurable (err n) := by
        unfold err
        exact hinc.sub ((qmd.score_measurable.const_inner (c := h)).const_mul _)
      refine Integrable.mono' hg
        (((ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _)).mul
          (herr.pow_const 2)).aestronglyMeasurable) ?_
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
        abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))] using hpoint n x
    calc
      (∫ x, ((M.law 0).rnDeriv M.dominating x).toReal * err n x ^ 2 ∂M.dominating)
          ≤ ∫ x, 4 * qmd.dqmRemainder
              ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating :=
        integral_mono_ae hf hg (ae_of_all _ (hpoint n))
      _ = 4 * ∫ x, qmd.dqmRemainder
              ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating :=
        integral_const_mul 4 _
  change Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, err n x ^ 2 ∂M.law 0) atTop (𝓝 0)
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left (hupper n) (Nat.cast_nonneg _)
  · convert (qmd.scaledDqmRemainder_tendsto h).const_mul 4 using 1 <;> ring

/-- For [a dominated i.i.d. model that is quadratic-mean differentiable](hyp:qmd) and [a fixed local direction](hyp:h), [the local probability mass outside the base-law support is little-o of one over the sample size](goal). -/
theorem local_zeroBaseDensity_mass (qmd : IIDQuadraticMeanDifferentiable M) (h : H) :
    Tendsto (fun n : ℕ => (n : ℝ) * (M.law ((Real.sqrt (n : ℝ))⁻¹ • h)
      {x | M.sqrtDensity 0 x = 0}).toReal) atTop (𝓝 0) := by
  -- On the zero set of the base density both the base term and score-linear term in the
  -- DQM expansion vanish, so the squared remainder is exactly the local density.
  letI : SigmaFinite M.dominating := M.dominating_sigmaFinite
  have hsqrt_meas (u : H) : Measurable (M.sqrtDensity u) := by
    unfold DominatedIIDModel.sqrtDensity
    exact Real.continuous_sqrt.measurable.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))
  have hzero : MeasurableSet {x | M.sqrtDensity 0 x = 0} :=
    (hsqrt_meas 0) (measurableSet_singleton 0)
  have hupper (n : ℕ) :
      (M.law ((Real.sqrt (n : ℝ))⁻¹ • h)
        {x | M.sqrtDensity 0 x = 0}).toReal ≤
        ∫ x, qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating := by
    let _ : IsProbabilityMeasure (M.law ((Real.sqrt (n : ℝ))⁻¹ • h)) :=
      M.probability _
    rw [← measureReal_def, ← Measure.setIntegral_toReal_rnDeriv
      (M.absolutelyContinuous ((Real.sqrt (n : ℝ))⁻¹ • h))]
    calc
      (∫ x in {x | M.sqrtDensity 0 x = 0},
          ((M.law ((Real.sqrt (n : ℝ))⁻¹ • h)).rnDeriv M.dominating x).toReal
          ∂M.dominating) =
          ∫ x in {x | M.sqrtDensity 0 x = 0},
            qmd.dqmRemainder ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hzero] with x hx
        rw [← Real.sq_sqrt ENNReal.toReal_nonneg]
        simp only [dqmRemainder, hx, mul_zero, sub_zero]
        rfl
      _ ≤ ∫ x, qmd.dqmRemainder
          ((Real.sqrt (n : ℝ))⁻¹ • h) x ^ 2 ∂M.dominating :=
        setIntegral_le_integral (qmd.dqmRemainder_sq_integrable _)
          (ae_of_all _ fun x => sq_nonneg _)
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  · intro n
    exact mul_le_mul_of_nonneg_left (hupper n) (Nat.cast_nonneg _)
  · exact qmd.scaledDqmRemainder_tendsto h

end IIDQuadraticMeanDifferentiable

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
