module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionFourier
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Kernel averages of the common-shift identity

Tonelli transports an arbitrary Borel sign kernel through the reflected sampling law,
then averages the pointwise common-shift Parseval identity. No fairness assumption is needed.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The reflected representative is Borel, including at the fold endpoints. This uses [the hm hypothesis](hyp:hm), [the stated conclusion](goal). -/
-- @node: reflExt_measurable
@[fun_prop] lemma reflExt_measurable {d : ℕ} {m : Cube d → ℝ}
    (hm : Measurable m) : Measurable (reflExt m) := by
  apply Complex.measurable_ofReal.comp
  apply hm.comp
  unfold fold
  apply measurable_pi_lambda
  intro j
  exact (measurable_const.mul
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply j)).subtype_val)
    |>.min (measurable_const.sub (measurable_const.mul
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp
        (measurable_pi_apply j)).subtype_val))

/-- Averaging common-shift Parseval against any Borel sign kernel.](goal) Under [the stated conditions](hyp:hd). This uses [the stated conclusion](goal). -/
-- @node: commonShift_kernel_parseval
lemma commonShift_kernel_parseval {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (ρ : Kernel (Fin n → Torus d) (Signs n))
    [IsMarkovKernel ρ] :
    (∫⁻ wt, ∫⁻ z,
      ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * reflExt m.val (wt.1 i - wt.2)‖ ^ 2
        ∂ρ wt.1 ∂(Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d)) =
    ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
      ∫⁻ w, ∫⁻ z, ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2
        ∂ρ w ∂Measure.pi (fun _ : Fin n => torusMeasure d) := by
  have hm := reflExt_measurable m.property.1
  have he (k : Fin d → ℤ) : Measurable (ek k) :=
    (UnitAddTorus.mFourier k).continuous.measurable
  have hmeas : Measurable (fun p : ((Fin n → Torus d) × Torus d) × Signs n =>
      ENNReal.ofReal ‖∑ i, (sgn (p.2 i) : ℂ) * reflExt m.val (p.1.1 i - p.1.2)‖ ^ 2) := by
    fun_prop
  rw [lintegral_prod]
  · have hswap (w : Fin n → Torus d) :
        (∫⁻ t, ∫⁻ z, ENNReal.ofReal
          ‖∑ i, (sgn (z i) : ℂ) * reflExt m.val (w i - t)‖ ^ 2 ∂ρ w ∂torusMeasure d) =
        ∫⁻ z, ∫⁻ t, ENNReal.ofReal
          ‖∑ i, (sgn (z i) : ℂ) * reflExt m.val (w i - t)‖ ^ 2 ∂torusMeasure d ∂ρ w := by
      apply lintegral_lintegral_swap
      exact (hmeas.comp (by fun_prop : Measurable
        (fun p : Torus d × Signs n => ((w, p.1), p.2)))).aemeasurable
    simp_rw [hswap]
    simp_rw [commonShift_parseval_lintegral hd (reflExt m.val) (reflExt_memLp m),
      mFourierCoeff_reflExt]
    change (∫⁻ w, ∫⁻ z, ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
      ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2 ∂ρ w
      ∂Measure.pi (fun _ : Fin n => torusMeasure d)) = _
    have hz (w : Fin n → Torus d) (k : Fin d → ℤ) :
        Measurable (fun z : Signs n => ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
          ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2) := by
      fun_prop
    simp_rw [lintegral_tsum (fun k => (hz _ k).aemeasurable)]
    rw [lintegral_tsum]
    · apply tsum_congr
      intro k
      have hfactor (w : Fin n → Torus d) :
          (∫⁻ z, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
            ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2 ∂ρ w) =
          ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
            ∫⁻ z, ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2 ∂ρ w :=
        lintegral_const_mul' _ _ (by finiteness)
      simp_rw [hfactor]
      exact lintegral_const_mul' _ _ (by finiteness)
    · intro k
      have hk : Measurable (fun p : (Fin n → Torus d) × Signs n =>
          ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
            ENNReal.ofReal ‖∑ i, (sgn (p.2 i) : ℂ) * ek k (p.1 i)‖ ^ 2) := by
        fun_prop
      exact hk.lintegral_kernel_prod_right'.aemeasurable
  · let hρ : Kernel ((Fin n → Torus d) × Torus d) (Signs n) :=
      ρ.comap Prod.fst measurable_fst
    exact (hmeas.lintegral_kernel_prod_right' (κ := hρ)).aemeasurable

/-- [ The original outcome imbalance has the Fourier kernel-average representation.](goal) Under [the stated conditions](hyp:hd,hX). -/
-- @node: reflection_kernel_fourier_identity
lemma reflection_kernel_fourier_identity {n d : ℕ} (hd : 0 < d)
    (m : CenteredL2Fn d) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Covariates n d) (hX : UniformDraw μ X)
    (ρ : Kernel (Fin n → Torus d) (Signs n)) [IsMarkovKernel ρ] :
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal |∑ i, sgn (z i) * m.val (X ω.1 i)| ^ 2
      ∂ρ (shiftedSample (X ω.1) ω.2.1 ω.2.2)
      ∂μ.prod ((reflectionLaw n d).prod (torusMeasure d))) =
    ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
      ∫⁻ w, ∫⁻ z, ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2
        ∂ρ w ∂Measure.pi (fun _ : Fin n => torusMeasure d) := by
  let Φ : (((Fin n → Torus d) × Torus d) × (Fin n → ℝ)) → ℝ≥0∞ :=
    fun p => ∫⁻ z, ENNReal.ofReal |∑ i, sgn (z i) * p.2 i| ^ 2 ∂ρ p.1.1
  have hΦ : Measurable Φ := by
    let hρ : Kernel (((Fin n → Torus d) × Torus d) × (Fin n → ℝ)) (Signs n) :=
      ρ.comap (fun p => p.1.1) (measurable_fst.comp measurable_fst)
    have hq : Measurable (fun q :
        ((((Fin n → Torus d) × Torus d) × (Fin n → ℝ)) × Signs n) =>
        ENNReal.ofReal |∑ i, sgn (q.2 i) * q.1.2 i| ^ 2) := by
      fun_prop
    exact hq.lintegral_kernel_prod_right' (κ := hρ)
  rw [show (∫⁻ ω, ∫⁻ z, ENNReal.ofReal |∑ i, sgn (z i) * m.val (X ω.1 i)| ^ 2
      ∂ρ (shiftedSample (X ω.1) ω.2.1 ω.2.2)
      ∂μ.prod ((reflectionLaw n d).prod (torusMeasure d))) =
    ∫⁻ wt, Φ (wt, fun i => (reflExt m.val (wt.1 i - wt.2)).re)
      ∂(Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d) from
        reflection_lintegral_transport n d Ω μ X hX m.val m.property.1 Φ hΦ]
  have hreal (w : Fin n → Torus d) (t : Torus d) (z : Signs n) :
      |∑ i, sgn (z i) * (reflExt m.val (w i - t)).re| =
        ‖∑ i, (sgn (z i) : ℂ) * reflExt m.val (w i - t)‖ := by
    simp only [reflExt, Complex.ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
      Complex.norm_real, Real.norm_eq_abs]
  simp only [Φ, hreal]
  exact commonShift_kernel_parseval hd m ρ

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
