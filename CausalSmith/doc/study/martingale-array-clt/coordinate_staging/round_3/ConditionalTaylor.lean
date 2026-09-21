/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.ExponentialBounds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional Taylor estimates for martingale characteristic functions

This module isolates the one-increment analytic estimates used by a
martingale-array characteristic-function argument.  It records the exact
conditional quadratic expansion, a bounded predictable pull-out estimate,
and the integrated truncated-remainder bound.  These results do not assume
independence.
-/

namespace Causalean.Stat

open Complex MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If [the conditioning sigma-algebra is contained in the ambient sigma-algebra](hyp:hm),
[a real random variable is integrable](hyp:hX), and [has conditional mean zero](hyp:hZero),
then [its complex embedding also has conditional mean
zero](goal). -/
theorem condExp_ofReal_ae_eq_zero [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hX : Integrable X μ) (hZero : μ[X | m] =ᵐ[μ] 0) :
    μ[(fun ω => (X ω : ℂ)) | m] =ᵐ[μ] 0 := by
  /- Apply `ContinuousLinearMap.comp_condExp_comm` to the real-to-complex
  continuous linear map, then rewrite with `hZero`. -/
  change μ[Complex.ofRealCLM ∘ X | m] =ᵐ[μ] 0
  calc
    μ[Complex.ofRealCLM ∘ X | m] =ᵐ[μ]
        Complex.ofRealCLM ∘ μ[X | m] :=
      (Complex.ofRealCLM.comp_condExp_comm hX).symm
    _ =ᵐ[μ] 0 :=
      hZero.mono (fun ω hω => by simp [Function.comp_apply, hω])

/-- For [a conditioning sigma-algebra contained in the ambient sigma-algebra](hyp:hm),
[a square-integrable real random variable](hyp:hX) with [conditional mean zero](hyp:hZero),
[the conditional characteristic-function increment is
exactly its constant term, conditional quadratic term, and conditional Taylor
remainder](goal). -/
theorem condExp_cexp_ae_eq_quadratic_add_remainder
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (hZero : μ[X | m] =ᵐ[μ] 0) (t : ℝ) :
    μ[(fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))) | m] =ᵐ[μ]
      fun ω =>
        1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
          ((μ[(fun ω => X ω ^ 2) | m] ω : ℝ) : ℂ)) +
          μ[(fun ω => expQuadraticRemainder (t * X ω)) | m] ω := by
  /- Rearrange the defining Taylor identity pointwise, establish integrability
  of every term from `hX` and the global remainder bound, and use conditional
  expectation linearity.  The linear term vanishes by
  `condExp_ofReal_ae_eq_zero`; commute real-to-complex coercion through the
  conditional expectation for the quadratic term. -/
  have hX1 : Integrable X μ := hX.integrable (by norm_num)
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have hlin : Integrable
      (fun ω => (Complex.I * (t : ℂ)) * (X ω : ℂ)) μ :=
    hX1.ofReal.const_mul _
  have hquad : Integrable
      (fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) μ :=
    hX2.ofReal.const_mul _
  have hexp : Integrable
      (fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))) μ := by
    have hmeas : AEStronglyMeasurable
        (fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))) μ := by
      fun_prop
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas ?_
    filter_upwards with ω
    rw [Complex.norm_exp]
    simp
  have hrem : Integrable
      (fun ω => expQuadraticRemainder (t * X ω)) μ := by
    apply (((hexp.sub (integrable_const (1 : ℂ))).sub hlin).add hquad).congr
    filter_upwards with ω
    rw [expQuadraticRemainder]
    push_cast
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hpoint : (fun ω =>
      Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))) =
      (fun ω => (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
        ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ) +
        expQuadraticRemainder (t * X ω)) := by
    funext ω
    rw [expQuadraticRemainder]
    push_cast
    ring
  rw [hpoint]
  have hconst : Integrable (fun _ : Ω => (1 : ℂ)) μ := integrable_const _
  have hbase : Integrable (fun ω =>
      (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
        ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) μ :=
    (hconst.add hlin).sub hquad
  have hsplit : μ[(fun ω =>
      (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
        ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ) +
        expQuadraticRemainder (t * X ω)) | m] =ᵐ[μ]
      fun ω =>
        μ[(fun ω => (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) | m] ω +
        μ[(fun ω => expQuadraticRemainder (t * X ω)) | m] ω := by
    convert condExp_add hbase hrem m using 1 <;> ext ω <;> rfl
  have hsub : μ[(fun ω =>
      (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
        ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) | m] =ᵐ[μ]
      fun ω =>
        μ[(fun ω => (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ)) | m] ω -
        μ[(fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) *
          ((X ω ^ 2 : ℝ) : ℂ)) | m] ω := by
    convert condExp_sub (hconst.add hlin) hquad m using 1 <;> ext ω <;> rfl
  have hadd : μ[(fun ω =>
      (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ)) | m] =ᵐ[μ]
      fun ω => μ[(fun _ : Ω => (1 : ℂ)) | m] ω +
        μ[(fun ω => (Complex.I * (t : ℂ)) * (X ω : ℂ)) | m] ω := by
    convert condExp_add hconst hlin m using 1 <;> ext ω <;> rfl
  have hlinZero : μ[(fun ω =>
      (Complex.I * (t : ℂ)) * (X ω : ℂ)) | m] =ᵐ[μ] 0 := by
    have hsmul : μ[(fun ω =>
        (Complex.I * (t : ℂ)) * (X ω : ℂ)) | m] =ᵐ[μ]
        fun ω => (Complex.I * (t : ℂ)) *
          μ[(fun ω => (X ω : ℂ)) | m] ω := by
      convert condExp_smul (μ := μ) (Complex.I * (t : ℂ))
        (fun ω => (X ω : ℂ)) m using 1 <;> ext ω <;> rfl
    have hzero := condExp_ofReal_ae_eq_zero (mΩ := mΩ) (m := m) (μ := μ)
      hm X hX1 hZero
    filter_upwards [hsmul, hzero] with ω hsmulω hzeroω
    simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero] using
      hsmulω.trans (congrArg ((Complex.I * (t : ℂ)) * ·) hzeroω)
  have hquadComm : μ[(fun ω => ((X ω ^ 2 : ℝ) : ℂ)) | m] =ᵐ[μ]
      fun ω => ((μ[(fun ω => X ω ^ 2) | m] ω : ℝ) : ℂ) := by
    change μ[Complex.ofRealCLM ∘ (fun ω => X ω ^ 2) | m] =ᵐ[μ]
      Complex.ofRealCLM ∘ μ[(fun ω => X ω ^ 2) | m]
    exact (Complex.ofRealCLM.comp_condExp_comm hX2).symm
  have hquadCE : μ[(fun ω =>
      ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) | m] =ᵐ[μ]
      fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) *
        μ[(fun ω => ((X ω ^ 2 : ℝ) : ℂ)) | m] ω := by
    convert condExp_smul (μ := μ) ((t ^ 2 / 2 : ℝ) : ℂ)
      (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) m using 1 <;> ext ω <;> rfl
  have hone : μ[(fun _ : Ω => (1 : ℂ)) | m] = fun _ => 1 := by
    exact condExp_const (μ := μ) hm (1 : ℂ)
  filter_upwards [hsplit, hsub, hadd, hlinZero, hquadCE, hquadComm]
    with ω hsplitω hsubω haddω hlinZeroω hquadCEω hquadCommω
  rw [hsplitω, hsubω, haddω, hlinZeroω, hquadCEω, hquadCommω]
  rw [congrFun hone ω]
  simp only [Pi.zero_apply]
  ring

/-- If [the conditioning sigma-algebra is contained in the ambient sigma-algebra](hyp:hm),
[an integrable complex function](hyp:hf) is multiplied by [a predictable complex weight](hyp:hg)
whose [norm has an almost-sure finite bound](hyp:hgBound),
then [integrating after conditional expectation gives the original weighted
integral](goal). -/
theorem integral_mul_condExp_eq_integral_mul_of_ae_bound
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (f g : Ω → ℂ) (hf : Integrable f μ) (hg : StronglyMeasurable[m] g)
    (B : ℝ) (hgBound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ B) :
    (∫ ω, g ω * μ[f | m] ω ∂μ) = ∫ ω, g ω * f ω ∂μ := by
  have hgf : Integrable (fun ω => g ω * f ω) μ :=
    hf.bdd_mul (hg.mono hm).aestronglyMeasurable hgBound
  have hpull : μ[(fun ω => g ω * f ω) | m] =ᵐ[μ]
      fun ω => g ω * μ[f | m] ω := by
    convert condExp_stronglyMeasurable_bilin_of_bound
      (mΩ := mΩ) (μ := μ) (ContinuousLinearMap.mul ℝ ℂ) hm hg hf B hgBound using 1 <;>
      ext ω <;> rfl
  calc
    (∫ ω, g ω * μ[f | m] ω ∂μ) =
        ∫ ω, μ[(fun ω => g ω * f ω) | m] ω ∂μ :=
      integral_congr_ae hpull.symm
    _ = ∫ ω, g ω * f ω ∂μ := by
      rw [integral_condExp (m₀ := mΩ) (μ := μ) hm]

/-- If [the conditioning sigma-algebra is contained in the ambient sigma-algebra](hyp:hm),
[an integrable complex error](hyp:hf) is multiplied by [a predictable complex weight](hyp:hg)
whose [norm is bounded by a nonnegative constant](hyp:hB,hgBound),
then [the norm of the integral of the weight times the conditional error is at
most that constant times the integral norm of the original error](goal). -/
theorem norm_integral_mul_condExp_le_of_ae_bound
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (f g : Ω → ℂ) (hf : Integrable f μ) (hg : StronglyMeasurable[m] g)
    (B : ℝ) (hB : 0 ≤ B) (hgBound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ B) :
    ‖∫ ω, g ω * μ[f | m] ω ∂μ‖ ≤ B * ∫ ω, ‖f ω‖ ∂μ := by
  /- Use the conditional-expectation pull-out theorem for the bounded
  `m`-measurable factor `g`, then `integral_condExp`.  Bound the resulting
  integral of `g * f` by the integral of its norm and use `hgBound`. -/
  have hgf : Integrable (fun ω => g ω * f ω) μ :=
    hf.bdd_mul (hg.mono hm).aestronglyMeasurable hgBound
  have hpull : μ[(fun ω => g ω * f ω) | m] =ᵐ[μ]
      fun ω => g ω * μ[f | m] ω := by
    convert condExp_stronglyMeasurable_bilin_of_bound
      (mΩ := mΩ) (μ := μ) (ContinuousLinearMap.mul ℝ ℂ) hm hg hf B hgBound using 1 <;>
      ext ω <;> rfl
  have hnorm : Integrable (fun ω => ‖g ω * f ω‖) μ := hgf.norm
  have hmajor : Integrable (fun ω => B * ‖f ω‖) μ := hf.norm.const_mul B
  calc
    ‖∫ ω, g ω * μ[f | m] ω ∂μ‖ =
        ‖∫ ω, μ[(fun ω => g ω * f ω) | m] ω ∂μ‖ := by
      rw [integral_congr_ae hpull]
    _ = ‖∫ ω, g ω * f ω ∂μ‖ := by
      rw [integral_condExp (m₀ := mΩ) (μ := μ) hm]
    _ ≤ ∫ ω, ‖g ω * f ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, B * ‖f ω‖ ∂μ := by
      apply integral_mono_ae hnorm hmajor
      filter_upwards [hgBound] with ω hω
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    _ = B * ∫ ω, ‖f ω‖ ∂μ := integral_const_mul _ _

/-- For [a square-integrable real random variable](hyp:hX), [a positive
truncation level](hyp:hη), and [a frequency small at that level](hyp:htη), [the
integrated quadratic exponential remainder is bounded by a cubic small-jump
term plus the truncated second moment of the large jumps](goal). -/
theorem integral_norm_expQuadraticRemainder_le
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (t η : ℝ)
    (hη : 0 < η) (htη : |t| * η ≤ 1) :
    (∫ ω, ‖expQuadraticRemainder (t * X ω)‖ ∂μ) ≤
      |t| ^ 3 * η * (∫ ω, X ω ^ 2 ∂μ) +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) *
          (∫ ω, if η < |X ω| then X ω ^ 2 else 0 ∂μ) := by
  /- Integrate `norm_expQuadraticRemainder_le_truncated`.  Obtain
  integrability of `X²`, the truncated square, and the remainder from `hX` and
  `norm_expQuadraticRemainder_le_global`, then distribute the integral over
  the two nonnegative constant multiples. -/
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have htrunc : Integrable
      (fun ω => if η < |X ω| then X ω ^ 2 else 0) μ := by
    let Y := hX.aestronglyMeasurable.mk X
    have hXY : X =ᵐ[μ] Y := hX.aestronglyMeasurable.ae_eq_mk
    have hYmeas : StronglyMeasurable Y :=
      hX.aestronglyMeasurable.stronglyMeasurable_mk
    have hY2 : Integrable (fun ω => Y ω ^ 2) μ :=
      hX2.congr (hXY.pow_const 2)
    have hs : MeasurableSet {ω | η < |Y ω|} :=
      measurableSet_lt measurable_const hYmeas.measurable.norm
    have htruncY : Integrable
        (fun ω => if η < |Y ω| then Y ω ^ 2 else 0) μ := by
      apply (hY2.indicator hs).congr
      filter_upwards with ω
      rw [Set.indicator]
      rfl
    exact htruncY.congr (hXY.mono (fun ω hω => by simp [hω]))
  let A : ℝ := |t| ^ 3 * η
  let C : ℝ := 2 / η ^ 2 + |t| / η + t ^ 2 / 2
  have hA : Integrable (fun ω => A * X ω ^ 2) μ := hX2.const_mul A
  have hC : Integrable
      (fun ω => C * (if η < |X ω| then X ω ^ 2 else 0)) μ :=
    htrunc.const_mul C
  have hmajor : Integrable (fun ω =>
      A * X ω ^ 2 + C * (if η < |X ω| then X ω ^ 2 else 0)) μ :=
    hA.add hC
  have hremMeas : AEStronglyMeasurable
      (fun ω => ‖expQuadraticRemainder (t * X ω)‖) μ := by
    have hXm := hX.aestronglyMeasurable
    unfold expQuadraticRemainder
    fun_prop
  have hbound : ∀ᵐ ω ∂μ,
      ‖expQuadraticRemainder (t * X ω)‖ ≤
        A * X ω ^ 2 + C * (if η < |X ω| then X ω ^ 2 else 0) :=
    ae_of_all μ fun ω => by
      simpa only [A, C] using
        norm_expQuadraticRemainder_le_truncated t (X ω) η hη htη
  have hrem : Integrable
      (fun ω => ‖expQuadraticRemainder (t * X ω)‖) μ := by
    apply hmajor.mono' hremMeas
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hω
  calc
    (∫ ω, ‖expQuadraticRemainder (t * X ω)‖ ∂μ) ≤
        ∫ ω, A * X ω ^ 2 +
          C * (if η < |X ω| then X ω ^ 2 else 0) ∂μ :=
      integral_mono_ae hrem hmajor hbound
    _ = A * (∫ ω, X ω ^ 2 ∂μ) +
        C * (∫ ω, if η < |X ω| then X ω ^ 2 else 0 ∂μ) := by
      rw [integral_add hA hC, integral_const_mul, integral_const_mul]
    _ = |t| ^ 3 * η * (∫ ω, X ω ^ 2 ∂μ) +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) *
          (∫ ω, if η < |X ω| then X ω ^ 2 else 0 ∂μ) := by
      rfl

end Causalean.Stat
