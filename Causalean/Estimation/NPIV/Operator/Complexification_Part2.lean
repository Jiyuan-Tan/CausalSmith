/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Operator.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Causalean.Estimation.NPIV.Operator.Complexification_Part1

/-! # Algebraic and norm laws for the real functional calculus

This second implementation part proves that `realCFC` preserves
self-adjointness, multiplication, and the resolvent-times-operator identity.
It also supplies the spectrum comparison and norm estimate used by the NPIV
spectral bias argument.
-/

public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Complexification

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

attribute [local instance 2000] instAlgebraRealLpCLM
/-- **`realCFC` preserves self-adjointness.**

For continuous real `f` and self-adjoint `A`, `realCFC A f` is itself
self-adjoint.  Proof strategy: `cfc (fun z : ℂ => (f z.re : ℂ))
(complexLift A)` is self-adjoint by `IsSelfAdjoint.cfc` (provided the
lifted symbol takes real values on the spectrum, which follows from
`f z.re` being real for real `z`); then `complexLift_adjoint`
combined with `reLp` ∘ `_` ∘ `ιLp` being a real adjunction transports
self-adjointness back to `realCFC A f`. -/
theorem realCFC_isSelfAdjoint
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) :
    IsSelfAdjoint (realCFC A f) := by
  let C : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A)
  have hC : IsSelfAdjoint C := by
    have hcl : IsSelfAdjoint (complexLift A) := complexLift_isSelfAdjoint hA
    rw [show C = cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) by rfl]
    rw [← cfc_real_eq_complex (a := complexLift A) (f := f) (ha := hcl)]
    exact IsSelfAdjoint.cfc
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change inner ℝ (realCFC A f x) y = inner ℝ x (realCFC A f y)
  rw [realCFC_apply A hA f hf x, realCFC_apply A hA f hf y]
  rw [inner_reLp_left (C (ιLp x)) y]
  change (inner ℂ (C (ιLp x)) (ιLp y)).re = inner ℝ x (reLp (C (ιLp y)))
  rw [real_inner_comm (reLp (C (ιLp y))) x]
  rw [inner_reLp_left (C (ιLp y)) x]
  calc
    (inner ℂ (C (ιLp x)) (ιLp y)).re =
        (inner ℂ (ιLp x) (C (ιLp y))).re := by
      exact congrArg Complex.re
        ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hC) (ιLp x) (ιLp y))
    _ = (inner ℂ (C (ιLp y)) (ιLp x)).re := by
      simpa using (inner_re_symm (𝕜 := ℂ) (x := C (ιLp y)) (y := ιLp x)).symm

private lemma complexLift_one_early :
    complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [complexLift_apply] using reLp_add_smul_imLp (μ := μ) f

private lemma complexLift_comp_early (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A.comp B) = (complexLift A).comp (complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [complexLift_apply, complexLift_apply]
  rw [reLp_complexLift, imLp_complexLift]
  rfl

private lemma complexLift_mul_early (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A * B) = complexLift A * complexLift B := by
  exact complexLift_comp_early A B

private lemma complexLift_sub_early (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A - B) = complexLift A - complexLift B := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (A (reLp f) - B (reLp f)) + Complex.I • ιLp (A (imLp f) - B (imLp f)) =
    complexLift A f - complexLift B f
  rw [complexLift_apply A f, complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

private lemma complexLift_algebraMap_real_early (r : ℝ) :
    complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f) = (r : ℂ) • f
  calc
    ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f)
        = (r : ℂ) • (ιLp (reLp f) + Complex.I • ιLp (imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • ιLp (imLp f)) =
        (r : ℂ) • (Complex.I • ιLp (imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [reLp_add_smul_imLp]

private lemma complexLift_resolvent_real_early
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - complexLift A =
      complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [complexLift_sub_early, complexLift_algebraMap_real_early]

private lemma complexLift_isUnit_early
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (complexLift B) := by
  have hone : complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    exact complexLift_one_early (μ := μ)
  refine Units.isUnit ⟨complexLift B, complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      complexLift B * complexLift ↑hB.unit⁻¹ = complexLift (B * ↑hB.unit⁻¹) := by
        rw [complexLift_mul_early]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      complexLift ↑hB.unit⁻¹ * complexLift B = complexLift (↑hB.unit⁻¹ * B) := by
        rw [complexLift_mul_early]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.val_inv_mul
      _ = 1 := hone

private theorem spectrum_complexLift_subset_real_early
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) - complexLift A) := by
    rw [complexLift_resolvent_real_early]
    exact complexLift_isUnit_early hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

private theorem cfc_lifted_preserves_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (v : Lp ℝ 2 μ) :
    ιLp (reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp v)))
      = cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp v) := by
  let a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := complexLift A
  let E : Type _ := Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ
  have ha : IsSelfAdjoint a := complexLift_isSelfAdjoint hA
  have hpresHom :
      ∀ F : C(spectrum ℝ a, ℝ),
        ∀ w : Lp ℝ 2 μ,
          ιLp (reLp ((cfcHom ha F : E) (ιLp w))) =
            (cfcHom ha F : E) (ιLp w) := by
    intro F
    open scoped ContinuousFunctionalCalculus in
    induction F using ContinuousMap.induction_on_of_compact with
    | const r =>
        intro w
        rw [show ContinuousMap.const (spectrum ℝ a) r =
            algebraMap ℝ C(spectrum ℝ a, ℝ) r from rfl]
        rw [AlgHomClass.commutes (cfcHom ha) r]
        change ιLp (reLp ((algebraMap ℝ E r) (ιLp w))) =
          (algebraMap ℝ E r) (ιLp w)
        change ιLp (reLp ((r : ℂ) • ιLp w)) = (r : ℂ) • ιLp w
        rw [reLp_ofReal_smul, reLp_comp_ιLp]
        exact map_smul ιLp r w
    | id =>
        rw [cfcHom_id ha]
        intro w
        rw [complexLift_real, reLp_comp_ιLp]
    | star_id =>
        rw [map_star, cfcHom_id ha, ha.star_eq]
        intro w
        rw [complexLift_real, reLp_comp_ιLp]
    | add F G hF hG =>
        rw [map_add]
        intro w
        change ιLp (reLp (((cfcHom ha F : E) + (cfcHom ha G : E)) (ιLp w))) =
          ((cfcHom ha F : E) + (cfcHom ha G : E)) (ιLp w)
        simp only [ContinuousLinearMap.add_apply]
        rw [← hF w, ← hG w]
        simp [map_add, reLp_comp_ιLp]
    | mul F G hF hG =>
        rw [map_mul]
        intro w
        let B : E := cfcHom ha F
        let C : E := cfcHom ha G
        change ιLp (reLp ((B * C) (ιLp w))) = (B * C) (ιLp w)
        change ιLp (reLp (B (C (ιLp w)))) = B (C (ιLp w))
        rw [← hG w]
        exact hF (reLp (C (ιLp w)))
    | frequently F hF =>
        intro w
        have hleft : Continuous (fun B : E => ιLp (reLp (B (ιLp w)))) :=
          ιLp.continuous.comp <| reLp.continuous.comp <|
            (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) (ιLp w)).continuous
        have hright : Continuous (fun B : E => B (ιLp w)) :=
          (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) (ιLp w)).continuous
        rw [← Set.mem_setOf
            (p := fun B : E => ιLp (reLp (B (ιLp w))) = B (ιLp w)),
          ← (isClosed_eq hleft hright).closure_eq]
        apply mem_closure_of_frequently_of_tendsto
          (hF.mono fun G hG => hG w)
        exact (cfcHom_continuous ha).tendsto F
  change ιLp (reLp ((cfc (fun z : ℂ => (f z.re : ℂ)) a) (ιLp v))) =
    (cfc (fun z : ℂ => (f z.re : ℂ)) a) (ιLp v)
  rw [← cfc_real_eq_complex (a := a) (f := f) (ha := ha)]
  rw [cfc_apply f a ha hf.continuousOn]
  exact hpresHom ⟨_, hf.continuousOn.restrict⟩ v

/-- **Symbol-multiplication law for `realCFC`.**

For self-adjoint `A` and continuous real symbols `f g : ℝ → ℝ`, the
real CFC of the pointwise product `fun x => f x * g x` equals the
operator composition `(realCFC A f).comp (realCFC A g)`.

This is the C*-algebra multiplication law transported through
complexification — `cfc_mul` lifts to the operator algebra
`Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` (a `CStarAlgebra`), and the composition
projects back through `reLp` because the complex CFC is multiplicative.

NOTE: this is the *symbol-multiplication* law `realCFC A (f·g)`, not
the *symbol-composition* law `realCFC A (f∘g)` discussed in the
comment block above — those are mathematically distinct, and only the
former is exposed here. -/
theorem realCFC_mul
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    realCFC A (fun x => f x * g x) = (realCFC A f).comp (realCFC A g) := by
  ext v
  rw [realCFC_apply A hA (fun x => f x * g x) (hf.mul hg) v]
  rw [ContinuousLinearMap.comp_apply]
  rw [realCFC_apply A hA f hf (realCFC A g v),
    realCFC_apply A hA g hg v]
  rw [cfc_lifted_preserves_real A hA g hg v]
  rw [show (fun z : ℂ => ((f z.re * g z.re : ℝ) : ℂ)) =
      fun z : ℂ => (f z.re : ℂ) * (g z.re : ℂ) by
    funext z
    norm_num]
  rw [cfc_mul (fun z : ℂ => (f z.re : ℂ)) (fun z : ℂ => (g z.re : ℂ))
    (complexLift A)
    (hf := (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn)
    (hg := (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn)]
  rfl

private lemma realCFC_congr_on_spectrum
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f g : ℝ → ℝ)
    (h : ∀ x ∈ spectrum ℝ A, f x = g x) (hA : IsSelfAdjoint A) :
    realCFC A f = realCFC A g := by
  apply ContinuousLinearMap.ext
  intro v
  change reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp v)) =
    reLp (cfc (fun z : ℂ => (g z.re : ℂ)) (complexLift A) (ιLp v))
  congr 2
  apply cfc_congr
  intro z hz
  have hzr : z.re ∈ spectrum ℝ A := spectrum_complexLift_subset_real_early hA hz
  simpa using congrArg (fun r : ℝ => (r : ℂ)) (h z.re hzr)

/-- **Resolvent symbol for `realCFC`.** For [a self-adjoint bounded operator `A`](hyp:hA) whose
[real spectrum lies in the nonnegative reals](hyp:hA_spec), and for [a strictly positive
regularization parameter λ](hyp:hlam), [composing the real-functional-calculus operator for the
affine symbol `x ↦ λ + x` with that for the resolvent symbol `x ↦ (λ + x)⁻¹` yields the identity
operator on the ambient L² space](goal).

For self-adjoint `A` with nonnegative real spectrum and `λ > 0`,
the symbol `fun x => (λ + x)⁻¹` is continuous and nonzero on
`spectrum ℝ A` (since `λ + x ≥ λ > 0` there), so its `realCFC` is
defined and is a two-sided inverse of `realCFC A (fun x => λ + x)`
in the operator algebra `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`.

Concretely: composition of these two `realCFC` operators equals the
identity `ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)`. This is the
`realCFC`-level resolvent law that the Tikhonov bias proof needs. -/
theorem realCFC_resolvent_mul_self
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (hA_spec : ∀ x ∈ spectrum ℝ A, 0 ≤ x)
    (lambda : ℝ) (hlam : 0 < lambda) :
    (realCFC A (fun x => lambda + x)).comp
        (realCFC A (fun x => (lambda + x)⁻¹))
      = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) := by
  have hsafe_ne : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  have hsafe_cont : Continuous (fun x : ℝ => (lambda + max 0 x)⁻¹) :=
    (continuous_const.add (continuous_const.max continuous_id)).inv₀ hsafe_ne
  have hagree : ∀ x ∈ spectrum ℝ A,
      (lambda + max 0 x)⁻¹ = (lambda + x)⁻¹ := fun x hx => by
    have hx0 : 0 ≤ x := hA_spec x hx
    rw [max_eq_right hx0]
  rw [← realCFC_congr_on_spectrum A (fun x => (lambda + max 0 x)⁻¹)
    (fun x => (lambda + x)⁻¹) hagree hA]
  rw [← realCFC_mul A hA (fun x => lambda + x)
    (fun x => (lambda + max 0 x)⁻¹) (continuous_const.add continuous_id) hsafe_cont]
  have hprod : ∀ x ∈ spectrum ℝ A,
      (lambda + x) * (lambda + max 0 x)⁻¹ = 1 := fun x hx => by
    have hx0 : 0 ≤ x := hA_spec x hx
    rw [max_eq_right hx0]
    have hne : lambda + x ≠ 0 := by
      have hpos : 0 < lambda + x := by linarith
      exact ne_of_gt hpos
    exact mul_inv_cancel₀ hne
  rw [realCFC_congr_on_spectrum A
    (fun x => (lambda + x) * (lambda + max 0 x)⁻¹)
    (fun _ : ℝ => (1 : ℝ)) hprod hA]
  apply ContinuousLinearMap.ext
  intro v
  rw [realCFC_apply A hA (fun _ : ℝ => (1 : ℝ)) continuous_const v]
  rw [ContinuousLinearMap.id_apply]
  change reLp (cfc (fun _ : ℂ => (1 : ℂ)) (complexLift A) (ιLp v)) = v
  rw [cfc_const_one ℂ (complexLift A)
    (ha := (complexLift_isSelfAdjoint hA).isStarNormal)]
  rw [ContinuousLinearMap.one_apply, reLp_comp_ιLp]

private lemma complexLift_one :
    complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [complexLift_apply] using reLp_add_smul_imLp (μ := μ) f

private lemma complexLift_comp (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A.comp B) = (complexLift A).comp (complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [complexLift_apply, complexLift_apply]
  rw [reLp_complexLift, imLp_complexLift]
  rfl

private lemma complexLift_mul (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A * B) = complexLift A * complexLift B := by
  exact complexLift_comp A B

private lemma complexLift_sub (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A - B) = complexLift A - complexLift B := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (A (reLp f) - B (reLp f)) + Complex.I • ιLp (A (imLp f) - B (imLp f)) =
    complexLift A f - complexLift B f
  rw [complexLift_apply A f, complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

private lemma complexLift_algebraMap_real (r : ℝ) :
    complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f) = (r : ℂ) • f
  calc
    ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f)
        = (r : ℂ) • (ιLp (reLp f) + Complex.I • ιLp (imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • ιLp (imLp f)) =
        (r : ℂ) • (Complex.I • ιLp (imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [reLp_add_smul_imLp]

private lemma complexLift_resolvent_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - complexLift A =
      complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [complexLift_sub, complexLift_algebraMap_real]

private lemma complexLift_isUnit
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (complexLift B) := by
  have hone : complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    exact complexLift_one (μ := μ)
  refine Units.isUnit ⟨complexLift B, complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      complexLift B * complexLift ↑hB.unit⁻¹ = complexLift (B * ↑hB.unit⁻¹) := by
        rw [complexLift_mul]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      complexLift ↑hB.unit⁻¹ * complexLift B = complexLift (↑hB.unit⁻¹ * B) := by
        rw [complexLift_mul]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.val_inv_mul
      _ = 1 := hone

private theorem spectrum_complexLift_subset_real
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) - complexLift A) := by
    rw [complexLift_resolvent_real]
    exact complexLift_isUnit hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

private lemma norm_reLp_le (u : Lp ℂ 2 μ) : ‖reLp u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) u] with ω h
  rw [show (((reLp u : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((u : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h]
  change ‖(((u : Lp ℂ 2 μ) : Ω → ℂ) ω).re‖ ≤ ‖(((u : Lp ℂ 2 μ) : Ω → ℂ) ω)‖
  exact RCLike.norm_re_le_norm (((u : Lp ℂ 2 μ) : Ω → ℂ) ω)

/-- **Norm-via-spectrum bound for `realCFC`.** For [a self-adjoint bounded operator
`A`](hyp:hA) and [a continuous real-valued symbol `f`](hyp:hf), if [`f` is bounded in absolute
value by a nonnegative constant `c` on the real spectrum of `A`](hyp:hc,hsup), then [the operator
`realCFC A f` is a contraction up to `c`: for every vector `g`, `‖realCFC A f g‖ ≤ c · ‖g‖`](goal).

Proof strategy:
1. Reduce to bounding `‖cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp g)‖`
   via `realCFC_apply` plus the contraction `‖reLp h‖ ≤ ‖h‖`
   (`reLp` has operator norm ≤ 1 because `RCLike.reCLM` does).
2. Bound that by `‖cfc … (complexLift A)‖ · ‖ιLp g‖`
   (operator norm), then use `‖ιLp g‖ = ‖g‖` (`ιLp_isometry`).
3. Apply `norm_cfc_le_iff` (in
   `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric`)
   to reduce `‖cfc (fun z => (f z.re : ℂ)) (complexLift A)‖ ≤ c` to
   `∀ z ∈ spectrum ℂ (complexLift A), |f z.re| ≤ c`.
4. For each such `z`, `IsSelfAdjoint.mem_spectrum_eq_re` (applied to
   the self-adjoint `complexLift A`, see
   `complexLift_isSelfAdjoint`) gives `z = (z.re : ℂ)`. Then transport
   `z.re ∈ spectrum ℝ A` via the spectrum-preservation fact for the
   complex lift (this may require a small auxiliary lemma; if mathlib
   doesn't expose it directly, prove it by inverting
   `λ - complexLift A = complexLift (λ - A)` for real `λ`). -/
theorem realCFC_norm_le
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f)
    (c : ℝ) (hc : 0 ≤ c) (hsup : ∀ x ∈ spectrum ℝ A, |f x| ≤ c)
    (g : Lp ℝ 2 μ) :
    ‖realCFC A f g‖ ≤ c * ‖g‖ := by
  let Acpx : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := complexLift A
  let C : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    cfc (fun z : ℂ => (f z.re : ℂ)) Acpx
  rw [realCFC_apply A hA f hf g]
  change ‖reLp (C (ιLp g))‖ ≤ c * ‖g‖
  have hC_norm : ‖C‖ ≤ c := by
    rw [show C = cfc (fun z : ℂ => (f z.re : ℂ)) Acpx by rfl]
    rw [norm_cfc_le_iff (fun z : ℂ => (f z.re : ℂ)) Acpx hc
      (hf := (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn)
      (ha := (complexLift_isSelfAdjoint hA).isStarNormal)]
    intro z hz
    have hzr : z.re ∈ spectrum ℝ A := spectrum_complexLift_subset_real hA hz
    simpa [Complex.norm_real, Real.norm_eq_abs] using hsup z.re hzr
  calc
    ‖reLp (C (ιLp g))‖
        ≤ ‖C (ιLp g)‖ := norm_reLp_le _
    _ = 1 * ‖C (ιLp g)‖ := by rw [one_mul]
    _ ≤ 1 * (‖C‖ * ‖ιLp g‖) := by
      gcongr
      exact C.le_opNorm _
    _ ≤ 1 * (c * ‖ιLp g‖) := by
      gcongr
    _ = c * ‖g‖ := by
      rw [one_mul, ιLp_isometry]

end Complexification
end NPIV
end Estimation
end Causalean
