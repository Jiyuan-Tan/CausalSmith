/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Operator.Adjoint
public import Causalean.Estimation.NPIV.Operator.Complexification
public import Causalean.Estimation.NPIV.Operator.Tikhonov
public import Causalean.Estimation.NPIV.SourceCondition
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Spectral source operators and the Tikhonov resolvent

This first spectral part defines `SpectralSourceCondition`, the real
functional-calculus power `(T†T)^(β/2)`, and its uniform bias constant.  It
identifies the ambient Lax–Milgram Tikhonov minimizer with the resolvent formula
and proves the scalar residual estimates used by the later bias bounds.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
/-- For a measurable sample space and its measure, the real-scalar algebra is the algebra of bounded complex-linear operators on the corresponding complex-valued $L^2$ space.

Local disambiguation of the real-scalar algebra structure on the complex
operator algebra `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`.

There are two definitionally equal but syntactically different ways to view this
algebra over `ℝ`: restriction of scalars from `ℂ` (`Algebra.complexToReal`, which
is what Mathlib's real continuous functional calculus for self-adjoint elements
is stated over) and the continuous-linear-map algebra `ContinuousLinearMap.algebra`
with real scalars.  Typeclass search picks the latter and, since it only unfolds
instance-reducible definitions, never identifies it with the former; Mathlib's
`IsSelfAdjoint.instContinuousFunctionalCalculus` then fails to apply (this is the
known diamond of `Mathlib.LinearAlgebra.Complex.Module`, mathlib4#10906).  Pinning
the restriction-of-scalars structure inside this file makes the real functional
calculus available and keeps every `cfc`-level rewrite in one instance path.  The
two structures agree by `rfl`, so nothing about the mathematics changes.

This mirrors the identically-named local instance in
`Causalean.Estimation.NPIV.Operator.Complexification`; both are `local`, so
neither leaks downstream. -/
noncomputable local instance (priority := 2000) instAlgebraRealLpCLM :
    Algebra ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Algebra.complexToReal

/-- For [an NPIV operator system](hyp:S) and [a source exponent](hyp:β), a spectral source
condition is the standard source condition on the normal operator of
`T : L²(σ(X)) → L²(σ(Z))`.

No density assumption on the candidate class is needed: population Tikhonov
regularization is posed on the full domain `L²(σ(X))`. -/
structure SpectralSourceCondition
    (S : OperatorSystem Ω μ) (β : ℝ) extends SourceCondition S β

/-- For [an NPIV operator system](hyp:S), [an operator on the trimmed realization of
`L²(σ(X))`](hyp:A), and [a real symbol](hyp:f), [the real continuous functional
calculus of that operator](goal) uses the measurable structure `σ(X)` explicitly. -/
noncomputable def OperatorSystem.realCFCTrim (S : OperatorSystem Ω μ)
    (A : Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ] Lp ℝ 2 (μ.trim S.m_X_le))
    (f : ℝ → ℝ) :
    Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ] Lp ℝ 2 (μ.trim S.m_X_le) :=
  @Complexification.realCFC Ω S.m_X (μ.trim S.m_X_le) A f

namespace SpectralSourceCondition

variable {S : OperatorSystem Ω μ} {β : ℝ}

/-- `T†T` is a positive operator. -/
lemma Tstar_T_isPositive (S : OperatorSystem Ω μ) :
    S.Tstar_T_trim.IsPositive := by
  unfold OperatorSystem.Tstar_T_trim OperatorSystem.TadjointTrim
  simpa [ContinuousLinearMap.comp_def, ContinuousLinearMap.comp_apply] using
    ContinuousLinearMap.isPositive_adjoint_comp_self S.TlinTrim

/-- Positivity of `T†T`: its real spectrum lies in `[0, ∞)`. -/
lemma Tstar_T_spectrum_nonneg (S : OperatorSystem Ω μ) :
    ∀ x ∈ spectrum ℝ S.Tstar_T_trim, 0 ≤ x := by
  intro x hx
  exact spectrum_nonneg_of_nonneg (a := S.Tstar_T_trim) (x := x) (by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact Tstar_T_isPositive S) hx

/-! ## The `(T†T)^{β/2}` operator, defined via real CFC -/

/-- For [a real source exponent](hyp:β), [the source symbol is the function sending each real number $x$ to $(\max\{x,0\})^{\beta/2}$](goal).

The symbol `x ↦ Real.rpow (max x 0) (β/2)` used by `spectralPower`.
Continuous on all of ℝ for `β ≥ 0`, and agrees with `x^{β/2}` on
`[0, ∞)`. -/
noncomputable def sourceSymbol (β : ℝ) : ℝ → ℝ :=
  fun x => Real.rpow (max x 0) (β/2)

/-- The source symbol is continuous whenever the source exponent is nonnegative. -/
lemma continuous_sourceSymbol {β : ℝ} (h : 0 ≤ β) :
    Continuous (sourceSymbol β) := by
  unfold sourceSymbol
  refine (Real.continuous_rpow_const ?_).comp (continuous_id.max continuous_const)
  linarith

/-- For [a spectral source condition](hyp:_sc), [the spectral-power operator is the real functional-calculus transform of the adjoint-product NPIV operator by the symbol $x\mapsto(\max\{x,0\})^{\beta/2}$](goal).

The operator `(T†T)^{β/2}`, defined as the real CFC of `T†T`
applied to the continuous symbol `x ↦ Real.rpow (max x 0) (β/2)`. -/
noncomputable def spectralPower (_sc : SpectralSourceCondition S β) :
    Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ] Lp ℝ 2 (μ.trim S.m_X_le) :=
  @Complexification.realCFC Ω S.m_X (μ.trim S.m_X_le)
    S.Tstar_T_trim (sourceSymbol β)

/-- Restated spectral identity using `spectralPower`. -/
lemma spectral_identity_h₀ (sc : SpectralSourceCondition S β) :
    S.primalTrimEquiv (S.hL2 S.h₀_mem) =
      sc.spectralPower (S.primalTrimEquiv (S.hL2 sc.w₀_mem)) :=
  sc.spectral_identity

/-! ## Bias constant -/

/-- For [a spectral source condition](hyp:_sc), [the bias constant is $(\max\{1,\lVert T^*T\rVert+1\})^\beta$](goal).

Uniform constant absorbing both regimes (β ≤ 2 and β > 2) of the
sup-on-spectrum analysis.

In the small-β regime (β ≤ 2) the constant is `≤ 1` and the rate is
`λ^β`; in the large-β regime (β > 2) the constant is `‖T†T‖^{β−2}` and
the rate saturates at `λ²`.  We bound both uniformly by
`Real.rpow (max 1 (‖T†T‖+1)) β`. -/
noncomputable def biasConst (_sc : SpectralSourceCondition S β) : ℝ :=
  Real.rpow (max 1 (‖S.Tstar_T_trim‖ + 1)) β

/-- The uniform Tikhonov bias constant is nonnegative. -/
lemma biasConst_nonneg (sc : SpectralSourceCondition S β) :
    0 ≤ sc.biasConst := by
  unfold biasConst
  exact Real.rpow_nonneg (le_max_of_le_left zero_le_one) _

/-! ## Lax–Milgram = resolvent on the full space -/

private lemma reLp_I_smul_local (f : Lp ℂ 2 μ) :
    Complexification.reLp ((Complex.I : ℂ) • f) = -Complexification.imLp f := by
  apply Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) ((Complex.I : ℂ) • f),
        Lp.coeFn_smul (Complex.I : ℂ) f,
        Lp.coeFn_neg (Complexification.imLp f),
        ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) f]
    with ω h_re h_smul h_neg h_f
  rw [h_neg]
  simp only [Pi.neg_apply]
  rw [show (((Complexification.reLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_re]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.imLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    -((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).im)
  simp

private lemma imLp_I_smul_local (f : Lp ℂ 2 μ) :
    Complexification.imLp ((Complex.I : ℂ) • f) = Complexification.reLp f := by
  apply Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) ((Complex.I : ℂ) • f),
        Lp.coeFn_smul (Complex.I : ℂ) f,
        ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_im h_smul h_f
  rw [show (((Complexification.imLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.imLp] using h_im]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).im =
    (((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re
  simp

private lemma reLp_ofReal_smul_local (r : ℝ) (f : Lp ℂ 2 μ) :
    Complexification.reLp ((r : ℂ) • f) = r • Complexification.reLp f := by
  apply Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) ((r : ℂ) • f),
        Lp.coeFn_smul (r : ℂ) f,
        Lp.coeFn_smul r (Complexification.reLp f),
        ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_re_smul h_smul h_rhs h_re
  rw [h_rhs]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.reLp ((r : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((r : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_re_smul]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_re]
  change ((r : ℂ) * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    r * ((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re)
  simp

private lemma reLp_complexLift_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    Complexification.reLp (Complexification.complexLift A f) = A (Complexification.reLp f) := by
  rw [Complexification.complexLift_apply]
  simp [map_add, reLp_I_smul_local, Complexification.reLp_comp_ιLp,
    Complexification.imLp_comp_ιLp]

private lemma imLp_complexLift_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    Complexification.imLp (Complexification.complexLift A f) = A (Complexification.imLp f) := by
  rw [Complexification.complexLift_apply]
  simp [map_add, imLp_I_smul_local, Complexification.reLp_comp_ιLp,
    Complexification.imLp_comp_ιLp]

private lemma complexLift_one_local :
    Complexification.complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [Complexification.complexLift_apply] using
    Complexification.reLp_add_smul_imLp (μ := μ) f

private lemma complexLift_comp_local (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Complexification.complexLift (A.comp B) =
      (Complexification.complexLift A).comp (Complexification.complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [Complexification.complexLift_apply, Complexification.complexLift_apply]
  rw [reLp_complexLift_local, imLp_complexLift_local]
  rfl

private lemma complexLift_mul_local (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Complexification.complexLift (A * B) =
      Complexification.complexLift A * Complexification.complexLift B := by
  exact complexLift_comp_local A B

private lemma complexLift_sub_local (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Complexification.complexLift (A - B) =
      Complexification.complexLift A - Complexification.complexLift B := by
  ext1 f
  rw [Complexification.complexLift_apply]
  change Complexification.ιLp (A (Complexification.reLp f) - B (Complexification.reLp f)) +
      Complex.I • Complexification.ιLp
        (A (Complexification.imLp f) - B (Complexification.imLp f)) =
    Complexification.complexLift A f - Complexification.complexLift B f
  rw [Complexification.complexLift_apply A f, Complexification.complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

private lemma complexLift_algebraMap_real_local (r : ℝ) :
    Complexification.complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [Complexification.complexLift_apply]
  change Complexification.ιLp (r • Complexification.reLp f) +
      Complex.I • Complexification.ιLp (r • Complexification.imLp f) = (r : ℂ) • f
  calc
    Complexification.ιLp (r • Complexification.reLp f) +
        Complex.I • Complexification.ιLp (r • Complexification.imLp f)
        = (r : ℂ) • (Complexification.ιLp (Complexification.reLp f) +
            Complex.I • Complexification.ιLp (Complexification.imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • Complexification.ιLp (Complexification.imLp f)) =
        (r : ℂ) • (Complex.I • Complexification.ιLp (Complexification.imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [Complexification.reLp_add_smul_imLp]

private lemma complexLift_resolvent_real_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - Complexification.complexLift A =
      Complexification.complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [complexLift_sub_local, complexLift_algebraMap_real_local]

private lemma complexLift_isUnit_local
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (Complexification.complexLift B) := by
  have hone : Complexification.complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    exact complexLift_one_local (μ := μ)
  refine Units.isUnit
    ⟨Complexification.complexLift B, Complexification.complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      Complexification.complexLift B * Complexification.complexLift ↑hB.unit⁻¹
          = Complexification.complexLift (B * ↑hB.unit⁻¹) := by
        rw [complexLift_mul_local]
      _ = Complexification.complexLift 1 := by
        exact congrArg (fun T => Complexification.complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      Complexification.complexLift ↑hB.unit⁻¹ * Complexification.complexLift B
          = Complexification.complexLift (↑hB.unit⁻¹ * B) := by
        rw [complexLift_mul_local]
      _ = Complexification.complexLift 1 := by
        exact congrArg (fun T => Complexification.complexLift T) hB.val_inv_mul
      _ = 1 := hone

private theorem spectrum_complexLift_subset_real_local
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (Complexification.complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) -
        Complexification.complexLift A) := by
    rw [complexLift_resolvent_real_local]
    exact complexLift_isUnit_local hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (Complexification.complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (Complexification.complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

/-- Given [a continuous linear operator and two real functions](hyp:Ω,μ,A,f,g), if [the functions
agree on the operator's spectrum](hyp:h) and [the operator is self-adjoint](hyp:hA), then [their real
continuous functional calculi at that operator agree](goal). -/
lemma realCFC_congr_on_spectrum_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f g : ℝ → ℝ)
    (h : ∀ x ∈ spectrum ℝ A, f x = g x) (hA : IsSelfAdjoint A) :
    Complexification.realCFC A f = Complexification.realCFC A g := by
  apply ContinuousLinearMap.ext
  intro v
  change Complexification.reLp (cfc (fun z : ℂ => (f z.re : ℂ))
      (Complexification.complexLift A) (Complexification.ιLp v)) =
    Complexification.reLp (cfc (fun z : ℂ => (g z.re : ℂ))
      (Complexification.complexLift A) (Complexification.ιLp v))
  congr 2
  apply cfc_congr
  intro z hz
  have hzr : z.re ∈ spectrum ℝ A := spectrum_complexLift_subset_real_local hA hz
  simpa using congrArg (fun r : ℝ => (r : ℂ)) (h z.re hzr)

private lemma realCFC_const_add
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A) (lambda : ℝ) :
    Complexification.realCFC A (fun x => lambda + x)
      = algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Complexification.realCFC_apply A hA (fun x => lambda + x)
    (continuous_const.add continuous_id) v]
  rw [show (fun z : ℂ => ((lambda + z.re : ℝ) : ℂ)) =
      fun z : ℂ => (lambda : ℂ) + (z.re : ℂ) by
    funext z
    simp]
  have hcl : IsSelfAdjoint (Complexification.complexLift A) :=
    Complexification.complexLift_isSelfAdjoint hA
  rw [cfc_const_add (lambda : ℂ) (fun z : ℂ => (z.re : ℂ))
    (Complexification.complexLift A)]
  change Complexification.reLp
      (((algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (lambda : ℂ) +
          cfc (fun z : ℂ => ((id z.re : ℝ) : ℂ)) (Complexification.complexLift A))
        (Complexification.ιLp v))) =
    ((algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A) v)
  rw [← cfc_real_eq_complex (a := Complexification.complexLift A) (f := id) (ha := hcl)]
  rw [cfc_id ℝ (Complexification.complexLift A) hcl]
  simp only [ContinuousLinearMap.add_apply]
  rw [map_add]
  rw [Algebra.algebraMap_eq_smul_one]
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [reLp_ofReal_smul_local, Complexification.reLp_comp_ιLp,
    Complexification.reLp_complexLift_real]

private lemma resolvent_left_inverse
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (hA_spec : ∀ x ∈ spectrum ℝ A, 0 ≤ x)
    {lambda : ℝ} (hlam : 0 < lambda) :
    (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A).comp
      (Complexification.realCFC A (fun x => x / (lambda + x)))
      = A := by
  rw [← realCFC_const_add A hA lambda]
  have hsafe_ne : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  have hsafe_cont : Continuous (fun x : ℝ => x * (lambda + max 0 x)⁻¹) :=
    continuous_id.mul ((continuous_const.add (continuous_const.max continuous_id)).inv₀ hsafe_ne)
  have hquot : Complexification.realCFC A (fun x => x / (lambda + x)) =
      Complexification.realCFC A (fun x => x * (lambda + max 0 x)⁻¹) := by
    apply realCFC_congr_on_spectrum_local A
    · intro x hx
      have hx0 : 0 ≤ x := hA_spec x hx
      rw [max_eq_right hx0]
      rfl
    · exact hA
  rw [hquot]
  rw [← Complexification.realCFC_mul A hA (fun x => lambda + x)
    (fun x => x * (lambda + max 0 x)⁻¹) (continuous_const.add continuous_id) hsafe_cont]
  have hprod : ∀ x ∈ spectrum ℝ A,
      (lambda + x) * (x * (lambda + max 0 x)⁻¹) = id x := fun x hx => by
    have hx0 : 0 ≤ x := hA_spec x hx
    rw [max_eq_right hx0]
    have hne : lambda + x ≠ 0 := by
      have hpos : 0 < lambda + x := by linarith
      exact ne_of_gt hpos
    calc
      (lambda + x) * (x * (lambda + x)⁻¹)
          = ((lambda + x) * (lambda + x)⁻¹) * x := by ring
      _ = x := by rw [mul_inv_cancel₀ hne, one_mul]
  rw [realCFC_congr_on_spectrum_local A
    (fun x => (lambda + x) * (x * (lambda + max 0 x)⁻¹)) id hprod hA]
  apply ContinuousLinearMap.ext
  intro v
  rw [Complexification.realCFC_id A hA v]

/-- **Resolvent identification of the Lax–Milgram minimiser.** For [any strictly positive
Tikhonov regularization level λ](hyp:lambda_pos), [the population Tikhonov
minimiser at level λ equals the resolvent expression obtained by applying the real functional
calculus of `T†T` to the symbol `x ↦ x/(λ+x)`, evaluated at the L² class of the structural
function `h₀`](goal).

Proof strategy:
* Set `Aλ := realCFC S.Tstar_T (fun x => x / (lambda + x))` and apply
  to `S.hL2 S.h₀_mem`.  Show `Aλ` is the unique element of
  `Lp ℝ 2 (μ.trim S.m_X_le)` satisfying `(T†T + λI) Aλ h₀ = T†T h₀`.
* Use `Complexification.realCFC_resolvent_mul_self` to get
  `(λ+x) · (x/(λ+x)) = x` at the symbol level, hence
  `realCFC (T†T) (fun x => (λ+x) · (x/(λ+x))) = realCFC (T†T) id =
  T†T` (via `realCFC_mul` and `realCFC_id`).
* By the variational identity `tikhonovMinimiserL2_optimality`, the minimiser
  satisfies the same operator equation on the primal space.  Uniqueness
  (from coercivity / strict convexity)
  gives the identification. -/
theorem tikhonovMinimiserL2_eq_resolvent
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
    S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda)
      = @Complexification.realCFC Ω S.m_X (μ.trim S.m_X_le)
          S.Tstar_T_trim (fun x => x / (lambda + x))
          (S.primalTrimEquiv (S.hL2 S.h₀_mem)) := by
  set A := S.Tstar_T_trim with hA_def
  set h₀ := S.primalTrimEquiv (S.hL2 S.h₀_mem) with hh₀_def
  set R : Lp ℝ 2 (μ.trim S.m_X_le) :=
    @Complexification.realCFC Ω S.m_X (μ.trim S.m_X_le)
      A (fun x => x / (lambda + x)) h₀
  set h_star : Lp ℝ 2 (μ.trim S.m_X_le) :=
    S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda)
  have hvar : ∀ v : Lp ℝ 2 (μ.trim S.m_X_le),
      inner ℝ (S.TlinTrim h_star) (S.TlinTrim v) + lambda * inner ℝ h_star v
        = inner ℝ (S.TlinTrim h₀) (S.TlinTrim v) := by
    intro v
    have hopt := S.tikhonovMinimiserL2_optimality lambda_pos
      (S.primalTrimEquiv.symm v)
    have hinner :
        inner ℝ (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda)) v =
          inner ℝ (S.tikhonovMinimiserL2 lambda)
            (S.primalTrimEquiv.symm v) := by
      calc
        inner ℝ (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda)) v =
            inner ℝ (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda))
              (S.primalTrimEquiv (S.primalTrimEquiv.symm v)) := by
                rw [S.primalTrimEquiv.apply_symm_apply]
        _ = inner ℝ (S.tikhonovMinimiserL2 lambda)
              (S.primalTrimEquiv.symm v) :=
          S.primalTrimEquiv.inner_map_map _ _
    rw [hinner]
    simpa [h_star, h₀, OperatorSystem.TlinTrim] using hopt
  have hop_star :
      S.TadjointTrim (S.TlinTrim h_star) + lambda • h_star =
        S.TadjointTrim (S.TlinTrim h₀) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_add_left, inner_smul_left]
    rw [OperatorSystem.TadjointTrim]
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    simpa using hvar v
  have hop_star' :
      A h_star + lambda • h_star = A h₀ := by
    simpa [hA_def, OperatorSystem.Tstar_T_trim,
      ContinuousLinearMap.comp_apply] using hop_star
  have hA_sa : IsSelfAdjoint A := by
    simpa [hA_def] using S.Tstar_T_trim_isSelfAdjoint
  have hres :
      (algebraMap ℝ
          (Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ]
            Lp ℝ 2 (μ.trim S.m_X_le)) lambda + A) R = A h₀ := by
    have h := @resolvent_left_inverse Ω S.m_X (μ.trim S.m_X_le) A hA_sa (by
      intro x hx
      exact Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)) lambda lambda_pos
    have happ :=
      congrArg (fun T : Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ]
        Lp ℝ 2 (μ.trim S.m_X_le) => T h₀) h
    simpa [R] using happ
  have hop_R : A R + lambda • R = A h₀ := by
    simpa [ContinuousLinearMap.add_apply, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, add_comm] using hres
  have hdiff : A (h_star - R) + lambda • (h_star - R) = 0 := by
    have heq : A h_star + lambda • h_star = A R + lambda • R :=
      hop_star'.trans hop_R.symm
    calc
      A (h_star - R) + lambda • (h_star - R)
          = (A h_star + lambda • h_star) - (A R + lambda • R) := by
        rw [map_sub, smul_sub]
        abel
      _ = 0 := by rw [heq]; simp
  have hpos_self :
      inner ℝ (A (h_star - R)) (h_star - R) = ‖S.TlinTrim (h_star - R)‖ ^ 2 := by
    subst A
    change inner ℝ (S.TadjointTrim (S.TlinTrim (h_star - R))) (h_star - R) = _
    rw [OperatorSystem.TadjointTrim, ContinuousLinearMap.adjoint_inner_left]
    exact real_inner_self_eq_norm_sq _
  have hzero :
      ‖S.TlinTrim (h_star - R)‖ ^ 2 + lambda * ‖h_star - R‖ ^ 2 = 0 := by
    have hpair := congrArg (fun u => inner ℝ u (h_star - R)) hdiff
    simp only [inner_zero_left, inner_add_left, inner_smul_left] at hpair
    have hnorm_sq : inner ℝ (h_star - R) (h_star - R) = ‖h_star - R‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    rw [hpos_self, hnorm_sq] at hpair
    simpa using hpair
  have hsq_zero : ‖h_star - R‖ ^ 2 = 0 := by
    have hT_nn : 0 ≤ ‖S.TlinTrim (h_star - R)‖ ^ 2 := sq_nonneg _
    have hw_nn : 0 ≤ ‖h_star - R‖ := norm_nonneg _
    nlinarith [hzero, hT_nn, lambda_pos, hw_nn]
  have hnorm_zero : ‖h_star - R‖ = 0 := by
    exact sq_eq_zero_iff.mp hsq_zero
  have hsub_zero : h_star - R = 0 := norm_eq_zero.mp hnorm_zero
  simpa [h_star, R, hA_def, h₀] using sub_eq_zero.mp hsub_zero

/-! ## Bias bounds -/

/-- Given [a self-adjoint continuous linear operator](hyp:Ω,μ,A,hA) and [two continuous real
functions](hyp:f,g,hf,hg), [the real continuous functional calculus of their difference equals the
difference of their calculi](goal). -/
lemma realCFC_sub_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Complexification.realCFC A (fun x => f x - g x) =
      Complexification.realCFC A f - Complexification.realCFC A g := by
  ext1 v
  rw [Complexification.realCFC_apply A hA (fun x => f x - g x) (hf.sub hg) v]
  simp only [ContinuousLinearMap.sub_apply]
  rw [Complexification.realCFC_apply A hA f hf v]
  rw [Complexification.realCFC_apply A hA g hg v]
  rw [show (fun z : ℂ => (((f z.re - g z.re : ℝ) : ℂ))) =
      fun z : ℂ => (f z.re : ℂ) - (g z.re : ℂ) by
    funext z
    norm_num]
  rw [cfc_sub (fun z : ℂ => (f z.re : ℂ)) (fun z : ℂ => (g z.re : ℂ))
    (Complexification.complexLift A)
    (hf := (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn)
    (hg := (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn)]
  simp

/-- For [a nonnegative spectral value, a positive regularization level, smoothness between zero and
two, and a scale at least one](hyp:x,lambda,β,B,hl,hx,hβ0,hβ2,hB), [the absolute residual source
symbol is bounded by the stated scale and regularization power](goal). -/
lemma residual_symbol_bound_small
    {x lambda β B : ℝ} (hl : 0 < lambda) (hx : 0 ≤ x)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hB : 1 ≤ B) :
    |(-lambda * sourceSymbol β x / (lambda + max 0 x))| ≤
      B ^ (β / 2) * lambda ^ (min β 2 / 2) := by
  have hb_nonneg : 0 ≤ β / 2 := by linarith
  have hb_le_one : β / 2 ≤ 1 := by linarith
  have hden_pos : 0 < lambda + x := by linarith
  have hden_max : lambda + max 0 x = lambda + x := by rw [max_eq_right hx]
  have hsrc : sourceSymbol β x = x ^ (β / 2) := by
    simp [sourceSymbol, max_eq_left hx]
  have hmin : min β 2 = β := min_eq_left hβ2
  rw [hden_max, hsrc, hmin]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hl]
  rw [abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hden_pos]
  have hx_le_den : x ≤ lambda + x := by linarith
  have hl_le_den : lambda ≤ lambda + x := by linarith
  have hpow_le : x ^ (β / 2) ≤ (lambda + x) ^ (β / 2) :=
    Real.rpow_le_rpow hx hx_le_den hb_nonneg
  have hdiv_le : x ^ (β / 2) / (lambda + x) ≤
      (lambda + x) ^ (β / 2) / (lambda + x) :=
    div_le_div_of_nonneg_right hpow_le (le_of_lt hden_pos)
  have hden_pow : (lambda + x) ^ (β / 2) / (lambda + x) =
      (lambda + x) ^ (β / 2 - 1) := by
    rw [Real.rpow_sub hden_pos, Real.rpow_one]
  have hpow_neg : (lambda + x) ^ (β / 2 - 1) ≤ lambda ^ (β / 2 - 1) := by
    exact Real.rpow_le_rpow_of_nonpos hl hl_le_den (by linarith)
  have hmul_lam : lambda * lambda ^ (β / 2 - 1) = lambda ^ (β / 2) := by
    calc
      lambda * lambda ^ (β / 2 - 1) =
          lambda ^ 1 * lambda ^ (β / 2 - 1) := by simp
      _ = lambda ^ (1 + (β / 2 - 1)) := (Real.rpow_add hl 1 (β / 2 - 1)).symm
      _ = lambda ^ (β / 2) := by ring_nf
  have hsmall : lambda * x ^ (β / 2) / (lambda + x) ≤ lambda ^ (β / 2) := by
    calc
      lambda * x ^ (β / 2) / (lambda + x)
          = lambda * (x ^ (β / 2) / (lambda + x)) := by ring
      _ ≤ lambda * ((lambda + x) ^ (β / 2) / (lambda + x)) := by gcongr
      _ = lambda * (lambda + x) ^ (β / 2 - 1) := by rw [hden_pow]
      _ ≤ lambda * lambda ^ (β / 2 - 1) := by gcongr
      _ = lambda ^ (β / 2) := hmul_lam
  have hBpow : 1 ≤ B ^ (β / 2) := Real.one_le_rpow hB hb_nonneg
  have hlpow_nonneg : 0 ≤ lambda ^ (β / 2) := Real.rpow_nonneg (le_of_lt hl) _
  calc
    lambda * x ^ (β / 2) / (lambda + x) ≤ lambda ^ (β / 2) := hsmall
    _ ≤ B ^ (β / 2) * lambda ^ (β / 2) := by nlinarith

/-- For [a nonnegative spectral value bounded by a scale, a positive regularization level, a
smoothness value above two, and a scale at least one](hyp:x,lambda,β,B,hl,hx,hxB,hβ2,hB), [the
absolute residual source symbol is bounded by the stated scale and regularization power](goal). -/
lemma residual_symbol_bound_large
    {x lambda β B : ℝ} (hl : 0 < lambda) (hx : 0 ≤ x) (hxB : x ≤ B)
    (hβ2 : 2 < β) (hB : 1 ≤ B) :
    |(-lambda * sourceSymbol β x / (lambda + max 0 x))| ≤
      B ^ (β / 2) * lambda ^ (min β 2 / 2) := by
  have hb_pos : 0 < β / 2 := by linarith
  have hb_minus_nonneg : 0 ≤ β / 2 - 1 := by linarith
  have hden_pos : 0 < lambda + x := by linarith
  have hden_max : lambda + max 0 x = lambda + x := by rw [max_eq_right hx]
  have hsrc : sourceSymbol β x = x ^ (β / 2) := by
    simp [sourceSymbol, max_eq_left hx]
  have hmin : min β 2 = 2 := min_eq_right (le_of_lt hβ2)
  rw [hden_max, hsrc, hmin]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hl]
  rw [abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hden_pos]
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hquot : x ^ (β / 2) / (lambda + x) ≤ B ^ (β / 2) := by
    by_cases hxzero : x = 0
    · subst x
      have hb_ne : β / 2 ≠ 0 := ne_of_gt hb_pos
      rw [Real.zero_rpow hb_ne]
      have hden0 : lambda + 0 = lambda := by ring
      rw [hden0, zero_div]
      exact Real.rpow_nonneg (le_of_lt hB_pos) _
    · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      have hx_le_den : x ≤ lambda + x := by linarith
      have hdiv_le : x ^ (β / 2) / (lambda + x) ≤ x ^ (β / 2) / x :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) hx_pos hx_le_den
      have hxpow_div : x ^ (β / 2) / x = x ^ (β / 2 - 1) := by
        rw [Real.rpow_sub hx_pos, Real.rpow_one]
      have hxBpow : x ^ (β / 2 - 1) ≤ B ^ (β / 2 - 1) :=
        Real.rpow_le_rpow hx hxB hb_minus_nonneg
      have hBexp : B ^ (β / 2 - 1) ≤ B ^ (β / 2) :=
        Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      calc
        x ^ (β / 2) / (lambda + x) ≤ x ^ (β / 2) / x := hdiv_le
        _ = x ^ (β / 2 - 1) := hxpow_div
        _ ≤ B ^ (β / 2 - 1) := hxBpow
        _ ≤ B ^ (β / 2) := hBexp
  calc
    lambda * x ^ (β / 2) / (lambda + x)
        = lambda * (x ^ (β / 2) / (lambda + x)) := by ring
    _ ≤ lambda * B ^ (β / 2) := by gcongr
    _ = B ^ (β / 2) * lambda := by ring

end SpectralSourceCondition

end NPIV
end Estimation
end Causalean
