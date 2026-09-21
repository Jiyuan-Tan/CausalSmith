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

/-! # Real-to-complex maps and operator lifts on `L²`

This first implementation part constructs real and imaginary projections, the
isometric real embedding, and the complex lift of a real continuous linear
operator.  It proves reconstruction, adjoint, and self-adjointness laws, then
defines `realCFC` and establishes its application and identity rules.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Complexification

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
/-- For a measurable sample space equipped with a measure, the real-scalar algebra structure on the algebra of continuous complex-linear operators on complex-valued square-integrable functions is obtained by restricting the usual complex scalar algebra to real scalars.

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
two structures agree by `rfl`, so nothing about the mathematics changes. -/
noncomputable local instance (priority := 2000) instAlgebraRealLpCLM :
    Algebra ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Algebra.complexToReal

/-! ## Section 1.  Real ↔ complex `L²` glue -/

/-- For [a measurable sample space](hyp:Ω) equipped with [a measure](hyp:μ), [the real-part operator](goal) maps each complex-valued square-integrable function to its pointwise real part, viewed as a real-valued square-integrable function.

Built from `RCLike.reCLM (K := ℂ) : ℂ →L[ℝ] ℝ` via
`ContinuousLinearMap.compLpL 2 μ`, which lifts a CLM on the value
spaces to a CLM between the corresponding `Lp` spaces.  The `Fact
(1 ≤ (2 : ENNReal))` premise is supplied by `fact_one_le_two_ennreal`. -/
noncomputable def reLp : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.compLpL 2 μ (RCLike.reCLM (K := ℂ))

/-- For [a measurable sample space](hyp:Ω) equipped with [a measure](hyp:μ), [the imaginary-part operator](goal) maps each complex-valued square-integrable function to its pointwise imaginary part, viewed as a real-valued square-integrable function.

Pointwise imaginary part on `L²(Ω, ℂ)`, bundled as a continuous
ℝ-linear map `Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ`.  Same construction as
`reLp` but with `RCLike.imCLM`. -/
noncomputable def imLp : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.compLpL 2 μ (RCLike.imCLM (K := ℂ))

/-- For [a measurable sample space](hyp:Ω) equipped with [a measure](hyp:μ), [the real-to-complex embedding](goal) maps each real-valued square-integrable function to the complex-valued square-integrable function having that real part and zero imaginary part.

Built from `RCLike.ofRealCLM (K := ℂ) : ℝ →L[ℝ] ℂ` via
`ContinuousLinearMap.compLpL 2 μ`. -/
noncomputable def ιLp : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  ContinuousLinearMap.compLpL 2 μ (RCLike.ofRealCLM (K := ℂ))

/-- `reLp` is a left-inverse of `ιLp`.

The pointwise statement is `RCLike.re_ofReal : RCLike.re (r : ℂ) = r`.
The Lp version follows by combining
`ContinuousLinearMap.coeFn_compLpL` (twice — once for `reLp`, once for
`ιLp`) and the pointwise identity, then rewriting back with
`Lp.ext`-style reasoning.  A clean one-liner is:
`simp [reLp, ιLp, ContinuousLinearMap.compLp_compLp, RCLike.reCLM_apply,
RCLike.ofRealCLM_apply, RCLike.re_ofReal]`. -/
lemma reLp_comp_ιLp (f : Lp ℝ 2 μ) : reLp (ιLp f) = f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) (ιLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) f]
    with ω h₁ h₂
  simpa [reLp, ιLp, h₂, RCLike.reCLM_apply, RCLike.ofRealCLM_apply,
    RCLike.ofReal_re] using h₁

/-- The imaginary part vanishes on the image of `ιLp` (pointwise
`RCLike.im_ofReal : RCLike.im (r : ℂ) = 0`). -/
lemma imLp_comp_ιLp (f : Lp ℝ 2 μ) : imLp (ιLp f) = 0 := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) (ιLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) f,
                  (Lp.coeFn_zero ℝ (2 : ENNReal) μ)]
    with ω h₁ h₂ hzero
  have hmain : (((imLp (ιLp f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ))
        ((RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)) := by
    simpa [imLp, ιLp, h₂] using h₁
  calc
    (((imLp (ιLp f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
        (RCLike.imCLM (K := ℂ))
          ((RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)) := hmain
    _ = 0 := by
      change RCLike.im
          ((RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)) = 0
      change RCLike.im ((((f : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ) = 0
      exact RCLike.ofReal_im (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)
    _ = ((0 : Lp ℝ 2 μ) : Ω → ℝ) ω := by rw [hzero]; rfl

/-- `ιLp` is an isometric embedding.  Follows from
`RCLike.ofRealLI` being a `LinearIsometry` and the fact that
`compLpL` of a norm-one CLM preserves norms on `L²`; concretely,
`‖ιLp f‖ = ‖f‖` reduces pointwise to `‖(r : ℂ)‖ = ‖r‖`
(`RCLike.norm_ofReal`). -/
lemma ιLp_isometry (f : Lp ℝ 2 μ) : ‖ιLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) f]
    with ω h
  rw [show (((ιLp f : Lp ℂ 2 μ) : Ω → ℂ) ω) =
      (RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω) by
    simpa [ιLp] using h]
  change ‖(RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)‖ =
      ‖(((f : Lp ℝ 2 μ) : Ω → ℝ) ω)‖
  rw [show (RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      ((((f : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ) by
    rw [RCLike.ofRealCLM_apply]
    rfl]
  exact RCLike.norm_ofReal (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)

/-- **Reconstruction identity**: every complex `L²`-class is the
complex combination of its real and imaginary parts re-embedded via
`ιLp`.  Pointwise this is `RCLike.re_add_im : (r.re : ℂ) + I * r.im = r`.

The displayed form uses the ℂ-action on `Lp ℂ 2 μ` (which is the
standard `Lp` module structure when the value space is ℂ). -/
lemma reLp_add_smul_imLp (f : Lp ℂ 2 μ) :
    ιLp (reLp f) + (Complex.I : ℂ) • ιLp (imLp f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ιLp (reLp f)) ((Complex.I : ℂ) • ιLp (imLp f)),
                  Lp.coeFn_smul (Complex.I : ℂ) (ιLp (imLp f)),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) (reLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) (imLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f,
                  ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) f]
    with ω h_add h_smul h_re_embed h_im_embed h_re h_im
  rw [h_add]
  simp only [Pi.add_apply]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((ιLp (reLp f) : Lp ℂ 2 μ) : Ω → ℂ) ω) =
      (RCLike.ofRealCLM (K := ℂ)) (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) by
    simpa [ιLp] using h_re_embed]
  rw [show (((ιLp (imLp f) : Lp ℂ 2 μ) : Ω → ℂ) ω) =
      (RCLike.ofRealCLM (K := ℂ)) (((imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) by
    simpa [ιLp] using h_im_embed]
  rw [show (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re]
  rw [show (((imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [imLp] using h_im]
  change (RCLike.re (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) : ℂ) +
      Complex.I * (RCLike.im (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) : ℂ) =
    (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)
  rw [mul_comm]
  exact RCLike.re_add_im (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)

/-! ## Section 2.  Operator lift `complexLift` -/

/-- For [a measurable sample space](hyp:Ω) equipped with [a measure](hyp:μ), [a continuous real-linear operator on real-valued square-integrable functions](hyp:A), and [a complex-valued square-integrable function](hyp:f), [the function-level complex lift](goal) is the complex-valued function obtained by applying the operator separately to the real and imaginary parts and then combining the resulting real-valued functions as real part plus $i$ times imaginary part.

The function-level definition of the complex lift.  Given a real
CLM `A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` and a complex `L²` class `f`, the
lift sends `f = (Re f) + i (Im f)` to `A(Re f) + i · A(Im f)` (with
the real outputs re-embedded via `ιLp`).

This is the candidate underlying function for `complexLift`.  ℂ-linearity
of the corresponding map is the only non-trivial obligation: it follows
from ℝ-linearity of `A`, `reLp`, `imLp`, `ιLp`, plus the fact that
multiplication by `i` permutes real and imaginary parts. -/
noncomputable def complexLiftFun
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ιLp (A (reLp f)) + (Complex.I : ℂ) • ιLp (A (imLp f))

private lemma reLp_I_smul (f : Lp ℂ 2 μ) :
    reLp ((Complex.I : ℂ) • f) = -imLp f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ))
                    ((Complex.I : ℂ) • f),
                  Lp.coeFn_smul (Complex.I : ℂ) f,
                  Lp.coeFn_neg (imLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) f]
    with ω h_re h_smul h_neg h_f
  rw [h_neg]
  simp only [Pi.neg_apply]
  rw [show (((reLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [imLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    -((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).im)
  simp

private lemma imLp_I_smul (f : Lp ℂ 2 μ) :
    imLp ((Complex.I : ℂ) • f) = reLp f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ))
                    ((Complex.I : ℂ) • f),
                  Lp.coeFn_smul (Complex.I : ℂ) f,
                  ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_im h_smul h_f
  rw [show (((imLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [imLp] using h_im]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).im =
    (((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re
  simp

/-- Multiplication by the imaginary unit is a continuous real-linear transformation of
complex-valued square-integrable functions. This helper supplies the imaginary-component
transformation used to lift real NPIV operators to complex functions. -/
noncomputable def I_smulCLM : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  let L : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun f => (Complex.I : ℂ) • f
      map_add' := by
        intro f g
        simp [smul_add]
      map_smul' := by
        intro r f
        apply Lp.ext
        filter_upwards [Lp.coeFn_smul (Complex.I : ℂ) (r • f),
                        Lp.coeFn_smul r f,
                        Lp.coeFn_smul r ((Complex.I : ℂ) • f),
                        Lp.coeFn_smul (Complex.I : ℂ) f]
          with ω h_left h_rf h_right h_if
        change ((((Complex.I : ℂ) • (r • f : Lp ℂ 2 μ) : Lp ℂ 2 μ) : Ω → ℂ) ω) =
          (((r • ((Complex.I : ℂ) • f) : Lp ℂ 2 μ) : Ω → ℂ) ω)
        rw [h_left, h_right]
        simp only [Pi.smul_apply]
        rw [h_rf, h_if]
        change Complex.I * ((r : ℂ) * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)) =
          (r : ℂ) * (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω))
        ring }
  L.mkContinuous 1 (by
    intro f
    rw [show ‖L f‖ = ‖f‖ by
      change ‖(Complex.I : ℂ) • f‖ = ‖f‖
      simpa using (norm_smul (Complex.I : ℂ) f)]
    rw [one_mul])

private lemma complexLiftFun_I_smul
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    complexLiftFun A ((Complex.I : ℂ) • f) = (Complex.I : ℂ) • complexLiftFun A f := by
  simp [complexLiftFun, reLp_I_smul, imLp_I_smul, map_neg, smul_add, smul_smul,
    add_comm]

private lemma complexLiftFun_map_smul
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    complexLiftFun A (c • f) = c • complexLiftFun A f := by
  let M : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
    (ιLp.comp (A.comp reLp)) + (I_smulCLM.comp (ιLp.comp (A.comp imLp)))
  have hM : ∀ g, M g = complexLiftFun A g := by
    intro g
    rfl
  have hI : ∀ g, M ((Complex.I : ℂ) • g) = (Complex.I : ℂ) • M g := by
    intro g
    rw [hM, hM]
    exact complexLiftFun_I_smul A g
  calc
    complexLiftFun A (c • f) = M (c • f) := by rw [hM]
    _ = M (((c.re : ℂ) + Complex.I * (c.im : ℂ)) • f) := by
      rw [show (c.re : ℂ) + Complex.I * (c.im : ℂ) = c by
        rw [mul_comm]
        exact RCLike.re_add_im c]
    _ = M (((c.re : ℂ) • f) + ((Complex.I * (c.im : ℂ)) • f)) := by
      rw [add_smul]
    _ = M ((c.re : ℝ) • f) + M ((Complex.I : ℂ) • ((c.im : ℝ) • f)) := by
      rw [map_add, mul_smul]
      rfl
    _ = (c.re : ℝ) • M f + (Complex.I : ℂ) • ((c.im : ℝ) • M f) := by
      rw [M.map_smul, hI, M.map_smul]
    _ = ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • M f := by
      rw [add_smul, mul_smul]
      rfl
    _ = c • complexLiftFun A f := by
      rw [show (c.re : ℂ) + Complex.I * (c.im : ℂ) = c by
        rw [mul_comm]
        exact RCLike.re_add_im c, hM]

/-- For [a measurable sample space](hyp:Ω) equipped with [a measure](hyp:μ) and [a continuous real-linear operator on real-valued square-integrable functions](hyp:A), [the complex lift](goal) is the continuous complex-linear operator on complex-valued square-integrable functions that applies the original operator separately to real and imaginary parts. It [first forms the continuous real-linear operator that combines the separately transformed components](step:1), then bundles that operator as a complex-linear map.

**Complex lift** of a real CLM.

`complexLift A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` is the unique ℂ-linear
continuous extension of `A` to the complexified `L²`.  Its underlying
function is `complexLiftFun A` (see `complexLift_apply` below).

Construction strategy for the proof-filler: build the bare `LinearMap`
over ℂ from `complexLiftFun A` (additivity is direct from additivity of
`reLp`, `imLp`, `ιLp` and `A`; ℂ-linearity reduces, after writing every
`c : ℂ` as `c.re + i c.im`, to ℝ-linearity of `A`), then bundle to a
`ContinuousLinearMap` via `LinearMap.mkContinuous` with a norm bound of
roughly `2 * ‖A‖` coming from
`‖ιLp (A (reLp f)) + I • ιLp (A (imLp f))‖ ≤ ‖A‖ ‖reLp f‖ + ‖A‖ ‖imLp f‖
≤ 2 ‖A‖ ‖f‖`. -/
noncomputable def complexLift
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let M : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
    (ιLp.comp (A.comp reLp)) + (I_smulCLM.comp (ιLp.comp (A.comp imLp)))
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := M
      map_add' := by
        intro f g
        exact M.map_add f g
      map_smul' := by
        intro c f
        simpa [M, complexLiftFun, I_smulCLM] using complexLiftFun_map_smul A c f }
  L.mkContinuous ‖M‖ (by
    intro f
    have h := M.le_opNorm f
    simpa [L] using h)

/-- The action equation for `complexLift`: it agrees with
`complexLiftFun A` on every input.

This is the contract that downstream proofs will rewrite by — together
with `reLp_comp_ιLp` and `imLp_comp_ιLp`, it is enough to compute
`complexLift A` on explicit elements of `Lp ℂ 2 μ`. -/
theorem complexLift_apply (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    complexLift A f
      = ιLp (A (reLp f)) + (Complex.I : ℂ) • ιLp (A (imLp f)) := by
  rfl

/-- Restriction of the complex lift to the real subspace recovers `A`.
`reLp_comp_ιLp` gives `reLp (ιLp g) = g` and `imLp_comp_ιLp` gives
`imLp (ιLp g) = 0`, so `complexLift_apply` collapses to
`ιLp (A g) + I • ιLp (A 0) = ιLp (A g)`. -/
theorem complexLift_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (g : Lp ℝ 2 μ) :
    complexLift A (ιLp g) = ιLp (A g) := by
  rw [complexLift_apply, reLp_comp_ιLp, imLp_comp_ιLp]
  simp

/-- Corollary of `complexLift_real`: projecting back via `reLp` gives
exactly `A g`.  Direct from `reLp_comp_ιLp`. -/
theorem reLp_complexLift_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (g : Lp ℝ 2 μ) :
    reLp (complexLift A (ιLp g)) = A g := by
  rw [complexLift_real, reLp_comp_ιLp]

/-! ## Section 3.  Adjoint and self-adjointness compatibility -/

private lemma inner_ιLp (u v : Lp ℝ 2 μ) :
    inner ℂ (ιLp u : Lp ℂ 2 μ) (ιLp v) = ((inner ℝ u v : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ a : Ω, inner ℂ (((ιLp u : Lp ℂ 2 μ) : Ω → ℂ) a)
        (((ιLp v : Lp ℂ 2 μ) : Ω → ℂ) a) ∂μ)
        = ∫ a : Ω, ((inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) a)
          (((v : Lp ℝ 2 μ) : Ω → ℝ) a) : ℝ) : ℂ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) u,
                          ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) v]
            with ω hu hv
          rw [show (((ιLp u : Lp ℂ 2 μ) : Ω → ℂ) ω) =
              (RCLike.ofRealCLM (K := ℂ)) (((u : Lp ℝ 2 μ) : Ω → ℝ) ω) by
            simpa [ιLp] using hu]
          rw [show (((ιLp v : Lp ℂ 2 μ) : Ω → ℂ) ω) =
              (RCLike.ofRealCLM (K := ℂ)) (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) by
            simpa [ιLp] using hv]
          change inner ℂ (((((u : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ))
              (((((v : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ)) =
            ((inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) ω)
              (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) : ℝ) : ℂ)
          rw [RCLike.inner_apply]
          rw [show inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) ω)
              (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) =
              (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) *
                (((u : Lp ℝ 2 μ) : Ω → ℝ) ω) by
            rfl]
          simp [mul_comm]
    _ = ((∫ a : Ω, inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) a)
          (((v : Lp ℝ 2 μ) : Ω → ℝ) a) ∂μ : ℝ) : ℂ) := by
          exact (integral_ofReal (𝕜 := ℂ) (μ := μ)
            (f := fun a : Ω => inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) a)
              (((v : Lp ℝ 2 μ) : Ω → ℝ) a)))

/-- Given [a real continuous linear operator on a square-integrable space and a complex-valued
square-integrable function](hyp:Ω,μ,A,f), [the real part of the operator's complexification equals
the original operator applied to the function's real part](goal). -/
lemma reLp_complexLift
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    reLp (complexLift A f) = A (reLp f) := by
  rw [complexLift_apply]
  simp [map_add, reLp_I_smul, reLp_comp_ιLp, imLp_comp_ιLp]

/-- Given [a real continuous linear operator on a square-integrable space and a complex-valued
square-integrable function](hyp:Ω,μ,A,f), [the imaginary part of the operator's complexification
equals the original operator applied to the function's imaginary part](goal). -/
lemma imLp_complexLift
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    imLp (complexLift A f) = A (imLp f) := by
  rw [complexLift_apply]
  simp [map_add, imLp_I_smul, reLp_comp_ιLp, imLp_comp_ιLp]

private lemma inner_ιLp_right (u : Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    inner ℂ (ιLp u : Lp ℂ 2 μ) f =
      ((inner ℝ u (reLp f) : ℝ) : ℂ) +
        Complex.I * ((inner ℝ u (imLp f) : ℝ) : ℂ) := by
  rw [← reLp_add_smul_imLp f]
  simp [inner_add_right, inner_smul_right, inner_ιLp, reLp_comp_ιLp,
    imLp_comp_ιLp, reLp_I_smul, imLp_I_smul]

private lemma complexLift_adjoint_apply_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (g : Lp ℝ 2 μ) :
    (complexLift A).adjoint (ιLp g) = ιLp (A.adjoint g) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_ιLp_right, inner_ιLp_right]
  rw [reLp_complexLift, imLp_complexLift]
  rw [ContinuousLinearMap.adjoint_inner_left A (reLp f) g,
      ContinuousLinearMap.adjoint_inner_left A (imLp f) g]

/-- For [a measurable sample space with a measure](hyp:Ω,μ) and [a continuous real-linear
operator on real-valued square-integrable functions](hyp:A), [complexifying the operator and
then taking its adjoint gives the same operator as complexifying its real adjoint](goal).

The complex lift commutes with taking adjoints.

Proof strategy: by definition of the adjoint via the inner product
identity `⟪(complexLift A).adjoint x, y⟫ = ⟪x, complexLift A y⟫`,
and `⟪ιLp u, ιLp v⟫_ℂ = (⟪u, v⟫_ℝ : ℂ)` (the inner product on
`Lp ℂ 2 μ` restricts on the real subspace to that of `Lp ℝ 2 μ`).  The
key Mathlib lemma is `ContinuousLinearMap.adjoint_inner_left` /
`adjoint_inner_right`. -/
theorem complexLift_adjoint (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    (complexLift A).adjoint = complexLift A.adjoint := by
  ext f
  rw [← reLp_add_smul_imLp f]
  rw [map_add, map_smul]
  rw [complexLift_adjoint_apply_real, complexLift_adjoint_apply_real]
  rw [complexLift_apply]
  simp [map_add, reLp_comp_ιLp, imLp_comp_ιLp, reLp_I_smul, imLp_I_smul]

/-- Self-adjointness is preserved by the complex lift.  Direct
corollary of `complexLift_adjoint` (rewrite `A.adjoint = A` inside the
RHS). -/
theorem complexLift_isSelfAdjoint
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (complexLift A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [complexLift_adjoint, hA.adjoint_eq]

/-! ## Section 4.  Real CFC via complexification -/

/-- Given [a real scalar and a complex-valued square-integrable function](hyp:Ω,μ,r,f), [the
real part of their scalar product is the scalar times the function's real part](goal). -/
lemma reLp_ofReal_smul (r : ℝ) (f : Lp ℂ 2 μ) :
    reLp ((r : ℂ) • f) = r • reLp f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) ((r : ℂ) • f),
                  Lp.coeFn_smul (r : ℂ) f,
                  Lp.coeFn_smul r (reLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_re_smul h_smul h_rhs h_re
  rw [h_rhs]
  simp only [Pi.smul_apply]
  rw [show (((reLp ((r : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((r : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re_smul]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re]
  change ((r : ℂ) * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    r * ((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re)
  simp

/-- Given [a complex-valued and a real-valued square-integrable function](hyp:Ω,μ,u,v), [the
real inner product of the first function's real part with the second equals the real part of the
complex inner product with the complex embedding of the second](goal). -/
lemma inner_reLp_left (u : Lp ℂ 2 μ) (v : Lp ℝ 2 μ) :
    inner ℝ (reLp u) v = (inner ℂ u (ιLp v)).re := by
  have h := inner_ιLp_right (μ := μ) v u
  calc
    inner ℝ (reLp u) v = inner ℝ v (reLp u) := by rw [real_inner_comm]
    _ = (inner ℂ (ιLp v) u).re := by
      rw [h]
      simp
    _ = (inner ℂ u (ιLp v)).re := by
      simpa using (inner_re_symm (𝕜 := ℂ) (x := u) (y := ιLp v)).symm

/-- For [a measurable sample space](hyp:Ω) equipped with [a measure](hyp:μ), [a continuous real-linear operator on real-valued square-integrable functions](hyp:A), and [a real-valued function of a real argument](hyp:f), [the real continuous-functional-calculus operator](goal) applies the complex continuous functional calculus to the complex lift of the operator with the symbol extended from the real part, then restricts the result back to real-valued square-integrable functions. It [first constructs the complex functional-calculus operator](step:1), then bundles its real-valued restriction as a continuous real-linear operator.

**Real CFC by complexification.**

Given a real CLM `A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` and a real-to-real
continuous symbol `f : ℝ → ℝ`, this is the operator obtained by
complexifying `A` via `complexLift`, applying Mathlib's complex `cfc`
with the lifted symbol `fun z : ℂ => (f z.re : ℂ)`, and projecting
back via `reLp` (precomposed with `ιLp`).

The action equation is `realCFC_apply` below; the algebra laws
`realCFC_id`, `realCFC_mul`, `realCFC_resolvent_mul_self`, and
`realCFC_norm_le` are the API used by the spectral rate proof.

The construction bundles the function
`fun g : Lp ℝ 2 μ =>
    reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp g))`
as a `ContinuousLinearMap` over ℝ.  ℝ-linearity follows from
ℂ-linearity of `cfc … (complexLift A)` and the fact that `ιLp` is
ℝ-linear and `reLp` is ℝ-linear.  Continuity follows from
boundedness of `cfc f a` (mathlib lemma
`cfc_apply_continuous` / `IsometricContinuousFunctionalCalculus`). -/
noncomputable def realCFC
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : ℝ → ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  let C : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A)
  let L : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun g => reLp (C (ιLp g))
      map_add' := by
        intro x y
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro r x
        simp only [map_smul]
        change reLp (C ((r : ℂ) • ιLp x)) = r • reLp (C (ιLp x))
        rw [C.map_smul]
        exact reLp_ofReal_smul r (C (ιLp x)) }
  L.mkContinuous (‖reLp (μ := μ)‖ * ‖C‖ * ‖ιLp (μ := μ)‖) (by
    intro x
    calc
      ‖L x‖ = ‖reLp (C (ιLp x))‖ := rfl
      _ ≤ ‖reLp (μ := μ)‖ * ‖C (ιLp x)‖ := reLp.le_opNorm (C (ιLp x))
      _ ≤ ‖reLp (μ := μ)‖ * (‖C‖ * ‖ιLp x‖) := by
        gcongr
        exact C.le_opNorm (ιLp x)
      _ ≤ ‖reLp (μ := μ)‖ * (‖C‖ * (‖ιLp (μ := μ)‖ * ‖x‖)) := by
        gcongr
        exact ιLp.le_opNorm x
      _ = ‖reLp (μ := μ)‖ * ‖C‖ * ‖ιLp (μ := μ)‖ * ‖x‖ := by ring)

/-- **Action equation for `realCFC`** — the basic rewrite rule used by
spectral proofs.

Given a self-adjoint real CLM `A` and a continuous real symbol `f`,
`realCFC A f g` equals the real part of
`cfc (f ∘ Complex.re) (complexLift A) (ιLp g)`. -/
theorem realCFC_apply
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (g : Lp ℝ 2 μ) :
    realCFC A f g
      = reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp g)) := by
  have _hA : IsSelfAdjoint A := hA
  have _hf : Continuous f := hf
  rfl

/-- **`realCFC` of the identity symbol recovers `A`.**

Pointwise on the complex side, `cfc (fun z => z) (complexLift A) =
complexLift A` (`cfc_id`).  Combined with `complexLift_real` and
`reLp_comp_ιLp` this collapses to `A g`.

Note: the symbol here is `(id : ℝ → ℝ)`; the lifted symbol
`fun z : ℂ => ((id z.re : ℝ) : ℂ) = (z.re : ℂ)` is *not* `cfc_id`
directly but rather agrees with the identity on the spectrum of
`complexLift A` because `complexLift` of a self-adjoint real CLM has
real spectrum (`IsSelfAdjoint.spectrumRestricts`). -/
theorem realCFC_id
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (g : Lp ℝ 2 μ) :
    realCFC A id g = A g := by
  rw [realCFC_apply A hA id continuous_id g]
  have hcl : IsSelfAdjoint (complexLift A) := complexLift_isSelfAdjoint hA
  rw [← cfc_real_eq_complex (a := complexLift A) (f := id) (ha := hcl)]
  rw [cfc_id ℝ (complexLift A) hcl]
  exact reLp_complexLift_real A g

/- A composition law `realCFC A (f ∘ g) = …` is intentionally not part of
   this API.  The naive shape `realCFC A (f ∘ g) = (realCFC A f).comp
   (realCFC A g)` is mathematically false: composition of CFC operators
   corresponds to *multiplication* of symbols (`cfc f a * cfc g a = cfc
   (f * g) a`), not composition.  The correct CFC composition law
   `cfc (f ∘ g) a = cfc f (cfc g a)` would translate, in this real-CFC
   setting, to `realCFC A (f ∘ g) = realCFC (realCFC A g) f` — which
   additionally requires `complexLift (realCFC A g) = cfc (g ∘ Complex.re)
   (complexLift A)` (real-subspace preservation of the complex CFC of a
   real symbol).  No current rate-proof consumer needs that extra API. -/

end Complexification
end NPIV
end Estimation
end Causalean
