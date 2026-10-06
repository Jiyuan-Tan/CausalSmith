/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Population Tikhonov minimiser via Lax–Milgram

Hilbert-space construction of the population Tikhonov minimiser and the
strong-convexity inequality used by the NPIV primal rate proof.  These facts
are deliberately separated from the spectral source-condition argument: this
file uses Lax–Milgram on the primal Hilbert space `L²(σ(X))`, while
`Operator/SpectralCalculus.lean` supplies the later resolvent and bias bounds.

## Outputs

For an `OperatorSystem Ω μ`:

* `OperatorSystem.tikhonovBilin S λ : L²(σ(X)) →L[ℝ] L²(σ(X)) →L[ℝ] ℝ` —
  the bilinear form `(u, v) ↦ ⟨T u, T v⟩ + λ ⟨u, v⟩`.
* `OperatorSystem.tikhonovBilin_isCoercive` (for `0 < λ`) — the bilinear
  form is coercive with constant `λ`.
* `OperatorSystem.tikhonovMinimiserL2 S λ : L²(σ(X))` — the L²-level
  Tikhonov minimiser, defined for `0 < λ` via Lax–Milgram,
  with arbitrary value (`0`) for `λ ≤ 0`.
* `OperatorSystem.tikhonovMinimiserL2_optimality` — the variational
  identity `⟨T h*, T v⟩ + λ ⟨h*, v⟩ = ⟨T h₀, T v⟩` for every `v`.
* `OperatorSystem.tikhonovMinimiserL2_strong_convexity` — the population
  strong-convexity inequality at the minimiser:

      λ ‖ĥ − h*‖² + ‖T(ĥ − h*)‖²
        ≤ ‖T(ĥ − h₀)‖² − ‖T(h* − h₀)‖² + λ(‖ĥ‖² − ‖h*‖²)

  for every `ĥ ∈ L²(σ(X))`.

The proof of strong convexity is the second-order Taylor identity at the
minimiser; the first-order term vanishes by `tikhonovMinimiserL2_optimality`.

Together these declarations provide the L² minimiser, its variational
identity, and the strong-convexity bound consumed by the spectral discharge in
`Operator/SpectralCalculus.lean`.
-/

module
public import Causalean.Estimation.NPIV.Operator.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Develops the Hilbert-space Tikhonov interface for NPIV inverse problems.
The module defines `OperatorSystem.tikhonovBilin`,
`OperatorSystem.tikhonovTarget`, and
`OperatorSystem.tikhonovMinimiserL2`; proves coercivity and the minimizer's
variational identity; and exposes
`OperatorSystem.tikhonovMinimiserL2_strong_convexity`, the L²-level population
strong-convexity inequality used by the primal rate theorem.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV

namespace OperatorSystem

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The Tikhonov bilinear form on the ambient space -/

/-- For [an NPIV operator system](hyp:S) and [a real regularization level](hyp:lambda), [the primal Tikhonov bilinear form sends two elements $u,v$ of `L²(σ(X))` to $\langle Tu,Tv\rangle+\lambda\langle u,v\rangle$](goal).

The **Tikhonov bilinear form** on `L²(σ(X))`:

    `tikhonovBilin λ u v := ⟪T u, T v⟫_{L²(μ)} + λ · ⟪u, v⟫_{L²(μ)}`.

For `0 < λ`, it is coercive with constant `λ`. -/
noncomputable def tikhonovBilin (S : OperatorSystem Ω μ) (lambda : ℝ) :
    S.PrimalL2 →L[ℝ] S.PrimalL2 →L[ℝ] ℝ :=
  (((innerSL ℝ : S.InstrumentL2 →L[ℝ] S.InstrumentL2 →L[ℝ] ℝ).comp
      S.Tlin).flip.comp S.Tlin).flip
    + lambda • (innerSL ℝ : S.PrimalL2 →L[ℝ] S.PrimalL2 →L[ℝ] ℝ)

/-- Pointwise formula for `tikhonovBilin`. -/
lemma tikhonovBilin_apply (S : OperatorSystem Ω μ) (lambda : ℝ)
    (u v : S.PrimalL2) :
    S.tikhonovBilin lambda u v
      = inner ℝ (S.Tlin u) (S.Tlin v) + lambda * inner ℝ u v := by
  change (((((innerSL ℝ : S.InstrumentL2 →L[ℝ] S.InstrumentL2 →L[ℝ] ℝ).comp
      S.Tlin).flip.comp S.Tlin).flip
        + lambda • (innerSL ℝ : S.PrimalL2 →L[ℝ] S.PrimalL2 →L[ℝ] ℝ)) u v)
    = inner ℝ (S.Tlin u) (S.Tlin v) + lambda * inner ℝ u v
  simp [coe_innerSL_apply]

/-- Symmetry of `tikhonovBilin`. -/
lemma tikhonovBilin_symm (S : OperatorSystem Ω μ) (lambda : ℝ)
    (u v : S.PrimalL2) :
    S.tikhonovBilin lambda u v = S.tikhonovBilin lambda v u := by
  simp [tikhonovBilin_apply, real_inner_comm]

/-- For [a nonparametric instrumental-variables operator system](hyp:Ω,μ,S) and [a strictly
positive regularization level](hyp:lambda,lambda_pos), [the primal Tikhonov bilinear form is coercive](goal). -/
lemma tikhonovBilin_isCoercive
    (S : OperatorSystem Ω μ)
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
    IsCoercive (S.tikhonovBilin lambda) := by
  refine ⟨lambda, lambda_pos, ?_⟩
  intro u
  change lambda * ‖u‖ * ‖u‖ ≤ S.tikhonovBilin lambda u u
  rw [tikhonovBilin_apply]
  simp
  nlinarith [sq_nonneg ‖S.Tlin u‖]

/-! ## The Tikhonov target functional -/

/-- For [an NPIV operator system](hyp:S), [the Tikhonov target functional sends each element of `L²(σ(X))` to the inner product of its transformed image with the transformed structural function](goal).

The **Tikhonov target functional** on the primal Hilbert space:

    `tikhonovTarget v := ⟪T h₀, T v⟫_{L²(σ(Z))}`. -/
noncomputable def tikhonovTarget (S : OperatorSystem Ω μ) :
    S.PrimalL2 →L[ℝ] ℝ :=
  ((innerSL ℝ : S.InstrumentL2 →L[ℝ] S.InstrumentL2 →L[ℝ] ℝ)
      (S.Tlin (S.hL2 S.h₀_mem))).comp S.Tlin

/-- Pointwise formula for the target functional. -/
lemma tikhonovTarget_apply (S : OperatorSystem Ω μ) (v : S.PrimalL2) :
    S.tikhonovTarget v
      = inner ℝ (S.Tlin (S.hL2 S.h₀_mem)) (S.Tlin v) := by
  simp [tikhonovTarget, coe_innerSL_apply]

/-! ## The L²-level Tikhonov minimiser via Lax–Milgram -/

/-- For [an NPIV operator system](hyp:S) and [a real regularization level](hyp:lambda), [the population Tikhonov minimiser is the unique variational solution in `L²(σ(X))` when λ is positive, and is zero otherwise](goal). [The construction applies Lax–Milgram to the coercive Tikhonov form and target functional for positive λ, and returns zero otherwise](step:1).

The **population Tikhonov minimiser** at level `λ` (L² level).

For `0 < λ`, defined as the unique `h*_λ ∈ L²(σ(X))` such that

    `tikhonovBilin λ h*_λ v = ⟪T h₀, T v⟫_{L²(μ)}`

for every `v`, obtained from Mathlib's `IsCoercive.continuousLinearEquivOfBilin`
applied to `tikhonovBilin_isCoercive`. For `λ ≤ 0` this returns `0` —
the optimality and pullback theorems below assume `0 < λ`. -/
noncomputable def tikhonovMinimiserL2
    (S : OperatorSystem Ω μ) (lambda : ℝ) : S.PrimalL2 :=
  if h : 0 < lambda then
    let complete : CompleteSpace S.PrimalL2 := inferInstance
    let coercive := tikhonovBilin_isCoercive S h
    let Bsharp :=
      @IsCoercive.continuousLinearEquivOfBilin S.PrimalL2 _ _ complete
        (S.tikhonovBilin lambda) coercive
    let w : S.PrimalL2 :=
      (@InnerProductSpace.toDual ℝ S.PrimalL2 _ _ _ complete).symm S.tikhonovTarget
    Bsharp.symm w
  else
    0

/-- **Variational identity for the Tikhonov minimiser.** For [a strictly positive Tikhonov
regularization level λ](hyp:lambda_pos) and [any element `v` of `L²(σ(X))`](hyp:v), [the population Tikhonov minimiser `h*_λ` at level λ satisfies the
identity `⟪T h*_λ, T v⟫ + λ · ⟪h*_λ, v⟫ = ⟪T h₀, T v⟫`, where `T` is the projection-composed
conditional-expectation operator and `h₀` is the L² class of the structural function](goal).

Direct restatement of the Lax–Milgram identity `tikhonovBilin h*_λ v = tikhonovTarget v`. -/
lemma tikhonovMinimiserL2_optimality
    (S : OperatorSystem Ω μ)
    {lambda : ℝ} (lambda_pos : 0 < lambda)
    (v : S.PrimalL2) :
    inner ℝ (S.Tlin (S.tikhonovMinimiserL2 lambda)) (S.Tlin v)
        + lambda * inner ℝ (S.tikhonovMinimiserL2 lambda) v
      = inner ℝ (S.Tlin (S.hL2 S.h₀_mem)) (S.Tlin v) := by
  let complete : CompleteSpace S.PrimalL2 := inferInstance
  let coercive := tikhonovBilin_isCoercive S lambda_pos
  let Bsharp :=
    @IsCoercive.continuousLinearEquivOfBilin S.PrimalL2 _ _ complete
      (S.tikhonovBilin lambda) coercive
  let w : S.PrimalL2 :=
    (@InnerProductSpace.toDual ℝ S.PrimalL2 _ _ _ complete).symm S.tikhonovTarget
  let ustar : S.PrimalL2 := Bsharp.symm w
  have hmin : S.tikhonovMinimiserL2 lambda = ustar := by
    simp [tikhonovMinimiserL2, lambda_pos, Bsharp, w, ustar]
  have hLM :=
    @IsCoercive.continuousLinearEquivOfBilin_apply S.PrimalL2 _ _ complete
      (S.tikhonovBilin lambda) coercive ustar v
  have htarget : inner ℝ w v = S.tikhonovTarget v := by
    exact @InnerProductSpace.toDual_symm_apply ℝ S.PrimalL2 _ _ _ complete
      (x := v) (y := S.tikhonovTarget)
  have hvar : S.tikhonovBilin lambda ustar v = S.tikhonovTarget v := by
    calc
      S.tikhonovBilin lambda ustar v = inner ℝ (Bsharp ustar) v :=
        hLM.symm
      _ = inner ℝ w v := by simp [ustar]
      _ = S.tikhonovTarget v := htarget
  rw [hmin]
  simpa [tikhonovBilin_apply, tikhonovTarget_apply] using hvar

/-! ## Strong convexity at the minimiser -/

/-- **Population strong convexity at the Tikhonov minimiser (L² level).** For [a strictly
positive Tikhonov regularization level λ](hyp:lambda_pos) and [any element `h` of `L²(σ(X))`](hyp:h), [the non-negative excess
`λ‖h − h*_λ‖² + ‖T(h − h*_λ)‖²` — the amount by which the quadratic Tikhonov objective at `h`
exceeds its value at the population minimiser `h*_λ` — is bounded above by
`‖T(h − h₀)‖² − ‖T(h*_λ − h₀)‖² + λ(‖h‖² − ‖h*_λ‖²)`, where `T` is the projection-composed
conditional-expectation operator and `h₀` is the structural function's L² class](goal).

Proof sketch (Taylor at the minimiser).  Expand both sides:

    LHS = λ(‖ĥ‖² − 2⟨ĥ, h*⟩ + ‖h*‖²) + ‖Tĥ‖² − 2⟨Tĥ, Th*⟩ + ‖Th*‖²,
    RHS = ‖Tĥ‖² − 2⟨Tĥ, Th₀⟩ + ‖Th₀‖²
          − ‖Th*‖² + 2⟨Th*, Th₀⟩ − ‖Th₀‖²
          + λ‖ĥ‖² − λ‖h*‖²
        = ‖Tĥ‖² − 2⟨Tĥ, Th₀⟩ − ‖Th*‖² + 2⟨Th*, Th₀⟩ + λ‖ĥ‖² − λ‖h*‖².

`RHS − LHS = 2⟨Tĥ, Th*⟩ − 2⟨Tĥ, Th₀⟩ + 2⟨Th*, Th₀⟩ − 2‖Th*‖²
              + 2λ⟨ĥ, h*⟩ − 2λ‖h*‖²
            = 2 (⟨Tĥ, Th*⟩ − ⟨Tĥ, Th₀⟩ + λ⟨ĥ, h*⟩
                 − (⟨Th*, Th*⟩ − ⟨Th*, Th₀⟩ + λ⟨h*, h*⟩))`.

Both bracketed terms are `B(h*, ĥ) − ⟨T h₀, T ĥ⟩` (resp. with `h*` in
place of `ĥ`), which vanishes by `tikhonovMinimiserL2_optimality`.  So
`RHS − LHS = 0` (in fact equality holds — strong convexity is an
**equality** at the minimiser, not a strict inequality). -/
lemma tikhonovMinimiserL2_strong_convexity
    (S : OperatorSystem Ω μ)
    {lambda : ℝ} (lambda_pos : 0 < lambda)
    (h : S.PrimalL2) :
    lambda * ‖h - S.tikhonovMinimiserL2 lambda‖ ^ 2
        + ‖S.Tlin (h - S.tikhonovMinimiserL2 lambda)‖ ^ 2
      ≤ ‖S.Tlin (h - S.hL2 S.h₀_mem)‖ ^ 2
          - ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2
          + lambda * (‖h‖ ^ 2 - ‖S.tikhonovMinimiserL2 lambda‖ ^ 2) := by
  let hstar := S.tikhonovMinimiserL2 lambda
  have hopt := S.tikhonovMinimiserL2_optimality lambda_pos (h - hstar)
  apply le_of_eq
  simp [hstar, norm_sub_sq_real, ContinuousLinearMap.map_sub, inner_sub_right,
    real_inner_comm] at hopt ⊢
  nlinarith [hopt]

end OperatorSystem

end NPIV
end Estimation
end Causalean
