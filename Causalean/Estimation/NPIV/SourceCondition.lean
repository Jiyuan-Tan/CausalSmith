/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# β-source condition and Tikhonov bias bound for the TRAE primal estimator

Defines the spectral and bias hypotheses used by the TRAE rate theorem of
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`.

* `SourceCondition S β` — the β-source condition at the primal nuisance
  `h₀`, with `β > 0`. Carries the witness
  `w₀ ∈ Hbar` and the spectral identity
      `(h₀)_{L²} = (T*T)^{β/2} (w₀)_{L²}`
  inside `L²(σ(X))`, realized as `Lp ℝ 2 (μ.trim S.m_X_le)`, where
  `(T*T)^{β/2}` is the real continuous functional
  calculus on the positive self-adjoint composite `T†T` built by
  complexification in `Operator/Complexification.lean`.  The symbol
  `x ↦ Real.rpow (max x 0) (β/2)` is continuous on all of ℝ and agrees
  with `x^{β/2}` on `[0, ∞) ⊇ spectrum ℝ (T†T)`. Here `T†T` acts on
  the full primal `L²(σ(X))`; this is not the candidate-subspace normal
  operator from the general closed-subspace formulation.
* `TikhonovBiasBound S β sc` — the two Tikhonov bias bounds the rate
  theorem consumes uniformly over every positive regularization level `λ > 0`
  (proof sketch lines 276–285):

      ‖h*_λ − h₀‖²_{L²(P_X)} ≲ ‖w₀‖_{L²(P_X)} λ^{min(β, 2)},
      ‖T(h*_λ − h₀)‖²_{L²(P_Z)} ≲ ‖w₀‖_{L²(P_X)} λ^{min(β+1, 2)}.

  Packaged as a reusable certificate here; `Operator/SpectralCalculus.lean`
  discharges it from `SpectralSourceCondition` via the real-CFC built in
  `Operator/Complexification.lean`.
-/

module
public import Causalean.Estimation.NPIV.Operator.Complexification
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Source Condition and Tikhonov Bias

This file records the β-source condition for the primal NPIV nuisance and the
Tikhonov bias bounds assumed by the primal rate theorem. The source condition
expresses the target nuisance as a spectral power of the normal operator
applied to an admissible witness, while the bias bundle stores the strong and
weak approximation inequalities later discharged by spectral calculus. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **β-source condition** represents the true primal nuisance as the image, under a
[positive](hyp:beta_pos) spectral power of the normal NPIV operator, of [an admissible
witness function in the primal candidate class](hyp:w₀_fun,w₀_mem), via [the spectral identity
expressing the nuisance as that power of the operator applied to the witness, inside the
`L²` space](hyp:spectral_identity).

This is the formal interface for the source condition at `h₀`
(`def:est-trae-source-condition`, line 47).

Carries a witness `w₀ ∈ Hbar` together with the spectral identity
`h₀ = (T*T)^{β/2} w₀` inside `Lp ℝ 2 (μ.trim S.m_X_le)`, where
`(T*T)^{β/2}` is the
real continuous functional calculus on the self-adjoint composite
`OperatorSystem.Tstar_T_trim` built by complexification in
`Operator/Complexification.lean`.

The continuous symbol used here is
`fun x => Real.rpow (max x 0) (β/2)`, which agrees with `x^{β/2}` on
`[0, ∞) ⊇ spectrum ℝ (T†T)` and is continuous on all of ℝ for `β ≥ 0`. -/
structure SourceCondition (S : OperatorSystem Ω μ) (β : ℝ) where
  /-- The source smoothness exponent is positive. -/
  beta_pos : 0 < β
  /-- The pre-image of `h₀` under the spectral lift `(T*T)^{β/2}`. -/
  w₀_fun : S.𝒳 → ℝ
  /-- `w₀` lies in the primal candidate set `Hbar`. -/
  w₀_mem : w₀_fun ∈ S.Hbar
  /-- Spectral identity:
      `(h₀)_{L²} = (T†T)^{β/2} (w₀)_{L²}` inside the canonical
      trimmed realization of `L²(σ(X))`. -/
  spectral_identity :
    S.primalTrimEquiv (S.hL2 S.h₀_mem)
      = @Complexification.realCFC Ω S.m_X (μ.trim S.m_X_le)
          S.Tstar_T_trim
          (fun x : ℝ => Real.rpow (max x 0) (β/2))
          (S.primalTrimEquiv (S.hL2 w₀_mem))

/-- The **uniform Tikhonov bias-bound** bundle for [an NPIV operator system](hyp:S),
[a source exponent](hyp:β), and [its source condition](hyp:sc) records [one nonnegative
constant](hyp:C,C_nonneg), [population solutions at every positive regularization
level](hyp:h_lambda_star_fun,h_lambda_star_mem), [their strong- and weak-metric bias
bounds](hyp:strong_bias,weak_bias), and [their population strong-convexity
inequality](hyp:strong_convexity).

The quantifier over `λ` is inside the certificate, so `C` cannot be chosen
after seeing the regularization level.  For every `λ > 0` the stored solution
`h*_λ ∈ Hbar` satisfies

    ‖h*_λ − h₀‖²_{L²(P_X)} ≤ C ‖w₀‖_{L²(P_X)} λ^{min(β, 2)},
    ‖T(h*_λ − h₀)‖²_{L²(P_Z)} ≤ C ‖w₀‖_{L²(P_X)} λ^{min(β+1, 2)}.

This is a reusable certificate carried alongside `SourceCondition`; spectral
calculus files discharge it from source conditions on `T*T`. -/
structure TikhonovBiasBound (S : OperatorSystem Ω μ) (β : ℝ)
    (sc : SourceCondition S β) where
  /-- The family of population Tikhonov solutions, indexed by the regularization level. -/
  h_lambda_star_fun : ℝ → S.𝒳 → ℝ
  /-- At every positive level, `h*_λ` lies in the primal candidate set `Hbar`. -/
  h_lambda_star_mem : ∀ {lambda : ℝ}, 0 < lambda → h_lambda_star_fun lambda ∈ S.Hbar
  /-- Constant absorbing the proof's `≲`. -/
  C : ℝ
  /-- The constant is non-negative. -/
  C_nonneg : 0 ≤ C
  /-- Strong-metric Tikhonov bias bound:
      `‖h*_λ − h₀‖²_{L²(P_X)} ≤ C · ‖w₀‖_{L²(P_X)} · λ^{min(β, 2)}`. -/
  strong_bias :
    ∀ {lambda : ℝ} (hlambda : 0 < lambda),
      S.strongNorm (S.hL2 (h_lambda_star_mem hlambda) - S.hL2 S.h₀_mem) ^ 2
        ≤ C * S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min β 2)
  /-- Weak-metric Tikhonov bias bound:
      `‖T(h*_λ − h₀)‖²_{L²(P_Z)} ≤ C · ‖w₀‖_{L²(P_X)} · λ^{min(β+1, 2)}`. -/
  weak_bias :
    ∀ {lambda : ℝ} (hlambda : 0 < lambda),
      S.weakNorm (S.hL2 (h_lambda_star_mem hlambda) - S.hL2 S.h₀_mem) ^ 2
        ≤ C * S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min (β + 1) 2)
  /-- **Population strong convexity** at `h*_λ` (proof sketch lines 287–304
      of `doc/basic_concepts/po/estimation/trae_inverse_problems.tex`).

      For any candidate `ĥ ∈ Hbar`,

          λ‖ĥ − h*_λ‖²_{L²(P_X)} + ‖T(ĥ − h*_λ)‖²_{L²(P_Z)}
            ≤ ‖T(ĥ − h₀)‖²_{L²(P_Z)} − ‖T(h*_λ − h₀)‖²_{L²(P_Z)}
              + λ(‖ĥ‖²_{L²(P_X)} − ‖h*_λ‖²_{L²(P_X)}).

      This field records the inequality as part of the certificate. The
      spectral-calculus discharge constructs the minimizer over the full
      primal `L²(σ(X))`, proves the ambient first-order identity, and requires
      a `TikhonovPullback` witness identifying that minimizer with an `Hbar`
      function. It does not prove minimization over an arbitrary closed
      candidate subspace. -/
  strong_convexity :
    ∀ {lambda : ℝ} (hlambda : 0 < lambda) h, ∀ hh : h ∈ S.Hbar,
      lambda * (S.strongNorm (S.hL2 hh - S.hL2 (h_lambda_star_mem hlambda))) ^ 2
          + (S.weakNorm (S.hL2 hh - S.hL2 (h_lambda_star_mem hlambda))) ^ 2
        ≤ (S.weakNorm (S.hL2 hh - S.hL2 S.h₀_mem)) ^ 2
            - (S.weakNorm (S.hL2 (h_lambda_star_mem hlambda) - S.hL2 S.h₀_mem)) ^ 2
            + lambda * ((S.strongNorm (S.hL2 hh)) ^ 2
                          - (S.strongNorm (S.hL2 (h_lambda_star_mem hlambda))) ^ 2)

/-- A fixed-level Tikhonov view packages [an NPIV operator system](hyp:S), [a source
exponent](hyp:β), [a selected regularization level](hyp:lambda), [the corresponding source
condition](hyp:sc), [a uniform bias certificate](hyp:uniform), and [positivity of the selected
level](hyp:lambda_pos), without changing the certificate's uniform constant. -/
structure TikhonovBiasBoundAt (S : OperatorSystem Ω μ) (β lambda : ℝ)
    (sc : SourceCondition S β) where
  /-- The uniform certificate from which this fixed-level view is obtained. -/
  uniform : TikhonovBiasBound S β sc
  /-- The selected regularization level is positive. -/
  lambda_pos : 0 < lambda

namespace TikhonovBiasBoundAt

variable {S : OperatorSystem Ω μ} {β lambda : ℝ} {sc : SourceCondition S β}

/-- The [population Tikhonov solution](goal) in [a fixed-level view](hyp:tb). -/
abbrev h_lambda_star_fun (tb : TikhonovBiasBoundAt S β lambda sc) : S.𝒳 → ℝ :=
  tb.uniform.h_lambda_star_fun lambda

/-- The fixed-level population solution from [a bias certificate](hyp:tb) [belongs to the
admissible class](goal). -/
lemma h_lambda_star_mem (tb : TikhonovBiasBoundAt S β lambda sc) :
    tb.h_lambda_star_fun ∈ S.Hbar :=
  tb.uniform.h_lambda_star_mem tb.lambda_pos

/-- The [level-independent bias constant](goal) in [a fixed-level view](hyp:tb). -/
abbrev C (tb : TikhonovBiasBoundAt S β lambda sc) : ℝ := tb.uniform.C

/-- The level-independent constant in [a fixed-level view](hyp:tb) [is nonnegative](goal). -/
lemma C_nonneg (tb : TikhonovBiasBoundAt S β lambda sc) : 0 ≤ tb.C :=
  tb.uniform.C_nonneg

/-- [A fixed-level view](hyp:tb) [bounds its strong-metric Tikhonov bias](goal). -/
lemma strong_bias (tb : TikhonovBiasBoundAt S β lambda sc) :
    S.strongNorm (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem) ^ 2
      ≤ tb.C * S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min β 2) :=
  tb.uniform.strong_bias tb.lambda_pos

/-- [A fixed-level view](hyp:tb) [satisfies the weak-metric bias bound](goal). -/
lemma weak_bias (tb : TikhonovBiasBoundAt S β lambda sc) :
    S.weakNorm (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem) ^ 2
      ≤ tb.C * S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min (β + 1) 2) :=
  tb.uniform.weak_bias tb.lambda_pos

/-- [A fixed-level view](hyp:tb) [satisfies population strong convexity](goal) for
[every admissible candidate](hyp:h,hh). -/
lemma strong_convexity (tb : TikhonovBiasBoundAt S β lambda sc)
    (h : S.𝒳 → ℝ) (hh : h ∈ S.Hbar) :
    lambda * (S.strongNorm (S.hL2 hh - S.hL2 tb.h_lambda_star_mem)) ^ 2
        + (S.weakNorm (S.hL2 hh - S.hL2 tb.h_lambda_star_mem)) ^ 2
      ≤ (S.weakNorm (S.hL2 hh - S.hL2 S.h₀_mem)) ^ 2
          - (S.weakNorm (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
          + lambda * ((S.strongNorm (S.hL2 hh)) ^ 2
                        - (S.strongNorm (S.hL2 tb.h_lambda_star_mem)) ^ 2) :=
  tb.uniform.strong_convexity tb.lambda_pos h hh

end TikhonovBiasBoundAt

end NPIV
end Estimation
end Causalean
