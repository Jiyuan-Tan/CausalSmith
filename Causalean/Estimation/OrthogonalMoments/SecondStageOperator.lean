/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract second-stage regression operator for the DR-Learner CATE estimator

This file provides the abstract `SecondStageOperator` bundle and stability
predicate described in `doc/basic_concepts/po/estimation/dr_learner_cate.tex`
(`def:est-cate-second-stage` and `def:est-cate-stability`). Its elimination
lemma can be used after a caller has supplied the conclusion required by that
stability predicate; it does not formalize `thm:est-cate-dr-oracle` itself.

The operator takes:
* a sample-size index `n`,
* a randomness scope `Ω` (carrying the data fold and any auxiliary randomness),
* a real-valued pseudo-outcome `f : γ × Bool × ℝ → ℝ` defined on data tuples
  `z = (x, a, y)`, and
* an evaluation point `x : γ`,

and returns a real number `̂E_{n,B}{f(Z) | X = x}`.

The structure here is deliberately abstract: the linear-smoother specialisation
lives in `Causalean/Estimation/OrthogonalMoments/LinearSmoother.lean`, and
callers supply a `BiasIdent` predicate to `Stable` / `Stable.isLittleOp` to encode the
conditional-bias identification (e.g. AIPW DR cross-product = condExp at fold A).

`Stable.isLittleOp` is the elimination lemma for the stability predicate.
-/

module
public import Causalean.Stat.Limit.Convergence
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Abstract Second-Stage Regression Operators

This file defines the target-agnostic second-stage operator used in DR-Learner
CATE estimation. The public API consists of `SecondStageOperator`, the
input-additivity predicate `SecondStageOperator.IsAdditiveInInput`, the oracle
estimator and oracle risk scale, the stability predicate `Stable`, and the
elimination lemma `Stable.isLittleOp`. It separates the operator itself from
additivity and conditional-bias identification assumptions. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory Filter Topology Causalean.Stat

/-- For [randomness and query spaces with a measure](hyp:Ω,μ,γ), an
abstract second-stage regression operator stores [an operator](hyp:evalAt)
mapping a sample size, a randomness scope, a real-valued pseudo-outcome
function, and a query point to an estimate, together with [joint measurability
for constant pseudo-outcomes](hyp:meas_evalAt_const). Stronger measurability
and linearity are deferred to concrete instances and separate predicates.

* `evalAt n ω f x` is the operator at sample size `n`, randomness scope `ω : Ω`,
  applied to the pseudo-outcome `f : γ × Bool × ℝ → ℝ` and evaluated at the
  query point `x : γ`.
* `meas_evalAt_const` is a minimal joint-measurability assumption: for every
  fixed constant pseudo-outcome `(fun _ => c)` the resulting
  `(ω, x) ↦ evalAt n ω _ x` is jointly measurable. Stronger measurability
  assumptions (e.g. measurability in the function argument) are deferred to
  concrete instances.

The linearity of the operator in its function input is **not** required by the
structure; the separate predicate `IsAdditiveInInput` below records only
additivity. This keeps the structure usable for nonlinear smoothers. -/
structure SecondStageOperator
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (γ : Type*) [MeasurableSpace γ] where
  evalAt : ℕ → Ω → (γ × Bool × ℝ → ℝ) → γ → ℝ
  meas_evalAt_const :
    ∀ (n : ℕ) (c : ℝ),
      Measurable (fun (p : Ω × γ) => evalAt n p.1 (fun _ => c) p.2)

namespace SecondStageOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {γ : Type*} [MeasurableSpace γ]

/-- For [a second-stage regression operator](hyp:op), [additivity in the
pseudo-outcome input](goal) means that, for every sample size, randomness
realization, pair of real-valued pseudo-outcome functions, and query point,
the estimate for their pointwise sum equals the sum of their separate estimates.
This predicate does not assert scalar homogeneity. -/
def IsAdditiveInInput (op : SecondStageOperator Ω μ γ) : Prop :=
  ∀ (n : ℕ) (ω : Ω) (f g : γ × Bool × ℝ → ℝ) (x : γ),
    op.evalAt n ω (fun z => f z + g z) x =
      op.evalAt n ω f x + op.evalAt n ω g x

/-- Given [a second-stage regression operator](hyp:op) and [a fixed
real-valued pseudo-outcome function](hyp:f), the [oracle estimator](goal) maps
each sample size, randomness realization, and query point to the operator's
estimate using that fixed pseudo-outcome. -/
def oracleEstimator (op : SecondStageOperator Ω μ γ)
    (f : γ × Bool × ℝ → ℝ) : ℕ → Ω → γ → ℝ :=
  fun n ω x => op.evalAt n ω f x

/-- Given [a second-stage regression operator](hyp:op), [a fixed real-valued
pseudo-outcome function](hyp:f), [a target function](hyp:target), [a query
point](hyp:x), and [a sample size](hyp:n), the [oracle pointwise risk scale](goal)
is the square root of the expected squared difference, over the operator's
randomness, between the oracle estimator and the target at that query point.

Oracle pointwise risk scale `R^*_n(x)` from `def:est-cate-dr-learner`:

  `R^*_n(x) := sqrt( ∫ (op.evalAt n ω f x - target x)^2 ∂μ )`.

This is the L²(μ) deviation of the oracle estimator from `target` at the
fixed query point `x`, treated as a deterministic function of `n`. -/
noncomputable def oracleRiskScale
    (op : SecondStageOperator Ω μ γ) (f : γ × Bool × ℝ → ℝ)
    (target : γ → ℝ) (x : γ) (n : ℕ) : ℝ :=
  Real.sqrt (∫ ω, (op.evalAt n ω f x - target x) ^ 2 ∂μ)

end SecondStageOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {γ : Type*} [MeasurableSpace γ]

/-- Given [a second-stage regression operator](hyp:op), [a target function](hyp:target),
[a sequence of distances between pseudo-outcomes](hyp:d_n), [a query point](hyp:x), and
[a conditional-bias identification criterion](hyp:BiasIdent), [stability](goal) means
that for every estimated pseudo-outcome sequence, true pseudo-outcome, and claimed
conditional-bias sequence satisfying the criterion, convergence of the distance to zero
in probability implies that the operator discrepancy after subtracting the smoothed bias
is negligible in probability relative to the oracle pointwise risk scale.

For every sequence of estimated pseudo-outcomes `fHat_n` and every true
pseudo-outcome `f`, with claimed conditional bias `bHat_n`, if `d_n →_p 0` and
the user-supplied conditional-bias identification predicate `BiasIdent`
holds, then the operator-level discrepancy between `evalAt _ fHat_n` and
`evalAt _ f`, *minus* the smoothed bias term `evalAt _ (bHat_n)`, is
`o_p(R^*_n(x))`.

`BiasIdent` encodes the concrete conditional-bias identification (e.g.
`bHat_n n ω u =ᵐ μ[fHat_n n ω Z − f Z | A_σ(n), σ(X) = u]` for a DR-Learner
with the AIPW pseudo-outcome). Concrete instances pass their explicit
identification predicate. -/
def Stable
    (op : SecondStageOperator Ω μ γ) (target : γ → ℝ)
    (d_n : ℕ → Ω → ℝ) (x : γ)
    (BiasIdent :
      (ℕ → Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → Ω → γ → ℝ) → Prop) : Prop :=
  ∀ (fHat_n : ℕ → Ω → γ × Bool × ℝ → ℝ) (f : γ × Bool × ℝ → ℝ)
    (bHat_n : ℕ → Ω → γ → ℝ),
    Tendsto_inProb d_n (fun _ => 0) μ →
    BiasIdent fHat_n f bHat_n →
    IsLittleOp
      (fun n ω =>
        op.evalAt n ω (fHat_n n ω) x - op.evalAt n ω f x
          - op.evalAt n ω (fun z => bHat_n n ω z.1) x)
      (fun n => SecondStageOperator.oracleRiskScale op f target x n) μ

/-- Given [a second-stage operator and all data appearing in a stability
claim](hyp:op,target,x,d_n,fHat_n,f,bHat_n,BiasIdent), [stability for those
data](hyp:hStab), [consistency of the supplied distance](hyp:hCons), and [the
caller-supplied bias-identification assertion](hyp:hBias), [the discrepancy in
the definition of stability is little-o in probability of the oracle risk
scale](goal).

This is an elimination lemma for `Stable`: it does not independently derive a
DR-Learner oracle expansion or the bias-identification assertion. -/
theorem Stable.isLittleOp
    (op : SecondStageOperator Ω μ γ) (target : γ → ℝ) (x : γ)
    (d_n : ℕ → Ω → ℝ)
    (fHat_n : ℕ → Ω → γ × Bool × ℝ → ℝ) (f : γ × Bool × ℝ → ℝ)
    (bHat_n : ℕ → Ω → γ → ℝ)
    (BiasIdent :
      (ℕ → Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → Ω → γ → ℝ) → Prop)
    (hStab : Stable op target d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) μ)
    (hBias : BiasIdent fHat_n f bHat_n) :
    IsLittleOp
      (fun n ω =>
        op.evalAt n ω (fHat_n n ω) x - op.evalAt n ω f x
          - op.evalAt n ω (fun z => bHat_n n ω z.1) x)
      (fun n => SecondStageOperator.oracleRiskScale op f target x n) μ := by
  exact hStab fHat_n f bHat_n hCons hBias

end OrthogonalMoments
end Estimation
end Causalean
