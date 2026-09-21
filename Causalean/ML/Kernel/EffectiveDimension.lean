/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Effective dimension of a trace-class operator

The **effective dimension** at regularization level `λ > 0` of a positive operator with
(summable, nonnegative) eigenvalue family `μ : ι → ℝ` is

    N(λ) = ∑ᵢ μᵢ / (μᵢ + λ) = tr(T (T + λ)⁻¹).

It is the quantity that governs the variance term of kernel ridge regression: the
Caponnetto–De Vito optimal-rate analysis expresses the minimax `L²(ρ)` rate of kernel ridge
through `N(λ)` and the eigenvalue-decay/source-condition exponents.  This file provides the
definition and its basic structural properties for the trace-class (summable-eigenvalue)
regime — the infinite-dimensional RKHS setting.

* `effectiveDimension_nonneg` — `0 ≤ N(λ)`;
* `summable_effectiveDimension_term` — the summand family is summable (so `N(λ)` is a genuine
  real number, not the fallback value of a non-summable `tsum`);
* `effectiveDimension_le_trace_div` — `N(λ) ≤ (tr T)/λ` (the crude dimension-free bound);
* `effectiveDimension_le_card` — over finitely many eigenvalues, `N(λ) ≤ #ι`;
* `effectiveDimension_antitone` — `N` is antitone in `λ` (more regularization ⇒ smaller
  effective dimension).

The downstream **rate** theorem (`N(λ)`/eigenvalue-decay ⇒ the `n^{-2rb/(2rb+1)}` kernel-ridge
`L²` rate) additionally requires Hilbert-space operator-concentration machinery (an operator
Bernstein inequality for `(T+λ)^{-1/2}(T − T̂ₙ)(T+λ)^{-1/2}`) that is a separate substrate; this
file is the definitional foundation it would build on.
-/

@[expose] public section

namespace Causalean.ML

open scoped Topology

variable {ι : Type*}

/-- [Effective dimension](goal) measures the spectral degrees of freedom retained by
regularization through [the regularized eigenvalue-ratio sum](step:1). It uses
[a real eigenvalue family](hyp:μ) over [an arbitrary index set](hyp:ι) at
[a real regularization level](hyp:lam). Without positivity, summability, and
nonzero denominators, zero-denominator terms and nonsummable totals follow the ambient
real-series convention and evaluate to zero.

The effective dimension is the trace-style quantity used in kernel-ridge variance bounds. -/
noncomputable def effectiveDimension (μ : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑' i, μ i / (μ i + lam)

/-- Each summand `μᵢ/(μᵢ+λ)` is nonnegative (for nonnegative eigenvalues and `λ > 0`). -/
lemma effectiveDimension_term_nonneg {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) (i : ι) : 0 ≤ μ i / (μ i + lam) :=
  div_nonneg (hμ i) (add_nonneg (hμ i) hlam.le)

/-- Each summand is dominated by `μᵢ/λ`. -/
lemma effectiveDimension_term_le_div {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) (i : ι) : μ i / (μ i + lam) ≤ μ i / lam := by
  gcongr <;> linarith [hμ i]

/-- Each summand is at most `1`. -/
lemma effectiveDimension_term_le_one {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) (i : ι) : μ i / (μ i + lam) ≤ 1 := by
  rw [div_le_one (add_pos_of_nonneg_of_pos (hμ i) hlam)]
  linarith [hμ i]

/-- [The effective-dimension summands form a summable family](goal) when
[the eigenvalues are nonnegative](hyp:hμ), [the regularization level is positive](hyp:hlam),
and [the eigenvalue family is summable](hyp:hsum). Thus
[the indexed spectral sum](hyp:ι,μ,lam) is genuine rather than a nonsummable-series default. -/
lemma summable_effectiveDimension_term {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) (hsum : Summable μ) :
    Summable (fun i => μ i / (μ i + lam)) :=
  Summable.of_nonneg_of_le (fun i => effectiveDimension_term_nonneg hμ hlam i)
    (fun i => effectiveDimension_term_le_div hμ hlam i) (hsum.div_const lam)

/-- The effective dimension is nonnegative. -/
lemma effectiveDimension_nonneg {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) : 0 ≤ effectiveDimension μ lam :=
  tsum_nonneg (fun i => effectiveDimension_term_nonneg hμ hlam i)

/-- **Trace bound.** [Effective dimension is at most total spectral mass divided by the
regularization level](goal) for [a nonnegative, summable eigenvalue family](hyp:μ,hμ,hsum)
over [the index set](hyp:ι) at [a positive regularization level](hyp:lam,hlam). This gives
only inverse-linear dependence on regularization; sharper decay-dependent rates require a
separate argument. -/
lemma effectiveDimension_le_trace_div {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) (hsum : Summable μ) :
    effectiveDimension μ lam ≤ (∑' i, μ i) / lam := by
  have hle : effectiveDimension μ lam ≤ ∑' i, μ i / lam :=
    Summable.tsum_le_tsum (fun i => effectiveDimension_term_le_div hμ hlam i)
      (summable_effectiveDimension_term hμ hlam hsum) (hsum.div_const lam)
  rwa [tsum_div_const] at hle

/-- Over finitely many eigenvalues, `N(λ)` never exceeds the ambient dimension `#ι`. -/
lemma effectiveDimension_le_card [Fintype ι] {μ : ι → ℝ} {lam : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 < lam) :
    effectiveDimension μ lam ≤ (Fintype.card ι : ℝ) := by
  unfold effectiveDimension
  rw [tsum_fintype]
  calc ∑ i, μ i / (μ i + lam)
      ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => effectiveDimension_term_le_one hμ hlam i
    _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]

/-- If [all eigenvalues are nonnegative](hyp:hμ), [the first regularization level is
positive](hyp:hlam₁), [the first level is no larger than the second](hyp:hle), and [the
eigenvalues are summable](hyp:hsum), then [effective dimension is antitone in the regularization
level](goal). -/
lemma effectiveDimension_antitone {μ : ι → ℝ} {lam₁ lam₂ : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) (hsum : Summable μ) :
    effectiveDimension μ lam₂ ≤ effectiveDimension μ lam₁ := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hle
  refine Summable.tsum_le_tsum (fun i => ?_)
    (summable_effectiveDimension_term hμ hlam₂ hsum)
    (summable_effectiveDimension_term hμ hlam₁ hsum)
  gcongr <;> linarith [hμ i, hlam₁, hle]

end Causalean.ML
