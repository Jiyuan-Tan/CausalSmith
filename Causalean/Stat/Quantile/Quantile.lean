/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Quantile function (generalized inverse of a cdf)

Causal-agnostic statistical primitive: a lower generalized inverse of
Mathlib's `cdf` for a real measure. For probability measures this is the usual
left-continuous quantile function:

    quantile μ τ := sInf {x : ℝ | τ ≤ cdf μ x}.

Mathlib provides `ProbabilityTheory.cdf μ : StieltjesFunction ℝ` (monotone,
right-continuous, with limits 0 / 1) but has **no** generalized inverse; this
file supplies it together with the key order characterisation

    quantile μ τ ≤ x  ↔  τ ≤ cdf μ x       (for `0 < τ < 1`),

i.e. the Galois-style connection between the cdf and its inverse.  This is the
foundation for quantile treatment effects (`PO/ID/Exact/QTE/QuantileEffect.lean`)
and the quantile form of Lee trimming.

The interior restriction `0 < τ < 1` is intrinsic: for `τ ≤ 0` the defining set
is all of `ℝ` (so `sInf = 0` is meaningless) and for `τ ≥ 1` it can be empty in
the continuous, full-support case.  These are exactly the degenerate quantiles.
File is project-agnostic and a candidate for upstream contribution to Mathlib.
-/

module
public import Mathlib.Probability.CDF

/-! # Quantile Function

This file defines the lower quantile function of a real measure as the
generalized inverse of its cumulative distribution function. It proves the
basic order characterization that connects cumulative distribution functions and
their quantiles away from the degenerate endpoints. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set Filter Topology

variable (μ : Measure ℝ)

/-- Given a [measure on the real line](hyp:μ) and a [real level](hyp:τ), the
[super-level set of Mathlib's totalized cumulative-distribution function](goal)
contains the real points where that function is at least the level.

For an arbitrary measure this is a generalized-inverse construction for Mathlib's
totalized `cdf`; it has the usual measure-CDF interpretation under
`IsProbabilityMeasure μ`. -/
def quantileSet (τ : ℝ) : Set ℝ := {x : ℝ | τ ≤ cdf μ x}

/-- Given a [measure on the real line](hyp:μ) and a [real level](hyp:τ), the
[lower generalized inverse of Mathlib's totalized `cdf`](goal) is the infimum of
its super-level set at that level.

For an arbitrary measure this definition is totalized; it is the usual lower
measure quantile when `μ` is a probability measure. -/
noncomputable def quantile (τ : ℝ) : ℝ := sInf (quantileSet μ τ)

variable {μ}

/-- If [a point belongs to a quantile super-level set](hyp:hx) and [a second point
is no smaller](hyp:hxx'), then [the second point also belongs to that set](goal). -/
lemma quantileSet_up_closed {τ x x' : ℝ}
    (hx : x ∈ quantileSet μ τ) (hxx' : x ≤ x') :
    x' ∈ quantileSet μ τ :=
  le_trans hx (monotone_cdf μ hxx')

/-- At [a strictly positive level](hyp:hτ), [the quantile super-level set of a
real measure is bounded below](goal).

The CDF tends to zero at negative infinity, so a point where it is below the
level supplies a lower bound. -/
lemma bddBelow_quantileSet {τ : ℝ}
    (hτ : 0 < τ) : BddBelow (quantileSet μ τ) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually_lt_const hτ)
  refine ⟨N, fun s hs => ?_⟩
  by_contra hlt
  push Not at hlt
  exact absurd hs (not_le.mpr (hN s hlt.le))

/-- At [a level strictly below one](hyp:hτ), [the quantile super-level set of a
real measure is nonempty](goal).

The CDF tends to one at positive infinity, so some point has CDF at least the
given level. -/
lemma nonempty_quantileSet {τ : ℝ}
    (hτ : τ < 1) : (quantileSet μ τ).Nonempty := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_cdf_atTop μ).eventually_const_lt hτ)
  exact ⟨N, (hN N le_rfl).le⟩

/-- **Key membership lemma.** At [a level strictly below one](hyp:hτ1), [the CDF
of a real measure at its lower quantile reaches that level](goal).

Only the upper endpoint condition is needed. The proof uses right-continuity of
the CDF. -/
lemma le_cdf_quantile {τ : ℝ} (hτ1 : τ < 1) :
    τ ≤ cdf μ (quantile μ τ) := by
  set a := quantile μ τ with ha
  have hne : (quantileSet μ τ).Nonempty := nonempty_quantileSet hτ1
  -- Every point strictly above the inf lies in the (up-closed) super-level set.
  have hgt : ∀ x, a < x → τ ≤ cdf μ x := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
    exact quantileSet_up_closed hs hsx.le
  -- Right-continuity: cdf μ → cdf μ a along `𝓝[Ioi a] a`.
  have htends : Tendsto (cdf μ) (𝓝[Ioi a] a) (𝓝 (cdf μ a)) :=
    ((cdf μ).right_continuous a).mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)
  -- Along that filter we stay in the super-level set, so the limit dominates τ.
  have hev : ∀ᶠ x in 𝓝[Ioi a] a, τ ≤ cdf μ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hgt x hx
  exact ge_of_tendsto htends hev

/-- **Galois connection (one direction).** If [the level is below one](hyp:hτ1)
and [its quantile is at most a point](hyp:hx), then [the CDF at that point has
reached the level](goal). -/
lemma le_cdf_of_quantile_le {τ x : ℝ} (hτ1 : τ < 1)
    (hx : quantile μ τ ≤ x) : τ ≤ cdf μ x :=
  le_trans (le_cdf_quantile hτ1) (monotone_cdf μ hx)

/-- **Galois connection (other direction).** If [the level is positive](hyp:hτ0)
and [the CDF at a point reaches that level](hyp:hx), then [the quantile is at
most that point](goal). -/
lemma quantile_le_of_le_cdf {τ x : ℝ}
    (hτ0 : 0 < τ) (hx : τ ≤ cdf μ x) :
    quantile μ τ ≤ x :=
  csInf_le (bddBelow_quantileSet hτ0) hx

/-- **Quantile / CDF Galois connection.** For [an interior probability level
$\tau\in(0,1)$](hyp:hτ0,hτ1), [the quantile of a real measure at
level $\tau$ is at most a point exactly when the CDF has reached $\tau$ there](goal). -/
theorem quantile_le_iff {τ x : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    quantile μ τ ≤ x ↔ τ ≤ cdf μ x :=
  ⟨le_cdf_of_quantile_le hτ1, quantile_le_of_le_cdf hτ0⟩

/-- If [the lower level is positive](hyp:hτ0), [the upper level is below
one](hyp:hτ'1), and [the lower level is at most the upper](hyp:hττ'), then [the
corresponding quantiles of a real measure are ordered](goal). -/
lemma quantile_mono {τ τ' : ℝ}
    (hτ0 : 0 < τ) (hτ'1 : τ' < 1) (hττ' : τ ≤ τ') :
    quantile μ τ ≤ quantile μ τ' :=
  quantile_le_of_le_cdf hτ0 (le_trans hττ' (le_cdf_quantile hτ'1))

end Causalean.Stat
