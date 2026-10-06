/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Convergence modes and stochastic order for random variables in metric and normed spaces

Causal-agnostic primitives for the estimation layer.  Wraps Mathlib's
`TendstoInMeasure` and `eLpNorm`; introduces `Tendsto_dist`, `IsBigOp`, and
`IsLittleOp` matching the natural-language definitions in
`doc/basic_concepts/po/estimation.tex` (`def:est-conv-prob`,
`def:est-conv-l2`, `def:est-conv-dist`, `def:est-stoch-order`).

All declarations are proved.  The arithmetic lemmas
`IsLittleOp.mul_isBigOp`, `IsBigOp.add`, and
`IsBigOp.mul_isLittleOp_one_isLittleOp`, plus the Δ-method helpers
`Tendsto_dist.tightness` and `IsBigOp.const_mul_tendsto_zero`, are
candidates for upstream contribution to Mathlib.
-/

module
public import Causalean.Mathlib.Probability.ConvergenceInDistribution
public import Causalean.Stat.Limit.StochasticOrder
public import Causalean.Tactic.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
Defines extended-metric-valued convergence in probability, scalar L² convergence and
convergence in distribution, and normed-space
stochastic-order notation used by the estimation layer.

The core predicates are `Tendsto_inProb`, `Tendsto_L2`, `Tendsto_dist`,
`IsBigOp`, and `IsLittleOp`.  The main theorem set includes deterministic-scalar
Slutsky for distributional convergence (`Tendsto_dist.const_mul_tendsto`),
tightness from convergence in distribution (`Tendsto_dist.tightness`),
degenerate Slutsky (`IsBigOp.const_mul_tendsto_zero`), and stochastic-order
arithmetic such as `IsLittleOp.add_eventually_nonneg_rate`,
`IsLittleOp.mul_isBigOp`, `IsBigOp.add`, and
`IsBigOp.mul_isLittleOp_one_isLittleOp`.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Convergence in probability -/

/-- Given [a sequence of random variables in an extended-distance space](hyp:Xn), [a limiting
random variable in that space](hyp:X), and [a measure on a measurable sample space](hyp:μ),
[convergence in probability](goal) means that, for every positive tolerance, the measure of
outcomes whose distance from the limit exceeds that tolerance tends to zero as the sample-size
index tends to infinity.

This is the fixed-space specialization of the row-varying convergence hub
`TendstoInProbability` along the natural-number limit. -/
@[deprecated "Use Causalean.Stat.Modes.TendstoInProbability." (since := "2026-09-18")]
abbrev Tendsto_inProb {E : Type*} [EDist E]
    (Xn : ℕ → Ω → E) (X : Ω → E) (μ : Measure Ω) : Prop :=
  Modes.TendstoInProbability (fun _ => μ) Xn atTop (fun _ => X)

/-- Convergence in probability of [a sequence in an extended-distance space](hyp:Xn) to [a
limit](hyp:X) under [a measure](hyp:μ) is exactly [convergence in measure of that sequence along
the natural numbers](goal). -/
@[causal_defs_simps]
lemma Tendsto_inProb_iff {E : Type*} [EDist E]
    (Xn : ℕ → Ω → E) (X : Ω → E) (μ : Measure Ω) :
    Tendsto_inProb Xn X μ ↔ TendstoInMeasure μ Xn atTop X :=
  Iff.rfl

/-- Convergence in probability of [a natural-number-indexed sequence](hyp:Xn) to [a fixed
limit](hyp:X) under [a fixed measure](hyp:μ) [is exactly the fixed-space specialization of the
row-varying convergence hub](goal). -/
lemma Tendsto_inProb_iff_hub {E : Type*} [EDist E]
    (Xn : ℕ → Ω → E) (X : Ω → E) (μ : Measure Ω) :
    Tendsto_inProb Xn X μ ↔
      Modes.TendstoInProbability (fun _ => μ) Xn atTop (fun _ => X) :=
  Iff.rfl

/-! ## L² convergence -/

/-- Given [a sequence of real-valued random variables](hyp:Xn), [a real-valued limiting random
variable](hyp:X), and [a measure on a measurable sample space](hyp:μ),
[$L^2$ convergence](goal) means that the $L^2$ norm of the difference between the indexed random
variable and the limit tends to zero as the index tends to infinity. -/
def Tendsto_L2 (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n => eLpNorm (fun ω => Xn n ω - X ω) 2 μ) atTop (𝓝 0)

/-! ## Convergence in distribution

Defined as weak convergence of the pushforward measures of `Xn` to a target
probability measure `Q` on ℝ.  Phrased at the measure level (rather than as
convergence to a limiting random variable) so the target laws — e.g. a
Gaussian — can be supplied directly. The compatibility wrapper below specializes
`Modes.TendstoInLaw` to a fixed measure and the natural-number limit. -/
/-- Given [a sequence of real-valued random variables carrying a measurability argument that the
definition no longer uses](hyp:Xn,_hXn), [a probability law on the real line](hyp:Q), and [a
probability measure on a measurable sample space](hyp:μ),
[convergence in distribution](goal) means that the sequence of induced laws converges weakly to
the specified real-line probability law.

This is the project-level scalar convergence-in-distribution wrapper, phrased directly
in terms of pushforward probability measures. -/
@[deprecated "Use Causalean.Stat.Modes.TendstoInLaw." (since := "2026-09-18")]
abbrev Tendsto_dist (Xn : ℕ → Ω → ℝ) (Q : Measure ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (_hXn : ∀ n, AEMeasurable (Xn n) μ) : Prop :=
  Modes.TendstoInLaw (fun _ => μ) Xn atTop Q

/-- Convergence in distribution of a sequence of real random variables to a probability law on
the real line is exactly convergence, in the space of probability measures on the real line, of
the pushforward laws of the random variables to that law. -/
@[causal_defs_simps]
lemma Tendsto_dist_iff (Xn : ℕ → Ω → ℝ) (Q : Measure ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ) :
    Tendsto_dist Xn Q μ hXn ↔
      Tendsto (β := ProbabilityMeasure ℝ)
        (fun n =>
          ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
        (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) :=
by
  constructor
  · intro h
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using h.tendsto
  · intro h
    refine ⟨hXn, by fun_prop, ?_⟩
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using h

/-- Deterministic-scalar Slutsky for the project's measure-level
`Tendsto_dist` wrapper.

If `Xn ⇒ Q` and `a n → a₀`, then `a n * Xn ⇒ Q.map (fun x => a₀ * x)`.
The nontrivial weak-convergence fact is isolated in
`MeasureTheory.ProbabilityMeasure.tendsto_map_mul_of_tendsto`. -/
theorem Tendsto_dist.const_mul_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {a : ℕ → ℝ} {a₀ : ℝ}
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n =>
        ⟨μ.map (fun ω => a n * Xn n ω),
          Measure.isProbabilityMeasure_map
            ((measurable_const.mul measurable_id).aemeasurable.comp_aemeasurable (hXn n))⟩)
      atTop
      (𝓝 ⟨Q.map (fun x : ℝ => a₀ * x),
        Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable⟩) := by
  have hScaled : ∀ n, AEMeasurable (fun ω => a n * Xn n ω) μ := fun n =>
    (measurable_const.mul measurable_id).aemeasurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure (Q.map (fun x : ℝ => a₀ * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  have hX' := (Tendsto_dist_iff Xn Q μ hXn).mp hX
  have hpm := MeasureTheory.ProbabilityMeasure.tendsto_map_mul_of_tendsto hX' ha
  refine hpm.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  change Measure.map (fun x : ℝ => a n * x) (μ.map (Xn n))
    = μ.map (fun ω => a n * Xn n ω)
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (measurable_const.mul measurable_id).aemeasurable
  · exact hXn n

/-! ## Stochastic order -/

/-- Given [a sequence of random variables in a seminormed additive group](hyp:Xn), [a real-valued
rate sequence](hyp:rn), and [a measure on a measurable sample space](hyp:μ), [boundedness in
probability at that rate](goal) — the familiar `Xₙ = O_p(rₙ)` — is the sequence specialization of
the filter-general stochastic-boundedness predicate.

This is a genuine abbreviation, not a separate notion: `IsBigOp` and
`Modes.BoundedInProbability` are the same proposition, so results proved about either apply to
both without a bridge. The hub requires a strictly positive multiplier, which is what stops the
predicate being satisfiable by taking the multiplier to be zero against a nonpositive rate —
`Xₙ = O_p(rₙ)` says nothing when `rₙ` is not positive, and the definition now reflects that. -/
abbrev IsBigOp {E : Type*} [SeminormedAddCommGroup E]
    (Xn : ℕ → Ω → E) (rn : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  Modes.BoundedInProbability (fun _ => μ) Xn atTop rn

/-- Given [a sequence of random variables in a seminormed additive group](hyp:Xn), [a real-valued
rate sequence](hyp:rn), and [a measure on a measurable sample space](hyp:μ), [negligibility in
probability relative to that rate](goal) — the familiar `Xₙ = o_p(rₙ)` — is the sequence
specialization of the filter-general stochastic little-o predicate.

As with `IsBigOp` this is an abbreviation rather than a second notion, so `IsLittleOp` and
`Modes.IsLittleOpF` are interchangeable. -/
abbrev IsLittleOp {E : Type*} [SeminormedAddCommGroup E]
    (Xn : ℕ → Ω → E) (rn : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  Modes.IsLittleOpF (fun _ => μ) Xn atTop rn

/-! ## Tightness and degenerate Slutsky (helpers for the Δ-method)

`Tendsto_dist.tightness` says that any sequence converging in distribution
is bounded in probability (Prokhorov tightness for a single tight limit).
`IsBigOp.const_mul_tendsto_zero` is the degenerate-Slutsky helper used in
the Δ-method linearization step: `a n · X n` is `o_p(1)` whenever
`a n → 0` and `X n` is `O_p(1)`. -/

/-- **Tightness from convergence in distribution.**  Suppose [a real-valued sequence `Xn` is
measurable at every sample size](hyp:hXn) and [it converges in distribution under `μ` to a
probability measure `Q` on ℝ](hyp:hX). Then [`Xn` is bounded in probability, `O_p(1)`](goal).
Standard fact: any single tight limit gives a tight sequence (Prokhorov). -/
theorem Tendsto_dist.tightness
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn) :
    IsBigOp Xn (fun _ => (1 : ℝ)) μ := by
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact ⟨1, one_pos, by simp [hδtop]⟩
  let s : ℕ → Set ℝ := fun n => {x | (n : ℝ) ≤ |x|}
  have hQtail : Tendsto (fun n => Q (s n)) atTop (𝓝 0) := by
    have hs : ∀ n, NullMeasurableSet (s n) Q := by
      intro n
      exact (isClosed_le continuous_const continuous_abs).measurableSet.nullMeasurableSet
    have hm : Antitone s := by
      intro i j hij x hx
      dsimp [s] at hx ⊢
      exact le_trans (Nat.cast_le.mpr hij) hx
    have hf : ∃ n, Q (s n) ≠ ⊤ := ⟨0, measure_ne_top Q _⟩
    have hinter : (⋂ n, s n) = ∅ := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        exact (not_lt_of_ge (Set.mem_iInter.mp hx n)) hn
      · intro hx
        cases hx
    have ht := tendsto_measure_iInter_atTop hs hm hf
    simpa [Function.comp_def, hinter] using ht
  have hhalf_pos : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hQevent := (ENNReal.tendsto_nhds_zero.mp hQtail) (δ / 2) hhalf_pos
  obtain ⟨N, hN⟩ := hQevent.exists
  refine ⟨(N + 1 : ℕ), by positivity, ?_⟩
  let F : Set ℝ := s N
  have hFclosed : IsClosed F := by
    exact isClosed_le continuous_const continuous_abs
  simp only [causal_defs_simps] at hX
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩
  have hpm : Filter.limsup (fun n => ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) F) atTop
      ≤ (ν : Measure ℝ) F := by
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (μs := νs) (μ := ν) hX hFclosed
  have hpoint : ∀ n, μ {ω | ((N + 1 : ℕ) : ℝ) * (fun _ => (1 : ℝ)) n ≤ |Xn n ω|}
      ≤ ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) F := by
    intro n
    change μ {ω | ((N + 1 : ℕ) : ℝ) * (fun _ => (1 : ℝ)) n ≤ |Xn n ω|}
      ≤ (μ.map (Xn n)) F
    rw [Measure.map_apply_of_aemeasurable (hXn n) hFclosed.measurableSet]
    apply measure_mono
    intro ω hω
    dsimp [F, s]
    have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_num
    exact hNle.trans (by simpa using hω)
  have hlim : Filter.limsup
      (fun n => μ {ω | ((N + 1 : ℕ) : ℝ) * (fun _ => (1 : ℝ)) n ≤ |Xn n ω|})
      atTop ≤ δ / 2 := calc
    _ ≤ Filter.limsup
        (fun n => ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) F) atTop :=
      Filter.limsup_le_limsup (Eventually.of_forall hpoint)
    _ ≤ (ν : Measure ℝ) F := hpm
    _ = Q F := rfl
    _ ≤ δ / 2 := by simpa [F] using hN
  have hhalf_lt : δ / 2 < δ := ENNReal.half_lt_self hδ.ne' hδtop
  exact (((Filter.limsup_le_iff
    (u := fun n => μ {ω | ((N + 1 : ℕ) : ℝ) * (fun _ => (1 : ℝ)) n ≤ |Xn n ω|})
    (x := δ / 2)).mp hlim) δ hhalf_lt).mono fun _ hi => hi.le

/-- **Degenerate Slutsky.**  If [a real-valued sequence `Xn` is bounded in probability,
`O_p(1)`, under `μ`](hyp:hX), and [a deterministic scalar sequence `a` converges to
`0`](hyp:ha), then [the product sequence `a n · Xn` is `o_p(1)`](goal).  Concretely: the product
of a sequence converging to `0` with a tight sequence is `o_p(1)`.

In particular, when `Xn ⇒ Q` for some probability measure `Q` and
`a n = 1/√n`, we get `a n · Xn →_p 0`.  Used in the Δ-method linearization
step to conclude `T_n − t₀ →_p 0` from `√n (T_n − t₀) ⇒ Q`. -/
theorem IsBigOp.const_mul_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Xn : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX : IsBigOp Xn (fun _ => (1 : ℝ)) μ)
    (ha : Tendsto a atTop (𝓝 0)) :
    IsLittleOp (fun n ω => a n * Xn n ω) (fun _ => (1 : ℝ)) μ := by
  have haLittle : Modes.IsLittleOpF (fun _ => μ) (fun n (_ : Ω) => a n) atTop
      (fun _ => (1 : ℝ)) := by
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have haevent : ∀ᶠ n in atTop, |a n| < ε := by
      have ht := (Metric.tendsto_nhds.mp ha) ε hε
      simpa [Real.dist_eq] using ht
    filter_upwards [haevent] with n hn
    rw [show {ω : Ω | ε * (1 : ℝ) ≤ ‖a n‖} = ∅ by
      ext ω
      simp [Real.norm_eq_abs, not_le.mpr hn]]
    simp
  simpa only [one_mul] using Modes.IsLittleOpF.mul_boundedInProbability haLittle hX
    (Eventually.of_forall fun _ => zero_lt_one)
    (Eventually.of_forall fun _ => zero_lt_one)

/-! ## Arithmetic of stochastic orders

Standard facts for stochastic-order bookkeeping.  These proved statements are
candidates for upstream contribution to Mathlib. -/

variable {Xn Yn : ℕ → Ω → ℝ} {rn sn : ℕ → ℝ} {μ : Measure Ω}

/-- The sum of two stochastic little-o terms is stochastic little-o for an
eventually nonnegative rate. -/
theorem IsLittleOp.add_eventually_nonneg_rate
    (hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rn n)
    (hX : IsLittleOp Xn rn μ) (hY : IsLittleOp Yn rn μ) :
    IsLittleOp (fun n ω => Xn n ω + Yn n ω) rn μ :=
  Modes.IsLittleOpF.add hX hY hrn_nonneg

/-- Domination by a positive constant times a stochastic little-o term preserves
the stochastic little-o rate. -/
theorem IsLittleOp.of_abs_le_const_mul
    {C : ℝ} (hC : 0 < C) (hY : IsLittleOp Yn rn μ)
    (hbound : ∀ n ω, |Xn n ω| ≤ C * |Yn n ω|) :
    IsLittleOp Xn rn μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hYevent := (ENNReal.tendsto_nhds_zero.mp
    (hY (ε / C) (div_pos hε hC))) δ hδ
  filter_upwards [hYevent] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  change (ε / C) * rn n ≤ |Yn n ω|
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  calc
    ε * rn n ≤ |Xn n ω| := by simpa [Real.norm_eq_abs] using hω
    _ ≤ C * |Yn n ω| := hbound n ω
    _ = |Yn n ω| * C := mul_comm _ _

/-- The sum of two `o_p(1)` sequences is `o_p(1)`. -/
theorem IsLittleOp.add_one
    (hX : IsLittleOp Xn (fun _ => (1 : ℝ)) μ)
    (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => Xn n ω + Yn n ω) (fun _ => (1 : ℝ)) μ :=
  IsLittleOp.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => zero_le_one)) hX hY

/-- Domination by a positive constant times an `o_p(1)` sequence preserves
`o_p(1)`. -/
theorem IsLittleOp.of_abs_le_const_mul_one
    {C : ℝ} (hC : 0 < C) (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ)
    (hbound : ∀ n ω, |Xn n ω| ≤ C * |Yn n ω|) :
    IsLittleOp Xn (fun _ => (1 : ℝ)) μ :=
  IsLittleOp.of_abs_le_const_mul (rn := fun _ => (1 : ℝ)) hC hY hbound

/-- Given [a positive constant](hyp:hC), [a sequence that is `o_p(1)`](hyp:hY), [events whose
complements have vanishing probability](hyp:hG), and [domination by that sequence on those
events](hyp:hbound), [the dominated sequence is itself `o_p(1)`](goal).

A bound available only on a high-probability event still gives `o_p(1)`, because the
conclusion is itself a statement in probability: the failure event contributes one more
vanishing term to the union bound. This is what lets hypotheses valid only near a target
parameter — where a consistent estimator sits with probability tending to one — drive
asymptotic arguments. -/
theorem IsLittleOp.of_abs_le_const_mul_one_on_event
    {C : ℝ} {G : ℕ → Set Ω} (hC : 0 < C)
    (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ)
    (hG : Tendsto (fun n => μ ((G n)ᶜ)) atTop (𝓝 0))
    (hbound : ∀ n ω, ω ∈ G n → |Xn n ω| ≤ C * |Yn n ω|) :
    IsLittleOp Xn (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hYt := hY (ε / C) (div_pos hε hC)
  have hsub : ∀ n, {ω | ε * (1 : ℝ) ≤ ‖Xn n ω‖} ⊆
      {ω | (ε / C) * (1 : ℝ) ≤ ‖Yn n ω‖} ∪ (G n)ᶜ := by
    intro n ω hω
    by_cases hg : ω ∈ G n
    · left
      have hx : ε ≤ |Xn n ω| := by simpa [Real.norm_eq_abs] using hω
      have hCy : ε ≤ C * |Yn n ω| := hx.trans (hbound n ω hg)
      have hy : ε / C ≤ |Yn n ω| := by
        rw [div_le_iff₀ hC]
        simpa [mul_comm] using hCy
      simpa [Real.norm_eq_abs] using hy
    · exact Or.inr hg
  have hsum : Tendsto
      (fun n => μ {ω | (ε / C) * (1 : ℝ) ≤ ‖Yn n ω‖} + μ ((G n)ᶜ))
      atTop (𝓝 0) := by
    simpa using hYt.add hG
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => bot_le) (fun n => ?_)
  calc
    μ {ω | ε * (1 : ℝ) ≤ ‖Xn n ω‖}
        ≤ μ ({ω | (ε / C) * (1 : ℝ) ≤ ‖Yn n ω‖} ∪ (G n)ᶜ) :=
      measure_mono (hsub n)
    _ ≤ _ := measure_union_le _ _

/-- If [the two rates are eventually positive](hyp:hrn,hsn), then a [stochastic little-o
factor](hyp:hX) times a [stochastically bounded factor](hyp:hY) is [stochastic little-o at the
product rate](goal). -/
theorem IsLittleOp.mul_isBigOp
    (hrn : ∀ᶠ n in atTop, 0 < rn n) (hsn : ∀ᶠ n in atTop, 0 < sn n)
    (hX : IsLittleOp Xn rn μ) (hY : IsBigOp Yn sn μ) :
    IsLittleOp (fun n ω => Xn n ω * Yn n ω) (fun n => rn n * sn n) μ := by
  exact Modes.IsLittleOpF.mul_boundedInProbability
    hX hY hrn hsn

/-- The sum of [two sequences bounded in probability at the same rate](hyp:hX,hY) is
[bounded in probability at that rate](goal). -/
theorem IsBigOp.add
    (hX : IsBigOp Xn rn μ) (hY : IsBigOp Yn rn μ) :
    IsBigOp (fun n ω => Xn n ω + Yn n ω) rn μ := by
  exact Modes.BoundedInProbability.add hX hY

/-- Slutsky-style product: `Xn = O_p(1)` and `Yn = o_p(1)` imply
`Xn · Yn = o_p(1)`. -/
theorem IsBigOp.mul_isLittleOp_one_isLittleOp
    (hX : IsBigOp Xn (fun _ => (1 : ℝ)) μ)
    (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => Xn n ω * Yn n ω) (fun _ => (1 : ℝ)) μ := by
  simpa [mul_comm] using Modes.IsLittleOpF.mul_boundedInProbability hY hX
    (Eventually.of_forall fun _ => zero_lt_one)
    (Eventually.of_forall fun _ => zero_lt_one)

end Causalean.Stat
