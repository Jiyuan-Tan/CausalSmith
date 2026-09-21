/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Limit.ContinuousMapping
import Mathlib.Data.Finset.Max

/-!
# Consistency of finite penalized model selection

This module supplies a paper-independent finite-model consistency argument.
Coordinatewise convergence in probability is first upgraded to convergence of
the largest coordinate error.  It then shows that a selector minimizing a
sample-size-scaled empirical loss plus deterministic sublinear penalties
eventually lies in the population-minimizer class.  The selector is expressed
with an explicit injective rank so applications can impose a fixed deterministic
tie rule.
-/

namespace Causalean.Stat

open Filter MeasureTheory Topology

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- For [an indexed real vector](hyp:x) and [a deterministic target vector](hyp:center), the
[largest absolute coordinate error](goal) is the maximum of their coordinatewise absolute
differences over a finite nonempty index type. -/
noncomputable def finiteMaxError [Fintype ι] [Nonempty ι]
    (x center : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |x i - center i|)

/-- If [empirical loss vectors](hyp:empirical) have
[coordinatewise population targets](hyp:population)
under [a sampling measure](hyp:μ), and [each coordinate converges in
probability](hyp:hcoord),
then the [largest absolute coordinate error converges in probability to zero](goal). -/
theorem tendsto_inProb_finiteMaxError [Fintype ι] [Nonempty ι]
    (empirical : ℕ → Ω → ι → ℝ) (population : ι → ℝ) (μ : Measure Ω)
    (hcoord : ∀ i, Tendsto_inProb
      (fun n ω => empirical n ω i) (fun _ => population i) μ) :
    Tendsto_inProb
      (fun n ω => finiteMaxError (empirical n ω) population) (fun _ => 0) μ := by
  classical
  have hcontinuous : ContinuousAt (fun x => finiteMaxError x population) population := by
    apply Continuous.continuousAt
    exact Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ =>
      ((continuous_apply i).sub continuous_const).abs
  simpa [finiteMaxError] using
    (Tendsto_inProb.pi_comp_continuousAt hcontinuous hcoord)

/-- If [empirical loss vectors](hyp:empirical) have
[coordinatewise population targets](hyp:population)
under [a sampling measure](hyp:μ), and [each coordinate converges in
probability](hyp:hcoord),
then, for [a positive tolerance](hyp:hε), the [probability that the largest coordinate error
exceeds that tolerance converges to zero](goal). -/
theorem tendsto_measure_finiteMaxError_ge_zero [Fintype ι] [Nonempty ι]
    (empirical : ℕ → Ω → ι → ℝ) (population : ι → ℝ) (μ : Measure Ω)
    (hcoord : ∀ i, Tendsto_inProb
      (fun n ω => empirical n ω i) (fun _ => population i) μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε ≤ finiteMaxError (empirical n ω) population})
      atTop (𝓝 0) := by
  classical
  have hconv := tendsto_inProb_finiteMaxError empirical population μ hcoord
  rw [Tendsto_inProb_iff, tendstoInMeasure_iff_dist] at hconv
  have hnonneg : ∀ n ω, 0 ≤ finiteMaxError (empirical n ω) population := by
    intro n ω
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (abs_nonneg (empirical n ω i - population i)).trans
      (Finset.le_sup' (s := Finset.univ) (f := fun j => |empirical n ω j - population j|)
        (Finset.mem_univ i))
  simpa [Real.dist_eq, abs_of_nonneg (hnonneg _ _)] using hconv ε hε

/-- For [a population-loss vector](hyp:population), the [population-minimizer class](goal)
contains exactly the model indices attaining its smallest loss. -/
def populationMinimizers (population : ι → ℝ) : Set ι :=
  {i | ∀ j, population i ≤ population j}

/-- Given [a deterministic tie rank](hyp:rank), [a criterion vector](hyp:criterion), and [a selected
model index](hyp:selected), the [ranked-minimizer condition](goal) says that the selected model has
a smaller criterion than each competitor, or an equal criterion and no larger rank. -/
def IsRankedMinimizer (rank : ι → ℕ) (criterion : ι → ℝ) (selected : ι) : Prop :=
  ∀ j, criterion selected < criterion j ∨
    criterion selected = criterion j ∧ rank selected ≤ rank j

/-- If [a selected model is a ranked minimizer](hyp:h), then, for [each competing model](hyp:j),
its [criterion value is no larger than the competitor's](goal). -/
theorem IsRankedMinimizer.le {rank : ι → ℕ} {criterion : ι → ℝ} {selected : ι}
    (h : IsRankedMinimizer rank criterion selected) (j : ι) :
    criterion selected ≤ criterion j := by
  rcases h j with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- Let [empirical losses](hyp:empirical) have [population losses](hyp:population) under [a
probability measure](hyp:μ), with deterministic [penalties](hyp:penalty), a deterministic tie
[rank](hyp:rank), and [a selected model](hyp:selector).  If [each empirical loss converges in
probability](hyp:hcoord), [population minimizers are separated by a positive gap](hyp:hgap),
[each penalty is sublinear](hyp:hpenalty), [the rank is injective](hyp:hrank), and [the selector
is always the ranked minimizer of the penalized empirical criterion](hyp:hselect), then the
[probability of selecting outside the population-minimizer class converges to zero](goal). -/
theorem finite_penalized_argmin_failure_tendsto_zero
    [Fintype ι] [Nonempty ι]
    (empirical : ℕ → Ω → ι → ℝ) (population : ι → ℝ)
    (penalty : ℕ → ι → ℝ) (rank : ι → ℕ) (selector : ℕ → Ω → ι)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hcoord : ∀ i, Tendsto_inProb
      (fun n ω => empirical n ω i) (fun _ => population i) μ)
    (hgap : ∃ gap : ℝ, 0 < gap ∧
      ∀ i ∈ populationMinimizers population,
        ∀ j ∉ populationMinimizers population, population i + gap ≤ population j)
    (hpenalty : ∀ i, Tendsto (fun n => penalty n i / (n : ℝ)) atTop (𝓝 0))
    (hrank : Function.Injective rank)
    (hselect : ∀ (n : ℕ) (ω : Ω), IsRankedMinimizer rank
      (fun i => (n : ℝ) * empirical n ω i + penalty n i) (selector n ω)) :
    Tendsto (fun n => μ {ω | selector n ω ∉ populationMinimizers population})
      atTop (𝓝 0) := by
  classical
  rcases Finset.exists_min_image Finset.univ population Finset.univ_nonempty with
    ⟨i₀, _, hi₀⟩
  have hi₀min : i₀ ∈ populationMinimizers population := by
    intro j
    exact hi₀ j (Finset.mem_univ j)
  rcases hgap with ⟨gap, hgap_pos, hgap⟩
  let δ : ℝ := gap / 8
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hpen_event : ∀ᶠ n in atTop, ∀ i, |penalty n i / (n : ℝ)| < δ := by
    rw [Filter.eventually_all]
    intro i
    have hi := (hpenalty i).eventually (Metric.ball_mem_nhds 0 hδ_pos)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hi
  have hn_event : ∀ᶠ n : ℕ in atTop, 0 < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    omega
  have hsubset : ∀ᶠ n : ℕ in atTop,
      {ω | selector n ω ∉ populationMinimizers population} ⊆
        {ω | δ ≤ finiteMaxError (empirical n ω) population} := by
    filter_upwards [hpen_event, hn_event] with n hpen hn
    intro ω hfail
    by_contra hsmall_not
    have hsmall : finiteMaxError (empirical n ω) population < δ := lt_of_not_ge hsmall_not
    have hcoord_bound : ∀ i, |empirical n ω i - population i| < δ := by
      intro i
      exact lt_of_le_of_lt
        (Finset.le_sup' (s := Finset.univ)
          (f := fun j => |empirical n ω j - population j|) (Finset.mem_univ i)) hsmall
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnreal_ne : (n : ℝ) ≠ 0 := hnreal.ne'
    have hopt := IsRankedMinimizer.le (hselect n ω) i₀
    have hoptdiv :
        empirical n ω (selector n ω) + penalty n (selector n ω) / (n : ℝ) ≤
          empirical n ω i₀ + penalty n i₀ / (n : ℝ) := by
      calc
        empirical n ω (selector n ω) + penalty n (selector n ω) / (n : ℝ) =
            ((n : ℝ) * empirical n ω (selector n ω) + penalty n (selector n ω)) /
              (n : ℝ) := by field_simp
        _ ≤ ((n : ℝ) * empirical n ω i₀ + penalty n i₀) / (n : ℝ) :=
          (div_le_div_iff_of_pos_right hnreal).2 hopt
        _ = empirical n ω i₀ + penalty n i₀ / (n : ℝ) := by field_simp
    have hgap_sel := hgap i₀ hi₀min (selector n ω) hfail
    have hsel_error := hcoord_bound (selector n ω)
    have hi₀_error := hcoord_bound i₀
    have hsel_pen := hpen (selector n ω)
    have hi₀_pen := hpen i₀
    rw [abs_lt] at hsel_error hi₀_error hsel_pen hi₀_pen
    dsimp [δ] at hsel_error hi₀_error hsel_pen hi₀_pen
    linarith
  have hmax := tendsto_measure_finiteMaxError_ge_zero empirical population μ hcoord hδ_pos
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmax
    (Filter.Eventually.of_forall fun _ => bot_le)
    (hsubset.mono fun n hn => measure_mono hn)

/-- Let [empirical losses](hyp:empirical) have [population losses](hyp:population) under [a
probability measure](hyp:μ), with deterministic [penalties](hyp:penalty), a deterministic tie
[rank](hyp:rank), and [a selected model](hyp:selector).  If [each empirical loss converges in
probability](hyp:hcoord), [population minimizers are separated by a positive gap](hyp:hgap),
[each penalty is sublinear](hyp:hpenalty), [the rank is injective](hyp:hrank), [the selector is
always the ranked minimizer of the penalized empirical criterion](hyp:hselect), and [each success
event is measurable](hyp:hmeas), then the [probability of selecting a population minimizer
converges to one](goal). -/
theorem finite_penalized_argmin_consistent
    [Fintype ι] [Nonempty ι]
    (empirical : ℕ → Ω → ι → ℝ) (population : ι → ℝ)
    (penalty : ℕ → ι → ℝ) (rank : ι → ℕ) (selector : ℕ → Ω → ι)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hcoord : ∀ i, Tendsto_inProb
      (fun n ω => empirical n ω i) (fun _ => population i) μ)
    (hgap : ∃ gap : ℝ, 0 < gap ∧
      ∀ i ∈ populationMinimizers population,
        ∀ j ∉ populationMinimizers population, population i + gap ≤ population j)
    (hpenalty : ∀ i, Tendsto (fun n => penalty n i / (n : ℝ)) atTop (𝓝 0))
    (hrank : Function.Injective rank)
    (hselect : ∀ (n : ℕ) (ω : Ω), IsRankedMinimizer rank
      (fun i => (n : ℝ) * empirical n ω i + penalty n i) (selector n ω))
    (hmeas : ∀ n, MeasurableSet {ω | selector n ω ∈ populationMinimizers population}) :
    Tendsto (fun n => μ {ω | selector n ω ∈ populationMinimizers population})
      atTop (𝓝 1) := by
  have hfailure := finite_penalized_argmin_failure_tendsto_zero empirical population penalty
    rank selector μ hcoord hgap hpenalty hrank hselect
  have hsuccess_eq : ∀ n,
      μ {ω | selector n ω ∈ populationMinimizers population} =
        1 - μ {ω | selector n ω ∉ populationMinimizers population} := by
    intro n
    let success : Set Ω := {ω | selector n ω ∈ populationMinimizers population}
    have hfailure_set : {ω | selector n ω ∉ populationMinimizers population} = successᶜ := by
      ext ω
      simp [success]
    have hsuccess_set : {ω | selector n ω ∈ populationMinimizers population} =
        ({ω | selector n ω ∉ populationMinimizers population} : Set Ω)ᶜ := by
      rw [hfailure_set, compl_compl]
    rw [hsuccess_set, measure_compl]
    · simp
    · simpa [hfailure_set, success] using (hmeas n).compl
    · exact measure_ne_top _ _
  simpa only [hsuccess_eq, tsub_zero] using
    (ENNReal.Tendsto.sub tendsto_const_nhds hfailure (Or.inl ENNReal.one_ne_top))

end Causalean.Stat
