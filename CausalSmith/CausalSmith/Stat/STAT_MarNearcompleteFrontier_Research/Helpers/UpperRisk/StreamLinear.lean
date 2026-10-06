module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.FallbackBias
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRiskVariance

/-!
# Moments of the linear first stream

The linear arrived score is a difference of two thinned Poisson counts.
Their exact moments give square integrability and an inverse-sample-size
variance budget for the linear term in equations (1) and (20).
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

/-- Count a Boolean event in an auxiliary stream. Given [the specified input `d`](hyp:d), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_streamEventCount
noncomputable def upper_streamEventCount {d : ℕ} (i : Fin 4) (E : Obs d → Bool)
    (streams : Fin 4 → FiniteSample (Obs d)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k : Fin (streams i).count =>
    E ((streams i).points k) = true)).card

/-- Stream event counts are measurable. Given [the specified input `d`](hyp:d), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamEventCount_measurable
lemma upper_streamEventCount_measurable {d : ℕ} (i : Fin 4) (E : Obs d → Bool) :
    Measurable (upper_streamEventCount i E) := by
  exact (upper_measurable_eventCount E).comp (measurable_pi_apply i)

/-- Thinning any of the four streams gives the Poisson law at intensity n/8
 times the event probability. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamEventCount_law
lemma upper_streamEventCount_law {n d : ℕ} (P : FullLaw d)
    (i : Fin 4) (E : Obs d → Bool) :
    Measure.map (upper_streamEventCount i E) (fourStreamLaw n P) =
      poissonMeasure (((n : NNReal) / 8) *
        ((observedLaw P).toMeasure {o | E o = true}).toNNReal) := by
  let Q := (observedLaw P).toMeasure
  let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun j =>
    finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass j)
  have (j : Fin 4) : IsProbabilityMeasure (ν j) := by
    dsimp [ν]
    infer_instance
  have hstream : Measure.map (fun streams => streams i) (fourStreamLaw n P) = ν i := by
    rw [show fourStreamLaw n P = Measure.pi ν from
      labeledStreamLaw_eq_independent _ _ _ _]
    simpa using (Measure.pi_map_eval (μ := ν) i)
  change Measure.map ((fun z : FiniteSample (Obs d) =>
    (Finset.univ.filter (fun k : Fin z.count => E (z.points k) = true)).card) ∘
    (fun streams => streams i)) (fourStreamLaw n P) = _
  rw [← Measure.map_map (upper_measurable_eventCount E) (measurable_pi_apply i), hstream]
  have h := upper_finitePoissonSampleLaw_eventCount Q
    ((n : NNReal) / 2 * uniformFourMass i) E (measurable_of_countable E)
  have hlam : (n : NNReal) / 2 * uniformFourMass i = (n : NNReal) / 8 := by
    unfold uniformFourMass
    ring
  simpa only [ν, hlam] using h

/-- Real event counts have finite second moments. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamEventCount_memLp_two
lemma upper_streamEventCount_memLp_two {n d : ℕ} (P : FullLaw d)
    (i : Fin 4) (E : Obs d → Bool) :
    MemLp (fun streams => (upper_streamEventCount i E streams : ℝ))
      2 (fourStreamLaw n P) := by
  have hp : MemLp (fun k : ℕ => (k : ℝ)) 2
      (Measure.map (upper_streamEventCount i E) (fourStreamLaw n P)) := by
    rw [upper_streamEventCount_law]
    exact Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two _
  exact hp.comp_of_map (upper_streamEventCount_measurable i E).aemeasurable

/-- The mean of an event count is its thinned intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamEventCount_mean
lemma upper_streamEventCount_mean {n d : ℕ} (P : FullLaw d)
    (i : Fin 4) (E : Obs d → Bool) :
    (∫ streams, (upper_streamEventCount i E streams : ℝ) ∂fourStreamLaw n P) =
      (n : ℝ) / 8 * (observedLaw P).toMeasure.real {o | E o = true} := by
  rw [← integral_map (upper_streamEventCount_measurable i E).aemeasurable
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable,
    upper_streamEventCount_law,
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  push_cast
  rfl

/-- The variance of an event count is its thinned intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamEventCount_variance
lemma upper_streamEventCount_variance {n d : ℕ} (P : FullLaw d)
    (i : Fin 4) (E : Obs d → Bool) :
    variance (fun streams => (upper_streamEventCount i E streams : ℝ))
      (fourStreamLaw n P) =
      (n : ℝ) / 8 * (observedLaw P).toMeasure.real {o | E o = true} := by
  change variance ((fun k : ℕ => (k : ℝ)) ∘ upper_streamEventCount i E)
    (fourStreamLaw n P) = _
  rw [← variance_map (measurable_of_countable (fun k : ℕ => (k : ℝ))).aemeasurable
    (upper_streamEventCount_measurable i E).aemeasurable, upper_streamEventCount_law]
  rw [variance_eq_sub
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two _)]
  simp only [Pi.pow_apply]
  rw [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.poisson_count_second_moment,
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  push_cast
  change ((n : ℝ) / 8 * (observedLaw P).toMeasure.real {o | E o = true}) ^ 2 +
    (n : ℝ) / 8 * (observedLaw P).toMeasure.real {o | E o = true} -
    ((n : ℝ) / 8 * (observedLaw P).toMeasure.real {o | E o = true}) ^ 2 = _
  ring

/-- The normalized arrived score from the first auxiliary stream. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_streamLinear
noncomputable def upper_streamLinear (n d : ℕ)
    (streams : Fin 4 → FiniteSample (Obs d)) : ℝ :=
  ((n : ℝ) / 8)⁻¹ * ∑ k : Fin (streams 0).count,
    upper_fallbackScore ((streams 0).points k)

/-- The linear term is the difference of positive and negative arrived counts. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_streamLinear_eq_counts
lemma upper_streamLinear_eq_counts {n d : ℕ}
    (streams : Fin 4 → FiniteSample (Obs d)) :
    upper_streamLinear n d streams = ((n : ℝ) / 8)⁻¹ *
      ((upper_streamEventCount 0 (fun o : Obs d => o.R && (o.A == o.RY)) streams : ℝ) -
       (upper_streamEventCount 0 (fun o : Obs d => o.R && !(o.A == o.RY)) streams : ℝ)) := by
  classical
  unfold upper_streamLinear upper_streamEventCount
  simp only [← Finset.sum_boole, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  cases ha : ((streams 0).points k).A <;>
    cases hr : ((streams 0).points k).R <;>
    cases hy : ((streams 0).points k).RY <;>
    norm_num [upper_fallbackScore, ha, hr, hy]

/-- The first-stream linear term is square integrable. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamLinear_memLp_two
lemma upper_streamLinear_memLp_two {n d : ℕ} (P : FullLaw d) :
    MemLp (upper_streamLinear n d) 2 (fourStreamLaw n P) := by
  convert ((upper_streamEventCount_memLp_two (n := n) P 0
    (fun o : Obs d => o.R && (o.A == o.RY))).sub
    (upper_streamEventCount_memLp_two (n := n) P 0
      (fun o : Obs d => o.R && !(o.A == o.RY)))).const_mul (((n : ℝ) / 8)⁻¹) using 1
  ext streams
  exact upper_streamLinear_eq_counts streams

/-- The linear term in the raw estimator agrees with the named first-stream score. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_fourStreamRawEstimate_eq_linear_add
lemma upper_fourStreamRawEstimate_eq_linear_add {n d : ℕ}
    (streams : Fin 4 → FiniteSample (Obs d)) :
    fourStreamRawEstimate n d streams = upper_streamLinear n d streams +
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * streamCellCorrection n d streams x a s) := by
  unfold fourStreamRawEstimate upper_streamLinear treatmentSign upper_fallbackScore
  dsimp only
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  dsimp [FiniteSample.points]
  simp only [div_eq_mul_inv]
  ring_nf
  rfl

/-- The linear-stream variance is bounded by a universal multiple of 1/n.
The two event probabilities are each at most one; no cell-count factor enters. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamLinear_variance_le
lemma upper_streamLinear_variance_le {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    variance (upper_streamLinear n d) (fourStreamLaw n P) ≤ 32 / (n : ℝ) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  let X := fun streams => (upper_streamEventCount 0
    (fun o : Obs d => o.R && (o.A == o.RY)) streams : ℝ)
  let Y := fun streams => (upper_streamEventCount 0
    (fun o : Obs d => o.R && !(o.A == o.RY)) streams : ℝ)
  have hX : MemLp X 2 (fourStreamLaw n P) := upper_streamEventCount_memLp_two P 0 _
  have hY : MemLp Y 2 (fourStreamLaw n P) := upper_streamEventCount_memLp_two P 0 _
  have hv : variance (fun streams => X streams - Y streams) (fourStreamLaw n P) ≤
      2 * variance X (fourStreamLaw n P) + 2 * variance Y (fourStreamLaw n P) := by
    have hp := variance_fun_add hX hY
    have hm := variance_fun_sub hX hY
    have hz := variance_nonneg (X := fun streams => X streams + Y streams)
      (μ := fourStreamLaw n P)
    linarith
  have hXv : variance X (fourStreamLaw n P) ≤ (n : ℝ) / 8 := by
    rw [upper_streamEventCount_variance]
    exact mul_le_of_le_one_right (by positivity) measureReal_le_one
  have hYv : variance Y (fourStreamLaw n P) ≤ (n : ℝ) / 8 := by
    rw [upper_streamEventCount_variance]
    exact mul_le_of_le_one_right (by positivity) measureReal_le_one
  have heq : upper_streamLinear n d = fun streams =>
      ((n : ℝ) / 8)⁻¹ * (X streams - Y streams) := by
    ext streams
    exact upper_streamLinear_eq_counts streams
  rw [heq, variance_const_mul]
  calc
    _ ≤ (((n : ℝ) / 8)⁻¹) ^ 2 * ((n : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith
    _ = _ := by
      have hnR : (n : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- The arrived score mean is the difference of its positive and negative
 event probabilities. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fallbackScore_mean_eq_event_difference
lemma upper_fallbackScore_mean_eq_event_difference {d : ℕ} (P : FullLaw d) :
    (∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure) =
      (observedLaw P).toMeasure.real {o | (o.R && (o.A == o.RY)) = true} -
      (observedLaw P).toMeasure.real {o | (o.R && !(o.A == o.RY)) = true} := by
  classical
  let Epos : Set (Obs d) := {o | (o.R && (o.A == o.RY)) = true}
  let Eneg : Set (Obs d) := {o | (o.R && !(o.A == o.RY)) = true}
  have heq : upper_fallbackScore (d := d) = fun o =>
      Epos.indicator (1 : Obs d → ℝ) o - Eneg.indicator (1 : Obs d → ℝ) o := by
    ext o
    cases ha : o.A <;> cases hr : o.R <;> cases hy : o.RY <;>
      norm_num [upper_fallbackScore, Epos, Eneg, Set.indicator, ha, hr, hy]
  rw [heq, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_indicator_one (by measurability), integral_indicator_one (by measurability)]

/-- Normalizing the first Poisson stream leaves the population arrived-score
 mean unchanged. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamLinear_mean
lemma upper_streamLinear_mean {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    (∫ streams, upper_streamLinear n d streams ∂fourStreamLaw n P) =
      ∫ o, upper_fallbackScore o ∂(observedLaw P).toMeasure := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have heq : upper_streamLinear n d = fun streams => ((n : ℝ) / 8)⁻¹ *
      ((upper_streamEventCount 0 (fun o : Obs d => o.R && (o.A == o.RY)) streams : ℝ) -
       (upper_streamEventCount 0 (fun o : Obs d => o.R && !(o.A == o.RY)) streams : ℝ)) := by
    ext streams
    exact upper_streamLinear_eq_counts streams
  rw [heq, integral_const_mul,
    integral_sub ((upper_streamEventCount_memLp_two P 0 _).integrable (by norm_num))
      ((upper_streamEventCount_memLp_two P 0 _).integrable (by norm_num)),
    upper_streamEventCount_mean, upper_streamEventCount_mean,
    upper_fallbackScore_mean_eq_event_difference]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- The linear-stream mean is exactly the arrived part of the identified
 centered target decomposition (1). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamLinear_mean_eq_arrived
lemma upper_streamLinear_mean_eq_arrived {n d : ℕ} (hn : 0 < n) (P : FullLaw d) :
    (∫ streams, upper_streamLinear n d streams ∂fourStreamLaw n P) =
      2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        treatmentSign a * arrivedCellMass P x a s * cellEta P x a s) := by
  rw [upper_streamLinear_mean hn P, upper_fallbackScore_mean]

end CausalSmith.Stat.MarNearcompleteFrontier
