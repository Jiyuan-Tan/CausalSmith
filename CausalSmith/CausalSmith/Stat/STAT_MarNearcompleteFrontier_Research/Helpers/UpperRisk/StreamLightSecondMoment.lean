module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.LightSecondMoment
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.PoissonPowerMoments
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamHeavyVariance

/-!
# Expected light-correction square envelope

The arrived-count law transports the raw Poisson moment bound to the actual
fourth stream. Integrating the pointwise envelope proves equation (8).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Stat.Concentration.Poisson

/-- Real-valued finite-stream event counts are measurable. Given [the specified input `d`](hyp:d), [the specified input `hE`](hyp:hE), [the stated mathematical conclusion holds](goal). Given [the specified input `E`](hyp:E). -/
-- @node: upper_measurable_finiteStreamCount
@[fun_prop]
lemma upper_measurable_finiteStreamCount {d : ℕ} (E : Set (Obs d))
    (hE : MeasurableSet E) :
    Measurable (fun z : FiniteSample (Obs d) =>
      finiteStreamCount z (fun o => o ∈ E)) := by
  classical
  have hm := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_eventCount E hE)
  convert hm using 1
  funext z
  simpa only [eventCount, Set.mem_ofPred_eq, Function.comp_apply] using
    upper_finiteStreamCount_eq_eventCount z (fun o => o ∈ E)

/-- The fourth-stream arrived count is measurable. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_measurable_streamC
@[fun_prop]
lemma upper_measurable_streamC {d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamC d streams x a s) := by
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hB : MeasurableSet B := by measurability
  exact (upper_measurable_finiteStreamCount B hB).comp (measurable_pi_apply 3)

/-- The fourth-stream light correction is measurable. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_measurable_streamH
@[fun_prop]
lemma upper_measurable_streamH {n d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamH n d streams x a s) := by
  have hC := upper_measurable_streamC x a s
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  have hA : MeasurableSet A := by measurability
  have hU : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamU d streams x a s) :=
    (upper_measurable_finiteStreamCount A hA).comp (measurable_pi_apply 3)
  unfold streamH lightCorrection shiftedFalling
  fun_prop

/-- All arrived-count powers are integrable under the ideal experiment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `r`](hyp:r), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamC_power_integrable
lemma upper_streamC_power_integrable {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) (r : ℕ) :
    Integrable (fun streams => (streamC d streams x a s) ^ r)
      (fourStreamLaw n P) := by
  have hc := upper_measurable_streamC x a s
  have hf : Measurable (fun c : ℝ => c ^ r) := by fun_prop
  change Integrable ((fun c : ℝ => c ^ r) ∘
    fun streams => streamC d streams x a s) (fourStreamLaw n P)
  apply (integrable_map_measure hf.aestronglyMeasurable hc.aemeasurable).mp
  rw [(upper_stream_arrived_count_law (n := n) P x a s).2]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mpr
      (poisson_power_integrable _ r)

/-- Equation (7) transferred through the actual arrived-count marginal. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `r`](hyp:r), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamC_power_moment_le
lemma upper_streamC_power_moment_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) (r : ℕ) :
    (∫ streams, (streamC d streams x a s) ^ r ∂fourStreamLaw n P) ≤
      (streamZ n P x a s + (r : ℝ)) ^ r := by
  have hc := upper_measurable_streamC x a s
  have hf : Measurable (fun c : ℝ => c ^ r) := by fun_prop
  rw [← integral_map hc.aemeasurable hf.aestronglyMeasurable,
    (upper_stream_arrived_count_law (n := n) P x a s).2,
    integral_map (measurable_of_countable _).aemeasurable hf.aestronglyMeasurable]
  have hrate : (streamPoissonRate n P x a s : ℝ) = streamZ n P x a s := by
    rfl
  rw [← hrate]
  exact poisson_power_moment_le (streamPoissonRate n P x a s) r

/-- Replacing the maximum by one plus the nonnegative count power gives an
integrable envelope for the light correction's square. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_sq_le_add_envelope_ae
lemma upper_streamH_sq_le_add_envelope_ae {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    ∀ᵐ streams ∂fourStreamLaw n P,
      (streamH n d streams x a s) ^ 2 ≤
        (64 : ℝ) ^ polyDegree n / 4 *
          (1 + (streamC d streams x a s / polyThreshold n) ^
            (2 * polyDegree n)) := by
  filter_upwards [upper_streamH_sq_le_degree_envelope_ae (n := n) P x a s]
    with streams hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply max_le
  · have hp : 0 ≤ (streamC d streams x a s / polyThreshold n) ^
        (2 * polyDegree n) := by
      rw [pow_mul]
      positivity
    linarith
  · linarith

/-- The coefficient and count-power envelope makes the actual light
correction square integrable without adding regularity premises. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_sq_integrable
lemma upper_streamH_sq_integrable {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    Integrable (fun streams => (streamH n d streams x a s) ^ 2)
      (fourStreamLaw n P) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have he : Integrable (fun streams => (64 : ℝ) ^ polyDegree n / 4 *
      (1 + (streamC d streams x a s / polyThreshold n) ^
        (2 * polyDegree n))) (fourStreamLaw n P) := by
    simp_rw [div_pow]
    exact ((integrable_const 1).add
      ((upper_streamC_power_integrable P x a s _).div_const _)).const_mul _
  apply he.mono' ((upper_measurable_streamH x a s).pow_const 2).aestronglyMeasurable
  filter_upwards [upper_streamH_sq_le_add_envelope_ae (n := n) P x a s]
    with streams hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (streamH n d streams x a s))]
  exact hs

/-- Integrating the envelope and applying the Poisson power moment bound
gives the growth factor in equation (8). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_second_moment_add_le
lemma upper_streamH_second_moment_add_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) ≤
      (64 : ℝ) ^ polyDegree n / 4 *
        (1 + ((streamZ n P x a s + (2 * polyDegree n : ℕ)) /
          polyThreshold n) ^ (2 * polyDegree n)) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hp := upper_streamC_power_integrable (n := n) P x a s (2 * polyDegree n)
  have he : Integrable (fun streams => (64 : ℝ) ^ polyDegree n / 4 *
      (1 + (streamC d streams x a s / polyThreshold n) ^
        (2 * polyDegree n))) (fourStreamLaw n P) := by
    simp_rw [div_pow]
    exact ((integrable_const 1).add (hp.div_const _)).const_mul _
  calc
    _ ≤ ∫ streams, (64 : ℝ) ^ polyDegree n / 4 *
        (1 + (streamC d streams x a s / polyThreshold n) ^
          (2 * polyDegree n)) ∂fourStreamLaw n P :=
      integral_mono_ae (upper_streamH_sq_integrable P x a s) he
        (upper_streamH_sq_le_add_envelope_ae P x a s)
    _ = (64 : ℝ) ^ polyDegree n / 4 *
        (1 + (∫ streams, (streamC d streams x a s) ^ (2 * polyDegree n)
          ∂fourStreamLaw n P) / polyThreshold n ^ (2 * polyDegree n)) := by
      simp_rw [div_pow]
      rw [integral_const_mul, integral_add (integrable_const 1) (hp.div_const _),
        integral_const, integral_div]
      simp
    _ ≤ _ := by
      rw [div_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add_right
      exact div_le_div_of_nonneg_right (upper_streamC_power_moment_le P x a s _)
        (by rw [pow_mul]; positivity)

/-- Equation (8) for the actual light-stream statistic, with explicit
universal constant one half. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_second_moment_le
lemma upper_streamH_second_moment_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) ≤
      (64 : ℝ) ^ polyDegree n / 2 *
        max 1 (((streamZ n P x a s + (2 * polyDegree n : ℕ)) /
          polyThreshold n) ^ (2 * polyDegree n)) := by
  apply (upper_streamH_second_moment_add_le P x a s).trans
  have h1 := le_max_left (1 : ℝ)
    (((streamZ n P x a s + (2 * polyDegree n : ℕ)) /
      polyThreshold n) ^ (2 * polyDegree n))
  have h2 := le_max_right (1 : ℝ)
    (((streamZ n P x a s + (2 * polyDegree n : ℕ)) /
      polyThreshold n) ^ (2 * polyDegree n))
  have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (show 0 ≤ (64 : ℝ) ^ polyDegree n / 4 by positivity)
  nlinarith only [hh]

end CausalSmith.Stat.MarNearcompleteFrontier
