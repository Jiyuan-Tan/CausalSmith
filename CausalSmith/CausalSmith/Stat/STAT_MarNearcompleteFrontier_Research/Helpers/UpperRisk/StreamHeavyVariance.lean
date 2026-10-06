module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamProduct
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamVarianceAlgebra

/-!
# Heavy correction product variance

Square integrability and independent stream moments give the cellwise variance
bound and its alphabet-uniform sum in equation (16) of the upper-risk proof.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

/-- The ideal four-stream experiment is a probability measure. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_fourStreamLaw_isProbabilityMeasure
lemma upper_fourStreamLaw_isProbabilityMeasure {n d : ℕ} (P : FullLaw d) :
    IsProbabilityMeasure (fourStreamLaw n P) := by
  rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        ((n : NNReal) / 2 * uniformFourMass i)) from
    labeledStreamLaw_eq_independent _ _ _ _]
  infer_instance

/-- The normalized missing-cell count is square integrable, including at zero
sample size under the totalized division convention. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamV_memLp_two
lemma upper_streamV_memLp_two {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    MemLp (fun streams => streamV n d streams x a s) 2 (fourStreamLaw n P) := by
  classical
  let μ := fourStreamLaw n P
  let Q := (observedLaw P).toMeasure
  let lam : NNReal := ((n : NNReal) / 2) * uniformFourMass 1
  let E : Obs d → Bool := fun o => decide (inCell o x a s ∧ o.R = false)
  let count : (Fin 4 → FiniteSample (Obs d)) → ℕ := fun streams =>
    (Finset.univ.filter (fun i : Fin (streams 1).count =>
      E ((streams 1).points i) = true)).card
  let rate : NNReal := lam * (Q {o | E o = true}).toNNReal
  have hstream : Measure.map (fun streams ↦ streams 1) μ =
      finitePoissonSampleLaw Q lam := by
    let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun i ↦
      finitePoissonSampleLaw Q (((n : NNReal) / 2) * uniformFourMass i)
    have (i : Fin 4) : IsProbabilityMeasure (ν i) := by
      dsimp [ν]
      infer_instance
    rw [show μ = Measure.pi ν by
      unfold μ fourStreamLaw ν
      exact labeledStreamLaw_eq_independent _ _ _ _]
    simpa [ν, Q, lam] using (Measure.pi_map_eval (μ := ν) 1)
  have hcountMeas : Measurable count :=
    (upper_measurable_eventCount E).comp (measurable_pi_apply 1)
  have hlaw : Measure.map count μ = poissonMeasure rate := by
    rw [show count = (fun z : FiniteSample (Obs d) =>
        (Finset.univ.filter (fun i : Fin z.count => E (z.points i) = true)).card) ∘
        (fun streams => streams 1) by rfl]
    rw [← Measure.map_map (upper_measurable_eventCount E)
      (measurable_pi_apply 1), hstream]
    exact upper_finitePoissonSampleLaw_eventCount Q lam E (measurable_of_countable E)
  have hcountReal (streams : Fin 4 → FiniteSample (Obs d)) :
      finiteStreamCount (streams 1)
        (fun o ↦ inCell o x a s ∧ o.R = false) = (count streams : ℝ) := by
    simpa only [count, E, decide_eq_true_eq] using
      upper_finiteStreamCount_eq_eventCount (streams 1)
        (fun o ↦ inCell o x a s ∧ o.R = false)
  have hV (streams : Fin 4 → FiniteSample (Obs d)) :
      streamV n d streams x a s = (count streams : ℝ) / ((n : ℝ) / 8) := by
    unfold streamV
    rw [hcountReal]
  have hp : MemLp (fun k : ℕ => (k : ℝ)) 2 (Measure.map count μ) := by
    rw [hlaw]
    exact Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rate
  have hc := hp.comp_of_map hcountMeas.aemeasurable
  simpa only [Function.comp_apply, ← div_eq_mul_inv, ← hV, μ] using
    hc.mul_const (((n : ℝ) / 8)⁻¹)

/-- The missing-count times heavy-correction statistic is square integrable:
the heavy factor has absolute value at most one half almost surely. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVD_memLp_two
lemma upper_streamVD_memLp_two {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    MemLp (fun streams => streamV n d streams x a s * streamD d streams x a s)
      2 (fourStreamLaw n P) := by
  have hv := upper_streamV_memLp_two (n := n) P x a s
  have hm := hv.aestronglyMeasurable.mul
    (upper_measurable_streamD x a s).aestronglyMeasurable
  apply hv.of_le_mul hm (c := (1 / 2 : ℝ))
  filter_upwards [upper_streamD_abs_le_half_ae (n := n) P x a s] with streams hs
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  nlinarith [abs_nonneg (streamV n d streams x a s)]

/-- The mean of the heavy correction has squared absolute size at most one
quarter under its almost-sure centered Bernoulli range. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamD_mean_sq_le
lemma upper_streamD_mean_sq_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, streamD d streams x a s ∂fourStreamLaw n P) ^ 2 ≤ (1 / 4 : ℝ) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hm := (upper_measurable_streamD x a s).aestronglyMeasurable
    (μ := fourStreamLaw n P)
  have hb := upper_streamD_abs_le_half_ae (n := n) P x a s
  have hi : Integrable (fun streams => |streamD d streams x a s|) (fourStreamLaw n P) := by
    apply Integrable.of_bound hm.norm (1 / 2)
    simpa only [Real.norm_eq_abs, abs_abs] using hb
  have hbound : |∫ streams, streamD d streams x a s ∂fourStreamLaw n P| ≤ 1 / 2 := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ _streams, (1 / 2 : ℝ) ∂fourStreamLaw n P :=
        integral_mono_ae hi (integrable_const _) hb
      _ = 1 / 2 := by simp
  have hs := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  norm_num only [sq_abs, div_pow] at hs ⊢
  exact hs

/-- Independent stream moments and the inverse-rate heavy variance bound give
the cellwise product-variance budget in equation (16). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamVD_variance_le
lemma upper_streamVD_variance_le {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    variance (fun streams => streamV n d streams x a s * streamD d streams x a s)
      (fourStreamLaw n P) ≤
      4 * (missingCellMass P x a s) ^ 2 / (1 + streamZ n P x a s) +
        (17 / 4 : ℝ) * (missingCellMass P x a s / ((n : ℝ) / 8)) := by
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  have hd : MemLp (fun streams => streamD d streams x a s) 2 (fourStreamLaw n P) := by
    apply MemLp.of_bound (upper_measurable_streamD x a s).aestronglyMeasurable (1 / 2)
    simpa only [Real.norm_eq_abs] using upper_streamD_abs_le_half_ae (n := n) P x a s
  have hvar := variance_eq_sub hd
  have hν : variance (fun streams => streamD d streams x a s) (fourStreamLaw n P) ≤
      4 / (1 + streamZ n P x a s) := by
    rw [variance_eq_integral hd.aemeasurable]
    exact upper_stream_heavy_variance_le P x a s
  rw [variance_eq_sub (upper_streamVD_memLp_two P x a s)]
  change (∫ streams, (streamV n d streams x a s * streamD d streams x a s) ^ 2
    ∂fourStreamLaw n P) -
    (∫ streams, streamV n d streams x a s * streamD d streams x a s
      ∂fourStreamLaw n P) ^ 2 ≤ _
  rw [upper_stream_vd_second_moment hn, upper_stream_vd_mean hn]
  have hsecond : (∫ streams, (streamD d streams x a s) ^ 2 ∂fourStreamLaw n P) =
      variance (fun streams => streamD d streams x a s) (fourStreamLaw n P) +
        (∫ streams, streamD d streams x a s ∂fourStreamLaw n P) ^ 2 := by
    change variance (fun streams => streamD d streams x a s) (fourStreamLaw n P) =
      (∫ streams, (streamD d streams x a s) ^ 2 ∂fourStreamLaw n P) -
        (∫ streams, streamD d streams x a s ∂fourStreamLaw n P) ^ 2 at hvar
    linarith
  rw [hsecond]
  have hw : 0 ≤ missingCellMass P x a s := by
    unfold missingCellMass
    exact sub_nonneg.mpr (arrivedCellMass_le_cellMass P x a s)
  have hz : 0 ≤ streamZ n P x a s :=
    mul_nonneg (by positivity) (arrivedCellMass_nonneg P x a s)
  exact heavyProductVariance_algebra_le hw (by positivity) hz hν
    (upper_streamD_mean_sq_le P x a s)

/-- The sum of the actual heavy product variances is bounded by 34 divided by
the sample size, uniformly over the alphabet and the legal arrival floors. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: upper_streamVD_variance_sum_le
lemma upper_streamVD_variance_sum_le {n d : ℕ} {q : ℝ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      variance (fun streams => streamV n d streams x a s * streamD d streams x a s)
        (fourStreamLaw n P)) ≤ 34 / (n : ℝ) := by
  calc
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
        (4 * (missingCellMass P x a s) ^ 2 / (1 + streamZ n P x a s) +
          (17 / 4 : ℝ) * (missingCellMass P x a s / ((n : ℝ) / 8))) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      exact upper_streamVD_variance_le hn P x a s
    _ ≤ 17 / (4 * ((n : ℝ) / 8)) :=
      heavyProductVariance_budget P h hq ((n : ℝ) / 8) (by positivity)
    _ = 34 / (n : ℝ) := by ring

end CausalSmith.Stat.MarNearcompleteFrontier
