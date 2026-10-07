module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamVariance

/-!
# Product moments of the independent missing and correction streams

These identities isolate the independence step in the heavy-cell variance
calculation of the upper-risk proof.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

private lemma measurable_finiteStreamCount_set {d : ℕ} (E : Set (Obs d))
    (hE : MeasurableSet E) :
    Measurable (fun z : FiniteSample (Obs d) =>
      finiteStreamCount z (fun o => o ∈ E)) := by
  classical
  have hm : Measurable (fun z : FiniteSample (Obs d) =>
      (eventCount z E : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_eventCount E hE)
  rw [show (fun z : FiniteSample (Obs d) =>
      finiteStreamCount z (fun o => o ∈ E)) =
      (fun z => (eventCount z E : ℝ)) by
    funext z
    simpa only [eventCount, Set.mem_ofPred_eq] using
      upper_finiteStreamCount_eq_eventCount z (fun o => o ∈ E)]
  exact hm

-- @node: upper_stream_vd_mean
/-- The mean of a cell's missing-count times heavy correction factors across
the independent second and fourth Poisson streams. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_vd_mean {n d : ℕ} (hn : 0 < n)
    (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∫ streams,
      streamV n d streams x a s * streamD d streams x a s
      ∂fourStreamLaw n P) =
      missingCellMass P x a s *
      (∫ streams, streamD d streams x a s
        ∂fourStreamLaw n P) := by
  classical
  let μ := fourStreamLaw n P
  let Q := (observedLaw P).toMeasure
  let μi : Fin 4 → Measure (FiniteSample (Obs d)) := fun i =>
    finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)
  have hμ : μ = Measure.pi μi := by
    unfold μ μi fourStreamLaw Q
    exact labeledStreamLaw_eq_independent _ _ _ _
  let _ : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  let M : Set (Obs d) := {o | inCell o x a s ∧ o.R = false}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  let v : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => o ∈ M) / ((n : ℝ) / 8)
  let corr : FiniteSample (Obs d) → ℝ := fun z =>
    heavyCorrection
      (finiteStreamCount z (fun o => o ∈ B))
      (finiteStreamCount z (fun o => o ∈ A))
  have hM : MeasurableSet M := by measurability
  have hB : MeasurableSet B := by measurability
  have hA : MeasurableSet A := by measurability
  have hv : Measurable v := by
    have hm := measurable_finiteStreamCount_set M hM
    unfold v
    exact hm.div measurable_const
  have hcorr : Measurable corr := by
    have hc := measurable_finiteStreamCount_set B hB
    have hu := measurable_finiteStreamCount_set A hA
    unfold corr heavyCorrection
    apply Measurable.ite (measurableSet_lt measurable_const hc) <;> fun_prop
  have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i) μ := by
    rw [hμ]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hind := (hi.indepFun (by decide : (1 : Fin 4) ≠ 3)).comp hv hcorr
  have hfactor : (∫ streams, v (streams 1) * corr (streams 3) ∂μ) =
      (∫ streams, v (streams 1) ∂μ) *
        ∫ streams, corr (streams 3) ∂μ := by
    exact hind.integral_fun_mul_eq_mul_integral
      (hv.comp (measurable_pi_apply 1)).aestronglyMeasurable
      (hcorr.comp (measurable_pi_apply 3)).aestronglyMeasurable
  have hvMean : (∫ streams, v (streams 1) ∂μ) =
      missingCellMass P x a s := by
    simpa only [μ, v, M, streamV, Set.mem_ofPred_eq] using
      upper_stream_v_mean hn P x a s
  calc
    (∫ streams,
      streamV n d streams x a s * streamD d streams x a s
      ∂fourStreamLaw n P) =
        ∫ streams, v (streams 1) * corr (streams 3) ∂μ := by
      congr 1
    _ = (∫ streams, v (streams 1) ∂μ) *
        ∫ streams, corr (streams 3) ∂μ := hfactor
    _ = missingCellMass P x a s *
        (∫ streams, streamD d streams x a s
          ∂fourStreamLaw n P) := by
      rw [hvMean]
      congr 1

-- @node: upper_stream_vd_second_moment
/-- The second moment of a cell's missing-count times heavy correction factors
across the independent second and fourth Poisson streams. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_vd_second_moment {n d : ℕ} (hn : 0 < n)
    (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∫ streams,
      (streamV n d streams x a s * streamD d streams x a s) ^ 2
      ∂fourStreamLaw n P) =
      ((missingCellMass P x a s) ^ 2 +
        missingCellMass P x a s / ((n : ℝ) / 8)) *
      (∫ streams, (streamD d streams x a s) ^ 2
        ∂fourStreamLaw n P) := by
  classical
  let μ := fourStreamLaw n P
  let Q := (observedLaw P).toMeasure
  let μi : Fin 4 → Measure (FiniteSample (Obs d)) := fun i =>
    finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)
  have hμ : μ = Measure.pi μi := by
    unfold μ μi fourStreamLaw Q
    exact labeledStreamLaw_eq_independent _ _ _ _
  let _ : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  let M : Set (Obs d) := {o | inCell o x a s ∧ o.R = false}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  let v : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => o ∈ M) / ((n : ℝ) / 8)
  let corr : FiniteSample (Obs d) → ℝ := fun z =>
    heavyCorrection
      (finiteStreamCount z (fun o => o ∈ B))
      (finiteStreamCount z (fun o => o ∈ A))
  have hM : MeasurableSet M := by measurability
  have hB : MeasurableSet B := by measurability
  have hA : MeasurableSet A := by measurability
  have hv : Measurable v := by
    have hm := measurable_finiteStreamCount_set M hM
    unfold v
    exact hm.div measurable_const
  have hcorr : Measurable corr := by
    have hc := measurable_finiteStreamCount_set B hB
    have hu := measurable_finiteStreamCount_set A hA
    unfold corr heavyCorrection
    apply Measurable.ite (measurableSet_lt measurable_const hc) <;> fun_prop
  have hv2 : Measurable (fun z => (v z) ^ 2) := by fun_prop
  have hcorr2 : Measurable (fun z => (corr z) ^ 2) := by fun_prop
  have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i) μ := by
    rw [hμ]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hind := (hi.indepFun (by decide : (1 : Fin 4) ≠ 3)).comp hv2 hcorr2
  have hfactor :
      (∫ streams, (v (streams 1)) ^ 2 * (corr (streams 3)) ^ 2 ∂μ) =
        (∫ streams, (v (streams 1)) ^ 2 ∂μ) *
          ∫ streams, (corr (streams 3)) ^ 2 ∂μ := by
    exact hind.integral_fun_mul_eq_mul_integral
      (hv2.comp (measurable_pi_apply 1)).aestronglyMeasurable
      (hcorr2.comp (measurable_pi_apply 3)).aestronglyMeasurable
  have hvMoment : (∫ streams, (v (streams 1)) ^ 2 ∂μ) =
      (missingCellMass P x a s) ^ 2 +
        missingCellMass P x a s / ((n : ℝ) / 8) := by
    simpa only [μ, v, M, streamV, Set.mem_ofPred_eq] using
      upper_stream_v_second_moment hn P x a s
  calc
    (∫ streams,
      (streamV n d streams x a s * streamD d streams x a s) ^ 2
      ∂fourStreamLaw n P) =
        ∫ streams, (v (streams 1)) ^ 2 * (corr (streams 3)) ^ 2 ∂μ := by
      congr 1
      funext streams
      simp only [v, corr, M, B, A, streamV, streamD, streamC, streamU,
        Set.mem_ofPred_eq]
      ring
    _ = (∫ streams, (v (streams 1)) ^ 2 ∂μ) *
        ∫ streams, (corr (streams 3)) ^ 2 ∂μ := hfactor
    _ = ((missingCellMass P x a s) ^ 2 +
          missingCellMass P x a s / ((n : ℝ) / 8)) *
        (∫ streams, (streamD d streams x a s) ^ 2
          ∂fourStreamLaw n P) := by
      rw [hvMoment]
      congr 1

end CausalSmith.Stat.MarNearcompleteFrontier
