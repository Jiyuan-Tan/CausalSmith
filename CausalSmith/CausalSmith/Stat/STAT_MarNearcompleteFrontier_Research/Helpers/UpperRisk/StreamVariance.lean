module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamPilot
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioSecondMoment

/-!
# Cellwise variance bounds for the four-stream correction

This module isolates the self-normalized heavy correction variance needed in
the paper's upper-risk aggregation.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

private lemma finiteStreamCount_eq_ratioEventCount {d : ℕ}
    (z : FiniteSample (Obs d)) (E : Obs d → Prop) :
    finiteStreamCount z E =
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
        {o | E o} z := by
  classical
  rcases z with ⟨N, points⟩
  unfold finiteStreamCount
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.iidEventCount
    FiniteSample.points FiniteSample.count
  rfl

-- @node: upper_streamD_abs_le_half_ae
/-- The heavy correction lies in the centered Bernoulli range almost surely. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_streamD_abs_le_half_ae {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    ∀ᵐ streams ∂fourStreamLaw n P,
      |streamD d streams x a s| ≤ (1 / 2 : ℝ) := by
  classical
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let frac : Set (Obs d) → Set (Obs d) → FiniteSample (Obs d) → ℝ :=
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
  have hAB : A ⊆ B := fun o ho => ⟨ho.1, ho.2.1⟩
  filter_upwards [streamU_eq_arrivedSuccess_ae (n := n) P x a s] with streams hs
  unfold streamD
  rw [hs]
  have hcountA := finiteStreamCount_eq_ratioEventCount (streams 3)
    (fun o => inCell o x a s ∧ o.R = true ∧ o.RY = true)
  have hcountB := finiteStreamCount_eq_ratioEventCount (streams 3)
    (fun o => inCell o x a s ∧ o.R = true)
  unfold heavyCorrection streamArrivedSuccessCount streamC
  rw [hcountA, hcountB]
  by_cases hzero :
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
        B (streams 3) = 0
  · simp [B, hzero]
  · have hpos : 0 <
        Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
          B (streams 3) :=
      lt_of_le_of_ne
        (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount_bounds
          B (streams 3)).1 (Ne.symm hzero)
    have hfrac :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction_bounds
        hAB (streams 3)
    have hrepr :
        Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount A (streams 3) /
            Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount B (streams 3) =
          frac A B (streams 3) := by
      simp [frac,
        Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction, hzero]
    rw [if_pos hpos, hrepr, abs_le]
    constructor <;> linarith

-- @node: upper_measurable_streamD
/-- The totalized heavy correction is measurable as a function of the streams. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
@[fun_prop]
lemma upper_measurable_streamD {d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamD d streams x a s) := by
  classical
  have hc (E : Set (Obs d)) :
      Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
        finiteStreamCount (streams 3) (fun o => o ∈ E)) := by
    have hE : MeasurableSet E := by measurability
    have hm :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.measurable_eventCount E hE
    have heq : (fun z : FiniteSample (Obs d) =>
        finiteStreamCount z (fun o => o ∈ E)) =
        (fun z => (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount z E : ℝ)) := by
      funext z
      simpa only [Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.eventCount,
        Set.mem_ofPred_eq] using
        upper_finiteStreamCount_eq_eventCount z (fun o => o ∈ E)
    change Measurable ((fun z => finiteStreamCount z (fun o => o ∈ E)) ∘
      fun streams : Fin 4 → FiniteSample (Obs d) => streams 3)
    rw [heq]
    exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm).comp
      (measurable_pi_apply 3)
  have hC : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamC d streams x a s) := hc {o | inCell o x a s ∧ o.R = true}
  have hU : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamU d streams x a s) := hc {o | inCell o x a s ∧ o.RY = true}
  unfold streamD heavyCorrection
  apply Measurable.ite (measurableSet_lt measurable_const hC) <;> fun_prop

-- @node: upper_stream_heavy_variance_uniform
/-- The centered heavy correction has mean squared size at most one quarter,
by its almost-sure centered Bernoulli range. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_heavy_variance_uniform {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams,
      (streamD d streams x a s -
        (∫ z, streamD d z x a s ∂fourStreamLaw n P)) ^ 2
      ∂fourStreamLaw n P) ≤ (1 / 4 : ℝ) := by
  classical
  have hμ : fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        ((n : NNReal) / 2 * uniformFourMass i)) := by
    unfold fourStreamLaw
    exact Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.labeledStreamLaw_eq_independent
      _ _ _ _
  letI : IsProbabilityMeasure (fourStreamLaw n P) := by
    rw [hμ]
    infer_instance
  have hm : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamD d streams x a s) := upper_measurable_streamD x a s
  have hb : ∀ᵐ streams ∂fourStreamLaw n P,
      streamD d streams x a s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    filter_upwards [upper_streamD_abs_le_half_ae (n := n) P x a s] with streams hs
    exact abs_le.mp hs
  have hv := ProbabilityTheory.variance_le_sq_of_bounded hb hm.aemeasurable
  rw [ProbabilityTheory.variance_eq_integral hm.aemeasurable] at hv
  norm_num at hv
  exact hv

-- @node: upper_stream_heavy_variance_small_rate
/-- The heavy correction satisfies the required inverse-rate bound whenever
the arrived-cell Poisson rate is at most fifteen. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_heavy_variance_small_rate {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) (hz : streamZ n P x a s ≤ 15) :
    (∫ streams,
      (streamD d streams x a s -
        (∫ z, streamD d z x a s ∂fourStreamLaw n P)) ^ 2
      ∂fourStreamLaw n P) ≤ 4 / (1 + streamZ n P x a s) := by
  have hz0 : 0 ≤ streamZ n P x a s := by
    unfold streamZ
    exact mul_nonneg (by positivity) (arrivedCellMass_nonneg P x a s)
  apply (upper_stream_heavy_variance_uniform (n := n) P x a s).trans
  apply (le_div_iff₀ (by positivity : 0 < 1 + streamZ n P x a s)).mpr
  linarith

/-- Splitting the containing event into successes and failures splits its
zero-safe empirical fraction as well. Given [the specified input `X`](hyp:X), [the specified input `A`](hyp:A), [the specified input `B`](hyp:B), [the specified input `hAB`](hyp:hAB), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_successFraction_complement
lemma upper_successFraction_complement {X : Type*} [MeasurableSpace X]
    {A B : Set X} (hAB : A ⊆ B) (z : FiniteSample X) :
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction A B z -
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction (B \ A) B z =
    2 * Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction A B z -
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction B B z := by
  classical
  open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean in
    have hc : eventCount A z + eventCount (B \ A) z = eventCount B z := by
      unfold eventCount iidEventCount
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hA : z.points i ∈ A
      · simp [hA, hAB hA]
      · by_cases hB : z.points i ∈ B <;> simp [hA, hB]
    unfold successFraction
    by_cases hz : eventCount B z = 0
    · simp [hz]
    · simp only [hz, if_false]
      rw [← hc]
      ring

-- @node: upper_stream_heavy_variance_le
/-- The fourth-stream heavy correction has variance at most a constant divided
by one plus its arrived-cell Poisson rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_heavy_variance_le {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams,
      (streamD d streams x a s -
        (∫ z, streamD d z x a s ∂fourStreamLaw n P)) ^ 2
      ∂fourStreamLaw n P) ≤
      4 / (1 + streamZ n P x a s) := by
  by_cases hz : streamZ n P x a s ≤ 15
  · exact upper_stream_heavy_variance_small_rate P x a s hz
  · classical
    let Q := (observedLaw P).toMeasure
    let lam : NNReal := (n : NNReal) / 2 * uniformFourMass (3 : Fin 4)
    let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
    let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
    let frac : Set (Obs d) → Set (Obs d) → FiniteSample (Obs d) → ℝ :=
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
    have hA : MeasurableSet A := by measurability
    have hB : MeasurableSet B := by measurability
    have hAB : A ⊆ B := fun o ho => ⟨ho.1, ho.2.1⟩
    have hCB : B \ A ⊆ B := Set.sdiff_subset
    have hμ : fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
        finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)) := by
      unfold fourStreamLaw Q
      exact Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.labeledStreamLaw_eq_independent
        _ _ _ _
    let : IsProbabilityMeasure (fourStreamLaw n P) := by rw [hμ]; infer_instance
    have hrate : (lam : ℝ) * Q.real B = streamZ n P x a s := by
      have hmass : Q.real B = arrivedCellMass P x a s := by
        rw [show Q.real B = ∑ o : Obs d,
            if inCell o x a s ∧ o.R = true then obsMass (observedLaw P) o else 0 by
          simpa only [Q, B, Measure.real] using
            observed_event_mass_toReal (observedLaw P)
              (fun o => inCell o x a s ∧ o.R = true)]
        simpa only [inCell, arrivedCellMass, and_assoc] using
          observed_arrived_mass P x a s
      rw [hmass]
      norm_num [lam, uniformFourMass, streamZ]
      left
      ring
    have hPB : 0 < Q.real B := by
      have hzpos : 0 < streamZ n P x a s := by linarith
      rw [← hrate] at hzpos
      exact (mul_pos_iff.mp hzpos).resolve_right (by
        intro hneg
        exact (not_lt_of_ge (by positivity : 0 ≤ (lam : ℝ))) hneg.1)
        |>.2
    let pA := Q.real A / Q.real B
    let pC := Q.real (B \ A) / Q.real B
    let c := (pA - pC) / 2
    have hpoint : ∀ᵐ streams ∂fourStreamLaw n P,
        streamD d streams x a s =
          (frac A B (streams 3) - frac (B \ A) B (streams 3)) / 2 := by
      filter_upwards [streamU_eq_arrivedSuccess_ae (n := n) P x a s] with streams hs
      rw [upper_successFraction_complement hAB]
      unfold streamD
      rw [hs]
      unfold heavyCorrection streamArrivedSuccessCount streamC
      rw [finiteStreamCount_eq_ratioEventCount, finiteStreamCount_eq_ratioEventCount]
      unfold Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
      by_cases hz0 : Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount B (streams 3) = 0
      · simp [B, hz0]
      · have hzpos : 0 < Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount B (streams 3) :=
          lt_of_le_of_ne
            (Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount_bounds B (streams 3)).1
            (Ne.symm hz0)
        simp only [hz0, if_false, B, hzpos, if_true]
        dsimp [A]
        field_simp [show Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount
          {o | inCell o x a s ∧ o.R = true} (streams 3) ≠ 0 from hz0]
    have hm := (upper_measurable_streamD x a s).aestronglyMeasurable
      (μ := fourStreamLaw n P)
    have herr (E : Set (Obs d)) (hE : MeasurableSet E) (hEB : E ⊆ B) :
        (∫ streams, (frac E B (streams 3) - Q.real E / Q.real B) ^ 2
          ∂fourStreamLaw n P) ≤ 4 / (1 + streamZ n P x a s) := by
      rw [hμ]
      rw [integral_comp_eval (μ := fun i : Fin 4 =>
          finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i))
        (i := (3 : Fin 4))
        (f := fun z => (frac E B z - Q.real E / Q.real B) ^ 2)
        (((Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.measurable_successFraction
          hE hB).sub measurable_const).pow_const 2).aestronglyMeasurable]
      simpa only [frac, lam, hrate] using
        CausalSmith.Stat.MarRareqLogfrontier.finitePoisson_successFraction_centered_sq_le
          Q lam hE hB hEB hPB
    have hint (E : Set (Obs d)) (hE : MeasurableSet E) (hEB : E ⊆ B) :
        Integrable (fun streams =>
          (frac E B (streams 3) - Q.real E / Q.real B) ^ 2) (fourStreamLaw n P) := by
      have hmeas : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
          (frac E B (streams 3) - Q.real E / Q.real B) ^ 2) := by
        fun_prop
      apply Integrable.of_bound hmeas.aestronglyMeasurable 1
      filter_upwards [] with streams
      have hf := Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction_bounds hEB (streams 3)
      have hp0 : 0 ≤ Q.real E / Q.real B := div_nonneg measureReal_nonneg hPB.le
      have hp1 : Q.real E / Q.real B ≤ 1 := (div_le_one hPB).mpr (measureReal_mono hEB)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      dsimp [frac]
      nlinarith
    have hDint : Integrable (fun streams => (streamD d streams x a s - c) ^ 2)
        (fourStreamLaw n P) := by
      apply Integrable.of_bound ((hm.sub aestronglyMeasurable_const).pow 2) ((1 / 2 + |c|) ^ 2)
      filter_upwards [upper_streamD_abs_le_half_ae (n := n) P x a s] with streams hb
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hab : |streamD d streams x a s - c| ≤ 1 / 2 + |c| := by
        calc
          _ ≤ |streamD d streams x a s| + |c| := abs_sub _ _
          _ ≤ _ := by linarith
      simpa only [sq_abs, Pi.pow_apply, Pi.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc
      _ = ProbabilityTheory.variance (fun streams => streamD d streams x a s)
          (fourStreamLaw n P) := (ProbabilityTheory.variance_eq_integral hm.aemeasurable).symm
      _ = ProbabilityTheory.variance (fun streams => streamD d streams x a s - c)
          (fourStreamLaw n P) := (ProbabilityTheory.variance_sub_const hm c).symm
      _ ≤ ∫ streams, (streamD d streams x a s - c) ^ 2 ∂fourStreamLaw n P :=
        ProbabilityTheory.variance_le_expectation_sq (hm.sub aestronglyMeasurable_const)
      _ ≤ ∫ streams, ((frac A B (streams 3) - pA) ^ 2 +
          (frac (B \ A) B (streams 3) - pC) ^ 2) / 2 ∂fourStreamLaw n P := by
        apply integral_mono_ae hDint (((hint A hA hAB).add (hint (B \ A) (hB.diff hA) hCB)).div_const 2)
        filter_upwards [hpoint] with streams hs
        rw [hs]
        dsimp [c]
        nlinarith [sq_nonneg ((frac A B (streams 3) - pA) + (frac (B \ A) B (streams 3) - pC))]
      _ = ((∫ streams, (frac A B (streams 3) - pA) ^ 2 ∂fourStreamLaw n P) +
          (∫ streams, (frac (B \ A) B (streams 3) - pC) ^ 2 ∂fourStreamLaw n P)) / 2 := by
        rw [integral_div, integral_add (hint A hA hAB) (hint (B \ A) (hB.diff hA) hCB)]
      _ ≤ _ := by
        have ha := herr A hA hAB
        have hc := herr (B \ A) (hB.diff hA) hCB
        dsimp only [pA, pC]
        linarith

end CausalSmith.Stat.MarNearcompleteFrontier
