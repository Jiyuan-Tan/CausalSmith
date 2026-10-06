module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamSupport
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

/-!
# Factorial corrected stream moments

This module contains the scalar factorial identities, the joint arrived-success
moment, and the integrability result used by the correction branch means.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal BigOperators
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

-- @node: upper_shiftedFalling_descFactorial
/-- The paper's shifted product becomes the usual falling factorial after
including the leading count. Given [the specified input `k`](hyp:k), [the specified input `v`](hyp:v), [the specified input `hv`](hyp:hv), [the stated mathematical conclusion holds](goal). -/
lemma upper_shiftedFalling_descFactorial (k v : ℕ) (hv : 1 ≤ v) :
    (k : ℝ) * shiftedFalling (k : ℝ) v = (k.descFactorial v : ℝ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
  unfold shiftedFalling
  simp only [Nat.succ_sub_one]
  rw [← descPochhammer_eval_eq_prod_range]
  rw [← descPochhammer_eval_eq_descFactorial (R := ℝ)]
  rw [descPochhammer_succ_left]
  simp only [eval_mul, eval_X, eval_comp, eval_sub, eval_one]

-- @node: upper_poisson_shiftedFalling_moment
/-- The scalar factorial moment needed after conditioning on the arrived count. Given [the specified input `rate`](hyp:rate), [the specified input `v`](hyp:v), [the specified input `hv`](hyp:hv), [the stated mathematical conclusion holds](goal). -/
lemma upper_poisson_shiftedFalling_moment (rate : NNReal) (v : ℕ) (hv : 1 ≤ v) :
    (∫ k : ℕ, (k : ℝ) * shiftedFalling (k : ℝ) v ∂poissonMeasure rate) =
      (rate : ℝ) ^ v := by
  simp_rw [upper_shiftedFalling_descFactorial _ _ hv]
  exact Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment rate v

private lemma shiftedFalling_nat_eq (k v : ℕ) (hv : 1 ≤ v) (hk : 1 ≤ k) :
    shiftedFalling (k : ℝ) v = ((k - 1).descFactorial (v - 1) : ℝ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
  unfold shiftedFalling
  simp only [Nat.succ_sub_one]
  rw [← descPochhammer_eval_eq_prod_range]
  rw [← descPochhammer_eval_eq_descFactorial (R := ℝ)]
  simp [Nat.cast_sub hk]

private lemma count_mul_shiftedFalling_eq_weightedFactorial {d v : ℕ}
    (hv : 1 ≤ v) (A B : Set (Obs d)) (hAB : A ⊆ B)
    (z : FiniteSample (Obs d)) :
    finiteStreamCount z (fun o => o ∈ A) *
        shiftedFalling (finiteStreamCount z (fun o => o ∈ B)) v =
      weightedFactorial A B v z := by
  classical
  rw [upper_finiteStreamCount_eq_eventCount,
    upper_finiteStreamCount_eq_eventCount]
  unfold weightedFactorial eventCount
  let IA := Finset.univ.filter fun i : Fin z.count => z.points i ∈ A
  let IB := Finset.univ.filter fun i : Fin z.count => z.points i ∈ B
  have hcard : IA.card ≤ IB.card := by
    apply Finset.card_le_card
    intro i hi
    simp only [IA, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [IB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hAB hi
  by_cases hIA : IA.card = 0
  · simp [IA, hIA]
  · have hIB : 1 ≤ IB.card := by omega
    rw [shiftedFalling_nat_eq IB.card v hv hIB]

/-- For [an observed-data probability mass function](hyp:p) and [a decidable event](hyp:E), [the event probability equals its explicit sum of point masses](goal). -/
lemma observed_event_mass_toReal {d : ℕ} (p : PMF (Obs d))
    (E : Obs d → Prop) [DecidablePred E] :
    (p.toMeasure {o | E o}).toReal =
      ∑ o : Obs d, if E o then obsMass p o else 0 := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro o ho
    by_cases hE : E o <;> simp [Set.indicator, hE, obsMass]
  · intro o ho
    by_cases hE : E o <;> simp [Set.indicator, hE, PMF.apply_ne_top]

-- @node: upper_stream_success_weighted_mean
/-- In one arrived cell, the success count weighted by a function of the total
arrived count has the same mean as the total count weighted by that function,
times the totalized arrived-success probability. This is the joint-count step
used in equation (4). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `v`](hyp:v), [the specified input `hv`](hyp:hv), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_success_weighted_mean {n d v : ℕ} (hv : 1 ≤ v)
    (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∫ streams,
      streamU d streams x a s * shiftedFalling (streamC d streams x a s) v
      ∂fourStreamLaw n P) =
      outcomeMean (observedLaw P) x a s *
        (∫ streams,
          streamC d streams x a s * shiftedFalling (streamC d streams x a s) v
          ∂fourStreamLaw n P) := by
  classical
  let Q := (observedLaw P).toMeasure
  let lam : NNReal := (n : NNReal) / 2 * uniformFourMass 3
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hA : MeasurableSet A := by measurability
  have hB : MeasurableSet B := by measurability
  have hAB : A ⊆ B := by
    intro o ho
    exact ⟨ho.1, ho.2.1⟩
  have hmap : Measure.map (fun streams => streams 3) (fourStreamLaw n P) =
      finitePoissonSampleLaw Q lam := by
    rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
        finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)) by
      unfold fourStreamLaw Q
      exact labeledStreamLaw_eq_independent _ _ _ _]
    simpa [lam] using (measurePreserving_eval (μ := fun i : Fin 4 =>
      finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i))
      (3 : Fin 4)).map_eq
  have htransfer (C D : Set (Obs d)) (hC : MeasurableSet C)
      (hD : MeasurableSet D) (hCD : C ⊆ D) :
      (∫ streams, weightedFactorial C D v (streams 3) ∂fourStreamLaw n P) =
        ∫ z, weightedFactorial C D v z ∂finitePoissonSampleLaw Q lam := by
    rw [← hmap]
    exact (integral_map (measurable_pi_apply 3).aemeasurable
      (measurable_weightedFactorial C D hC hD v).aestronglyMeasurable).symm
  have hleft :
      (∫ streams,
        streamU d streams x a s * shiftedFalling (streamC d streams x a s) v
        ∂fourStreamLaw n P) =
      ∫ z, weightedFactorial A B v z ∂finitePoissonSampleLaw Q lam := by
    calc
      _ = ∫ streams,
          streamArrivedSuccessCount d streams x a s *
            shiftedFalling (streamC d streams x a s) v ∂fourStreamLaw n P := by
        apply integral_congr_ae
        filter_upwards [streamU_eq_arrivedSuccess_ae P x a s] with streams hs
        rw [hs]
      _ = ∫ streams, weightedFactorial A B v (streams 3) ∂fourStreamLaw n P := by
        apply integral_congr_ae
        filter_upwards [] with streams
        simpa only [streamArrivedSuccessCount, streamC, A, B, Set.mem_ofPred_eq] using
          count_mul_shiftedFalling_eq_weightedFactorial hv A B hAB (streams 3)
      _ = _ := htransfer A B hA hB hAB
  have hright :
      (∫ streams,
        streamC d streams x a s * shiftedFalling (streamC d streams x a s) v
        ∂fourStreamLaw n P) =
      ∫ z, weightedFactorial B B v z ∂finitePoissonSampleLaw Q lam := by
    calc
      _ = ∫ streams, weightedFactorial B B v (streams 3) ∂fourStreamLaw n P := by
        apply integral_congr_ae
        filter_upwards [] with streams
        simpa only [streamC, B, Set.mem_ofPred_eq] using
          count_mul_shiftedFalling_eq_weightedFactorial hv B B (Set.Subset.rfl) (streams 3)
      _ = _ := htransfer B B hB hB Set.Subset.rfl
  have houtcome : outcomeMean (observedLaw P) x a s = (Q A).toReal / (Q B).toReal := by
    unfold outcomeMean
    rw [observed_event_mass_toReal (observedLaw P)
      (fun o => inCell o x a s ∧ o.R = true ∧ o.RY = true),
      observed_event_mass_toReal (observedLaw P)
        (fun o => inCell o x a s ∧ o.R = true)]
    simp only [inCell, and_assoc]
  rw [hleft, hright, houtcome,
    finitePoisson_nestedEvent_factorialMoment Q lam A B hA hB hAB v hv,
    finitePoisson_nestedEvent_factorialMoment Q lam B B hB hB Set.Subset.rfl v hv]
  by_cases hQB : (Q B).toReal = 0
  · have hQA : (Q A).toReal = 0 := by
      have hle : Q A ≤ Q B := measure_mono hAB
      have hleR : (Q A).toReal ≤ (Q B).toReal :=
        ENNReal.toReal_mono (measure_ne_top Q B) hle
      exact le_antisymm (hleR.trans (le_of_eq hQB)) ENNReal.toReal_nonneg
    rw [hQA, hQB]
    simp
  · field_simp [hQB]

-- @node: upper_stream_factorial_moment
/-- Equation (4): the centered success count times a shifted falling
factorial has expectation equal to the centered cell mean times the
corresponding Poisson-rate power. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `v`](hyp:v), [the specified input `hv`](hyp:hv), [the specified input `P`](hyp:P), [the specified input `q`](hyp:q), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_factorial_moment {n d v : ℕ} (hv : 1 ≤ v)
    (P : FullLaw d) {q : ℝ} (h : LawClass d q P)
    (x : Fin d) (a s : Bool) :
    (∫ streams,
      (streamU d streams x a s - streamC d streams x a s / 2) *
        shiftedFalling (streamC d streams x a s) v
        ∂fourStreamLaw n P) =
      cellEta P x a s * (streamZ n P x a s) ^ v := by
  classical
  let μ := fourStreamLaw n P
  let rate := streamPoissonRate n P x a s
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hA : MeasurableSet A := by measurability
  have hB : MeasurableSet B := by measurability
  have hAB : A ⊆ B := by
    intro o ho
    exact ⟨ho.1, ho.2.1⟩
  let countC : (Fin 4 → FiniteSample (Obs d)) → ℝ :=
    fun streams => streamC d streams x a s
  let f : ℝ → ℝ := fun c => c * shiftedFalling c v
  have hf : Measurable f := by
    unfold f shiftedFalling
    fun_prop
  have hcountC : Measurable countC := by
    have hevent : Measurable (fun z : FiniteSample (Obs d) => eventCount z B) :=
      measurable_eventCount B hB
    have hcast : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
    rw [show countC = (fun k : ℕ => (k : ℝ)) ∘
        (fun z : FiniteSample (Obs d) => eventCount z B) ∘
          (fun streams : Fin 4 → FiniteSample (Obs d) => streams 3) by
      funext streams
      simpa only [countC, streamC, eventCount, B, Set.mem_ofPred_eq,
        Function.comp_apply] using
        upper_finiteStreamCount_eq_eventCount (streams 3)
          (fun o => inCell o x a s ∧ o.R = true)]
    exact hcast.comp (hevent.comp (measurable_pi_apply 3))
  have hCint : Integrable (fun streams =>
      streamC d streams x a s * shiftedFalling (streamC d streams x a s) v) μ := by
    have hscalar := Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      rate v
    have hscalar' : Integrable (fun k : ℕ =>
        (k : ℝ) * shiftedFalling (k : ℝ) v) (poissonMeasure rate) := by
      simpa only [upper_shiftedFalling_descFactorial _ _ hv] using hscalar
    have hdist := (upper_stream_arrived_count_law (n := n) P x a s).2
    change Integrable (f ∘ countC) μ
    apply (integrable_map_measure hf.aestronglyMeasurable hcountC.aemeasurable).mp
    rw [show Measure.map countC μ =
        Measure.map (fun k : ℕ => (k : ℝ)) (poissonMeasure rate) by
      simpa only [countC, μ, rate] using hdist]
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr (by
        simpa [f, Function.comp_def] using hscalar')
  have hUint : Integrable (fun streams =>
      streamU d streams x a s * shiftedFalling (streamC d streams x a s) v) μ := by
    let Q := (observedLaw P).toMeasure
    let lam : NNReal := (n : NNReal) / 2 * uniformFourMass 3
    have hmap : Measure.map (fun streams => streams 3) μ =
        finitePoissonSampleLaw Q lam := by
      rw [show μ = Measure.pi (fun i : Fin 4 =>
          finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)) by
        unfold μ fourStreamLaw Q
        exact labeledStreamLaw_eq_independent _ _ _ _]
      simpa [lam] using (measurePreserving_eval (μ := fun i : Fin 4 =>
        finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i))
        (3 : Fin 4)).map_eq
    have hw := integrable_weightedFactorial Q lam A B hA hB hAB v hv
    have hwstreams : Integrable
        (fun streams => weightedFactorial A B v (streams 3)) μ := by
      apply (integrable_map_measure
        (measurable_weightedFactorial A B hA hB v).aestronglyMeasurable
        (measurable_pi_apply 3).aemeasurable).mp
      rw [hmap]
      exact hw
    apply Integrable.congr hwstreams
    have hUae := streamU_eq_arrivedSuccess_ae (n := n) P x a s
    filter_upwards [hUae] with streams hU
    rw [hU]
    have hp : streamArrivedSuccessCount d streams x a s *
        shiftedFalling (streamC d streams x a s) v =
          weightedFactorial A B v (streams 3) := by
      simpa only [streamArrivedSuccessCount, streamC, A, B, Set.mem_ofPred_eq] using
        count_mul_shiftedFalling_eq_weightedFactorial hv A B hAB (streams 3)
    exact hp.symm
  have hCmoment : (∫ streams,
      streamC d streams x a s * shiftedFalling (streamC d streams x a s) v ∂μ) =
      (streamZ n P x a s) ^ v := by
    have hdist := (upper_stream_arrived_count_law (n := n) P x a s).2
    calc
      _ = ∫ c : ℝ, f c ∂Measure.map countC μ := by
        exact (integral_map hcountC.aemeasurable hf.aestronglyMeasurable).symm
      _ = ∫ c : ℝ, f c ∂Measure.map (fun k : ℕ => (k : ℝ))
          (poissonMeasure rate) := by rw [show Measure.map countC μ = _ by
            simpa only [countC, μ, rate] using hdist]
      _ = ∫ k : ℕ, (k : ℝ) * shiftedFalling (k : ℝ) v ∂poissonMeasure rate := by
        rw [integral_map (measurable_of_countable _).aemeasurable
          hf.aestronglyMeasurable]
      _ = (rate : ℝ) ^ v := upper_poisson_shiftedFalling_moment rate v hv
      _ = (streamZ n P x a s) ^ v := by
        congr 1
  rw [show (fun streams =>
      (streamU d streams x a s - streamC d streams x a s / 2) *
        shiftedFalling (streamC d streams x a s) v) =
      (fun streams =>
        streamU d streams x a s * shiftedFalling (streamC d streams x a s) v -
        (1 / 2 : ℝ) * (streamC d streams x a s *
          shiftedFalling (streamC d streams x a s) v)) by funext streams; ring]
  rw [integral_sub hUint (hCint.const_mul (1 / 2 : ℝ)), integral_const_mul,
    upper_stream_success_weighted_mean hv P x a s, hCmoment]
  unfold cellEta
  ring

/-- For [a positive factorial order](hyp:hv), [a full-data law](hyp:P), [a covariate cell](hyp:x), and [treatment and arrival indicators](hyp:a,s), [the centered factorial stream statistic is integrable under the four-stream law](goal). -/
lemma upper_stream_factorial_integrable {n d v : ℕ} (hv : 1 ≤ v)
    (P : FullLaw d) (x : Fin d) (a s : Bool) :
    Integrable (fun streams =>
      (streamU d streams x a s - streamC d streams x a s / 2) *
        shiftedFalling (streamC d streams x a s) v) (fourStreamLaw n P) := by
  classical
  let Q := (observedLaw P).toMeasure
  let lam : NNReal := (n : NNReal) / 2 * uniformFourMass 3
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hA : MeasurableSet A := by measurability
  have hB : MeasurableSet B := by measurability
  have hAB : A ⊆ B := fun o ho => ⟨ho.1, ho.2.1⟩
  have hmap : Measure.map (fun streams => streams 3) (fourStreamLaw n P) =
      finitePoissonSampleLaw Q lam := by
    rw [show fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
        finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)) by
      unfold fourStreamLaw Q
      exact labeledStreamLaw_eq_independent _ _ _ _]
    simpa [lam] using (measurePreserving_eval (μ := fun i : Fin 4 =>
      finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i))
      (3 : Fin 4)).map_eq
  have hweighted (C D : Set (Obs d)) (hC : MeasurableSet C)
      (hD : MeasurableSet D) (hCD : C ⊆ D) :
      Integrable (fun streams => weightedFactorial C D v (streams 3))
        (fourStreamLaw n P) := by
    apply (integrable_map_measure
      (measurable_weightedFactorial C D hC hD v).aestronglyMeasurable
      (measurable_pi_apply 3).aemeasurable).mp
    rw [hmap]
    exact integrable_weightedFactorial Q lam C D hC hD hCD v hv
  have hU : Integrable (fun streams => streamU d streams x a s *
      shiftedFalling (streamC d streams x a s) v) (fourStreamLaw n P) := by
    apply Integrable.congr (hweighted A B hA hB hAB)
    filter_upwards [streamU_eq_arrivedSuccess_ae (n := n) P x a s] with streams hs
    rw [hs]
    have hp : streamArrivedSuccessCount d streams x a s *
        shiftedFalling (streamC d streams x a s) v =
          weightedFactorial A B v (streams 3) := by
      simpa only [streamArrivedSuccessCount, streamC, A, B, Set.mem_ofPred_eq] using
        count_mul_shiftedFalling_eq_weightedFactorial hv A B hAB (streams 3)
    exact hp.symm
  have hC : Integrable (fun streams => streamC d streams x a s *
      shiftedFalling (streamC d streams x a s) v) (fourStreamLaw n P) := by
    apply Integrable.congr (hweighted B B hB hB Set.Subset.rfl)
    filter_upwards [] with streams
    have hp : streamC d streams x a s *
        shiftedFalling (streamC d streams x a s) v =
          weightedFactorial B B v (streams 3) := by
      simpa only [streamC, B, Set.mem_ofPred_eq] using
        count_mul_shiftedFalling_eq_weightedFactorial hv B B Set.Subset.rfl
          (streams 3)
    exact hp.symm
  apply Integrable.congr (hU.sub (hC.const_mul (1 / 2 : ℝ)))
  filter_upwards [] with streams
  simp only [Pi.sub_apply]
  ring

end CausalSmith.Stat.MarNearcompleteFrontier
