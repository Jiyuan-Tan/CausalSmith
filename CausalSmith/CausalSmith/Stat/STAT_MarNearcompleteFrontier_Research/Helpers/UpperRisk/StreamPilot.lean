module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCorrections

/-!
# Pilot selection of the light and heavy correction branches

These paper-local identities combine the proved branch means using independence
of the third pilot stream from the fourth correction stream.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
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

private lemma measurable_streamCpilot {d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamCpilot d streams x a s) := by
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hB : MeasurableSet B := by measurability
  unfold streamCpilot
  change Measurable ((fun z => finiteStreamCount z (fun o => o ∈ B)) ∘
    fun streams : Fin 4 → FiniteSample (Obs d) => streams 2)
  exact (measurable_finiteStreamCount_set B hB).comp (measurable_pi_apply 2)

private lemma measurable_streamC {d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamC d streams x a s) := by
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  have hB : MeasurableSet B := by measurability
  unfold streamC
  change Measurable ((fun z => finiteStreamCount z (fun o => o ∈ B)) ∘
    fun streams : Fin 4 → FiniteSample (Obs d) => streams 3)
  exact (measurable_finiteStreamCount_set B hB).comp (measurable_pi_apply 3)

private lemma measurable_streamU {d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamU d streams x a s) := by
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  have hA : MeasurableSet A := by measurability
  unfold streamU
  change Measurable ((fun z => finiteStreamCount z (fun o => o ∈ A)) ∘
    fun streams : Fin 4 → FiniteSample (Obs d) => streams 3)
  exact (measurable_finiteStreamCount_set A hA).comp (measurable_pi_apply 3)

private lemma measurable_streamH {n d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamH n d streams x a s) := by
  have hC := measurable_streamC x a s
  have hU := measurable_streamU x a s
  unfold streamH lightCorrection shiftedFalling
  fun_prop

private lemma measurable_streamD {d : ℕ} (x : Fin d) (a s : Bool) :
    Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
      streamD d streams x a s) := by
  have hC := measurable_streamC x a s
  have hU := measurable_streamU x a s
  unfold streamD heavyCorrection
  apply Measurable.ite (measurableSet_lt measurable_const hC)
  · fun_prop
  · fun_prop

private lemma integrable_streamH {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    Integrable (fun streams => streamH n d streams x a s)
      (fourStreamLaw n P) := by
  unfold streamH lightCorrection
  apply integrable_finsetSum
  intro t ht
  have hv : 1 ≤ t + 1 := by omega
  simpa only [mul_assoc] using
    (upper_stream_factorial_integrable hv P x a s).const_mul
      (correctionCoeff n (t + 1))

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

private lemma integrable_streamD {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    Integrable (fun streams => streamD d streams x a s)
      (fourStreamLaw n P) := by
  classical
  let Q := (observedLaw P).toMeasure
  have hμ : fourStreamLaw n P = Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)) := by
    unfold fourStreamLaw Q
    exact labeledStreamLaw_eq_independent _ _ _ _
  letI : IsProbabilityMeasure (fourStreamLaw n P) := by
    rw [hμ]
    infer_instance
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.R = true ∧ o.RY = true}
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let frac : Set (Obs d) → Set (Obs d) → FiniteSample (Obs d) → ℝ :=
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
  have hAB : A ⊆ B := fun o ho => ⟨ho.1, ho.2.1⟩
  have hpoint : ∀ᵐ streams ∂fourStreamLaw n P,
      streamD d streams x a s =
        frac A B (streams 3) - (1 / 2 : ℝ) * frac B B (streams 3) := by
    filter_upwards [streamU_eq_arrivedSuccess_ae (n := n) P x a s] with streams hs
    unfold streamD
    rw [hs]
    have hcountA := finiteStreamCount_eq_ratioEventCount (streams 3)
      (fun o => inCell o x a s ∧ o.R = true ∧ o.RY = true)
    have hcountB := finiteStreamCount_eq_ratioEventCount (streams 3)
      (fun o => inCell o x a s ∧ o.R = true)
    unfold heavyCorrection streamArrivedSuccessCount streamC frac
    rw [hcountA, hcountB]
    unfold Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
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
      simp [B, hzero, hpos]
      rfl
  apply Integrable.of_bound (measurable_streamD x a s).aestronglyMeasurable (3 / 2)
  filter_upwards [hpoint] with streams hs
  rw [hs, Real.norm_eq_abs]
  have h₁ := Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction_bounds
    hAB (streams 3)
  have h₂ := Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction_bounds
    (Set.Subset.rfl : B ⊆ B) (streams 3)
  rw [abs_le]
  constructor <;> linarith

/-- Probability that the third stream selects the light correction in a cell. -/
noncomputable def streamPilotLightProb {d : ℕ} (n : ℕ) (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  (fourStreamLaw n P).real
    {streams | streamCpilot d streams x a s ≤ polyThreshold n / 4}

-- @node: upper_stream_pilot_light_prob_poisson
/-- The pilot light-selection probability is the Poisson probability that the
arrived-cell pilot count is below its threshold. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_pilot_light_prob_poisson {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    streamPilotLightProb n P x a s =
      (poissonMeasure (streamPoissonRate n P x a s)).real
        {k : ℕ | (k : ℝ) ≤ polyThreshold n / 4} := by
  let threshold : ℝ := polyThreshold n / 4
  let S : Set ℝ := Set.Iic threshold
  have hS : MeasurableSet S := measurableSet_Iic
  have hcount := measurable_streamCpilot x a s
  have hcast : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  have hlaw := (upper_stream_arrived_count_law (n := n) P x a s).1
  have happ := congrArg (fun ν : Measure ℝ => (ν S).toReal) hlaw
  rw [Measure.map_apply hcount hS, Measure.map_apply hcast hS] at happ
  unfold streamPilotLightProb
  change ((fourStreamLaw n P)
      ((fun streams => streamCpilot d streams x a s) ⁻¹' S)).toReal =
    (poissonMeasure (streamPoissonRate n P x a s)
      ((fun k : ℕ => (k : ℝ)) ⁻¹' S)).toReal
  exact happ

-- @node: upper_stream_pilot_branch_mean
/-- Independence of the pilot and correction streams mixes their light and
heavy expected corrections with the pilot selection probability. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_pilot_branch_mean {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) =
      streamPilotLightProb n P x a s *
        (∫ streams, streamH n d streams x a s ∂fourStreamLaw n P) +
      (1 - streamPilotLightProb n P x a s) *
        (∫ streams, streamD d streams x a s ∂fourStreamLaw n P) := by
  classical
  let μ := fourStreamLaw n P
  let Q := (observedLaw P).toMeasure
  let μi : Fin 4 → Measure (FiniteSample (Obs d)) := fun i =>
    finitePoissonSampleLaw Q ((n : NNReal) / 2 * uniformFourMass i)
  have hμ : μ = Measure.pi μi := by
    unfold μ μi fourStreamLaw Q
    exact labeledStreamLaw_eq_independent _ _ _ _
  letI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  let B : Set (Obs d) := {o | inCell o x a s ∧ o.R = true}
  let A : Set (Obs d) := {o | inCell o x a s ∧ o.RY = true}
  let c : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => o ∈ B)
  let u : FiniteSample (Obs d) → ℝ := fun z =>
    finiteStreamCount z (fun o => o ∈ A)
  let pilot : FiniteSample (Obs d) → ℝ := fun z =>
    if c z ≤ polyThreshold n / 4 then 1 else 0
  let light : FiniteSample (Obs d) → ℝ := fun z => lightCorrection n (c z) (u z)
  let heavy : FiniteSample (Obs d) → ℝ := fun z => heavyCorrection (c z) (u z)
  have hB : MeasurableSet B := by measurability
  have hA : MeasurableSet A := by measurability
  have hc : Measurable c := measurable_finiteStreamCount_set B hB
  have hu : Measurable u := measurable_finiteStreamCount_set A hA
  have hp : Measurable pilot := by
    unfold pilot
    apply Measurable.ite (measurableSet_le hc measurable_const) <;> fun_prop
  have hl : Measurable light := by
    unfold light lightCorrection shiftedFalling
    fun_prop
  have hd : Measurable heavy := by
    unfold heavy heavyCorrection
    apply Measurable.ite (measurableSet_lt measurable_const hc) <;> fun_prop
  have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i) μ := by
    rw [hμ]
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hi23 := hi.indepFun (by decide : (2 : Fin 4) ≠ 3)
  have hindLight := hi23.comp hp hl
  have hnot : Measurable (fun z => 1 - pilot z) := measurable_const.sub hp
  have hindHeavy := hi23.comp hnot hd
  have hpInt : Integrable (fun streams => pilot (streams 2)) μ :=
    Integrable.of_bound (hp.comp (measurable_pi_apply 2)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun streams => by
        unfold pilot
        split_ifs <;> norm_num)
  have hnInt : Integrable (fun streams => 1 - pilot (streams 2)) μ :=
    (integrable_const 1).sub hpInt
  have hlInt : Integrable (fun streams => light (streams 3)) μ := by
    simpa only [μ, light, c, u, streamH, streamC, streamU, B, A,
      Set.mem_ofPred_eq] using integrable_streamH P x a s
  have hdInt : Integrable (fun streams => heavy (streams 3)) μ := by
    simpa only [μ, heavy, c, u, streamD, streamC, streamU, B, A,
      Set.mem_ofPred_eq] using integrable_streamD P x a s
  have hfacLight : (∫ streams, pilot (streams 2) * light (streams 3) ∂μ) =
      (∫ streams, pilot (streams 2) ∂μ) *
        ∫ streams, light (streams 3) ∂μ :=
    hindLight.integral_fun_mul_eq_mul_integral
      (hp.comp (measurable_pi_apply 2)).aestronglyMeasurable
      (hl.comp (measurable_pi_apply 3)).aestronglyMeasurable
  have hfacHeavy : (∫ streams, (1 - pilot (streams 2)) * heavy (streams 3) ∂μ) =
      (∫ streams, 1 - pilot (streams 2) ∂μ) *
        ∫ streams, heavy (streams 3) ∂μ :=
    hindHeavy.integral_fun_mul_eq_mul_integral
      ((measurable_const.sub (hp.comp (measurable_pi_apply 2))).aestronglyMeasurable)
      (hd.comp (measurable_pi_apply 3)).aestronglyMeasurable
  have hprodLight : Integrable
      (fun streams => pilot (streams 2) * light (streams 3)) μ := by
    convert hindLight.integrable_mul hpInt hlInt using 1 <;> funext streams <;> rfl
  have hprodHeavy : Integrable
      (fun streams => (1 - pilot (streams 2)) * heavy (streams 3)) μ := by
    convert hindHeavy.integrable_mul hnInt hdInt using 1 <;> funext streams <;> rfl
  let E : Set (Fin 4 → FiniteSample (Obs d)) :=
    {streams | streamCpilot d streams x a s ≤ polyThreshold n / 4}
  have hE : MeasurableSet E :=
    measurableSet_le (measurable_streamCpilot x a s) measurable_const
  have hpMean : (∫ streams, pilot (streams 2) ∂μ) =
      streamPilotLightProb n P x a s := by
    rw [show (fun streams => pilot (streams 2)) = E.indicator (fun _ => (1 : ℝ)) by
      funext streams
      simp only [pilot, c, E, Set.indicator, Set.mem_ofPred_eq, streamCpilot, B]
      rfl]
    rw [integral_indicator_const (1 : ℝ) hE]
    simp only [smul_eq_mul, mul_one, μ, streamPilotLightProb, E]
  have hnMean : (∫ streams, 1 - pilot (streams 2) ∂μ) =
      1 - streamPilotLightProb n P x a s := by
    rw [show (fun streams => 1 - pilot (streams 2)) =
        Eᶜ.indicator (fun _ => (1 : ℝ)) by
      funext streams
      simp only [pilot, c, E, Set.indicator, Set.mem_compl_iff,
        Set.mem_ofPred_eq, streamCpilot, B]
      split_ifs <;> simp_all]
    rw [integral_indicator_const (1 : ℝ) hE.compl]
    simp only [smul_eq_mul, mul_one, measureReal_compl hE, probReal_univ,
      μ, streamPilotLightProb, E]
  rw [show (fun streams => streamG n d streams x a s) =
      (fun streams => pilot (streams 2) * light (streams 3) +
        (1 - pilot (streams 2)) * heavy (streams 3)) by
    funext streams
    unfold streamG
    simp only [pilot, light, heavy, c, u, streamCpilot, streamH, streamD, B, A,
      Set.mem_ofPred_eq]
    norm_num [div_eq_mul_inv] at *
    split_ifs <;> simp_all [streamC, streamU]]
  change (∫ streams, pilot (streams 2) * light (streams 3) +
      (1 - pilot (streams 2)) * heavy (streams 3) ∂μ) =
    streamPilotLightProb n P x a s * (∫ streams, light (streams 3) ∂μ) +
      (1 - streamPilotLightProb n P x a s) * (∫ streams, heavy (streams 3) ∂μ)
  rw [integral_add hprodLight hprodHeavy, hfacLight, hfacHeavy, hpMean, hnMean]

-- @node: upper_stream_pilot_bias
/-- The selected correction's cellwise bias is the sum of its light
Chebyshev remainder and heavy empty-count remainder. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `q`](hyp:q), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_pilot_bias {n d : ℕ} (P : FullLaw d)
    {q : ℝ} (h : LawClass d q P) (x : Fin d) (a s : Bool) :
    (∫ streams, streamG n d streams x a s ∂fourStreamLaw n P) -
        cellEta P x a s =
      -cellEta P x a s *
        (streamPilotLightProb n P x a s *
            (qPoly n).eval (streamZ n P x a s) +
          (1 - streamPilotLightProb n P x a s) *
            Real.exp (-(streamZ n P x a s))) := by
  rw [upper_stream_pilot_branch_mean P x a s,
    upper_stream_light_mean P h x a s,
    upper_stream_heavy_mean P h x a s]
  ring

end CausalSmith.Stat.MarNearcompleteFrontier
