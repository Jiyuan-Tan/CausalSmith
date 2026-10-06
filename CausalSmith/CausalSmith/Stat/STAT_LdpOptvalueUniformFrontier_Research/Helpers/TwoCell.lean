module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellError

/-!
# Two-cell calibration assembly

Admissible attaining decisions bound both minimax values. The saturated experiment
uses a fixed message, the midpoint estimate, and the whole causal target interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

variable {n d : ℕ}

/-- Assume [the stated attain condition](hyp:hAttain). [One noninteractive attaining procedure gives upper bounds in either protocol class](goal). -/
-- @node: causalAttainment_minimax_upper
lemma causalAttainment_minimax_upper (S : SamplingScheme n d) (eps r h C0 : ℝ)
    (hAttain : CausalAttainment S eps r h C0) (C : ProtocolClassLabel) :
    minimaxRisk S C eps ≤ ENNReal.ofReal (C0*r) ∧
      honestLength S C eps ≤ ENNReal.ofReal (C0*h) := by
  obtain ⟨Q, hNI, T, I, _hTranscript, hBounds⟩ := hAttain
  have hQ : protocolClass C Q eps := by
    cases C with
    | NI => exact hNI
    | SI => exact NoninteractiveClass.toSequentialClass Q eps hNI
  let q : {Q : LocalProtocol n (ObsRecord d) // protocolClass C Q eps} := ⟨Q, hQ⟩
  constructor
  · unfold minimaxRisk riskValue
    apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk ⟨q, T⟩).trans
    apply iSup_le
    intro P
    exact (hBounds P.1 P.2).1
  · unfold honestLength lengthValue
    let J : {I : IntervalDecision Q (1/4) (3/4) //
        ∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)} :=
      ⟨I, fun P hP => (hBounds P hP).2.1⟩
    apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk ⟨q, J⟩).trans
    apply iSup_le
    intro P
    exact (hBounds P.1 P.2).2.2

/-- Assume [the stated hr condition](hyp:hr), [the stated hh condition](hyp:hh), [the stated c condition](hyp:hC), and [the stated attain condition](hyp:hAttain). [Increasing a nonnegative comparison constant preserves attained upper bounds](goal). -/
-- @node: causalAttainment_mono_constant
lemma causalAttainment_mono_constant (S : SamplingScheme n d) (eps r h C0 C1 : ℝ)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hC : C0 ≤ C1)
    (hAttain : CausalAttainment S eps r h C0) : CausalAttainment S eps r h C1 := by
  obtain ⟨Q, hNI, T, I, hTranscript, hBounds⟩ := hAttain
  refine ⟨Q, hNI, T, I, hTranscript, ?_⟩
  intro P hP
  obtain ⟨hRisk, hCov, hLength⟩ := hBounds P hP
  exact ⟨hRisk.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hr)),
    hCov, hLength.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hh))⟩

/-- Fix [the sample size and the dimension](hyp:n,d). [Fixed-message original-record protocol for the saturated branch](goal). -/
-- @node: midpointProtocol
def midpointProtocol (n d : ℕ) : LocalProtocol n (ObsRecord d) where
  Seed := Fin 1
  seedMeasurable := inferInstance
  seedStandard := inferInstance
  seedLaw := Measure.dirac 0
  seedProbability := inferInstance
  Message := fun _ => Bool
  messageMeasurable := fun _ => inferInstance
  messageStandard := fun _ => inferInstance
  kernels := fun _ => Kernel.deterministic (fun _ => false) measurable_const
  markov := fun _ => inferInstance

/-- Assume [a nonnegative privacy budget](hyp:heps). [A fixed message satisfies privacy at every history and seed](goal). -/
-- @node: midpointProtocol_noninteractive
lemma midpointProtocol_noninteractive (eps : ℝ) (heps : 0 ≤ eps) :
    NoninteractiveClass (midpointProtocol n d) eps := by
  constructor
  · intro i o o' eta r E hE
    change (Measure.dirac false) E ≤ ENNReal.ofReal (Real.exp eps) * (Measure.dirac false) E
    exact le_mul_of_one_le_left (bot_le)
      (by simpa using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr heps))
  · intro i o eta eta' r
    rfl

/-- Fix [the sample size and the dimension](hyp:n,d). [Midpoint estimate, independent of all coins](goal). -/
-- @node: midpointEstimator
def midpointEstimator (n d : ℕ) : Estimator (midpointProtocol n d) :=
  ⟨fun _ => 1/2, measurable_const⟩

/-- Fix [the sample size and the dimension](hyp:n,d). [Full causal target interval, independent of all coins](goal). -/
-- @node: fullCausalInterval
def fullCausalInterval (n d : ℕ) : IntervalDecision (midpointProtocol n d) (1/4) (3/4) where
  lo := fun _ => 1/4
  hi := fun _ => 3/4
  measurable_lo := measurable_const
  measurable_hi := measurable_const
  ordered := fun _ => by norm_num
  range_lo := fun _ => by norm_num [Set.mem_Icc]
  range_hi := fun _ => by norm_num [Set.mem_Icc]

/-- Assume [the stated hv condition](hyp:hv). [The saturated procedure has risk at most one sixteenth and perfect coverage](goal). -/
-- @node: midpoint_decision_bounds
lemma midpoint_decision_bounds (L : Measure (DecisionSpace (midpointProtocol n d)))
    [IsProbabilityMeasure L] (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    squaredRisk L (midpointEstimator n d) v ≤ ENNReal.ofReal (1/16 : ℝ) ∧
      coverage L (fullCausalInterval n d) v = 1 ∧
      expectedLength L (fullCausalInterval n d) = ENNReal.ofReal (1/2 : ℝ) := by
  have hsq : (1/2 - v)^2 ≤ (1/16 : ℝ) := by
    nlinarith [hv.1, hv.2, mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [squaredRisk, midpointEstimator, lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_le_ofReal hsq
  · have hEvent : Causalean.Stat.coverageEvent (fullCausalInterval n d).lo
        (fullCausalInterval n d).hi v = Set.univ := by
      ext w
      simp only [Causalean.Stat.coverageEvent, fullCausalInterval, Set.mem_setOf_eq,
        Set.mem_univ, iff_true]
      exact hv
    rw [coverage, hEvent, probReal_univ]
  · norm_num [expectedLength, fullCausalInterval, Causalean.Stat.intervalLength]

/-- Assume [the stated allowed condition](hyp:hAllowed), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [the stated ht condition](hyp:ht). [Saturation of both two-cell rates is attained by fixed messages and the full interval](goal). -/
-- @node: two_cell_saturated_attainment
lemma two_cell_saturated_attainment (n : ℕ) (eps : ℝ) (hAllowed : Allowed n 2 eps)
    (S : SamplingScheme n 2) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (ht : (n : ℝ)*eps^2 ≤ 1) :
    CausalAttainment S eps (min 1 (1/(n*eps^2)))
      (min 1 (1/(Real.sqrt n*eps))) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have heps := hAllowed.2.2.1
  have htpos : (0 : ℝ) < n*eps^2 := mul_pos hn (sq_pos_of_pos heps)
  have hspos : 0 < Real.sqrt n*eps := mul_pos (Real.sqrt_pos.2 hn) heps
  have hssq : (Real.sqrt n*eps)^2 = n*eps^2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]
  have hs : Real.sqrt n*eps ≤ 1 := by nlinarith
  have hr : min 1 (1/(n*eps^2)) = (1 : ℝ) :=
    min_eq_left ((le_div_iff₀ htpos).2 (by simpa using ht))
  have hh : min 1 (1/(Real.sqrt n*eps)) = (1 : ℝ) :=
    min_eq_left ((le_div_iff₀ hspos).2 (by simpa using hs))
  rw [hr, hh]
  refine ⟨midpointProtocol n 2, midpointProtocol_noninteractive eps heps.le,
    midpointEstimator n 2, fullCausalInterval n 2, ?_, ?_⟩
  · exact ⟨fun _ => 1/2, measurable_const, fun _ => rfl⟩
  · intro P hP
    letI := hP.1
    haveI := sampling_decisionLaw_probability S hIID hRandom (midpointProtocol n 2) P hP.2
    obtain ⟨hRisk, hCov, hLength⟩ := midpoint_decision_bounds
      (decisionLaw S (midpointProtocol n 2) P) (value P)
      (causal_value_range P hP.2 (by norm_num))
    refine ⟨hRisk.trans (ENNReal.ofReal_le_ofReal (by norm_num)), ?_, ?_⟩
    · rw [hCov]; norm_num
    · rw [hLength]; norm_num

end CausalSmith.Stat.LdpOptvalueUniformFrontier
