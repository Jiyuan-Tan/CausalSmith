module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Protocol
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Minimax.MinimaxValue

/-!
# Helpers/Decision

Finite original-record private value frontiers: Helpers/Decision.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ} {α : Type} [MeasurableSpace α] {Q : LocalProtocol n α}
/-- Fix [the local protocol Q](hyp:Q). [Measurable decisions using only transcript, seed and analyst randomizer](goal). -/
abbrev Estimator (Q : LocalProtocol n α) := {T : DecisionSpace Q → ℝ // Measurable T}
-- @realizes T(Borel real decision); @realizes \widehat D(same Borel decision for TV)
/-- Fix [the local protocol Q](hyp:Q) and [the real parameter lower and the real parameter upper](hyp:lower,upper). [Connected, ordered, closed interval decisions in a fixed range](goal). -/
structure IntervalDecision (Q : LocalProtocol n α) (lower upper : ℝ) where
  lo : DecisionSpace Q → ℝ -- @realizes I(lower endpoint) @realizes J_{\mathrm{TV}}(lower endpoint)
  hi : DecisionSpace Q → ℝ -- @realizes I(upper endpoint) @realizes J_{\mathrm{TV}}(upper endpoint)
  measurable_lo : Measurable lo
  measurable_hi : Measurable hi
  ordered : ∀ w, lo w ≤ hi w -- @realizes I(ordered endpoints); @realizes J_{\mathrm{TV}}(ordered endpoints)
  range_lo : ∀ w, lo w ∈ Set.Icc lower upper
    -- @realizes I(lower endpoint range); @realizes J_{\mathrm{TV}}(lower endpoint range)
  range_hi : ∀ w, hi w ∈ Set.Icc lower upper
    -- @realizes I(upper endpoint range); @realizes J_{\mathrm{TV}}(upper endpoint range)
/-- Fix [the probability law L](hyp:L), [the estimator T](hyp:T), and [the real parameter v](hyp:v). [Extended nonnegative squared-error expectation; infinite risks stay infinite](goal). -/
def squaredRisk (L : Measure (DecisionSpace Q)) (T : Estimator Q) (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal ((T.1 w - v)^2) ∂L
/-- Fix [the probability law L](hyp:L) and [the interval procedure I](hyp:I). [Expected connected interval length](goal). -/
def expectedLength {lower upper : ℝ} (L : Measure (DecisionSpace Q))
    (I : IntervalDecision Q lower upper) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (Causalean.Stat.intervalLength (I.lo w) (I.hi w)) ∂L
/-- Fix [the probability law L](hyp:L), [the interval procedure I](hyp:I), and [the real parameter v](hyp:v). [Coverage of a deterministic population target](goal). -/
def coverage {lower upper : ℝ} (L : Measure (DecisionSpace Q))
    (I : IntervalDecision Q lower upper) (v : ℝ) : ℝ :=
  L.real (Causalean.Stat.coverageEvent I.lo I.hi v)
/-- Fix [the probability law M](hyp:M), [the probability law target](hyp:target), [the local protocol laws](hyp:laws), [the protocol-class label](hyp:C), and [the privacy budget](hyp:eps). [Generic decision value over a law class and a population target](goal). -/
def riskValue {Ω : Type} [MeasurableSpace Ω] (M : Set (Measure Ω)) (target : Measure Ω → ℝ)
    (laws : (Q : LocalProtocol n α) → Measure Ω → Measure (DecisionSpace Q))
    (C : ProtocolClassLabel) (eps : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (e : (Q : {Q : LocalProtocol n α // protocolClass C Q eps}) × Estimator Q.1)
      (p : {p : Measure Ω // p ∈ M}) => squaredRisk (laws e.1.1 p.1) e.2 (target p.1))
/-- Fix [the probability law M](hyp:M), [the probability law target](hyp:target), [the local protocol laws](hyp:laws), [the protocol-class label](hyp:C), and [the privacy budget and the real parameter lower and the real parameter upper](hyp:eps,lower,upper). [Generic globally honest connected-interval value](goal). -/
def lengthValue {Ω : Type} [MeasurableSpace Ω] (M : Set (Measure Ω)) (target : Measure Ω → ℝ)
    (laws : (Q : LocalProtocol n α) → Measure Ω → Measure (DecisionSpace Q))
    (C : ProtocolClassLabel) (eps lower upper : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (e : (Q : {Q : LocalProtocol n α // protocolClass C Q eps}) ×
      {I : IntervalDecision Q.1 lower upper //
        ∀ p ∈ M, (0.90 : ℝ) ≤ coverage (laws Q.1 p) I (target p)})
      (p : {p : Measure Ω // p ∈ M}) => expectedLength (laws e.1.1 p.1) e.2.1)

-- @node: def:risk
/-- Fix [the sampling scheme S](hyp:S), [the protocol-class label](hyp:C), and [the privacy budget](hyp:eps). [Mechanism-optimal scalar causal risk](goal). -/
def minimaxRisk (S : SamplingScheme n d) (C : ProtocolClassLabel) (eps : ℝ) : ℝ≥0∞ :=
  riskValue (causalClass d) value (decisionLaw S) C eps
  -- @realizes \mathfrak R(minimax extended MSE)

-- @node: def:honest-length
/-- Fix [the sampling scheme S](hyp:S), [the protocol-class label](hyp:C), and [the privacy budget](hyp:eps). [Globally 0.90-honest connected causal interval length](goal). -/
def honestLength (S : SamplingScheme n d) (C : ProtocolClassLabel) (eps : ℝ) : ℝ≥0∞ :=
  lengthValue (causalClass d) value (decisionLaw S) C eps (1/4) (3/4)
  -- @realizes \mathfrak H(minimax honest length)
/-- Fix [the local protocol Q](hyp:Q). [Finite alphabet certificate for attaining protocols](goal). -/
def FiniteMessages (Q : LocalProtocol n α) : Prop := ∀ i, Finite (Q.Message i)
/-- Fix [the local protocol Q](hyp:Q) and [the estimator T](hyp:T). [A decision is transcript-only when the public and analyst coins do not alter it](goal). -/
def TranscriptOnly (Q : LocalProtocol n α) (T : Estimator Q) : Prop :=
  ∃ f : ProtocolTranscript Q → ℝ, Measurable f ∧ ∀ w, T.1 w = f w.1
/-- Fix [the sampling scheme S](hyp:S) and [the privacy budget and the public seed and the stated h condition and the constant C0](hyp:eps,r,h,C0). [A concrete NI protocol and decisions attaining both upper orders](goal). -/
def CausalAttainment (S : SamplingScheme n d) (eps r h C0 : ℝ) : Prop :=
  ∃ (Q : LocalProtocol n (ObsRecord d)), NoninteractiveClass Q eps ∧
    ∃ (T : Estimator Q) (I : IntervalDecision Q (1/4) (3/4)), TranscriptOnly Q T ∧
      ∀ P ∈ causalClass d,
        squaredRisk (decisionLaw S Q P) T (value P) ≤ ENNReal.ofReal (C0 * r) ∧
        (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P) ∧
        expectedLength (decisionLaw S Q P) I ≤ ENNReal.ofReal (C0 * h)
/-- [NI optimization is over a smaller protocol class](goal). -/
-- @node: ni_si_values
lemma ni_si_values (S : SamplingScheme n d) (eps : ℝ) :
    minimaxRisk S .SI eps ≤ minimaxRisk S .NI eps ∧
    honestLength S .SI eps ≤ honestLength S .NI eps := by
  constructor
  · unfold minimaxRisk riskValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    let q : {Q : LocalProtocol n (ObsRecord d) // protocolClass .SI Q eps} :=
      ⟨e.1.1, NoninteractiveClass.toSequentialClass e.1.1 eps e.1.2⟩
    exact iInf_le_of_le ⟨q, e.2⟩ le_rfl
  · unfold honestLength lengthValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    let q : {Q : LocalProtocol n (ObsRecord d) // protocolClass .SI Q eps} :=
      ⟨e.1.1, NoninteractiveClass.toSequentialClass e.1.1 eps e.1.2⟩
    exact iInf_le_of_le ⟨q, e.2⟩ le_rfl


end CausalSmith.Stat.LdpOptvalueUniformFrontier
