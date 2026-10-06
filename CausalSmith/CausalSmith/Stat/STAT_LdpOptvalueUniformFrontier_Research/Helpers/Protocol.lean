module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Basic
public import Causalean.Mathlib.Probability.Kernel.FiniteSequence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Helpers/Protocol

Finite original-record private value frontiers: Helpers/Protocol.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


open Causalean.Mathlib.Probability.Kernel.FiniteSequence
-- @env: S2
variable {n d : ℕ} {α : Type} [MeasurableSpace α]

/-- Fix [the sample size](hyp:n) and [the parameter α](hyp:α). [All law-independent choices of a one-message sequential protocol](goal). -/
structure LocalProtocol (n : ℕ) (α : Type) [MeasurableSpace α] where
  Seed : Type -- @realizes \mathcal R(standard-Borel seed carrier)
  seedMeasurable : MeasurableSpace Seed
  seedStandard : @StandardBorelSpace Seed seedMeasurable -- @realizes \mathcal R(Borel)
  seedLaw : @Measure Seed seedMeasurable -- @realizes \lambda(law); @realizes R(seed)
  seedProbability :
    @IsProbabilityMeasure Seed seedMeasurable seedLaw -- @realizes \lambda(probability)
  Message : Fin n → Type -- @realizes \mathcal Z(message spaces) @realizes i(Fin n)
  messageMeasurable : ∀ i, MeasurableSpace (Message i)
  messageStandard : ∀ i,
    @StandardBorelSpace (Message i) (messageMeasurable i) -- @realizes \mathcal Z(Borel)
  kernels : letI := seedMeasurable; letI := messageMeasurable;
    KernelFamily (α × Seed) Message -- @realizes Q(kernels); @realizes \mathsf K(kernels)
  markov : letI := seedMeasurable; letI := messageMeasurable;
    ∀ i, IsMarkovKernel (kernels i)

attribute [instance] LocalProtocol.seedMeasurable LocalProtocol.seedStandard
  LocalProtocol.seedProbability LocalProtocol.messageMeasurable LocalProtocol.messageStandard
  LocalProtocol.markov
/-- Fix [the local protocol Q](hyp:Q) and [the participant index](hyp:i). [History immediately preceding a participant](goal). -/
abbrev ProtocolHistory (Q : LocalProtocol n α) (i : Fin n) :=
  History Q.Message i.val (Nat.le_of_lt i.isLt)
  -- @realizes \mathcal H(product of previous messages) @realizes \ell(previous-stage index)
/-- Fix [the local protocol Q](hyp:Q). [Complete dependent transcript](goal). -/
abbrev ProtocolTranscript (Q : LocalProtocol n α) := Transcript Q.Message
  -- @realizes \mathbf Z(private transcript)

-- @node: ass:full-record-privacy
/-- Fix [the local protocol Q](hyp:Q) and [the privacy budget](hyp:eps). [Pure privacy for every input pair, seed, history and measurable output event](goal). -/
def FullRecordPrivacy (Q : LocalProtocol n α) (eps : ℝ) : Prop :=
  ∀ (i : Fin n) (o o' : α) (eta : ProtocolHistory Q i) (r : Q.Seed)
    (E : Set (Q.Message i)), MeasurableSet E →
    Q.kernels i ((o,r),eta) E ≤ ENNReal.ofReal (Real.exp eps) * Q.kernels i ((o',r),eta) E
    -- @realizes o(input argument) @realizes o'(second input) @realizes \eta(history) @realizes r(seed) @realizes E(Borel event)

-- @node: ass:noninteraction
/-- Fix [the local protocol Q](hyp:Q). [Constancy in all message histories](goal). -/
def Noninteraction (Q : LocalProtocol n α) : Prop :=
  ∀ (i : Fin n) (o : α) (eta eta' : ProtocolHistory Q i) (r : Q.Seed),
    Q.kernels i ((o,r),eta) = Q.kernels i ((o,r),eta') -- @realizes \eta\prime(second history)

-- @node: def:sequential-class
/-- Fix [the local protocol Q](hyp:Q) and [the privacy budget](hyp:eps). [The declared sequential class](goal). -/
structure SequentialClass (Q : LocalProtocol n α) (eps : ℝ) : Prop where
  privacy : FullRecordPrivacy Q eps -- @realizes \mathfrak Q_{\mathrm{SI}}(all-history privacy)

-- @node: def:noninteractive-class
/-- Fix [the local protocol Q](hyp:Q) and [the privacy budget](hyp:eps). [The declared noninteractive class](goal). -/
structure NoninteractiveClass (Q : LocalProtocol n α) (eps : ℝ) : Prop where
  privacy : FullRecordPrivacy Q eps
  noninteraction : Noninteraction Q
  -- @realizes \mathfrak Q_{\mathrm{NI}}(privacy and history constancy)
/-- Fix [the protocol-class label](hyp:C), [the local protocol Q](hyp:Q), and [the privacy budget](hyp:eps). [Select one of the two protocol classes](goal). -/
def protocolClass (C : ProtocolClassLabel) (Q : LocalProtocol n α) (eps : ℝ) : Prop :=
  match C with
  | .NI => NoninteractiveClass Q eps
  | .SI => SequentialClass Q eps
  -- @realizes \mathfrak Q(class selector); @realizes \mathfrak K(same selector on paired inputs)
/-- [NI protocols are sequential protocols](goal). -/
-- @node: NoninteractiveClass.toSequentialClass
lemma NoninteractiveClass.toSequentialClass (Q : LocalProtocol n α) (eps : ℝ)
    (h : NoninteractiveClass Q eps) : SequentialClass Q eps := by
  exact ⟨h.privacy⟩
/-- [Analyst's uniform randomizer law](goal). -/
def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1) -- @realizes U(Uniform[0,1])
/-- Fix [the sample size and the dimension](hyp:n,d). [Scheme for the joint input, public seed and analyst randomizer](goal). -/
def SamplingScheme (n d : ℕ) : Type 1 :=
  (R : Type) → [MeasurableSpace R] → Measure R → Measure (FullRecord d) →
    Measure ((Fin n → ObsRecord d) × R × ℝ) -- @realizes \mathbf O(n-record carrier)

-- @node: ass:iid-people
/-- Fix [the sampling scheme S](hyp:S). [On the declared causal model and standard-Borel public-seed spaces, the records marginal is the n-fold observed product law](goal). -/
def IidPeople (S : SamplingScheme n d) : Prop :=
  ∀ (R : Type) [MeasurableSpace R] [StandardBorelSpace R]
    (lam : Measure R) [IsProbabilityMeasure lam]
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P], CausalModel P →
    (S R lam P).map Prod.fst = Measure.pi (fun _ : Fin n => observedLaw P)

-- @node: ass:independent-randomness
/-- Fix [the sampling scheme S](hyp:S). [On the declared causal model and standard-Borel public-seed spaces, the seed and analyst randomizer form a product independent of the record vector](goal). -/
def IndependentRandomness (S : SamplingScheme n d) : Prop :=
  ∀ (R : Type) [MeasurableSpace R] [StandardBorelSpace R]
    (lam : Measure R) [IsProbabilityMeasure lam]
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P], CausalModel P →
    S R lam P = ((S R lam P).map Prod.fst).prod (lam.prod uniform01)
    -- @realizes R(independent seed) @realizes U(independent randomizer)
/-- Fix [the sample size and the dimension](hyp:n,d). [Canonical iid scheme, displaying non-vacuity of the sampling atoms](goal). -/
def canonicalScheme (n d : ℕ) : SamplingScheme n d :=
  fun _ _ lam P => (Measure.pi (fun _ : Fin n => observedLaw P)).prod (lam.prod uniform01)
/-- [Canonical iid certificate](goal). -/
-- @node: canonicalScheme_iidPeople
lemma canonicalScheme_iidPeople : IidPeople (canonicalScheme n d) := by
  intro R _ _ lam _ P _ _
  simp [canonicalScheme, Measure.map_fst_prod, uniform01, Real.volume_Icc, Measure.prod_apply]
/-- [Canonical independent-randomness certificate](goal). -/
-- @node: canonicalScheme_independentRandomness
lemma canonicalScheme_independentRandomness : IndependentRandomness (canonicalScheme n d) := by
  intro R _ _ lam _ P _ hP
  rw [canonicalScheme_iidPeople R lam P hP]
  rfl
/-- Fix [the local protocol Q](hyp:Q), [the function o](hyp:o), and [the public seed](hyp:r). [Conditional transcript law for fixed records and seed](goal). -/
def fixedTranscriptLaw (Q : LocalProtocol n α) (o : Fin n → α) (r : Q.Seed) :
    Measure (ProtocolTranscript Q) :=
  transcriptLaw Q.kernels (fun i => (o i,r))
/-- Fix [the local protocol Q](hyp:Q). [Private decision observation space](goal). -/
abbrev DecisionSpace (Q : LocalProtocol n α) := ProtocolTranscript Q × Q.Seed × ℝ
/-- Fix [the sampling scheme S](hyp:S), [the local protocol Q](hyp:Q), and [the probability law P](hyp:P). [Joint transcript, seed and analyst randomizer law induced by any sampling scheme](goal). -/
def decisionLaw (S : SamplingScheme n d) (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) : Measure (DecisionSpace Q) :=
  (S Q.Seed Q.seedLaw P).bind (fun w =>
    (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2)))
/-- Fix [the local protocol Q](hyp:Q) and [the probability law p](hyp:p). [Canonical decision law for an arbitrary input alphabet](goal). -/
def canonicalDecisionLaw (Q : LocalProtocol n α) (p : Measure α) : Measure (DecisionSpace Q) :=
  -- @realizes \mathbf Z^{\mathsf K}(canonical paired transcript)
  ((Measure.pi (fun _ : Fin n => p)).prod (Q.seedLaw.prod uniform01)).bind (fun w =>
    (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2)))
/-- Fix [the sampling scheme S](hyp:S), [the local protocol Q](hyp:Q), and [the probability law P](hyp:P). [Joint seed/transcript marginal](goal). -/
def seedTranscriptLaw (S : SamplingScheme n d) (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) : Measure (Q.Seed × ProtocolTranscript Q) :=
  (decisionLaw S Q P).map (fun w => (w.2.1,w.1))
/-- Fix [the local protocol Q](hyp:Q) and [the probability law p](hyp:p). [Canonical joint seed/transcript law on an arbitrary alphabet](goal). -/
def canonicalSeedTranscriptLaw (Q : LocalProtocol n α) (p : Measure α) :
    Measure (Q.Seed × ProtocolTranscript Q) :=
  (canonicalDecisionLaw Q p).map (fun w => (w.2.1,w.1))


end CausalSmith.Stat.LdpOptvalueUniformFrontier
