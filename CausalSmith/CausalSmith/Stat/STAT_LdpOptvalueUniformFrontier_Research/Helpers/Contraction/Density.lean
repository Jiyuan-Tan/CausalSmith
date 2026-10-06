module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.FiniteDensity
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.TSignedCausalBridge
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Helpers/Contraction/Density

Finite original-record private value frontiers: Helpers/Contraction/Density.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ} {Q : LocalProtocol n (ObsRecord d)}
-- @env: S3
variable (eps : ℝ) -- @realizes \varepsilon(privacy budget, scoped by Allowed)
/-- Fix [the dimension](hyp:d) and [the privacy budget](hyp:eps). [Coordinate privacy derivative scale](goal). -/
def derivativeScale (d : ℕ) (eps : ℝ) : ℝ :=
  (Real.exp eps - 1)/(2*d) -- @realizes \beta((exp ε−1)/(2d))
/-- Fix [the dimension](hyp:d) and [the probability law nu](hyp:nu). [Product prior, independent of the public seed](goal). -/
def productPrior (d : ℕ) (nu : Measure ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => nu) -- @realizes \Pi_0(ν0 tensor d) @realizes \Pi_1(ν1 tensor d)
/-- Fix [the local protocol Q](hyp:Q), [the function theta](hyp:theta), and [the public seed](hyp:r). [Fixed-seed transcript law after integrating iid observed records](goal). -/
def conditionalTranscriptLaw (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (r : Q.Seed) : Measure (ProtocolTranscript Q) :=
  (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).bind
    (fun o => fixedTranscriptLaw Q o r)
/-- Fix [the local protocol Q](hyp:Q) and [the public seed](hyp:r). [Reference transcript law under the zero vector](goal). -/
def referenceLaw (Q : LocalProtocol n (ObsRecord d)) (r : Q.Seed) :
    Measure (ProtocolTranscript Q) :=
  conditionalTranscriptLaw Q (fun _ => 0) r -- @realizes \Lambda_r^Q(zero-parameter reference)
/-- Fix [the sampling scheme S](hyp:S), [the local protocol Q](hyp:Q), and [the probability law nu](hyp:nu). [Mixture seed/transcript law induced by a product prior](goal). -/
def mixtureLaw (S : SamplingScheme n d) (Q : LocalProtocol n (ObsRecord d))
    (nu : Measure ℝ) : Measure (Q.Seed × ProtocolTranscript Q) :=
  (productPrior d nu).bind (fun theta => seedTranscriptLaw S Q (symmetricLaw theta))
  -- @realizes \mathsf M_0^Q(ν0 mixture) @realizes \mathsf M_1^Q(ν1 mixture)
/-- Fix [the amplitude](hyp:a) and [the probability law nu](hyp:nu). [Support and probability requirements of an amplitude prior](goal). -/
def AmplitudePrior (a : ℝ) (nu : Measure ℝ) : Prop :=
  IsProbabilityMeasure nu ∧ nu (Set.Icc (-a) a)ᶜ = 0
  -- @realizes \nu_0(probability supported on amplitude interval) @realizes \nu_1(same)
/-- Fix [the order](hyp:k) and [the probability law nu0 and the probability law nu1](hyp:nu0,nu1). [Moment equality below the cancellation degree](goal). -/
def MatchingMoments (k : ℕ) (nu0 nu1 : Measure ℝ) : Prop :=
  ∀ q : ℕ, q < k → (∫ u, u^q ∂nu0) = ∫ u, u^q ∂nu1
  -- @realizes q(lower-degree index) @realizes u(real integration variable)
/-- Fix [the function p](hyp:p), [the function theta](hyp:theta), [the public seed](hyp:r), [the protocol transcript](hyp:z), [the coordinate index](hyp:j), and [the order](hyp:k). [Coordinate derivative of a proposed density version](goal). -/
def densityDerivative (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (theta : Fin d → ℝ) (r : Q.Seed) (z : ProtocolTranscript Q) (j : Fin d) (k : ℕ) : ℝ :=
  iteratedDeriv k (fun x => p (Function.update theta j x,r,z)) (theta j)
/-- Fix [the local protocol Q](hyp:Q), [the privacy budget](hyp:eps), and [the function p](hyp:p). [Full density version, polynomiality and derivative assertions](goal). -/
def DensityCertificate (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ) : Prop :=
  Measurable p ∧
  (∀ theta ∈ parameterCube d, ∀ r,
    (∀ z, 0 ≤ p (theta,r,z)) ∧
    (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta,r,z))) =
      conditionalTranscriptLaw Q theta r) ∧
  (∀ theta r z j, ∃ coeff : Fin (n+1) → ℝ,
    ∀ x : ℝ, p (Function.update theta j x,r,z) = ∑ k, coeff k * x^k.val) ∧
  (∀ theta ∈ parameterCube d, ∀ r j k, 1 ≤ k → k ≤ n →
    (∫ z, |densityDerivative p theta r z j k| ∂(referenceLaw Q r)) ≤
      (k.factorial : ℝ) * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k) ∧
  (∀ theta r z j k, n < k → densityDerivative p theta r z j k = 0)
  -- @realizes p^Q(joint measurable polynomial density and L1 derivatives)
/-- Fix [the function theta](hyp:theta). [Clipping extends cube-indexed probability experiments to the whole parameter space](goal). -/
-- @node: densityCubeClamp
def densityCubeClamp (theta : Fin d → ℝ) : Fin d → ℝ :=
  fun j => max (-(1/2 : ℝ)) (min (1/2 : ℝ) (theta j))

/-- [Coordinatewise parameter clipping is measurable](goal). -/
-- @node: measurable_densityCubeClamp
@[fun_prop] lemma measurable_densityCubeClamp :
    Measurable (densityCubeClamp : (Fin d → ℝ) → Fin d → ℝ) := by
  unfold densityCubeClamp
  fun_prop

/-- [Clipped parameters belong to the declared cube. [](](goal). -/
-- @node: densityCubeClamp_mem
lemma densityCubeClamp_mem (theta : Fin d → ℝ) : densityCubeClamp theta ∈ parameterCube d := by
  intro j
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Assume [the stated htheta condition](hyp:htheta). [Clipping fixes all parameters of the declared experiment. [](](goal). -/
-- @node: densityCubeClamp_eq
lemma densityCubeClamp_eq (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
    densityCubeClamp theta = theta := by
  funext j
  exact max_eq_right ((htheta j).1.trans_eq (min_eq_right (htheta j).2).symm) |>.trans
    (min_eq_right (htheta j).2)

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Integrating fixed-input probability transcript laws preserves total mass](goal). -/
-- @node: conditionalTranscriptLaw_probability
lemma conditionalTranscriptLaw_probability (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d) (r : Q.Seed) :
    IsProbabilityMeasure (conditionalTranscriptLaw Q theta r) := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  rw [conditionalTranscriptLaw, Measure.bind_apply MeasurableSet.univ
    (show Measurable (fun o => fixedTranscriptLaw Q o r) by fun_prop).aemeasurable]
  have hmass (o : Fin n → ObsRecord d) : fixedTranscriptLaw Q o r Set.univ = 1 := by
    have hprob := Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_transcriptLaw
      Q.kernels Q.markov (fun i => (o i,r))
    exact hprob.measure_univ
  simp only [hmass, lintegral_one, measure_univ]

/-- [Finite input summation makes the clipped transcript experiment jointly measurable](goal) when [the record dimension is positive](hyp:hd). -/
-- @node: measurable_conditionalTranscriptLaw_clipped
@[fun_prop] lemma measurable_conditionalTranscriptLaw_clipped
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) :
    Measurable (fun w : (Fin d → ℝ) × Q.Seed =>
      conditionalTranscriptLaw Q (densityCubeClamp w.1) w.2) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hobs : Measurable (fun w : (Fin d → ℝ) × Q.Seed =>
      observedLaw (symmetricLaw (densityCubeClamp w.1))) := by
    exact (Measure.measurable_map observe (by fun_prop)).comp
      (measurable_symmetricLaw_parameter.comp (measurable_densityCubeClamp.comp measurable_fst))
  have hexpand (w : (Fin d → ℝ) × Q.Seed) :
      conditionalTranscriptLaw Q (densityCubeClamp w.1) w.2 E =
      ∑ o : Fin n → ObsRecord d, fixedTranscriptLaw Q o w.2 E *
        ∏ i, observedLaw (symmetricLaw (densityCubeClamp w.1)) {o i} := by
    haveI := symmetricLaw_probability _ (densityCubeClamp_mem w.1) hd
    haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (densityCubeClamp w.1))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    rw [conditionalTranscriptLaw, Measure.bind_apply hE
      (show Measurable (fun o => fixedTranscriptLaw Q o w.2) by fun_prop).aemeasurable,
      lintegral_fintype]
    simp only [Measure.pi_singleton]
  simp_rw [hexpand]
  apply Finset.measurable_sum
  intro o _
  apply Measurable.mul
  · exact (Measure.measurable_coe hE).comp
      ((measurable_fixedTranscriptLaw Q).comp
        (show Measurable (fun w : (Fin d → ℝ) × Q.Seed => (o,w.2)) by fun_prop))
  · apply Finset.measurable_prod
    intro i _
    exact (Measure.measurable_coe (measurableSet_singleton _)).comp hobs

/-- Assume [positive dimension](hyp:hd). [Full support of the zero-contrast iid input law dominates every transcript experiment. [](](goal). -/
-- @node: conditionalTranscriptLaw_absolutelyContinuous
lemma conditionalTranscriptLaw_absolutelyContinuous (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (r : Q.Seed) (hd : 0 < d) :
    conditionalTranscriptLaw Q theta r ≪ referenceLaw Q r := by
  have hcube : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  haveI := symmetricLaw_probability (fun _ : Fin d => 0) hcube hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (fun _ : Fin d => 0))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply finite_bind_absolutelyContinuous _ _ _ (by fun_prop)
  intro o
  rw [Measure.pi_singleton]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => observed_symmetric_zero_atom hd (o i))

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN_of_gate), [sequential local privacy of the protocol](hyp:hQ), [sample size at least two](hyp:hn), [dimension at least two](hyp:hd), and [a privacy budget in the interval from zero to one](hyp:heps). [Density polynomial existence with its version identities, conditional on the RN gate](goal). -/
-- @node: density_polynomial_of_gate
lemma density_polynomial_of_gate (hRN_of_gate : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hn : 2 ≤ n) (hd : 2 ≤ d) (heps : eps ∈ Set.Ioc 0 1) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      Measurable p ∧ ∀ theta ∈ parameterCube d, ∀ r,
        (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta,r,z))) =
          conditionalTranscriptLaw Q theta r := by
  let K : Kernel ((Fin d → ℝ) × Q.Seed) (ProtocolTranscript Q) :=
    ⟨fun w => conditionalTranscriptLaw Q (densityCubeClamp w.1) w.2,
      measurable_conditionalTranscriptLaw_clipped Q (by omega)⟩
  let L : Kernel ((Fin d → ℝ) × Q.Seed) (ProtocolTranscript Q) :=
    ⟨fun w => referenceLaw Q w.2, by
      have hzero : densityCubeClamp (fun _ : Fin d => (0 : ℝ)) = fun _ => 0 :=
        densityCubeClamp_eq _ (by intro j; constructor <;> norm_num)
      have hm := (measurable_conditionalTranscriptLaw_clipped Q (by omega)).comp
        (show Measurable (fun w : (Fin d → ℝ) × Q.Seed =>
          ((fun _ : Fin d => (0 : ℝ)), w.2)) by fun_prop)
      simpa only [Function.comp_def, hzero, referenceLaw] using hm⟩
  haveI : IsMarkovKernel K := ⟨fun w =>
    conditionalTranscriptLaw_probability Q _ (densityCubeClamp_mem w.1) (by omega) w.2⟩
  haveI : IsMarkovKernel L := ⟨fun w =>
    conditionalTranscriptLaw_probability Q _ (by intro j; constructor <;> norm_num)
      (by omega) w.2⟩
  haveI : StandardBorelSpace (ProtocolTranscript Q) := by
    unfold ProtocolTranscript Causalean.Mathlib.Probability.Kernel.FiniteSequence.Transcript
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.History
    infer_instance
  obtain ⟨f, hf, hrep⟩ := real_kernel_density_of_gate hRN_of_gate K L
    (fun w => conditionalTranscriptLaw_absolutelyContinuous Q _ w.2 (by omega))
  refine ⟨fun w => f ((w.1,w.2.1),w.2.2), hf.comp (by fun_prop), ?_⟩
  intro theta htheta r
  have h := hrep (theta,r)
  change (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (f ((theta,r),z))) =
    conditionalTranscriptLaw Q (densityCubeClamp theta) r at h
  rwa [densityCubeClamp_eq theta htheta] at h


end CausalSmith.Stat.LdpOptvalueUniformFrontier
