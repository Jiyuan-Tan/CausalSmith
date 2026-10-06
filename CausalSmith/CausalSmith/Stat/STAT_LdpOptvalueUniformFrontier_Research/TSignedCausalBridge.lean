module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Bridge.AncillaryTranscript

/-!
# Signed causal experiment bridge

Causal identification, symmetric realization, and two-way private experiment equivalence.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology Classical
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

-- @node: prop:signed-causal-bridge
/-- For a scheme with [iid participants and independent randomization](hyp:hIID,hRandom) and
[at least two cells](hyp:hd), the signed construction proves [causal identification, symmetric-law
realization, and two-way private experiment equivalence](goal). -/
theorem signed_causal_bridge (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (hd : 2 ≤ d) :
    (∀ P : Measure (FullRecord d), IsProbabilityMeasure P → CausalModel P →
      (∀ j, signedCellMean P j = contrast P j) ∧
      (observedLaw P).map signedObserve = pairedLaw (contrast P) ∧
      value P = baseline P + signedNorm (contrast P)/2 ∧
      value P = baseline P + Causalean.Stat.tvDist (pairedLaw (contrast P)) (pairedUniform d)) ∧
    (∀ theta ∈ parameterCube d,
      IsProbabilityMeasure (symmetricLaw theta) ∧ CausalModel (symmetricLaw theta) ∧
      value (symmetricLaw theta) = 1/2 + signedNorm theta/2 ∧
      (∀ (j : Fin d) (s a : Bool),
        (symmetricLaw theta).real {w | cell w = j ∧ signedObserve (observe w) = (j,s) ∧ arm w = a} =
          (pairedLaw theta).real {(j,s)}/2) ∧
      (∀ᵐ w ∂symmetricLaw theta, signVal (outcome w) = obsSign (observe w) * signVal (arm w))) ∧
    (∀ eps : ℝ,
      (∀ Q : LocalProtocol n (ObsRecord d),
        (SequentialClass Q eps → SequentialClass (averagedProtocol Q) eps) ∧
        (NoninteractiveClass Q eps → NoninteractiveClass (averagedProtocol Q) eps) ∧
        ∀ theta ∈ parameterCube d,
          seedTranscriptLaw S Q (symmetricLaw theta) =
            canonicalSeedTranscriptLaw (averagedProtocol Q) (pairedLaw theta)) ∧
      (∀ K : LocalProtocol n (PairedSymbol d),
        (SequentialClass K eps → SequentialClass (pulledProtocol K) eps) ∧
        (NoninteractiveClass K eps → NoninteractiveClass (pulledProtocol K) eps) ∧
        ∀ theta ∈ parameterCube d,
          seedTranscriptLaw S (pulledProtocol K) (symmetricLaw theta) =
            canonicalSeedTranscriptLaw K (pairedLaw theta))) := by
  constructor
  · intro P hprob hP
    letI := hprob
    refine ⟨signedCellMean_eq_contrast P hP, ?_, causal_value_decomposition P hP hd, ?_⟩
    · exact causal_signed_law P hP (by omega)
    · haveI : IsProbabilityMeasure (pairedLaw (contrast P)) :=
        pairedFamily_subset_simplex (by omega)
          (Set.mem_image_of_mem pairedLaw (contrast_mem_parameterCube P hP))
      rw [← tvFromUniform_eq_tvDist _ (by omega)]
      rw [tvFromUniform_pairedLaw _ (contrast_mem_parameterCube P hP) (by omega)]
      exact causal_value_decomposition P hP hd
  constructor
  · intro theta htheta
    refine ⟨?_, ?_, ?_, ?_, Filter.Eventually.of_forall outcome_sign_reconstruction⟩
    · exact symmetricLaw_probability theta htheta (by omega)
    · exact symmetricLaw_causalModel theta htheta (by omega)
    · exact symmetricLaw_value theta htheta (by omega)
    · exact symmetricLaw_ancillary theta htheta
  · intro eps
    constructor
    · intro Q
      obtain ⟨hSI, hNI⟩ := (signed_protocol_classes (n := n) (d := d) eps).1 Q
      refine ⟨hSI, hNI, ?_⟩
      intro theta htheta
      rw [seedTranscriptLaw, symmetricLaw_reconstructed_decisionLaw
        S hIID hRandom (by omega) Q theta htheta]
      haveI : IsProbabilityMeasure (pairedLaw theta) :=
        pairedFamily_subset_simplex (by omega) (Set.mem_image_of_mem pairedLaw htheta)
      rw [averagedProtocol_reconstructed_decisionLaw]
      rfl
    · intro K
      obtain ⟨hSI, hNI⟩ := (signed_protocol_classes (n := n) (d := d) eps).2 K
      refine ⟨hSI, hNI, ?_⟩
      intro theta htheta
      exact congrArg (fun μ => μ.map (fun w => (w.2.1,w.1)))
        (pulledProtocol_decisionLaw S hIID hRandom hd K theta htheta)


end CausalSmith.Stat.LdpOptvalueUniformFrontier
