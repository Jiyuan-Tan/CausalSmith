module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerRegimes
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.TWeightedPacketConstruction

/-! TObservedLower -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
universe u


/-- [Assuming the four cited Jacobi-packet facts](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate), [for any public class constants](hyp:K) [whose lower and upper envelope constants bracket the power-density coefficient (κ+1)2^κ, so that the class is nonempty](hyp:hK), [smoothness exponent positive and at most one](hyp:hbeta), [design exponent between zero and two](hyp:hkappa) and [any prescribed positive total-variation level τ](hyp:htau), [explicit Bernoulli threshold witnesses in the model have a common design, legal ranks, target separation of the order of the frontier rate, and observed-product total variation at most τ](goal); the separation constant depends on τ. -/
-- @node: thm:observed-lower
theorem observed_lower (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) (K : ClassConstants) (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hK : K.clo ≤ (kappa+1)*(2 : ℝ)^kappa ∧ (kappa+1)*(2 : ℝ)^kappa ≤ K.chi)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ c C epsilon Cpacket cPacket : ℝ,
      0 < c ∧ 0 < C ∧ 0 < epsilon ∧ 0 < Cpacket ∧ 0 < cPacket ∧
      (∀ m : ℕ, 4 ≤ m → PacketBounds kappa Cpacket cPacket m) ∧
      ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
    ∀ sigma ∈ Icc (0 : ℝ) (1/4), ∃ Pplus Pminus Pstar : ProbabilityMeasure (StructSpace S), -- @realizes Palt(three probability-law witnesses)
      NoisyDoseModelClass E K beta kappa sigma (Pplus : Measure (StructSpace S)) ∧
      NoisyDoseModelClass E K beta kappa sigma (Pminus : Measure (StructSpace S)) ∧
      NoisyDoseModelClass E K beta kappa sigma (Pstar : Measure (StructSpace S)) ∧
      BinaryPotentialOutcomes E (Pplus : Measure (StructSpace S)) ∧
      BinaryPotentialOutcomes E (Pminus : Measure (StructSpace S)) ∧
      BinaryPotentialOutcomes E (Pstar : Measure (StructSpace S)) ∧
      (∀ P ∈ ({Pplus, Pminus, Pstar} : Set (ProbabilityMeasure (StructSpace S))),
        RankUniform (P : Measure (StructSpace S)) ∧
        RankTreatmentIndependence (P : Measure (StructSpace S)) ∧
        StructuralThreshold E (P : Measure (StructSpace S)) ∧
        IIDSampling n sigma (P : Measure (StructSpace S)) (experiment n sigma (P : Measure (StructSpace S)))) ∧
      (Pplus : Measure (StructSpace S)).map (fun w => (sX w, sA w)) =
        (Pminus : Measure (StructSpace S)).map (fun w => (sX w, sA w)) ∧
      (Pplus : Measure (StructSpace S)).map (fun w => (sX w, sA w)) =
        (Pstar : Measure (StructSpace S)).map (fun w => (sX w, sA w)) ∧
      c*frontierRate beta kappa sigma n ≤
        |causalTarget E (Pplus : Measure (StructSpace S))-causalTarget E (Pminus : Measure (StructSpace S))| ∧
      Causalean.Stat.tvDist (experiment n sigma (Pplus : Measure (StructSpace S)))
        (experiment n sigma (Pminus : Measure (StructSpace S))) ≤ tau ∧
      LowerWitnessConstruction E beta kappa n sigma epsilon cPacket C
        (Pplus : Measure (StructSpace S)) (Pminus : Measure (StructSpace S))
        (Pstar : Measure (StructSpace S)) := by
  obtain ⟨c, C, epsilon, Cpacket, cPacket, hc, hC, hepsilon, hCpacket, hcPacket,
    hpacket, n0, hregimes⟩ := lower_regime_witnesses hLocalization_of_gate
      hLipschitz_of_gate hNorm_of_gate hGamma_of_gate beta kappa hbeta hkappa tau htau
  refine ⟨c, C, epsilon, Cpacket, cPacket, hc, hC, hepsilon, hCpacket,
    hcPacket, hpacket, n0, ?_⟩
  intro S _ E n hn sigma hsigma
  obtain ⟨muPlus, muMinus, hrange, hholder, hsep, htv, h, ell, m, J,
    hprofiles, hseries⟩ := hregimes S E n hn sigma hsigma
  have hplus := lowerWitness_membership E K beta kappa sigma hbeta hkappa hsigma hK
    muPlus (fun a b => (hholder a b).1)
  have hminus := lowerWitness_membership E K beta kappa sigma hbeta hkappa hsigma hK
    muMinus (fun a b => (hholder a b).2)
  have hreferenceHolder : ∀ a b : Dose,
      |(referenceProfile a : ℝ)-(referenceProfile b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta := by
    intro a b
    simp only [referenceProfile, ContinuousMap.const_apply, sub_self, abs_zero]
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hstar := lowerWitness_membership E K beta kappa sigma hbeta hkappa hsigma hK
    referenceProfile hreferenceHolder
  refine ⟨lowerWitness E kappa hkappa muPlus, lowerWitness E kappa hkappa muMinus,
    lowerWitness E kappa hkappa referenceProfile, hplus.1, hminus.1, hstar.1,
    hplus.2.1, hminus.2.1, hstar.2.1, ?_,
    lowerWitness_common_design E kappa hkappa muPlus muMinus,
    lowerWitness_common_design E kappa hkappa muPlus referenceProfile, hsep, htv, ?_⟩
  · intro P hP
    have hlegal : ∀ mu : ThresholdProfile,
        RankUniform (lowerWitnessLaw E kappa mu) ∧
        RankTreatmentIndependence (lowerWitnessLaw E kappa mu) ∧
        StructuralThreshold E (lowerWitnessLaw E kappa mu) →
        RankUniform (lowerWitnessLaw E kappa mu) ∧
        RankTreatmentIndependence (lowerWitnessLaw E kappa mu) ∧
        StructuralThreshold E (lowerWitnessLaw E kappa mu) ∧
        IIDSampling n sigma (lowerWitnessLaw E kappa mu)
          (experiment n sigma (lowerWitnessLaw E kappa mu)) := by
      intro mu hmu
      exact ⟨hmu.1, hmu.2.1, hmu.2.2, iidSampling_holds n sigma _⟩
    rcases hP with rfl | rfl | hP
    · exact hlegal muPlus ⟨hplus.2.2.1, hplus.2.2.2.1, hplus.2.2.2.2.1⟩
    · exact hlegal muMinus ⟨hminus.2.2.1, hminus.2.2.2.1, hminus.2.2.2.2.1⟩
    · have hP' : P = lowerWitness E kappa hkappa referenceProfile := hP
      subst P
      exact hlegal referenceProfile ⟨hstar.2.2.1, hstar.2.2.2.1, hstar.2.2.2.2.1⟩
  · exact ⟨muPlus, muMinus, h, ell, m, J, hprofiles, rfl, rfl, rfl, hseries⟩

end CausalSmith.Stat.NoisydoseWeakdesignTransition
