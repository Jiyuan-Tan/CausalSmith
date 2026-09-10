import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessFactorization
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessSpectral
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessValidity
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.QuotientLaw

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

/-- The explicit two-class law remains in the uniformly conditioned model through the collision,
with unequal latent weights and nonsingular proxy matrices. -/
-- @node: prop:two-class-witness-valid
theorem two_class_witness_valid (eps : ℝ) (hEps : WitnessPerturbationDomain eps) :
    let hlo := hEps.1
    let hhi := hEps.2
    let _hP := witnessLaw_isProbabilityMeasure eps hlo hhi
    letI := _hP
    ∃ hM : UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (witnessLaw eps),
    (obsLaw (witnessLaw eps)).real {o | o.T = false} = 12 / 25 ∧
    (obsLaw (witnessLaw eps)).real {o | o.T = true} = 13 / 25 ∧
    det2 (targetFeature (witnessLaw eps)) = 3 / 5 ∧
    det2 (referenceFeature (witnessLaw eps) false) = 2 / 5 ∧
    det2 (referenceFeature (witnessLaw eps) true) = 2 / 5 ∧
    det2 (observedProxyMoment (obsSummary (witnessLaw eps)) false) = 3 / 50 ∧
    det2 (observedProxyMoment (obsSummary (witnessLaw eps)) true) =
      (2 / 5 : ℝ) * (3 / 5) * (36 / 169) ∧
    latentMass (witnessLaw eps) 0 = 2 / 5 ∧
    latentMass (witnessLaw eps) 1 = 3 / 5 ∧
    AtomicLaw.LawModulo.toMeasure (quotientLaw (witnessLaw eps) hM) =
      ENNReal.ofReal (2 / 5 : ℝ) • Measure.dirac (1 / 4 - eps) +
        ENNReal.ofReal (3 / 5 : ℝ) • Measure.dirac (1 / 4 + eps) ∧
    (eps = 0 →
      Function.Injective (Matrix.toEuclideanLin (targetFeature (witnessLaw eps))) ∧
      Function.Injective (Matrix.toEuclideanLin (referenceFeature (witnessLaw eps) false)) ∧
      Function.Injective (Matrix.toEuclideanLin (referenceFeature (witnessLaw eps) true)) ∧
      AtomicLaw.LawModulo.toMeasure (quotientLaw (witnessLaw eps) hM) = Measure.dirac (1 / 4) ∧
      latentMass (witnessLaw eps) 0 ≠ latentMass (witnessLaw eps) 1) := by
  obtain ⟨hlo, hhi⟩ := hEps
  letI := witnessLaw_isProbabilityMeasure eps hlo hhi
  let hM : UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10)
      (witnessLaw eps) :=
    { referenceProxySeparation := witness_referenceProxySeparation eps hlo hhi
      coreDomain := by norm_num [CoreParameterDomain]
      targetProxySeparation := witness_targetProxySeparation eps hlo hhi
      consistency := witness_consistency eps
      latentIgnorability := witness_armwiseLatentIgnorability eps hlo hhi
      anchor := witness_anchor eps
      boundedX := witness_boundedX eps
      boundedProxyProduct := witness_boundedProxyProduct eps
      boundedOutcomeProxyProduct := witness_boundedOutcomeProxyProduct eps
      latentArmPositivity := witness_latentArmPositivity eps hlo hhi
      proxyRankMargin := witness_proxyRankMargin eps hlo hhi }
  have hq : AtomicLaw.LawModulo.toMeasure (quotientLaw (witnessLaw eps) hM) =
      ENNReal.ofReal (2 / 5 : ℝ) • Measure.dirac (1 / 4 - eps) +
        ENNReal.ofReal (3 / 5 : ℝ) • Measure.dirac (1 / 4 + eps) := by
    rw [quotientLaw, AtomicLaw.LawModulo.toMeasure_eq_of_mk]
    unfold AtomicLaw.ProbabilityLaw.toMeasure AtomicLaw.toMeasure quotientLawRaw
    rw [Fin.sum_univ_two]
    change ENNReal.ofReal (latentMass (witnessLaw eps) 0) •
        Measure.dirac (latentEffect (witnessLaw eps) 0) +
      ENNReal.ofReal (latentMass (witnessLaw eps) 1) •
        Measure.dirac (latentEffect (witnessLaw eps) 1) = _
    rw [witness_latentMass eps hlo hhi, witness_latentMass eps hlo hhi,
      witness_latentEffect eps hlo hhi, witness_latentEffect eps hlo hhi]
    norm_num
  refine ⟨hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hq, ?_⟩
  · simpa [obsArm] using obs_witness_arm_mass eps hlo hhi false
  · simpa [obsArm] using obs_witness_arm_mass eps hlo hhi true
  · exact witness_det_targetFeature eps hlo hhi
  · exact witness_det_referenceFeature eps hlo hhi false
  · exact witness_det_referenceFeature eps hlo hhi true
  · exact witness_observedProxyMoment_det eps hlo hhi false
  · exact witness_observedProxyMoment_det eps hlo hhi true
  · simpa using witness_latentMass eps hlo hhi (0 : Fin 2)
  · simpa using witness_latentMass eps hlo hhi (1 : Fin 2)
  · intro heps
    subst eps
    constructor
    · rw [witness_targetFeature 0 (by norm_num) (by norm_num)]
      apply two_by_two_injective_of_signalMinSingular_pos
      exact lt_of_lt_of_le (by norm_num) witnessTargetMatrix_signalMinSingular
    constructor
    · rw [witness_referenceFeature 0 (by norm_num) (by norm_num) false]
      apply two_by_two_injective_of_signalMinSingular_pos
      exact lt_of_lt_of_le (by norm_num) witnessReferenceMatrix_false_signalMinSingular
    constructor
    · rw [witness_referenceFeature 0 (by norm_num) (by norm_num) true]
      apply two_by_two_injective_of_signalMinSingular_pos
      exact lt_of_lt_of_le (by norm_num) witnessReferenceMatrix_true_signalMinSingular
    constructor
    · rw [hq]
      norm_num
      rw [← add_smul]
      congr 1
      rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (2 / 5 : ℝ))] <;> norm_num
    · rw [witness_latentMass 0 (by norm_num) (by norm_num),
        witness_latentMass 0 (by norm_num) (by norm_num)]
      norm_num

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
