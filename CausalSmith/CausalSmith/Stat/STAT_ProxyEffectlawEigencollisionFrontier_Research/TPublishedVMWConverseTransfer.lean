import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Risk
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TMatchingLocalLowerBounds
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TTwoClassWitnessValid
import Causalean.Stat.Minimax.Pinsker
import Causalean.Mathlib.InformationTheory.ProductKLLeCam

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

noncomputable def FullDataProbabilityLaw.lawRisk {n : ℕ}
    (Q : FullDataProbabilityLaw (FullData 2 2 2))
    (hvalid : AtomicLaw.Valid (quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10))))
    (est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10))) : ℝ := by
  letI := Q.prob
  let target := AtomicLaw.LawModulo.ofProbabilityLaw
    ⟨quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10)), hvalid⟩
  exact ∫ sample, AtomicLaw.LawModulo.wass1 (est.eval sample) target
    ∂sampleLaw (n := n) Q.measure

noncomputable def FullDataProbabilityLaw.weightRisk {n : ℕ}
    (Q : FullDataProbabilityLaw (FullData 2 2 2))
    (est : WeightEstimator 2 2 2 n) : ℝ := by
  letI := Q.prob
  exact expectedWeightRisk Q.measure
    (orderedMasses (quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10)))) est

/-- Distinct effects in a gap stratum imply the qualitative spectral-separation condition. -/
-- @node: publishedVMWConverseTransfer_gapStratum_separated
lemma gapStratum_publishedSpectralSeparation
    {g : ℝ} {P : Measure (FullData 2 2 2)} [IsProbabilityMeasure P]
    (hM : GapStratum (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (g := g) P) :
    PublishedSpectralSeparation (latentEffect P) := by
  have hmass (u : Fin 2) : 0 < latentMass P u := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 10)
      ((hM.toUCVMWModel.latentArmPositivity u false).trans
        (measureReal_mono (fun _ hw => hw.1)))
  have hfilter : (Finset.univ.filter fun u : Fin 2 => 0 < latentMass P u) =
      Finset.univ := Finset.filter_eq_self.mpr fun u _ => hmass u
  have hcard : ((Finset.univ : Finset (Fin 2)).image (latentEffect P)).card =
      (Finset.univ : Finset (Fin 2)).card := by
    rw [Finset.card_univ]
    simpa [DistinctEffects, hfilter] using hM.distinctEffects
  have hinj := Finset.card_image_iff.mp hcard
  intro u v huv
  exact fun huvEq => huv (hinj (by simp) (by simp) huvEq)

/-- Relative to one fixed nominal published-scope handle, any comparator classes containing the
explicit quotient and separated labeled witness pairs inherit the two Le Cam converses. No upper
or confidence result is transferred. -/
-- @node: thm:published-vmw-converse-transfer
theorem published_vmw_converse_transfer
    (publishedScope : PublishedVMWScopeHandle)
    (publishedMargins : PublishedVMWMarginRecord)
    (hVMWModelScope_of_gate : VMWModelScope publishedScope publishedMargins)
    (hVMWSeparatedRecoveryScope_of_gate : VMWSeparatedRecoveryScope publishedScope) :
    ∃ a c : ℝ,
      0 < a ∧ a ≤ 1 / 8 ∧ -- @realizes \(a\)(universal amplitude in (0,1/8])
      0 < c ∧ -- @realizes \(c\)(positive published-converse lower constant)
      ∀ n : ℕ, 1 ≤ n →
      (∃ (hW0 : IsProbabilityMeasure (witnessLaw 0))
          (hW1 : IsProbabilityMeasure (witnessLaw (a / Real.sqrt n))),
        letI := hW0
        letI := hW1
        PublishedVMWModel publishedScope (witnessLaw 0) ∧
          PublishedVMWModel publishedScope (witnessLaw (a / Real.sqrt n)) ∧
          ¬ PublishedVMWRecoveryRegime publishedScope (witnessLaw 0)) ∧
      (∀ (Vnu : Set (FullDataProbabilityLaw (FullData 2 2 2))),
        (∀ Q ∈ Vnu, letI := Q.prob; PublishedVMWModel publishedScope Q.measure) →
        (∃ Q0 ∈ Vnu, ∃ Q1 ∈ Vnu, Q0.measure = witnessLaw 0 ∧
          Q1.measure = witnessLaw (a / Real.sqrt n)) →
        (∀ est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10)),
          ∃ Q ∈ Vnu, ∃ hvalid : AtomicLaw.Valid
            (quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10))),
              c / Real.sqrt n ≤ Q.lawRisk hvalid est)) ∧
      ∀ g : ℝ, GapScaleDomain g →
        let h := calibratedDisplacement a n g
        TangentAmplitudeDomain h ∧
        (∃ (hPath0 : IsProbabilityMeasure (pathLaw g 0))
            (hPath1 : IsProbabilityMeasure (pathLaw g h)),
          letI := hPath0
          letI := hPath1
          PublishedVMWModel publishedScope (pathLaw g 0) ∧
          PublishedVMWModel publishedScope (pathLaw g h) ∧
            PublishedSpectralSeparation (latentEffect (pathLaw g 0)) ∧
            PublishedSpectralSeparation (latentEffect (pathLaw g h))) ∧
          ∀ (Vp : Set (FullDataProbabilityLaw (FullData 2 2 2))),
          (∀ Q ∈ Vp, letI := Q.prob; PublishedVMWModel publishedScope Q.measure) →
          (∃ Q0 ∈ Vp, ∃ Q1 ∈ Vp, Q0.measure = pathLaw g 0 ∧
            Q1.measure = pathLaw g h) →
          ∀ est : WeightEstimator 2 2 2 n,
            ∃ Q ∈ Vp, c * min 1 (Real.sqrt n * g)⁻¹ ≤ Q.weightRisk est := by
  obtain ⟨cLoc, a, cLower, CKL, hcLoc, ha, haMax, hcLower, hCKL, hlower⟩ :=
    matching_local_lower_bounds
  refine ⟨a, cLower, ha, haMax, hcLower, ?_⟩
  intro n hn
  have hpair := (hlower n hn).2.2.1
  obtain ⟨hW0, hW1, hM0, hM1, hpairKL, hpairSep⟩ := hpair
  have hpub0 : PublishedVMWModel publishedScope (witnessLaw 0) :=
    (hVMWModelScope_of_gate.2 2 2 2 (witnessLaw 0) hW0).2
      (ucvmwModel_publishedQualitativeConditions 2 2 2 2 (1 / 10) (1 / 10)
        (witnessLaw 0) hM0.toUCVMWModel.coreDomain hM0.toUCVMWModel)
  have hpub1 : PublishedVMWModel publishedScope (witnessLaw (a / Real.sqrt n)) :=
    (hVMWModelScope_of_gate.2 2 2 2 (witnessLaw (a / Real.sqrt n)) hW1).2
      (ucvmwModel_publishedQualitativeConditions 2 2 2 2 (1 / 10) (1 / 10)
        (witnessLaw (a / Real.sqrt n)) hM1.toUCVMWModel.coreDomain hM1.toUCVMWModel)
  have hnotsep : ¬ PublishedSpectralSeparation (latentEffect (witnessLaw 0)) := by
    intro hsep
    have h01 := hsep (0 : Fin 2) (1 : Fin 2) (by decide)
    rw [witness_latentEffect 0 (by norm_num) (by norm_num),
      witness_latentEffect 0 (by norm_num) (by norm_num)] at h01
    norm_num at h01
  have hnotRecovery : ¬ PublishedVMWRecoveryRegime publishedScope (witnessLaw 0) := by
    intro hRecovery
    have hscope := hVMWSeparatedRecoveryScope_of_gate.2.1 2 2 2
      (witnessLaw 0) hW0 (by norm_num [VMWPositiveDimensionDomain]) |>.mp hRecovery
    exact hnotsep hscope.2.2.2.2.2.2.2.2
  refine ⟨⟨hW0, hW1, hpub0, hpub1, hnotRecovery⟩, ?_, ?_⟩
  · intro Vnu _hVPublished hcontain
    obtain ⟨Q0, hQ0, Q1, hQ1, hQ0eq, hQ1eq⟩ := hcontain
    intro est
    obtain ⟨P, hP, hLocal, hwhich, hRisk⟩ := (hlower n hn).1 est
    rcases hwhich with hP0 | hP1
    · have hvalidQ0 : AtomicLaw.Valid
          (quotientLawRaw Q0.measure (effectRadius 2 2 (1 / 10))) := by
        simpa [hQ0eq] using quotientLawRaw_valid (witnessLaw 0) hM0.toUCVMWModel
      refine ⟨Q0, hQ0, hvalidQ0, ?_⟩
      subst P
      simpa [FullDataProbabilityLaw.lawRisk, expectedLawRisk, quotientLaw, hQ0eq] using hRisk
    · have hvalidQ1 : AtomicLaw.Valid
          (quotientLawRaw Q1.measure (effectRadius 2 2 (1 / 10))) := by
        simpa [hQ1eq] using
          quotientLawRaw_valid (witnessLaw (a / Real.sqrt n)) hM1.toUCVMWModel
      refine ⟨Q1, hQ1, hvalidQ1, ?_⟩
      subst P
      simpa [FullDataProbabilityLaw.lawRisk, expectedLawRisk, quotientLaw, hQ1eq] using hRisk
  · intro g hGap
    obtain ⟨hg, hgMax⟩ := hGap
    have hlocalPair := (hlower n hn).2.2.2 g ⟨hg, hgMax⟩
    dsimp only at hlocalPair
    obtain ⟨hDomain, hPath, hBase, hLocalPath, hLocalBase, hPathKL, hWeight⟩ := hlocalPair
    let h := calibratedDisplacement a n g
    have hpubPath : PublishedVMWModel publishedScope (pathLaw g h) :=
      (hVMWModelScope_of_gate.2 2 2 2 (pathLaw g h) hPath).2
        (ucvmwModel_publishedQualitativeConditions 2 2 2 2 (1 / 10) (1 / 10)
          (pathLaw g h) hLocalPath.toGapStratum.toUCVMWModel.coreDomain
          hLocalPath.toGapStratum.toUCVMWModel)
    have hpubBase : PublishedVMWModel publishedScope (pathLaw g 0) :=
      (hVMWModelScope_of_gate.2 2 2 2 (pathLaw g 0) hBase).2
        (ucvmwModel_publishedQualitativeConditions 2 2 2 2 (1 / 10) (1 / 10)
          (pathLaw g 0) hLocalBase.toGapStratum.toUCVMWModel.coreDomain
          hLocalBase.toGapStratum.toUCVMWModel)
    have hsepPath := gapStratum_publishedSpectralSeparation hLocalPath.toGapStratum
    have hsepBase := gapStratum_publishedSpectralSeparation hLocalBase.toGapStratum
    refine ⟨hDomain, ⟨hBase, hPath, hpubBase, hpubPath, hsepBase, hsepPath⟩, ?_⟩
    intro Vp _hVPublished hcontain est
    obtain ⟨Q0, hQ0, Q1, hQ1, hQ0eq, hQ1eq⟩ := hcontain
    obtain ⟨P, hP, hLocal, hwhich, hRisk⟩ :=
      (hlower n hn).2.1 g ⟨hg, hgMax⟩ est
    rcases hwhich with hP0 | hP1
    · refine ⟨Q0, hQ0, ?_⟩
      subst P
      simpa [FullDataProbabilityLaw.weightRisk, expectedWeightRisk, hQ0eq] using hRisk
    · refine ⟨Q1, hQ1, ?_⟩
      subst P
      simpa [FullDataProbabilityLaw.weightRisk, expectedWeightRisk, hQ1eq] using hRisk

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
