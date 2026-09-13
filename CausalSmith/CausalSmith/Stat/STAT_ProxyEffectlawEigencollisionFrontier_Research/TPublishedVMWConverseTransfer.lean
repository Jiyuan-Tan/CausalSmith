import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Risk
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TMatchingLocalLowerBounds
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TTwoClassWitnessValid
import Causalean.Stat.Minimax.Pinsker
import Causalean.Mathlib.InformationTheory.ProductKLLeCam

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open scoped BigOperators

/-- For [the supplied parameters](hyp:Q,hvalid,est), [law Risk](goal) is given by [its defining clause](step:1). -/
noncomputable def FullDataProbabilityLaw.lawRisk {n : ℕ}
    (Q : FullDataProbabilityLaw (FullData 2 2 2))
    (hvalid : AtomicLaw.Valid (quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10))))
    (est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10))) : ℝ := by
  letI := Q.prob
  let target := AtomicLaw.LawModulo.ofProbabilityLaw
    ⟨quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10)), hvalid⟩
  exact ∫ sample, AtomicLaw.LawModulo.wass1 (est.eval sample) target
    ∂sampleLaw (n := n) Q.measure

/-- For [the supplied parameters](hyp:Q,est), [weight Risk](goal) is given by [its defining clause](step:1). -/
noncomputable def FullDataProbabilityLaw.weightRisk {n : ℕ}
    (Q : FullDataProbabilityLaw (FullData 2 2 2))
    (est : WeightEstimator 2 2 2 n) : ℝ := by
  letI := Q.prob
  exact expectedWeightRisk Q.measure
    (orderedMasses (quotientLawRaw Q.measure (effectRadius 2 2 (1 / 10)))) est

/-- Distinct effects in a gap stratum imply the qualitative spectral-separation condition.     Under [the stated inputs and assumptions](hyp:g,P,hM,hM), [the stated conclusion](goal) holds. -/
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

/-- Under [model membership](hyp:hM), [the leading right singular vectors of the stacked proxy
moment give a signal-spanning basis satisfying the published population equations](goal). -/
-- @node: publishedTopRightSignalBasis_exists
lemma publishedTopRightSignalBasis_exists
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ∃ basis : SignalBasis dx k,
      PublishedVMWTopRightSingularBasis (obsSummary P) basis ∧
      basis.SpansSignal (obsSummary P) := by
  classical
  rcases hM.coreDomain with ⟨hk, hkx, _hkz, hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  let Q : ModelLaw k dx dz L pi0 sigma0 := ⟨P, inferInstance, hM⟩
  let facts := Classical.choice (modelCompressedSpectralFacts_exists Q)
  let A := stackedProxyMoment (obsSummary P)
  let S := singularSystem A
  let r : Fin k → Fin dx := fun j => ⟨j, j.isLt.trans_le hkx⟩
  let V : SignalBasis dx k :=
    { V := fun i j => S.right (r j) i
      orthonormal := by
        intro i j
        by_cases hij : i = j
        · subst j
          simpa using S.right_orthonormal (r i) (r i)
        · have hrij : r i ≠ r j := by
            intro h
            apply hij
            exact Fin.ext (by simpa [r] using congrArg Fin.val h)
          simpa [hij, hrij] using S.right_orthonormal (r i) (r j) }
  have hspos (j : Fin k) : 0 < S.sigma (r j) := by
    rw [S.sigma_eq]
    have hlast := stackedProxyMoment_minSingular P hk hkx hL hpi hsigma hM
    have hant := (Matrix.toEuclideanLin A).singularValues_antitone
      (Nat.le_sub_one_of_lt j.isLt)
    exact (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le
      (hlast.trans (by simpa [A, singularValue] using hant))
  have htop : PublishedVMWTopRightSingularBasis (obsSummary P) V := by
    intro j
    change Matrix.mulVec (A.transpose * A) (fun i => S.right (r j) i) =
      singularValue A j.val ^ 2 • (fun i => S.right (r j) i)
    rw [← Matrix.mulVec_mulVec]
    have hr : A.mulVec (fun i => S.right (r j) i) =
        S.sigma (r j) • (fun i => S.left (r j) i) := by
      funext y
      change (∑ x, A y x * S.right (r j) x) = _
      exact S.apply_right (r j) y
    rw [hr, Matrix.mulVec_smul]
    have hl : A.transpose.mulVec (fun i => S.left (r j) i) =
        S.sigma (r j) • (fun i => S.right (r j) i) := by
      funext x
      change (∑ y, A y x * S.left (r j) y) = _
      exact S.apply_left_transpose (r j) x
    rw [hl]
    ext i
    simp [S.sigma_eq, r]
    ring
  have hAdjRange : LinearMap.range (Matrix.toEuclideanLin A).adjoint ≤
      signalRowspace (obsSummary P) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    let y0 : Euc dz := WithLp.toLp 2 (fun i : Fin dz => y.ofLp ⟨i, by omega⟩)
    let y1 : Euc dz := WithLp.toLp 2 (fun i : Fin dz => y.ofLp ⟨dz + i, by omega⟩)
    have heq : (Matrix.toEuclideanLin A).adjoint y =
        Matrix.toEuclideanLin (obsSummary P).M0.transpose y0 +
          Matrix.toEuclideanLin (obsSummary P).M1.transpose y1 := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      apply PiLp.ext
      intro i
      change (∑ q, A q i * y.ofLp q) =
        (∑ q, (obsSummary P).M0 q i * y0.ofLp q) +
          ∑ q, (obsSummary P).M1 q i * y1.ofLp q
      let e : Fin (dz + dz) ≃ Fin (2 * dz) := finCongr (by omega)
      rw [← e.sum_comp (fun q => A q i * y.ofLp q), Fin.sum_univ_add]
      simp [A, stackedProxyMoment, y0, y1, e]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      have hi : Fin.cast (by omega : dz + dz = 2 * dz) (Fin.addNat x dz) =
          (⟨dz + x.val, by omega⟩ : Fin (2 * dz)) := by
        apply Fin.ext
        simp [Nat.add_comm]
      rw [hi]
    rw [heq]
    exact Submodule.add_mem _
      ((le_sup_left : LinearMap.range (Matrix.toEuclideanLin (obsSummary P).M0.transpose) ≤
        signalRowspace (obsSummary P)) ⟨y0, rfl⟩)
      ((le_sup_right : LinearMap.range (Matrix.toEuclideanLin (obsSummary P).M1.transpose) ≤
        signalRowspace (obsSummary P)) ⟨y1, rfl⟩)
  have hcol (j : Fin k) : WithLp.toLp 2 (fun i => S.right (r j) i) ∈
      LinearMap.range (Matrix.toEuclideanLin A).adjoint := by
    have hadj : (Matrix.toEuclideanLin A).adjoint =
        Matrix.toEuclideanLin A.transpose := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      rfl
    let left : Euc (2 * dz) := WithLp.toLp 2 (fun i => S.left (r j) i)
    refine ⟨(S.sigma (r j))⁻¹ • left, ?_⟩
    rw [hadj, LinearMap.map_smul]
    have hl : Matrix.toEuclideanLin A.transpose left =
        S.sigma (r j) • WithLp.toLp 2 (fun i => S.right (r j) i) := by
      apply PiLp.ext
      intro i
      change (∑ y, A y i * S.left (r j) y) = _
      exact S.apply_left_transpose (r j) i
    rw [hl, smul_smul]
    simp [hspos j |>.ne']
  have hVle : LinearMap.range (Matrix.toEuclideanLin V.V) ≤
      signalRowspace (obsSummary P) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have heq : Matrix.toEuclideanLin V.V y =
        ∑ j : Fin k, y j • WithLp.toLp 2 (fun i => S.right (r j) i) := by
      apply PiLp.ext
      intro i
      change (Matrix.mulVec V.V y.ofLp) i = _
      simp [V, Matrix.mulVec, dotProduct, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (hAdjRange (hcol j))
  have hVrank : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin V.V)) = k := by
    change Module.finrank ℝ (LinearMap.range (signalBasisLinearIsometry V).toLinearMap) = k
    rw [(signalBasisLinearIsometry V).toLinearMap.finrank_range_of_inj
      (signalBasisLinearIsometry V).injective, finrank_euclideanSpace]
    simp
  have hSignalRank : Module.finrank ℝ (signalRowspace (obsSummary P)) = k := by
    change Module.finrank ℝ (signalRowspace Q.summary) = k
    rw [← facts.spans]
    change Module.finrank ℝ
      (LinearMap.range (signalBasisLinearIsometry facts.basis).toLinearMap) = k
    rw [(signalBasisLinearIsometry facts.basis).toLinearMap.finrank_range_of_inj
      (signalBasisLinearIsometry facts.basis).injective, finrank_euclideanSpace]
    simp
  refine ⟨V, htop, ?_⟩
  exact Submodule.eq_of_le_of_finrank_le hVle (by rw [hVrank, hSignalRank])

/-- Every law in this paper's uniformly conditioned class satisfies the finite envelopes,
marginal arm positivity, and population singular margins of the concrete published Assumption 4.
This is derived from model membership rather than assumed by the converse. -/
private lemma concreteVMWAssumption4_of_ucvmwModel
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ConcreteVMWAssumption4 P := by
  rcases hM.coreDomain with ⟨hk, hkx, hkz, hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  rcases publishedTopRightSignalBasis_exists P hM with ⟨basis, htop, hspans⟩
  refine ⟨⟨by omega, hkx, hkz⟩,
    L, L, L, k * pi0, pi0 * sigma0 ^ 2,
    by linarith, by linarith, by linarith, ?_, ?_,
    hM.boundedX, hM.boundedProxyProduct, hM.boundedOutcomeProxyProduct, ?_, ?_⟩
  · positivity
  · positivity
  · intro t
    exact arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t
  · refine ⟨basis, htop,
      stackedProxyMoment_minSingular P hk hkx hL hpi hsigma hM, ?_⟩
    intro t
    exact (observedProxyMoment_compression_margin
      P hk hkx hL hpi hsigma hM t basis hspans).2

/-- Relative to one fixed nominal published-scope handle, any comparator classes containing the
explicit quotient and separated labeled witness pairs inherit the two Le Cam converses. No upper
or confidence result is transferred.        Under [the stated inputs and assumptions](hyp:publishedScope,publishedMargins,hVMWModelScope_of_gate,hVMWSeparatedRecoveryScope_of_gate), [the stated conclusion](goal) holds. -/
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
          ConcreteVMWAssumption4 (witnessLaw 0) ∧
          PublishedVMWModel publishedScope (witnessLaw (a / Real.sqrt n)) ∧
          ConcreteVMWAssumption4 (witnessLaw (a / Real.sqrt n)) ∧
          ¬ PublishedVMWRecoveryRegime publishedScope (witnessLaw 0)) ∧
      (∀ (Vnu : Set (FullDataProbabilityLaw (FullData 2 2 2))),
        (∀ Q ∈ Vnu, letI := Q.prob;
          PublishedVMWModel publishedScope Q.measure ∧ ConcreteVMWAssumption4 Q.measure) →
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
          ConcreteVMWAssumption4 (pathLaw g 0) ∧
          PublishedVMWModel publishedScope (pathLaw g h) ∧
          ConcreteVMWAssumption4 (pathLaw g h) ∧
            PublishedSpectralSeparation (latentEffect (pathLaw g 0)) ∧
            PublishedSpectralSeparation (latentEffect (pathLaw g h))) ∧
          ∀ (Vp : Set (FullDataProbabilityLaw (FullData 2 2 2))),
          (∀ Q ∈ Vp, letI := Q.prob;
            PublishedVMWModel publishedScope Q.measure ∧ ConcreteVMWAssumption4 Q.measure) →
          (∃ Q0 ∈ Vp, ∃ Q1 ∈ Vp, Q0.measure = pathLaw g 0 ∧
            Q1.measure = pathLaw g h) →
          ∀ est : WeightEstimator 2 2 2 n,
            ∃ Q ∈ Vp, c * min 1 (Real.sqrt n * g)⁻¹ ≤ Q.weightRisk est := by
  obtain ⟨a, cLower, CKL, ha, haMax, hcLower, hCKL, hlower⟩ :=
    matching_local_lower_bounds (1 / 4) (by exact ⟨by norm_num, by norm_num⟩)
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
  have hA40 : ConcreteVMWAssumption4 (witnessLaw 0) := by
    exact concreteVMWAssumption4_of_ucvmwModel (witnessLaw 0) hM0.toUCVMWModel
  have hA41 : ConcreteVMWAssumption4 (witnessLaw (a / Real.sqrt n)) := by
    exact concreteVMWAssumption4_of_ucvmwModel
      (witnessLaw (a / Real.sqrt n)) hM1.toUCVMWModel
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
  refine ⟨⟨hW0, hW1, hpub0, hA40, hpub1, hA41, hnotRecovery⟩, ?_, ?_⟩
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
    have hA4Path : ConcreteVMWAssumption4 (pathLaw g h) := by
      exact concreteVMWAssumption4_of_ucvmwModel
        (pathLaw g h) hLocalPath.toGapStratum.toUCVMWModel
    have hA4Base : ConcreteVMWAssumption4 (pathLaw g 0) := by
      exact concreteVMWAssumption4_of_ucvmwModel
        (pathLaw g 0) hLocalBase.toGapStratum.toUCVMWModel
    have hsepPath := gapStratum_publishedSpectralSeparation hLocalPath.toGapStratum
    have hsepBase := gapStratum_publishedSpectralSeparation hLocalBase.toGapStratum
    refine ⟨hDomain,
      ⟨hBase, hPath, hpubBase, hA4Base, hpubPath, hA4Path, hsepBase, hsepPath⟩, ?_⟩
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
