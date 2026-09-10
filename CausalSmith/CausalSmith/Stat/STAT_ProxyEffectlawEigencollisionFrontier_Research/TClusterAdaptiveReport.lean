import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.THonestRootNConfidence
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ClusterBounds

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

/-- On the summary event, associated true clusters partition the target support, lie in their
reported intervals, and obey the atom-floor external-gap mass bounds. -/
-- @node: thm:cluster-adaptive-report
theorem cluster_adaptive_report
    (k dx dz : ℕ) (pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ (C0 : ℝ) (hC0 : ConcentrationConstantDomain C0),
    ∀ (L : ℝ), (hL : 1 ≤ L) →
    ∃ (hClat : 0 < prescribedLatticeConstant k dx dz L pi0 sigma0),
    ∀ n : ℕ, (hn : 1 ≤ n) → ∃
      (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
      (R : SummaryRepairData k dx dz n L pi0 sigma0)
      (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A),
    ∀ alpha : ℝ, (hAlpha : MiscoverageDomain alpha) →
    A.atomFloor = pi0 ∧
    (∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
      letI := _hP
      (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
      ∀ sample, AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) ≤
        prescribedLatticeConstant k dx dz L pi0 sigma0 *
          (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹)) ∧
    ∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
      letI := _hP
      (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
      (1 - alpha ≤ (sampleLaw (n := n) P).real (summaryEvent (n := n) P C0 L alpha)) ∧
      ∀ sample ∈ summaryEvent (n := n) P C0 L alpha,
        let report := clusterReport R A hA sample alpha C0
          (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
          hC0 hL hpi hpiMax hClat
        let nu := (quotientLaw P hM).representative.1
        (∀ x, x ∈ nu.support ↔ ∃! C, C ∈ report.Kcomponents ∧ x ∈ report.Ktrue nu C) ∧
        (∀ C ∈ report.Kcomponents, report.Ktrue nu C ⊆ nu.support) ∧
        (∀ C ∈ report.Kcomponents, ∀ x ∈ report.Ktrue nu C,
          (report.supportInterval C).1 ≤ x ∧ x ≤ (report.supportInterval C).2) ∧
        (∀ C ∈ report.Kcomponents,
          (report.massInterval C).1 ≤ clusterMass report.rho nu C ∧
          clusterMass report.rho nu C ≤ (report.massInterval C).2) ∧
        (∀ C ∈ report.Kcomponents, (report.Ktrue nu C).card = 1 →
          (report.supportInterval C).2 - (report.supportInterval C).1 ≤ 4 * report.rho ∧
          (report.massInterval C).2 - (report.massInterval C).1 ≤
            8 / pi0 * min 1
              ((confidenceSets R A hA sample alpha C0
                (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
                hC0 hL hpi hpiMax hClat).Ralpha / (effectGap P).toReal)) ∧
        (∀ C ∈ report.Kcomponents, report.externalGap nu C = ⊤ →
          (report.massInterval C).2 - (report.massInterval C).1 = 0) ∧
        (∀ C ∈ report.Kcomponents,
          (report.massInterval C).2 - (report.massInterval C).1 ≤
            8 / pi0 * min 1
              ((confidenceSets R A hA sample alpha C0
              (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
                hC0 hL hpi hpiMax hClat).Ralpha /
                (report.externalGap nu C).toReal)) ∧
        CalgHasConstrainedRepresentation
          (confidenceSets R A hA sample alpha C0
            (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
          hC0 hL hpi hpiMax hClat) (latticeLaw A sample) := by
  obtain ⟨C0, hC0, hconc⟩ := uniform_summary_concentration k dx dz pi0 sigma0
    hk hkx hkz hpi hpiMax hsigma hsigmaMax
  refine ⟨C0, hC0, ?_⟩
  intro L hL
  obtain ⟨Ctail, hClat, hCtail, hlattice⟩ :=
    polynomial_lattice_law_estimator k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  refine ⟨hClat, ?_⟩
  intro n hn
  obtain ⟨A, hA, hAfloor, hmeas, heval, hfloor, hthreshold, hcount, hops, hdet, htail⟩ :=
    hlattice n hn
  obtain ⟨Cmod, hCmod, hmodel, Fbar, hFcont, hFmeas, hFlip, hFext, hFuniq⟩ :=
    gap_free_positive_measure_modulus k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  obtain ⟨R, hRlip⟩ := summaryRepair_with_modulus k dx dz n L pi0 sigma0 Cmod
    hk hkx hkz hL hpi hpiMax hsigma hsigmaMax Fbar hFcont hFlip hFext
  refine ⟨A, R, hA, ?_⟩
  intro alpha hAlpha
  obtain ⟨halpha, halphaMax⟩ := hAlpha
  refine ⟨hAfloor, hdet, ?_⟩
  intro P hP
  letI := hP
  intro hM
  have hnpos : 0 < n := by omega
  constructor
  · let bad : Set (Fin n → Obs dx dz) :=
      {sample | summaryRadius n alpha C0 L < dS (empSummary sample) (obsSummary P)}
    have hbad : (sampleLaw (n := n) P).real bad ≤ alpha := by
      simpa [bad, summaryRadius] using
        (hconc L n hL hn P hP hM alpha ⟨halpha, halphaMax⟩).1
    have hbadMeas : MeasurableSet bad := by
      apply measurableSet_lt measurable_const
      have hc : Continuous (fun s : SummarySpace dx dz => dS s (obsSummary P)) :=
        (dS_continuous dx dz).uncurry_right (obsSummary P)
      exact hc.measurable.comp empSummary_measurable
    rw [show summaryEvent (n := n) P C0 L alpha = badᶜ by
      ext sample
      simp [summaryEvent, bad]]
    rw [measureReal_compl hbadMeas]
    have hone : (sampleLaw (n := n) P).real Set.univ = 1 := by simp [Measure.real]
    rw [hone]
    exact sub_le_sub_left hbad 1
  · intro sample hs
    let Clat := prescribedLatticeConstant k dx dz L pi0 sigma0
    let CS := confidenceSets R A hA sample alpha C0 Clat hnpos halpha halphaMax
      hC0 hL hpi hpiMax hClat
    let report := clusterReport R A hA sample alpha C0 Clat hnpos halpha halphaMax
      hC0 hL hpi hpiMax hClat
    let nu := (quotientLaw P hM).representative.1
    let center := (latticeLaw A sample).representative.1
    let rho := CS.Ralpha / pi0
    have hd : dS (empSummary sample) (obsSummary P) ≤ summaryRadius n alpha C0 L := hs
    have hW : AtomicLaw.LawModulo.wass1 (latticeLaw A sample) (quotientLaw P hM) ≤
        CS.Ralpha := by
      have hb := hdet P hP hM sample
      change AtomicLaw.LawModulo.wass1 (latticeLaw A sample) (quotientLaw P hM) ≤ _
      exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hd (le_refl _)) hClat.le)
    have hnuCalg : quotientLaw P hM ∈ CS.Calg := by
      change AtomicLaw.AtomFloor pi0 nu ∧
        AtomicLaw.LawModulo.wass1 (quotientLaw P hM) (latticeLaw A sample) ≤ CS.Ralpha
      exact ⟨quotientLaw_atomFloor P hpi hM, by
        rw [AtomicLaw.LawModulo.wass1_comm]
        exact hW⟩
    have hCalg : ∀ q ∈ CS.Calg,
        AtomicLaw.AtomFloor pi0 q.representative.1 ∧
          AtomicLaw.wass1 q.representative.1 center ≤ CS.Ralpha := by
      intro q hq
      exact hq
    have hnuRep :
        (AtomicLaw.LawModulo.ofProbabilityLaw ⟨nu, (quotientLaw P hM).representative.2⟩).representative.1 =
          nu := by
      have heq : AtomicLaw.LawModulo.ofProbabilityLaw
          (quotientLaw P hM).representative = quotientLaw P hM := Quotient.out_eq _
      rw [show (⟨nu, (quotientLaw P hM).representative.2⟩ :
          AtomicLaw.ProbabilityLaw k (effectRadius dz L sigma0)) =
          (quotientLaw P hM).representative from rfl, heq]
    have hcore := cluster_deterministic_report
      (center := center) (nu := nu) (rho := rho)
      (latticeLaw A sample).representative.2 (quotientLaw P hM).representative.2
      hpi (by
        have hk0 : (0 : ℝ) < 2 * k := by positivity
        have hk1 : (1 : ℝ) ≤ 2 * k := by exact_mod_cast (show 1 ≤ 2 * k by omega)
        calc pi0 ≤ 1 / (2 * k : ℝ) := hpiMax
          _ ≤ 1 := (div_le_one hk0).mpr hk1)
      CS.Ralpha_pos (by rfl)
      (by simpa [center, latticeLaw] using hfloor sample)
      (quotientLaw_atomFloor P hpi hM) CS.Calg hCalg
      (by
        have heq : AtomicLaw.LawModulo.ofProbabilityLaw
            (quotientLaw P hM).representative = quotientLaw P hM := Quotient.out_eq _
        rw [heq]
        exact hnuCalg) hnuRep
    rcases hcore with ⟨hpart, hsubset, hsupp, hmass, hsingleSupp, htop, hgeneral⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ∀ x, x ∈ nu.support ↔ ∃! C,
        C ∈ components (rho := rho) center ∧
          x ∈ associatedSupport (rho := rho) nu C
      exact hpart
    · intro C hC x hx
      exact (Finset.mem_filter.mp hx).1
    · change ∀ C ∈ components (rho := rho) center,
        ∀ x ∈ associatedSupport (rho := rho) nu C,
          sInf (C : Set ℝ) - rho ≤ x ∧ x ≤ sSup (C : Set ℝ) + rho
      exact hsupp
    · change ∀ C ∈ components (rho := rho) center,
        sInf {m | ∃ q ∈ CS.Calg, m = clusterMass rho q.representative.1 C} ≤
          clusterMass rho nu C ∧
        clusterMass rho nu C ≤
          sSup {m | ∃ q ∈ CS.Calg, m = clusterMass rho q.representative.1 C}
      exact hmass
    · intro C hC hcard
      have hC' : C ∈ components (rho := rho) center := by
        simpa [report, clusterReport, CS, confidenceSets, Clat, rho, center] using hC
      have hcard' : (associatedSupport (rho := rho) nu C).card = 1 := by
        change (associatedSupport (rho := rho) nu C).card = 1 at hcard
        exact hcard
      constructor
      · exact hsingleSupp C hC' hcard'
      · apply cluster_singleton_width_from_external P hM
          (by simpa [nu, rho] using hcard')
          CS.Ralpha_pos.le hpi
        · intro htopC
          exact htop C hC' htopC
        · exact hgeneral C hC'
    · intro C hC htopC
      have hC' : C ∈ components (rho := rho) center := by
        change C ∈ components (rho := rho) center at hC
        exact hC
      have htopC' : clusterExternalGap (rho := rho) nu C = ⊤ := by
        change clusterExternalGap (rho := rho) nu C = ⊤ at htopC
        exact htopC
      change sSup {m | ∃ q ∈ CS.Calg, m = clusterMass rho q.representative.1 C} -
          sInf {m | ∃ q ∈ CS.Calg, m = clusterMass rho q.representative.1 C} = 0
      exact htop C hC' htopC'
    · intro C hC
      have hC' : C ∈ components (rho := rho) center := by
        change C ∈ components (rho := rho) center at hC
        exact hC
      change sSup {m | ∃ q ∈ CS.Calg, m = clusterMass rho q.representative.1 C} -
          sInf {m | ∃ q ∈ CS.Calg, m = clusterMass rho q.representative.1 C} ≤
        8 / pi0 * min 1 (CS.Ralpha / (clusterExternalGap (rho := rho) nu C).toReal)
      exact hgeneral C hC'
    · exact confidenceSets_constrainedRepresentation R A hA sample alpha C0 Clat
        hnpos halpha halphaMax hC0 hL hpi hpiMax hClat

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
