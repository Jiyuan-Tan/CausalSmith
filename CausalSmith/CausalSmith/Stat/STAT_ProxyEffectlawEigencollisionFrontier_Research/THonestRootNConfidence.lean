import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Concentration
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ObservedLawAdapters
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TPolynomialLatticeEstimator
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TSummaryRepairTotalBorel
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TCollisionUniformRootN

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

-- @node: honestConfidence_latentClass_real_eq_sum_cells
lemma latentClass_real_eq_sum_cells {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsFiniteMeasure P] (u : Fin k) :
    P.real (latentClass u) = ∑ t : Bool, P.real (latentCell u t) := by
  rw [show latentClass u = ⋃ t : Bool, latentCell u t by
    ext w
    simp [latentClass, latentCell]]
  apply measureReal_iUnion_fintype (h' := fun t => measure_ne_top P (latentCell u t))
  · intro t s hts
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro w hwt hws
    exact hts (hwt.2.symm.trans hws.2)
  · exact fun t => measurableSet_latentCell u t

-- @node: honestConfidence_latentMass_two_pi0
lemma latentMass_two_pi0_le {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpos : LatentArmPositivity (pi0 := pi0) P) (u : Fin k) :
    2 * pi0 ≤ latentMass P u := by
  rw [latentMass, latentClass_real_eq_sum_cells P u, Fintype.sum_bool]
  simpa [two_mul] using add_le_add (hpos u true) (hpos u false)

-- @node: honestConfidence_atomFloor_of_measureEquivalent
lemma AtomicLaw.AtomFloor.of_measureEquivalent {k : ℕ} {radius m : ℝ}
    {a b : AtomicLaw.ProbabilityLaw k radius}
    (hab : a.MeasureEquivalent b) (hb : AtomicLaw.AtomFloor m b.1) :
    AtomicLaw.AtomFloor m a.1 := by
  classical
  intro x hx
  have hagg := hab.aggregate_weight x
  have hapos : 0 < ∑ i with a.1.atom i = x, a.1.weight i := by
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.mp hi).2
    exact lt_of_lt_of_le hi' (Finset.single_le_sum
      (fun j _ => a.2.1 j) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩))
  have hbpos : 0 < ∑ i with b.1.atom i = x, b.1.weight i := by
    rwa [hagg] at hapos
  obtain ⟨i, hi, hipos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i _ => b.2.1 i)).mp hbpos
  rw [hagg]
  apply hb x
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hipos⟩,
      (Finset.mem_filter.mp hi).2⟩

-- @node: honestConfidence_quotient_atomFloor
lemma quotientLaw_atomFloor {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    AtomicLaw.AtomFloor pi0 (quotientLaw P hM).representative.1 := by
  let raw : AtomicLaw.ProbabilityLaw k (effectRadius dz L sigma0) :=
    ⟨quotientLawRaw P (effectRadius dz L sigma0), quotientLawRaw_valid P hM⟩
  have hraw : AtomicLaw.AtomFloor pi0 raw.1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    have huPos := (Finset.mem_filter.mp hu).2
    have hmass := latentMass_two_pi0_le P hM.latentArmPositivity u
    calc
      pi0 ≤ latentMass P u := by linarith
      _ ≤ ∑ i with raw.1.atom i = raw.1.atom u, raw.1.weight i :=
        Finset.single_le_sum (fun i _ => raw.2.1 i)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩)
  apply hraw.of_measureEquivalent
  exact (Quotient.eq_mk_iff_out (x := quotientLaw P hM) (y := raw)).mp rfl

noncomputable def wassDiameter {k : ℕ} {radius : ℝ}
    (C : Set (AtomicLaw.LawModulo k radius)) : ℝ :=
  sSup {d | ∃ x ∈ C, ∃ y ∈ C, d = AtomicLaw.LawModulo.wass1 x y}

-- @node: honestConfidence_summaryRepair_with_modulus
lemma summaryRepair_with_modulus
    (k dx dz n : ℕ) (L pi0 sigma0 Cmod : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz)
    (hL : 1 ≤ L) (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (Fbar : {q // q ∈ summaryClosure k dx dz L pi0 sigma0} →
      AtomicLaw.LawModulo k (effectRadius dz L sigma0))
    (hFcont : Continuous Fbar)
    (hFlip : ∀ q q', AtomicLaw.LawModulo.wass1 (Fbar q) (Fbar q') ≤
      Cmod * dS q.1 q'.1)
    (hFext : ∀ Q : ModelLaw k dx dz L pi0 sigma0,
      Fbar ⟨Q.summary, subset_closure ⟨Q, rfl⟩⟩ = by
        letI := Q.prob
        exact quotientLaw Q.P Q.model) :
    ∃ R : SummaryRepairData k dx dz n L pi0 sigma0,
      ∀ q q', AtomicLaw.LawModulo.wass1 (R.Fbar q) (R.Fbar q') ≤
        Cmod * dS q.1 q'.1 := by
  let K := summaryClosure k dx dz L pi0 sigma0
  have hKc : IsCompact K :=
    (summary_closure_compact k dx dz L pi0 sigma0 hk hkx hkz hL
      hpi hpiMax hsigma hsigmaMax).2.1
  have hkp : 0 < k := by omega
  have hradius : 0 ≤ effectRadius dz L sigma0 := by unfold effectRadius; positivity
  by_cases he : K = ∅
  · let R : SummaryRepairData k dx dz n L pi0 sigma0 := {
      k_pos := hkp, radius_nonneg := hradius, Fbar := Fbar, Pi := fun _ => 0
      continuousFbar := hFcont, extendsOnModel := hFext, measurablePi := measurable_const
      nearest := by intro s hne; exact False.elim (hne (by simpa [K] using he))
      empty_fallback := by intro _ s; rfl
      measurableRepair := by
        have he' : summaryClosure k dx dz L pi0 sigma0 = ∅ := by simpa [K] using he
        simp only [he', dite_true]
        exact measurable_const }
    exact ⟨R, hFlip⟩
  · have hne : K.Nonempty := nonempty_iff_ne_empty.mpr he
    let d := Fintype.card (SummaryRepairCoordIndex dx dz)
    let e : SummarySpace dx dz ≃ₜ Euc d := (summaryRepairSpaceHomeomorph dx dz).trans
      (euclideanReindexHomeomorph (Fintype.equivFin (SummaryRepairCoordIndex dx dz)))
    obtain ⟨Pi, hPm, hPK, hPmin⟩ := compactLoss_selector_of_homeomorph d e K hne hKc dS
      (dS_continuous dx dz)
    let R : SummaryRepairData k dx dz n L pi0 sigma0 := {
      k_pos := hkp, radius_nonneg := hradius, Fbar := Fbar, Pi := Pi
      continuousFbar := hFcont, extendsOnModel := hFext, measurablePi := hPm
      nearest := fun s _ => ⟨hPK s, hPmin s⟩
      empty_fallback := by intro hs; exact False.elim (he (by simpa [K] using hs))
      measurableRepair := by
        have he' : summaryClosure k dx dz L pi0 sigma0 ≠ ∅ := by simpa [K] using he
        simp only [he', dite_false]
        have hsubmem : ∀ s, Pi s ∈ summaryClosure k dx dz L pi0 sigma0 := by
          intro s
          simpa [K] using hPK s
        have hsub : Measurable (fun s =>
            (⟨Pi s, hsubmem s⟩ : {q // q ∈ summaryClosure k dx dz L pi0 sigma0})) :=
          hPm.subtype_mk
        simpa [Function.comp_def] using hFcont.measurable.comp (hsub.comp empSummary_measurable) }
    exact ⟨R, hFlip⟩

set_option maxHeartbeats 0 in
/-- Simultaneous honesty and the two separate root-n diameter bounds, without asserting an
equality or inclusion between the confidence sets. -/
-- @node: thm:honest-root-n-confidence
theorem honest_root_n_confidence
    (k dx dz : ℕ) (pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ (C0 : ℝ) (hC0 : ConcentrationConstantDomain C0),
      ∀ L : ℝ, (hL : 1 ≤ L) →
    ∃ (Cmod : ℝ)
      (hClat : 0 < prescribedLatticeConstant k dx dz L pi0 sigma0)
      (_hCmod : 0 < Cmod),
    ∀ n : ℕ, (hn : 1 ≤ n) → ∃
      (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
      (R : SummaryRepairData k dx dz n L pi0 sigma0)
      (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A),
      ∀ alpha : ℝ, (hAlpha : MiscoverageDomain alpha) →
      (∀ sample,
        let CS := confidenceSets R A hA sample alpha C0
          (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
          hC0 hL hpi hpiMax hClat
        CS.Ctheory.Nonempty ∧ CS.Calg.Nonempty ∧
        CalgHasConstrainedRepresentation CS (latticeLaw A sample)) ∧
      (∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
        letI := _hP
        (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
        (1 - alpha ≤ (sampleLaw (n := n) P).real {sample |
          let CS := confidenceSets R A hA sample alpha C0
            (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
            hC0 hL hpi hpiMax hClat
          quotientLaw P hM ∈ CS.Ctheory ∩ CS.Calg})) ∧
      ∀ sample,
        let CS := confidenceSets R A hA sample alpha C0
          (prescribedLatticeConstant k dx dz L pi0 sigma0) (by omega) hAlpha.1 hAlpha.2
          hC0 hL hpi hpiMax hClat
        wassDiameter CS.Ctheory ≤ 4 * Cmod * summaryRadius n alpha C0 L ∧
        wassDiameter CS.Calg ≤ 2 * CS.Ralpha := by
  obtain ⟨C0, hC0, hconc⟩ := uniform_summary_concentration k dx dz pi0 sigma0
    hk hkx hkz hpi hpiMax hsigma hsigmaMax
  refine ⟨C0, hC0, ?_⟩
  intro L hL
  obtain ⟨Cmod, hCmod, hmodel, Fbar, hFcont, hFmeas, hFlip, hFext, hFuniq⟩ :=
    gap_free_positive_measure_modulus k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  obtain ⟨Ctail, hClat, hCtail, hlattice⟩ :=
    polynomial_lattice_law_estimator k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  refine ⟨Cmod, hClat, hCmod, ?_⟩
  intro n hn
  obtain ⟨A, hAstruct, hAfloor, hAsummaryMeas, hAeval, hAfloorAll,
      hAthreshold, hAcount, hAops, hAdet, hAtail⟩ := hlattice n hn
  obtain ⟨R, hRlip⟩ := summaryRepair_with_modulus k dx dz n L pi0 sigma0 Cmod
    hk hkx hkz hL hpi hpiMax hsigma hsigmaMax Fbar hFcont hFlip hFext
  refine ⟨A, R, hAstruct, ?_⟩
  intro alpha hAlpha
  obtain ⟨halpha, halphaMax⟩ := hAlpha
  have hnpos : 0 < n := by omega
  let Clat := prescribedLatticeConstant k dx dz L pi0 sigma0
  have hrpos : 0 < summaryRadius n alpha C0 L :=
    summaryRadius_pos n alpha C0 L hnpos halpha halphaMax hC0 hL
  have theory_nonempty (sample : Fin n → Obs dx dz) :
      (theoreticalConfidenceSet R sample alpha C0).Nonempty := by
    by_cases hK : summaryClosure k dx dz L pi0 sigma0 = ∅
    · rw [theoreticalConfidenceSet, if_pos hK]
      exact singleton_nonempty _
    · rw [theoreticalConfidenceSet, if_neg hK]
      let q : {q // q ∈ summaryClosure k dx dz L pi0 sigma0} :=
        ⟨R.Pi (empSummary sample), (R.nearest _ hK).1⟩
      refine ⟨R.Fbar q, q, ?_, rfl⟩
      have hz : 0 ≤ 2 * summaryRadius n alpha C0 L := by positivity
      simpa [q, dS, matrixCLM] using hz
  have calg_nonempty (sample : Fin n → Obs dx dz) :
      (confidenceSets R A hAstruct sample alpha C0 Clat hnpos halpha halphaMax
        hC0 hL hpi hpiMax hClat).Calg.Nonempty := by
    refine ⟨latticeLaw A sample, ?_⟩
    simp only [confidenceSets, Set.mem_setOf_eq]
    exact ⟨by simpa [latticeLaw] using hAfloorAll sample,
      (AtomicLaw.LawModulo.wass1_self _).le.trans
        (confidenceRadius_pos hnpos halpha halphaMax hC0 hL hClat).le⟩
  constructor
  · intro sample
    let CS := confidenceSets R A hAstruct sample alpha C0 Clat hnpos halpha halphaMax
      hC0 hL hpi hpiMax hClat
    exact ⟨theory_nonempty sample, calg_nonempty sample,
      confidenceSets_constrainedRepresentation R A hAstruct sample alpha C0 Clat
        hnpos halpha halphaMax hC0 hL hpi hpiMax hClat⟩
  constructor
  · intro P hP
    letI := hP
    intro hM
    let Q : ModelLaw k dx dz L pi0 sigma0 := ⟨P, hP, hM⟩
    have hKne : summaryClosure k dx dz L pi0 sigma0 ≠ ∅ := by
      intro hK
      have hmem : Q.summary ∈ summaryClosure k dx dz L pi0 sigma0 :=
        subset_closure ⟨Q, rfl⟩
      rw [hK] at hmem
      exact hmem
    let bad : Set (Fin n → Obs dx dz) :=
      {sample | summaryRadius n alpha C0 L < dS (empSummary sample) (obsSummary P)}
    have hbad : (sampleLaw (n := n) P).real bad ≤ alpha := by
      simpa [bad, summaryRadius] using
        (hconc L n hL hn P hP hM alpha ⟨halpha, halphaMax⟩).1
    have hbadMeas : MeasurableSet bad := by
      apply measurableSet_lt measurable_const
      have hc : Continuous (fun s : SummarySpace dx dz => dS s (obsSummary P)) :=
        (dS_continuous dx dz).uncurry_right (obsSummary P)
      exact hc.measurable.comp empSummary_measurable
    have hgood : badᶜ ⊆ {sample |
        let CS := confidenceSets R A hAstruct sample alpha C0 Clat hnpos halpha halphaMax
          hC0 hL hpi hpiMax hClat
        quotientLaw P hM ∈ CS.Ctheory ∩ CS.Calg} := by
      intro sample hs
      have hd : dS (empSummary sample) (obsSummary P) ≤ summaryRadius n alpha C0 L :=
        le_of_not_gt hs
      constructor
      · change quotientLaw P hM ∈ theoreticalConfidenceSet R sample alpha C0
        rw [theoreticalConfidenceSet, if_neg hKne]
        refine ⟨⟨Q.summary, subset_closure ⟨Q, rfl⟩⟩, ?_, ?_⟩
        · have hnear := (R.nearest (empSummary sample) hKne).2 Q.summary
            (subset_closure ⟨Q, rfl⟩)
          have hnear' : dS (empSummary sample) (R.Pi (empSummary sample)) ≤
              dS (empSummary sample) Q.summary := by
            calc
              dS (empSummary sample) (R.Pi (empSummary sample)) =
                  dS (R.Pi (empSummary sample)) (empSummary sample) := dS_symm _ _
              _ ≤ dS Q.summary (empSummary sample) := hnear
              _ = dS (empSummary sample) Q.summary := dS_symm _ _
          have htri := dS_triangle Q.summary (empSummary sample)
            (R.Pi (empSummary sample))
          have hnearR : dS (empSummary sample) (R.Pi (empSummary sample)) ≤
              summaryRadius n alpha C0 L :=
            hnear'.trans (by
              rw [show Q.summary = obsSummary P from rfl]
              exact hd)
          calc
            dS Q.summary (R.Pi (empSummary sample))
                ≤ dS Q.summary (empSummary sample) +
                    dS (empSummary sample) (R.Pi (empSummary sample)) := htri
            _ ≤ 2 * summaryRadius n alpha C0 L := by
              rw [show Q.summary = obsSummary P from rfl,
                dS_symm (obsSummary P) (empSummary sample)]
              linarith [hnearR]
        · exact (R.extendsOnModel Q).symm
      · simp only [confidenceSets, Set.mem_setOf_eq]
        constructor
        · exact quotientLaw_atomFloor P hpi hM
        · rw [AtomicLaw.LawModulo.wass1_comm]
          have hdet := hAdet P hP hM sample
          change AtomicLaw.LawModulo.wass1 (latticeLaw A sample) (quotientLaw P hM) ≤ _
          rw [latticeLaw]
          exact hdet.trans (mul_le_mul_of_nonneg_left (add_le_add hd (le_refl _))
            hClat.le)
    have hcompl : 1 - alpha ≤ (sampleLaw (n := n) P).real badᶜ := by
      rw [measureReal_compl hbadMeas]
      have hone : (sampleLaw (n := n) P).real Set.univ = 1 := by simp [Measure.real]
      rw [hone]
      exact sub_le_sub_left hbad 1
    exact hcompl.trans (measureReal_mono hgood)
  · intro sample
    let CS := confidenceSets R A hAstruct sample alpha C0 Clat hnpos halpha halphaMax
      hC0 hL hpi hpiMax hClat
    constructor
    · unfold wassDiameter
      apply csSup_le
      · obtain ⟨x, hx⟩ := theory_nonempty sample
        exact ⟨AtomicLaw.LawModulo.wass1 x x, x, hx, x, hx, rfl⟩
      · rintro d ⟨x, hx, y, hy, rfl⟩
        by_cases hK : summaryClosure k dx dz L pi0 sigma0 = ∅
        · rw [show CS.Ctheory = {AtomicLaw.LawModulo.deltaZeroLaw R.k_pos
              R.radius_nonneg} by simp [CS, confidenceSets, theoreticalConfidenceSet, hK]] at hx hy
          rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy,
            AtomicLaw.LawModulo.wass1_self]
          positivity
        · rw [show CS.Ctheory = theoreticalConfidenceSet R sample alpha C0 by rfl,
            theoreticalConfidenceSet, if_neg hK] at hx hy
          rcases hx with ⟨qx, hqx, rfl⟩
          rcases hy with ⟨qy, hqy, rfl⟩
          have hqy' : dS (R.Pi (empSummary sample)) qy.1 ≤
              2 * summaryRadius n alpha C0 L := by
            rw [dS_symm]
            exact hqy
          have hqdist : dS qx.1 qy.1 ≤ 4 * summaryRadius n alpha C0 L := by
            calc
              dS qx.1 qy.1 ≤ dS qx.1 (R.Pi (empSummary sample)) +
                  dS (R.Pi (empSummary sample)) qy.1 :=
                dS_triangle _ _ _
              _ ≤ 4 * summaryRadius n alpha C0 L := by
                calc
                  _ ≤ 2 * summaryRadius n alpha C0 L +
                      2 * summaryRadius n alpha C0 L := add_le_add hqx hqy'
                  _ = 4 * summaryRadius n alpha C0 L := by ring
          exact (hRlip qx qy).trans (by
            calc
              Cmod * dS qx.1 qy.1 ≤ Cmod * (4 * summaryRadius n alpha C0 L) :=
                mul_le_mul_of_nonneg_left hqdist hCmod.le
              _ = 4 * Cmod * summaryRadius n alpha C0 L := by ring)
    · unfold wassDiameter
      apply csSup_le
      · obtain ⟨x, hx⟩ := calg_nonempty sample
        exact ⟨AtomicLaw.LawModulo.wass1 x x, x, hx, x, hx, rfl⟩
      · rintro d ⟨x, hx, y, hy, rfl⟩
        have hx' := hx.2
        have hy' := hy.2
        calc
          AtomicLaw.LawModulo.wass1 x y ≤
              AtomicLaw.LawModulo.wass1 x (latticeLaw A sample) +
                AtomicLaw.LawModulo.wass1 (latticeLaw A sample) y :=
            AtomicLaw.LawModulo.wass1_triangle _ _ _
          _ ≤ CS.Ralpha + CS.Ralpha := by
            rw [AtomicLaw.LawModulo.wass1_comm (latticeLaw A sample) y]
            exact add_le_add hx' hy'
          _ = 2 * CS.Ralpha := by ring

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
