import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Concentration
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TPolynomialLatticeEstimator
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TSummaryRepairTotalBorel

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

/-- The total empirical five-block summary is Borel measurable, including its empty-arm
branches. -/
-- @node: empSummary_measurable
lemma empSummary_measurable {n dx dz : ℕ} : Measurable (@empSummary n dx dz) := by
  have hc (t : Bool) : Measurable (@armCount n dx dz t) := by
    unfold armCount
    simp_rw [Finset.card_filter]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite
      (measurableSet_eq_fun
        (measurable_obs_T.comp (measurable_pi_apply i)) measurable_const)
      measurable_const measurable_const
  have hm (weighted t : Bool) (a : Fin dz) (b : Fin dx) :
      Measurable (fun sample : Fin n → Obs dx dz =>
        empiricalArmMatrix weighted t sample a b) := by
    unfold empiricalArmMatrix
    apply Measurable.mul
    · exact (measurable_const.max
        ((measurable_from_nat : Measurable fun m : ℕ => (m : ℝ)).comp (hc t))).inv
    · apply Finset.measurable_sum
      intro i hi
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_obs_T.comp (measurable_pi_apply i)) measurable_const)
        (by
          have hX : Measurable (fun sample : Fin n → Obs dx dz => (sample i).X b) :=
            ((measurable_pi_apply b).comp measurable_obs_X).comp (measurable_pi_apply i)
          have hZ : Measurable (fun sample : Fin n → Obs dx dz => (sample i).Z a) :=
            ((measurable_pi_apply a).comp measurable_obs_Z).comp (measurable_pi_apply i)
          have hY : Measurable (fun sample : Fin n → Obs dx dz => (sample i).Y) :=
            measurable_obs_Y.comp (measurable_pi_apply i)
          cases weighted
          · convert hZ.mul hX using 1 <;> ext sample <;> simp
          · exact (hY.mul hZ).mul hX)
        measurable_const
  let e := summaryRepairSpaceHomeomorph dx dz
  have he : Measurable (fun sample : Fin n → Obs dx dz => e (empSummary sample)) := by
    change Measurable (fun sample : Fin n → Obs dx dz =>
      summaryRepairToEuc (empSummary sample))
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    rcases i with ⟨b, a, j⟩ | j
    · fin_cases b
      · exact hm false false a j
      · exact hm false true a j
      · exact hm true false a j
      · exact hm true true a j
    · apply Measurable.mul measurable_const
      apply Finset.measurable_sum
      intro i hi
      exact ((measurable_pi_apply j).comp measurable_obs_X).comp (measurable_pi_apply i)
  convert e.symm.continuous.measurable.comp he using 1
  ext sample
  exact e.symm_apply_apply (empSummary sample)

/-- The computable lattice and theoretical nearest-summary estimators simultaneously attain the
collision-uniform root-n quotient-law rate. -/
-- @node: thm:collision-uniform-root-n
theorem collision_uniform_root_n
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(C\)(positive collision-uniform upper constant)
      ∀ n : ℕ, 1 ≤ n →
    ∃ (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
      (R : SummaryRepairData k dx dz n L pi0 sigma0),
      IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A ∧
      Measurable A.estimate ∧ Measurable (summaryRepair R) ∧
      ∀ eta : ℝ, TailLevelDomain eta →
      ∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
        letI := _hP
        (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
        (sampleLaw (n := n) P).real {sample |
          max (AtomicLaw.LawModulo.wass1 (A.estimate sample)
              (quotientLaw P hM))
            (AtomicLaw.LawModulo.wass1 (summaryRepair R sample)
              (quotientLaw P hM)) >
            C * Real.sqrt (Real.log (C / eta) / n)} ≤ eta := by
  obtain ⟨C0, hC0, hconc⟩ := uniform_summary_concentration k dx dz pi0 sigma0
    hk hkx hkz hpi hpiMax hsigma hsigmaMax
  obtain ⟨ClatTail, hClat, hClatTail, hlattice⟩ :=
    polynomial_lattice_law_estimator k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  obtain ⟨Cmod, hCmod, hmod, Fbar, hFcont, hFmeas, hFlip, hFext, hFuniq⟩ :=
    gap_free_positive_measure_modulus k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  let C : ℝ := max (2 * ClatTail) (max (2 * C0) (4 * Cmod * C0 * L))
  have hC : 0 < C := lt_of_lt_of_le (mul_pos (by norm_num) hClatTail)
    (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨A, hAstruct, hAfloor, hAsummaryMeas, hAeval, hAfloorAll,
      hAthreshold, hAcount, hAops, hAdet, hAtail⟩ := hlattice n hn
  let K := summaryClosure k dx dz L pi0 sigma0
  have hKc : IsCompact K :=
    (summary_closure_compact k dx dz L pi0 sigma0 hk hkx hkz hL
      hpi hpiMax hsigma hsigmaMax).2.1
  have hkp : 0 < k := by omega
  have hradius : 0 ≤ effectRadius dz L sigma0 := by unfold effectRadius; positivity
  have hRexists : ∃ R : SummaryRepairData k dx dz n L pi0 sigma0,
      Measurable (summaryRepair R) ∧
      ∀ q q', AtomicLaw.LawModulo.wass1 (R.Fbar q) (R.Fbar q') ≤
        Cmod * dS q.1 q'.1 := by
    by_cases he : K = ∅
    · let R : SummaryRepairData k dx dz n L pi0 sigma0 := {
        k_pos := hkp, radius_nonneg := hradius, Fbar := Fbar, Pi := fun _ => 0
        continuousFbar := hFcont
        extendsOnModel := hFext
        measurablePi := measurable_const
        nearest := by intro s hne; exact False.elim (hne (by simpa [K] using he))
        empty_fallback := by intro _ s; rfl
        measurableRepair := by
          have he' : summaryClosure k dx dz L pi0 sigma0 = ∅ := by simpa [K] using he
          simp only [he', dite_true]
          exact measurable_const }
      exact ⟨R, R.measurableRepair, hFlip⟩
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
          simpa [Function.comp_def] using hFmeas.comp (hsub.comp empSummary_measurable) }
      exact ⟨R, R.measurableRepair, hFlip⟩
  obtain ⟨R, hRmeas, hRlip⟩ := hRexists
  refine ⟨A, R, hAstruct, ?_, hRmeas, ?_⟩
  · rw [hAeval]
    exact hAsummaryMeas.comp empSummary_measurable
  · intro eta hEta P hP
    rcases hEta with ⟨heta, hetaHalf⟩
    letI := hP
    intro hM
    have heta2 : 0 < eta / 2 := by positivity
    have heta2Half : eta / 2 < 1 / 2 := by linarith
    have hAt := hAtail (eta / 2) ⟨heta2, heta2Half⟩ P hP hM
    have hSt := (hconc L n hL hn P hP hM (eta / 2) ⟨heta2, heta2Half⟩).1
    let Q : ModelLaw k dx dz L pi0 sigma0 := ⟨P, hP, hM⟩
    have hKne : summaryClosure k dx dz L pi0 sigma0 ≠ ∅ := by
      intro he
      have hmem : Q.summary ∈ summaryClosure k dx dz L pi0 sigma0 :=
        subset_closure ⟨Q, rfl⟩
      rw [he] at hmem
      exact hmem
    have hrepair (sample : Fin n → Obs dx dz) :
        AtomicLaw.LawModulo.wass1 (summaryRepair R sample) (quotientLaw P hM) ≤
          2 * Cmod * dS (empSummary sample) (obsSummary P) := by
      have hnear := (R.nearest (empSummary sample) hKne).2 Q.summary
        (subset_closure ⟨Q, rfl⟩)
      have htri := dS_triangle (R.Pi (empSummary sample)) (empSummary sample) Q.summary
      have hdist : dS (R.Pi (empSummary sample)) Q.summary ≤
          2 * dS (empSummary sample) Q.summary := by
        rw [dS_symm Q.summary (empSummary sample)] at hnear
        linarith
      have hqmem := (R.nearest (empSummary sample) hKne).1
      have hLip := hRlip ⟨R.Pi (empSummary sample), hqmem⟩
        ⟨Q.summary, subset_closure ⟨Q, rfl⟩⟩
      have hrepairEq : summaryRepair R sample =
          R.Fbar ⟨R.Pi (empSummary sample), hqmem⟩ := by
        simp [summaryRepair, hKne]
      rw [hrepairEq]
      have hLip' : AtomicLaw.LawModulo.wass1
          (R.Fbar ⟨R.Pi (empSummary sample), hqmem⟩) (quotientLaw P hM) ≤
          Cmod * dS (R.Pi (empSummary sample)) Q.summary := by
        simpa only [R.extendsOnModel Q] using hLip
      exact hLip'.trans (by
        calc
          Cmod * dS (R.Pi (empSummary sample)) Q.summary ≤
              Cmod * (2 * dS (empSummary sample) Q.summary) :=
            mul_le_mul_of_nonneg_left hdist hCmod.le
          _ = 2 * Cmod * dS (empSummary sample) Q.summary := by ring)
    have hClat_le : 2 * ClatTail ≤ C := le_max_left _ _
    have hC0_le : 2 * C0 ≤ C := le_trans (le_max_left _ _)
      (le_max_right _ _)
    have hrepairCoef : 4 * Cmod * C0 * L ≤ C :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have threshold_mono (B : ℝ) (hB : 0 < B) (h2B : 2 * B ≤ C) :
        B * Real.sqrt (Real.log (B / (eta / 2)) / n) ≤
          C * Real.sqrt (Real.log (C / eta) / n) := by
      have hBC : B ≤ C := le_trans (le_mul_of_one_le_left hB.le (by norm_num)) h2B
      have hratio : B / (eta / 2) ≤ C / eta := by
        calc
          B / (eta / 2) = (2 * B) / eta := by field_simp
          _ ≤ C / eta := div_le_div_of_nonneg_right h2B heta.le
      have hlog : Real.log (B / (eta / 2)) ≤ Real.log (C / eta) :=
        Real.log_le_log (div_pos hB heta2) hratio
      have hsqrt : Real.sqrt (Real.log (B / (eta / 2)) / (n : ℝ)) ≤
          Real.sqrt (Real.log (C / eta) / (n : ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      exact mul_le_mul hBC hsqrt (Real.sqrt_nonneg _) hC.le
    have hAthreshold := threshold_mono ClatTail hClatTail hClat_le
    have hSthreshold :
        2 * Cmod * (C0 * L * Real.sqrt (Real.log (C0 / (eta / 2)) / n)) ≤
          C * Real.sqrt (Real.log (C / eta) / n) := by
      have hC0pos : 0 < C0 := lt_of_lt_of_le (by norm_num) hC0
      have hratio : C0 / (eta / 2) ≤ C / eta := by
        calc
          C0 / (eta / 2) = (2 * C0) / eta := by field_simp
          _ ≤ C / eta := div_le_div_of_nonneg_right hC0_le heta.le
      have hlog : Real.log (C0 / (eta / 2)) ≤ Real.log (C / eta) :=
        Real.log_le_log (div_pos hC0pos heta2) hratio
      have hsqrt : Real.sqrt (Real.log (C0 / (eta / 2)) / (n : ℝ)) ≤
          Real.sqrt (Real.log (C / eta) / (n : ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      have hcoef : 2 * Cmod * C0 * L ≤ C := by
        calc
          2 * Cmod * C0 * L ≤ 4 * Cmod * C0 * L := by
            have hx : 0 ≤ Cmod * C0 * L := by positivity
            nlinarith
          _ ≤ C := hrepairCoef
      calc
        2 * Cmod * (C0 * L * Real.sqrt (Real.log (C0 / (eta / 2)) / n)) =
            (2 * Cmod * C0 * L) *
              Real.sqrt (Real.log (C0 / (eta / 2)) / n) := by ring
        _ ≤ C * Real.sqrt (Real.log (C / eta) / n) :=
          mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _) (by positivity)
    have hsubset : {sample |
          max (AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM))
            (AtomicLaw.LawModulo.wass1 (summaryRepair R sample) (quotientLaw P hM)) >
              C * Real.sqrt (Real.log (C / eta) / n)} ⊆
        {sample | ClatTail * Real.sqrt (Real.log (ClatTail / (eta / 2)) / n) <
          AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM)} ∪
        {sample | C0 * L * Real.sqrt (Real.log (C0 / (eta / 2)) / n) <
          dS (empSummary sample) (obsSummary P)} := by
      intro sample hs
      rw [Set.mem_union]
      by_cases ha : ClatTail * Real.sqrt (Real.log (ClatTail / (eta / 2)) / n) <
          AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM)
      · exact Or.inl ha
      · right
        have hmax : C * Real.sqrt (Real.log (C / eta) / n) <
            AtomicLaw.LawModulo.wass1 (summaryRepair R sample) (quotientLaw P hM) := by
          have haC : AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) ≤
              C * Real.sqrt (Real.log (C / eta) / n) :=
            (le_of_not_gt ha).trans hAthreshold
          exact lt_of_not_ge fun hrle => (not_lt_of_ge (max_le haC hrle)) hs
        by_contra hsumm
        have hsummLe : dS (empSummary sample) (obsSummary P) ≤
            C0 * L * Real.sqrt (Real.log (C0 / (eta / 2)) / n) := le_of_not_gt hsumm
        exact (not_lt_of_ge (hrepair sample |>.trans
          (mul_le_mul_of_nonneg_left hsummLe (by positivity))))
          (lt_of_le_of_lt hSthreshold hmax)
    calc
      (sampleLaw (n := n) P).real {sample |
          max (AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM))
            (AtomicLaw.LawModulo.wass1 (summaryRepair R sample) (quotientLaw P hM)) >
              C * Real.sqrt (Real.log (C / eta) / n)} ≤
          (sampleLaw (n := n) P).real
            ({sample | ClatTail * Real.sqrt (Real.log (ClatTail / (eta / 2)) / n) <
              AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM)} ∪
             {sample | C0 * L * Real.sqrt (Real.log (C0 / (eta / 2)) / n) <
              dS (empSummary sample) (obsSummary P)}) := measureReal_mono hsubset
      _ ≤ eta / 2 + eta / 2 := by
        exact (measureReal_union_le _ _).trans (add_le_add hAt hSt)
      _ = eta := by ring

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
