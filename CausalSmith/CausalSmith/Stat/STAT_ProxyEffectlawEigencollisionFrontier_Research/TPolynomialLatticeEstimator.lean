import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Concentration
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeFunctionalCalculus
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeMeasurability

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

/-- Existence and deterministic/high-probability guarantees of the explicit no-advice structured
lattice estimator, including its atom floor and polynomial candidate count. -/
-- @node: prop:polynomial-net-law-estimator
theorem polynomial_lattice_law_estimator
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ) (hk : 2 ≤ k) (hkx : k ≤ dx)
    (hkz : k ≤ dz) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hpiMax : pi0 ≤ 1 / (2 * k : ℝ)) (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ C : ℝ, 0 < prescribedLatticeConstant k dx dz L pi0 sigma0 ∧
      0 < C ∧ -- @realizes \(C\)(positive lattice complexity and tail constant)
      ∀ n : ℕ, 1 ≤ n →
    ∃ A : LatticeEstimator k dx dz n (effectRadius dz L sigma0),
      IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A ∧
      A.atomFloor = pi0 ∧
      Measurable A.summaryRule ∧
      (A.estimate = fun sample => A.summaryRule (empSummary sample)) ∧
      (∀ sample, AtomicLaw.AtomFloor pi0 (A.estimate sample).representative.1) ∧
      (∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
        letI := _hP
        (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
        ThresholdRecoversDimension k (pi0 * sigma0 ^ 2 / 2) (obsSummary P) ∧
        ∀ s, dS s (obsSummary P) < pi0 * sigma0 ^ 2 / 2 →
          ThresholdRecoversDimension k (pi0 * sigma0 ^ 2 / 2) s) ∧
      (A.candidateCount : ℝ) ≤ C * Real.rpow (n : ℝ) ((dx * k + k^2 + 2*k - 1 : ℝ) / 2) ∧
      (latticeOperationCount A : ℝ) ≤
        C * (n + Real.rpow (n : ℝ) ((dx * k + k^2 + 2*k - 1 : ℝ) / 2)) ∧
      (∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
        letI := _hP
        (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
        ∀ sample, AtomicLaw.LawModulo.wass1 (A.estimate sample)
          (quotientLaw P hM) ≤
          prescribedLatticeConstant k dx dz L pi0 sigma0 *
            (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹)) ∧
      ∀ eta : ℝ, TailLevelDomain eta →
        ∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
          (sampleLaw (n := n) P).real {sample |
            AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) >
              C * Real.sqrt (Real.log (C / eta) / n)} ≤ eta := by
  obtain ⟨Ccount, hCcount, hcount⟩ := prescribed_latticeOperationCount_polynomial_bound
    k dx dz L pi0 sigma0 hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  obtain ⟨C0, hC0, hconc⟩ :=
    uniform_summary_concentration k dx dz pi0 sigma0 hk hkx hkz hpi hpiMax
      hsigma hsigmaMax
  let Clat := prescribedLatticeConstant k dx dz L pi0 sigma0
  let Ctail := max C0 (max (Real.exp 1) (Clat * (C0 * L + 1)))
  let C := max Ccount Ctail
  have hClat : 0 < Clat := prescribedLatticeConstant_pos
    k dx dz L pi0 sigma0 hk hkx hkz hL hpi hsigma
  have hCtail : 0 < Ctail := lt_of_lt_of_le (Real.exp_pos 1)
    (le_trans (le_max_left _ _) (le_max_right _ _))
  have hC : 0 < C := hCtail.trans_le (le_max_right _ _)
  refine ⟨C, hClat, hC, ?_⟩
  intro n hn
  obtain ⟨A, hA, hatom, hmeas, hestimate, hfloor⟩ :=
    structuredLatticeEstimator_exists (n := n) hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  have hcounts := hcount n hn A hA
  have hCcountLe : Ccount ≤ C := le_max_left _ _
  have hrpow0 : 0 ≤ Real.rpow (n : ℝ)
      ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcand : (A.candidateCount : ℝ) ≤ C * Real.rpow (n : ℝ)
      ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) :=
    hcounts.1.trans (mul_le_mul_of_nonneg_right hCcountLe hrpow0)
  have hwork : (latticeOperationCount A : ℝ) ≤
      C * (n + Real.rpow (n : ℝ)
        ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2)) := by
    have hsum0 : 0 ≤ (n : ℝ) + Real.rpow (n : ℝ)
        ((dx * k + k ^ 2 + 2 * k - 1 : ℝ) / 2) :=
      add_nonneg (Nat.cast_nonneg n) hrpow0
    exact hcounts.2.trans (mul_le_mul_of_nonneg_right hCcountLe hsum0)
  refine ⟨A, hA, hatom, hmeas, hestimate, hfloor, ?_, hcand, hwork, ?_, ?_⟩
  · intro P hP
    letI := hP
    intro hM
    exact ⟨model_thresholdRecoversDimension P hM,
      fun s hs => model_thresholdRecoversDimension_of_dS_lt P hM s hs⟩
  · intro P hP
    letI := hP
    intro hM sample
    exact prescribedEstimator_wass1_le P A hA sample hn hk hkx hkz hL hpi hpiMax
      hsigma hsigmaMax hM
  · intro eta hEta P hP
    rcases hEta with ⟨heta, hetaHalf⟩
    letI := hP
    intro hM
    have hdev := (hconc L n hL hn P hP hM eta ⟨heta, hetaHalf⟩).1
    have hCtailLe : Ctail ≤ C := le_max_right _ _
    have hC0C : C0 ≤ C :=
      (le_max_left _ _).trans hCtailLe
    have hexpC : Real.exp 1 ≤ C :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans hCtailLe
    have hcoefC : Clat * (C0 * L + 1) ≤ C :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans hCtailLe
    have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
    have hetaOne : eta ≤ 1 := by linarith
    have hratioExp : Real.exp 1 ≤ C / eta := by
      rw [le_div_iff₀ heta]
      exact (mul_le_of_le_one_right (Real.exp_pos 1).le hetaOne).trans hexpC
    have hlogOne : 1 ≤ Real.log (C / eta) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hratioExp
    have hratio : C0 / eta ≤ C / eta := div_le_div_of_nonneg_right hC0C heta.le
    have hlog : Real.log (C0 / eta) ≤ Real.log (C / eta) :=
      Real.log_le_log (div_pos hC0pos heta) hratio
    have hsqrt : Real.sqrt (Real.log (C0 / eta) / (n : ℝ)) ≤
        Real.sqrt (Real.log (C / eta) / (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
    have hinv : (Real.sqrt n)⁻¹ ≤
        Real.sqrt (Real.log (C / eta) / (n : ℝ)) := by
      calc
        (Real.sqrt n)⁻¹ = Real.sqrt ((n : ℝ)⁻¹) := (Real.sqrt_inv _).symm
        _ = Real.sqrt (1 / (n : ℝ)) := by rw [one_div]
        _ ≤ Real.sqrt (Real.log (C / eta) / (n : ℝ)) := by
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_right hlogOne (Nat.cast_nonneg n)
    have hsubset : {sample |
          AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) >
            C * Real.sqrt (Real.log (C / eta) / n)} ⊆
        {sample | C0 * L * Real.sqrt (Real.log (C0 / eta) / n) <
          dS (empSummary sample) (obsSummary P)} := by
      intro sample hs
      by_contra hgood
      have hdS : dS (empSummary sample) (obsSummary P) ≤
          C0 * L * Real.sqrt (Real.log (C0 / eta) / n) := le_of_not_gt hgood
      have hw := prescribedEstimator_wass1_le P A hA sample hn hk hkx hkz hL hpi
        hpiMax hsigma hsigmaMax hM
      have hbound : Clat *
          (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) ≤
          C * Real.sqrt (Real.log (C / eta) / n) := by
        calc
          _ ≤ Clat * (C0 * L * Real.sqrt (Real.log (C0 / eta) / n) +
              (Real.sqrt n)⁻¹) := mul_le_mul_of_nonneg_left
                (add_le_add hdS (le_refl _)) hClat.le
          _ ≤ Clat * (C0 * L * Real.sqrt (Real.log (C / eta) / n) +
              Real.sqrt (Real.log (C / eta) / n)) := by
                gcongr
          _ = (Clat * (C0 * L + 1)) *
              Real.sqrt (Real.log (C / eta) / n) := by ring
          _ ≤ C * Real.sqrt (Real.log (C / eta) / n) :=
            mul_le_mul_of_nonneg_right hcoefC (Real.sqrt_nonneg _)
      exact (not_lt_of_ge (hw.trans (by simpa [Clat] using hbound))) hs
    exact (measureReal_mono hsubset).trans hdev

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
