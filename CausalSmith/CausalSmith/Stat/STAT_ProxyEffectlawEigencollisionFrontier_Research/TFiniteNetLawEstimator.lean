import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Concentration
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.LatticeEstimator
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.NetLibraryCertificates

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

/-- The advised class-dependent finite library is total and Borel, has the displayed polynomial
size, and obeys the deterministic gap-free modulus bound.  Its spectral output and operation count
come from the same result-bearing exact-real primitive execution. -/
-- @node: thm:polynomial-net-law-estimator
theorem finite_net_law_estimator
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ Cmod C : ℝ,
      0 < Cmod ∧ -- @realizes \(C_{\mathrm{mod}}\)(positive finite-net modulus constant)
      0 < C ∧ -- @realizes \(C\)(positive finite-net complexity and tail constant)
      ∀ n : ℕ, 1 ≤ n →
    ∀ primitives : ExactRealPrimitives,
    ∀ A : NetLibrary k dx dz n L pi0 sigma0,
    Measurable (netLawEstimator (n := n) primitives A) ∧
    ((@Fintype.card A.index A.finiteIndex : ℕ) : ℝ) ≤
      C * Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2) ∧
      (∀ sample : Fin n → Obs dx dz, ((netOperationCount primitives A sample).total : ℝ) ≤
        C * (n + Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2)) ∧
        (netExactRealProgram primitives A sample).trace =
          netSummaryTrace n dx dz ++ netSearchTrace A ++
            match (netExactRealProgram primitives A sample).selected with
            | none => []
            | some i => (exactRealSpectralRun primitives (A.summary i)
                (A.representative_feasible i)).trace) ∧
      (∀ sample : Fin n → Obs dx dz, ∀ i,
        (netExactRealProgram primitives A sample).selected = some i →
        (∀ j, dS (A.summary i) (empSummary sample) ≤
          dS (A.summary j) (empSummary sample)) ∧
        (∀ j, dS (A.summary i) (empSummary sample) =
          dS (A.summary j) (empSummary sample) → A.lexRank i ≤ A.lexRank j) ∧
        let run := exactRealSpectralRun primitives (A.summary i) (A.representative_feasible i)
        netLawEstimator primitives A sample = run.output.effectLaw ∧
        (∀ t, Function.Injective (Matrix.toEuclideanLin
          (observedProxyMoment (A.summary i) t * run.output.basis.V))) ∧
        (∀ j, pi0 * sigma0 ^ 2 / 2 ≤ singularValue
          (stackedProxyMoment (A.summary i)) j ↔ j < k) ∧
        (∀ z : ℂ, MatrixEigenvalue
          (compressedOperator (A.summary i) run.output.basis run.output.spans) z →
            ∃ r, z = run.output.eigenvalue r)) ∧
      (∀ i (H : RectMatrix (2 * dz) dx),
        ‖matrixCLM H‖ < pi0 * sigma0 ^ 2 / 2 →
        ThresholdRecoversMatrixDimension k (pi0 * sigma0 ^ 2 / 2)
          (stackedProxyMoment (A.summary i) + H)) ∧
      (∀ i, ∃ Q : ModelLaw k dx dz L pi0 sigma0,
        Q.summary = A.summary i ∧
          (exactRealSpectralRun primitives (A.summary i)
            (A.representative_feasible i)).output.effectLaw = by
          letI := Q.prob
          exact quotientLaw Q.P Q.model) ∧
      (∀ i, AtomicLaw.Valid
        ((exactRealSpectralRun primitives (A.summary i)
          (A.representative_feasible i)).output.effectLaw.representative.1)) ∧
      (∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
        letI := _hP
        (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
        ∀ sample : Fin n → Obs dx dz, AtomicLaw.LawModulo.wass1
          (netLawEstimator primitives A sample)
          (quotientLaw P hM) ≤
          Cmod * (2 * dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹)) ∧
      ∀ eta : ℝ, TailLevelDomain eta →
        ∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) →
          (sampleLaw (n := n) P).real {sample |
            AtomicLaw.LawModulo.wass1 (netLawEstimator primitives A sample)
              (quotientLaw P hM) >
              C * Real.sqrt (Real.log (C / eta) / n)} ≤ eta := by
  obtain ⟨Cmod, hCmod, hmodel, _⟩ := gap_free_positive_measure_modulus
    k dx dz L pi0 sigma0 hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  obtain ⟨Ccard, hCcard, hcard⟩ :=
    netLibrary_card_polynomial_bound k dx dz L pi0 sigma0 hk hkx hkz hL
  obtain ⟨Cwork, hCwork, hwork⟩ :=
    netOperationCount_polynomial_bound k dx dz L pi0 sigma0 hk hkx hkz hL
  obtain ⟨C0, hC0, hconc⟩ :=
    uniform_summary_concentration k dx dz pi0 sigma0 hk hkx hkz hpi hpiMax
      hsigma hsigmaMax
  let Ctail := max C0 (max (Real.exp 1) (Cmod * (2 * C0 * L + 1)))
  let C := max Ccard (max Cwork Ctail)
  have hCtail : 0 < Ctail := lt_of_lt_of_le (Real.exp_pos 1)
    (le_trans (le_max_left _ _) (le_max_right _ _))
  have hC : 0 < C := hCtail.trans_le
    ((le_max_right Cwork Ctail).trans (le_max_right Ccard (max Cwork Ctail)))
  refine ⟨Cmod, C, hCmod, hC, ?_⟩
  intro n hn primitives A
  have hCcardLe : Ccard ≤ C := le_max_left _ _
  have hCworkLe : Cwork ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hrpow0 : 0 ≤ Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcardA : ((@Fintype.card A.index A.finiteIndex : ℕ) : ℝ) ≤
      C * Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2) :=
    (hcard n hn A).trans (mul_le_mul_of_nonneg_right hCcardLe hrpow0)
  refine ⟨netLawEstimator_measurable primitives A, hcardA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample
    have hs0 : 0 ≤ (n : ℝ) + Real.rpow (n : ℝ)
        ((4 * dz * dx + dx : ℝ) / 2) := add_nonneg (Nat.cast_nonneg n) hrpow0
    refine ⟨(hwork n hn primitives A sample).trans
      (mul_le_mul_of_nonneg_right hCworkLe hs0), ?_⟩
    unfold netExactRealProgram
    split <;> simp
  · intro sample i hsel
    have hi := nearestLibraryIndex_spec A (empSummary sample) i (by
      rw [← netProgram_selected_eq_nearest primitives A sample]
      exact hsel)
    refine ⟨hi.1, hi.2, ?_⟩
    let run := exactRealSpectralRun primitives (A.summary i) (A.representative_feasible i)
    change netLawEstimator primitives A sample = run.output.effectLaw ∧
      (∀ t, Function.Injective (Matrix.toEuclideanLin
        (observedProxyMoment (A.summary i) t * run.output.basis.V))) ∧
      (∀ j, pi0 * sigma0 ^ 2 / 2 ≤ singularValue
        (stackedProxyMoment (A.summary i)) j ↔ j < k) ∧
      (∀ z : ℂ, MatrixEigenvalue
        (compressedOperator (A.summary i) run.output.basis run.output.spans) z →
          ∃ r, z = run.output.eigenvalue r)
    exact ⟨netLawEstimator_eq_of_selected primitives A sample i hsel,
      run.output.armwiseFullRank, run.output.thresholdRetainsExactlySignal,
      run.output.eigenvalue_complete⟩
  · intro i H hH
    obtain ⟨Q, hQ⟩ := A.representative_feasible i
    rw [← hQ]
    exact modelSummary_thresholdRecovers_of_perturbation Q H hH
  · intro i
    exact exactRealSpectralRun_eq_quotient primitives (A.summary i)
      (A.representative_feasible i)
  · intro i
    exact exactRealSpectralRun_output_valid primitives (A.summary i)
      (A.representative_feasible i)
  · intro P hP
    letI := hP
    intro hM sample
    exact netEstimator_wass1_le primitives A hCmod.le hmodel P hP hM sample
  · intro eta hEta P hP
    rcases hEta with ⟨heta, hetaHalf⟩
    letI := hP
    intro hM
    have hdev := (hconc L n hL hn P hP hM eta ⟨heta, hetaHalf⟩).1
    have hCtailLe : Ctail ≤ C :=
      (le_max_right Cwork Ctail).trans (le_max_right Ccard (max Cwork Ctail))
    have hC0C : C0 ≤ C := (le_max_left _ _).trans hCtailLe
    have hexpC : Real.exp 1 ≤ C :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans hCtailLe
    have hcoefC : Cmod * (2 * C0 * L + 1) ≤ C :=
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
          AtomicLaw.LawModulo.wass1 (netLawEstimator primitives A sample)
            (quotientLaw P hM) > C * Real.sqrt (Real.log (C / eta) / n)} ⊆
        {sample | C0 * L * Real.sqrt (Real.log (C0 / eta) / n) <
          dS (empSummary sample) (obsSummary P)} := by
      intro sample hs
      by_contra hgood
      have hdS : dS (empSummary sample) (obsSummary P) ≤
          C0 * L * Real.sqrt (Real.log (C0 / eta) / n) := le_of_not_gt hgood
      have hw := netEstimator_wass1_le primitives A hCmod.le hmodel P hP hM sample
      have hbound : Cmod *
          (2 * dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) ≤
          C * Real.sqrt (Real.log (C / eta) / n) := by
        calc
          _ ≤ Cmod * (2 * (C0 * L * Real.sqrt (Real.log (C0 / eta) / n)) +
              (Real.sqrt n)⁻¹) := mul_le_mul_of_nonneg_left
                (add_le_add (mul_le_mul_of_nonneg_left hdS (by norm_num)) (le_refl _))
                hCmod.le
          _ ≤ Cmod * (2 * (C0 * L * Real.sqrt (Real.log (C / eta) / n)) +
              Real.sqrt (Real.log (C / eta) / n)) := by gcongr
          _ = (Cmod * (2 * C0 * L + 1)) *
              Real.sqrt (Real.log (C / eta) / n) := by ring
          _ ≤ C * Real.sqrt (Real.log (C / eta) / n) :=
            mul_le_mul_of_nonneg_right hcoefC (Real.sqrt_nonneg _)
      exact (not_lt_of_ge (hw.trans hbound)) hs
    exact (measureReal_mono hsubset).trans hdev

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
