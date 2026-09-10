import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.OrderedMassStability
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TCollisionUniformRootN

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

/-- Uniform labeled-coordinate upper bound on the gap stratum; inverse-gap behavior is confined
to ordered labels. -/
-- @node: thm:labeled-weight-upper
theorem labeled_weight_upper
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(C\)(positive labeled-risk upper constant)
      ∀ n : ℕ, 1 ≤ n →
      ∃ R : SummaryRepairData k dx dz n L pi0 sigma0,
      ∃ est : WeightEstimator k dx dz n,
      est.eval = orderedWeightEstimator R ∧
      ∀ g : ℝ, GapScaleDomain g →
      ∀ (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
        letI := _hP
        (hM : GapStratum (L := L) (pi0 := pi0) (sigma0 := sigma0) (g := g) P) →
        expectedWeightRisk P
          (orderedMasses (quotientLaw P hM.toUCVMWModel).representative.1) est ≤
          C * min 1 (Real.sqrt n * g)⁻¹ := by
  obtain ⟨Ctail, hCtail, htail⟩ := collision_uniform_root_n
    k dx dz L pi0 sigma0 hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  let A : ℝ := max Ctail 2
  let B : ℝ := A * Real.sqrt (Real.log (2 * A)) + A ^ 2 * Real.sqrt Real.pi / 2
  let K : ℝ := 8 + 16 / pi0
  let C : ℝ := max 2 (K * B)
  have hA : 2 ≤ A := le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hBpos : 0 < B := by
    dsimp [B]
    have hlog : 0 < Real.log (2 * A) := Real.log_pos (by nlinarith)
    positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨Alat, R, _hAlat, _hAlatMeas, hRMeas, htailR⟩ := htail n hn
  let est : WeightEstimator k dx dz n := {
    eval := orderedWeightEstimator R
    measurable := orderedWeightEstimator_measurable R
    simplex := fun sample => orderedMasses_inSimplex (by omega)
      (summaryRepair R sample).representative.1
      (summaryRepair R sample).representative.2 }
  refine ⟨R, est, rfl, ?_⟩
  intro g hGap P hP
  obtain ⟨hg, _hgMax⟩ := hGap
  letI := hP
  intro hM
  have htargetEq :
      orderedMasses (quotientLaw P hM.toUCVMWModel).representative.1 =
        orderedMasses (quotientLawRaw P (effectRadius dz L sigma0)) := by
    let nu : AtomicLaw.ProbabilityLaw k (effectRadius dz L sigma0) :=
      ⟨quotientLawRaw P (effectRadius dz L sigma0),
        quotientLawRaw_valid P hM.toUCVMWModel⟩
    have hrel : (quotientLaw P hM.toUCVMWModel).representative.MeasureEquivalent nu := by
      change (AtomicLaw.probabilityLawSetoid k (effectRadius dz L sigma0)).r
        (quotientLaw P hM.toUCVMWModel).representative nu
      change (AtomicLaw.probabilityLawSetoid k (effectRadius dz L sigma0)).r
        (AtomicLaw.LawModulo.ofProbabilityLaw nu).representative nu
      exact (Quotient.eq_mk_iff_out
        (x := AtomicLaw.LawModulo.ofProbabilityLaw nu) (y := nu)).mp rfl
    exact orderedMasses_eq_of_measureEquivalent
      (quotientLaw P hM.toUCVMWModel).representative nu hrel
  rw [htargetEq]
  let Z : (Fin n → Obs dx dz) → ℝ := fun sample =>
    AtomicLaw.LawModulo.wass1 (summaryRepair R sample) (quotientLaw P hM.toUCVMWModel)
  have htailA : ∀ eta : ℝ, 0 < eta → eta < 1 / 2 →
      (sampleLaw (n := n) P).real
        {sample | A * Real.sqrt (Real.log (A / eta) / n) < Z sample} ≤ eta := by
    intro eta heta hetaMax
    have hprob := htailR eta ⟨heta, hetaMax⟩ P hP hM.toUCVMWModel
    have hCA : Ctail ≤ A := le_max_left _ _
    have hratio : Ctail / eta ≤ A / eta := div_le_div_of_nonneg_right hCA heta.le
    have hlog : Real.log (Ctail / eta) ≤ Real.log (A / eta) :=
      Real.log_le_log (div_pos hCtail heta) hratio
    have hsqrt : Real.sqrt (Real.log (Ctail / eta) / (n : ℝ)) ≤
        Real.sqrt (Real.log (A / eta) / (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
    have hthreshold : Ctail * Real.sqrt (Real.log (Ctail / eta) / (n : ℝ)) ≤
        A * Real.sqrt (Real.log (A / eta) / (n : ℝ)) :=
      mul_le_mul hCA hsqrt (Real.sqrt_nonneg _) hApos.le
    refine (measureReal_mono (μ := sampleLaw (n := n) P) ?_).trans hprob
    intro sample hs
    exact lt_of_le_of_lt hthreshold (lt_of_lt_of_le hs (le_max_right _ _))
  have hmean : (∫ sample, Z sample ∂sampleLaw (n := n) P) ≤ B / Real.sqrt n := by
    exact integral_le_of_sqrt_log_tail (sampleLaw (n := n) P) Z
      (fun sample => lawModulo_wass1_nonneg _ _) A n hA hn htailA
  have htargetSimplex : InSimplex
      (orderedMasses (quotientLawRaw P (effectRadius dz L sigma0))) :=
    orderedMasses_inSimplex (by omega) _ (quotientLawRaw_valid P hM.toUCVMWModel)
  have hWraw (sample : Fin n → Obs dx dz) :
      AtomicLaw.wass1 (quotientLawRaw P (effectRadius dz L sigma0))
          (summaryRepair R sample).representative.1 = Z sample := by
    calc
      AtomicLaw.wass1 (quotientLawRaw P (effectRadius dz L sigma0))
          (summaryRepair R sample).representative.1 =
          AtomicLaw.LawModulo.wass1 (quotientLaw P hM.toUCVMWModel)
            (AtomicLaw.LawModulo.ofProbabilityLaw (summaryRepair R sample).representative) := by
              rw [quotientLaw, AtomicLaw.LawModulo.wass1_ofProbabilityLaw]
      _ = AtomicLaw.LawModulo.wass1 (quotientLaw P hM.toUCVMWModel)
            (summaryRepair R sample) := by
              congr 1
              exact Quotient.out_eq _
      _ = Z sample := AtomicLaw.LawModulo.wass1_comm _ _
  have hpoint (sample : Fin n → Obs dx dz) :
      ∑ i, |est.eval sample i -
          orderedMasses (quotientLawRaw P (effectRadius dz L sigma0)) i| ≤
        K * Z sample / g := by
    have hZnn : 0 ≤ Z sample := lawModulo_wass1_nonneg _ _
    by_cases hsmall : AtomicLaw.wass1
        (quotientLawRaw P (effectRadius dz L sigma0))
        (summaryRepair R sample).representative.1 < pi0 * (g / 2) / 4
    · have hlocal := gapStratum_orderedMasses_l1_le P hM hg
        (summaryRepair R sample).representative.1
        (summaryRepair R sample).representative.2 hsmall
      change ∑ i, |orderedWeightEstimator R sample i -
          orderedMasses (quotientLawRaw P (effectRadius dz L sigma0)) i| ≤ _
      have h8K : (8 : ℝ) ≤ K := by
        have hnonneg : 0 ≤ 16 / pi0 := div_nonneg (by norm_num) hpi.le
        dsimp [K]
        linarith
      calc
        _ ≤ 8 * AtomicLaw.wass1
            (quotientLawRaw P (effectRadius dz L sigma0))
            (summaryRepair R sample).representative.1 / g := hlocal
        _ = 8 * Z sample / g := by rw [hWraw]
        _ ≤ K * Z sample / g := by gcongr
    · have hdiam := simplex_l1_le_two (est.simplex sample) htargetSimplex
      have hlarge : pi0 * (g / 2) / 4 ≤ Z sample := by
        rw [← hWraw]
        exact le_of_not_gt hsmall
      have htwo : (2 : ℝ) ≤ 16 / pi0 * Z sample / g := by
        rw [show 16 / pi0 * Z sample / g = 16 * Z sample / (pi0 * g) by
          field_simp]
        rw [le_div_iff₀ (mul_pos hpi hg)]
        nlinarith
      have hcoeff : 16 / pi0 ≤ K := by dsimp [K]; linarith
      exact hdiam.trans (htwo.trans (by gcongr))
  have hZmeas : Measurable Z := by
    dsimp [Z]
    simpa [AtomicLaw.LawModulo.dist_eq_wass1] using
      hRMeas.dist (measurable_const : Measurable
        (fun _ : Fin n → Obs dx dz => quotientLaw P hM.toUCVMWModel))
  have hradius : 0 ≤ effectRadius dz L sigma0 := by unfold effectRadius; positivity
  have hZint : Integrable Z (sampleLaw (n := n) P) := by
    apply (integrable_const (2 * effectRadius dz L sigma0)).mono hZmeas.aestronglyMeasurable
    filter_upwards with sample
    rw [Real.norm_eq_abs, abs_of_nonneg (lawModulo_wass1_nonneg _ _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hradius)]
    exact AtomicLaw.LawModulo.wass1_le_two_radius hradius _ _
  have hriskRate : expectedWeightRisk P
      (orderedMasses (quotientLawRaw P (effectRadius dz L sigma0))) est ≤
      (K * B) * (Real.sqrt n * g)⁻¹ := by
    unfold expectedWeightRisk
    calc
      (∫ sample, ∑ i, |est.eval sample i -
          orderedMasses (quotientLawRaw P (effectRadius dz L sigma0)) i|
          ∂sampleLaw (n := n) P) ≤
          ∫ sample, K * Z sample / g ∂sampleLaw (n := n) P := by
            apply integral_mono_of_nonneg
            · filter_upwards with sample
              exact Finset.sum_nonneg fun _ _ => abs_nonneg _
            · exact (hZint.const_mul K).div_const g
            · filter_upwards with sample
              exact hpoint sample
      _ = K * (∫ sample, Z sample ∂sampleLaw (n := n) P) / g := by
        rw [integral_div, integral_const_mul]
      _ ≤ K * (B / Real.sqrt n) / g := by gcongr
      _ = (K * B) * (Real.sqrt n * g)⁻¹ := by
        have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
        field_simp
  have hriskTwo : expectedWeightRisk P
      (orderedMasses (quotientLawRaw P (effectRadius dz L sigma0))) est ≤ 2 := by
    unfold expectedWeightRisk
    calc
      (∫ sample, ∑ i, |est.eval sample i -
          orderedMasses (quotientLawRaw P (effectRadius dz L sigma0)) i|
          ∂sampleLaw (n := n) P) ≤ ∫ _sample, (2 : ℝ) ∂sampleLaw (n := n) P := by
            apply integral_mono_of_nonneg
            · filter_upwards with sample
              exact Finset.sum_nonneg fun _ _ => abs_nonneg _
            · exact integrable_const _
            · filter_upwards with sample
              exact simplex_l1_le_two (est.simplex sample) htargetSimplex
      _ = 2 := by simp
  by_cases hrate : (Real.sqrt n * g)⁻¹ ≤ 1
  · rw [min_eq_right hrate]
    exact hriskRate.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) hg.le)))
  · rw [min_eq_left (le_of_not_ge hrate)]
    rw [mul_one]
    exact hriskTwo.trans (show (2 : ℝ) ≤ C from le_max_left _ _)

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
