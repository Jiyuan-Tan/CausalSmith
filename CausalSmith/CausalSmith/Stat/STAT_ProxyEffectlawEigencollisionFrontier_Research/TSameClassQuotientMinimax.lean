import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TCollisionUniformRootN
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TMatchingLocalLowerBounds

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

/-- Root-n upper and lower bounds hold on the same uniformly conditioned two-class model. -/
-- @node: prop:same-class-quotient-minimax
theorem same_class_quotient_minimax :
    ∃ c C : ℝ,
      0 < c ∧ -- @realizes \(c\)(positive same-class quotient lower constant)
      0 < C ∧ -- @realizes \(C\)(positive finite same-class quotient upper constant)
      c < C ∧
      ∀ n : ℕ, 1 ≤ n →
      (∀ est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10)),
        ∃ (P : Measure (FullData 2 2 2)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          ∃ hM : UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) P,
            c / Real.sqrt n ≤ expectedLawRisk P hM est) ∧
      ∃ est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10)),
        ∀ (P : Measure (FullData 2 2 2)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          (hM : UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) P) →
            expectedLawRisk P hM est ≤ C / Real.sqrt n := by
  obtain ⟨cLoc, a, cLower, CKL, hcLoc, ha, haMax, hcLower, hCKL, hlower⟩ :=
    matching_local_lower_bounds
  obtain ⟨Ctail, hCtail, hupper⟩ :=
    collision_uniform_root_n 2 2 2 2 (1 / 10) (1 / 10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let A : ℝ := max Ctail 2
  let B : ℝ := A * Real.sqrt (Real.log (2 * A)) + A ^ 2 * Real.sqrt Real.pi / 2
  let C : ℝ := max B (2 * cLower)
  have hA : 2 ≤ A := le_max_right _ _
  have hBpos : 0 < B := by
    dsimp [B]
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
    have hlogpos : 0 < Real.log (2 * A) := Real.log_pos (by nlinarith)
    positivity
  have hCpos : 0 < C := hBpos.trans_le (le_max_left _ _)
  have hcC : cLower < C := by
    apply lt_of_lt_of_le _ (le_max_right B (2 * cLower))
    linarith
  refine ⟨cLower, C, hcLower, hCpos, hcC, ?_⟩
  intro n hn
  constructor
  · intro est
    obtain ⟨P, hP, hLocal, _hWitness, hRisk⟩ := (hlower n hn).1 est
    exact ⟨P, hP, hLocal.toUCVMWModel, hRisk⟩
  · obtain ⟨Alat, R, hAlat, hAlatMeas, hRMeas, htail⟩ := hupper n hn
    let est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10)) :=
      ⟨Alat.estimate, hAlatMeas⟩
    refine ⟨est, ?_⟩
    intro P hP
    letI := hP
    intro hM
    let Z : (Fin n → Obs 2 2) → ℝ := fun sample =>
      AtomicLaw.LawModulo.wass1 (Alat.estimate sample) (quotientLaw P hM)
    have htailA : ∀ eta : ℝ, 0 < eta → eta < 1 / 2 →
        (sampleLaw (n := n) P).real
          {sample | A * Real.sqrt (Real.log (A / eta) / n) < Z sample} ≤ eta := by
      intro eta heta hetaMax
      have hprob := htail eta ⟨heta, hetaMax⟩ P hP hM
      have hCA : Ctail ≤ A := le_max_left _ _
      have hratio : Ctail / eta ≤ A / eta := by
        exact div_le_div_of_nonneg_right hCA heta.le
      have hlog : Real.log (Ctail / eta) ≤ Real.log (A / eta) := by
        exact Real.log_le_log (div_pos hCtail heta) hratio
      have hsqrt : Real.sqrt (Real.log (Ctail / eta) / (n : ℝ)) ≤
          Real.sqrt (Real.log (A / eta) / (n : ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      have hthreshold : Ctail * Real.sqrt (Real.log (Ctail / eta) / (n : ℝ)) ≤
          A * Real.sqrt (Real.log (A / eta) / (n : ℝ)) := by
        exact mul_le_mul hCA hsqrt (Real.sqrt_nonneg _) (le_trans (by norm_num) hA)
      refine (measureReal_mono (μ := sampleLaw (n := n) P) ?_).trans hprob
      intro sample hs
      change Ctail * Real.sqrt (Real.log (Ctail / eta) / (n : ℝ)) <
        max (AtomicLaw.LawModulo.wass1 (Alat.estimate sample) (quotientLaw P hM))
          (AtomicLaw.LawModulo.wass1 (summaryRepair R sample) (quotientLaw P hM))
      exact lt_of_le_of_lt hthreshold (lt_of_lt_of_le hs (le_max_left _ _))
    have hmean := integral_le_of_sqrt_log_tail (sampleLaw (n := n) P) Z
      (fun sample => lawModulo_wass1_nonneg _ _) A n hA hn htailA
    change (∫ sample, Z sample ∂sampleLaw (n := n) P) ≤ C / Real.sqrt n
    exact hmean.trans (div_le_div_of_nonneg_right (le_max_left B (2 * cLower))
      (Real.sqrt_nonneg n))

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
