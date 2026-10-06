module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.NormalizationEvents

/-! Deterministic target separation on the normalization good event. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open Set

/-- A legal selected latent vector on the normalization good event produces an
ATE with the hypothesis orientation and at least three quarters of the
calibrated paper separation. -/
lemma latentToLaw_oriented_ate_lower
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (theta : Fin (n - 1) → LatentCell)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (he : ∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1)
    (hgood : normalizationGood n rho h theta) :
    3 * converseC2 * M * rho / (4 * Hrho n rho) ≤
      (if h then 1 else -1) *
        ateTarget
          (latentToLaw n M rho converseKappa (selectedGamma n rho)
            (dualDegree n rho) theta (by omega)
            (by
              unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
            (by linarith) hrho (by unfold converseKappa; norm_num)
            (selectedGamma_mem_Icc n rho hn)) := by
  classical
  have hJ : 0 < dualDegree n rho := by
    unfold dualDegree
    exact lt_of_lt_of_le (by decide) (le_max_left _ _)
  have hM0 : 0 ≤ M := by linarith
  have hkappa : 0 ≤ converseKappa := by
    unfold converseKappa
    norm_num
  have hgamma : selectedGamma n rho ∈ Icc (0 : ℝ) 1 :=
    selectedGamma_mem_Icc n rho hn
  let P := latentToLaw n M rho converseKappa (selectedGamma n rho)
    (dualDegree n rho) theta (by omega) hJ hM0 hrho hkappa hgamma
  have hs : LatentLawSpec n M rho converseKappa (selectedGamma n rho)
      (dualDegree n rho) theta P := by
    dsimp [P]
    unfold latentToLaw
    rw [dif_pos hq, dif_pos he, dif_pos hu]
    exact Classical.choose_spec
      (latentLaw_exists n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta (by omega) hJ hM0 hrho hkappa hgamma hq he hu)
  have hate := latentLawSpec_ateTarget_eq_ratio (by omega : 0 < n) hs
  have hratio := normalizationGood_ratio_lower hn hgood
  have hscale : 0 ≤ M * rho / 4 :=
    div_nonneg (mul_nonneg hM0 hrho.1) (by norm_num)
  change 3 * converseC2 * M * rho / (4 * Hrho n rho) ≤
    (if h then 1 else -1) * ateTarget P
  calc
    3 * converseC2 * M * rho / (4 * Hrho n rho) =
        (M * rho / 4) * (3 * converseC2 / Hrho n rho) := by ring
    _ ≤ (M * rho / 4) *
        (selectedGamma n rho * selectedAlignedScoreTotal n rho h theta /
          selectedRawMassTotal n rho theta) :=
      mul_le_mul_of_nonneg_left hratio hscale
    _ = (if h then 1 else -1) * ateTarget P := by
      rw [hate]
      unfold selectedAlignedScoreTotal selectedRawMassTotal
      ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
