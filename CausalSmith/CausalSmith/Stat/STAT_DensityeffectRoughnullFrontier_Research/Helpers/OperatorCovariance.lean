module
public import Causalean.Stat.LinearModel.GaussMarkov.Variance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.BandRemainderNorms
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainSquareIntegrability
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyMoments

/-! Covariance quadratic forms are scalar variances. Orthogonal histogram bands
turn the multiband form envelope into the public operator-norm allowance (18). -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The observed chain covariance form equals the variance of its scalar contrast. -/
-- @node: contrastCovariance_form_eq_variance
lemma contrastCovariance_form_eq_variance (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) :
    covarianceForm (contrastCovariance P train mx my L T J q kt) f =
      variance (fun eval => inner ℝ (coefficientChain train mx my L T J q kt eval 0) f)
        (evalLaw P m) := by
  letI : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hLp := memLp_coefficientChain P train mx my L T J q kt 0 2
  have hmean (i : Fin J) := hilbert_energy_coordinate_mean
    (hLp.integrable (by norm_num)) i
  have h := Causalean.Stat.GaussMarkov.variance_linearCombination
    (fun i eval => coefficientChain train mx my L T J q kt eval 0 i)
    (fun i => hilbert_energy_coordinate_memLp hLp i) (fun i => f i)
  have hcov : Causalean.Stat.GaussMarkov.covMatrix
      (fun i eval => coefficientChain train mx my L T J q kt eval 0 i)
      (evalLaw P m) = contrastCovariance P train mx my L T J q kt := by
    funext i j
    simp only [Causalean.Stat.GaussMarkov.covMatrix, covariance, hmean,
      contrastCovariance, contrastMean]
  rw [hcov] at h
  symm
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Causalean.Stat.GaussMarkov.quadVar, dotProduct, Matrix.mulVec,
    Finset.mul_sum, covarianceForm, mul_assoc, mul_left_comm, mul_comm] using h

/-- Covariance forms of the observable coefficient chain are nonnegative. -/
-- @node: contrastCovariance_form_nonneg
lemma contrastCovariance_form_nonneg (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) :
    0 ≤ covarianceForm (contrastCovariance P train mx my L T J q kt) f := by
  rw [contrastCovariance_form_eq_variance]
  exact variance_nonneg _ _

/-- The squared norms of all dyadic bands sum to the test vector's squared norm. -/
-- @node: sum_band_norm_sq
lemma sum_band_norm_sq (L T : ℕ) (hL : Dyadic L) (f : Hj (2 ^ T * L)) :
    ∑ t ∈ Finset.range (T + 1), ‖Qband L (2 ^ T * L) t f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← band_remainder_sum_norm_sq L T hL _
    (fun t ht => by have := Finset.mem_range.mp ht; omega) (fun _ => f),
    sum_Qband_eq_self]

/-- Weighting orthogonal bands by their largest rank bounds the multiband energy. -/
-- @node: weighted_band_norm_sq_le
lemma weighted_band_norm_sq_le (L T : ℕ) (hL : Dyadic L) (kt : ℕ → ℕ)
    (f : Hj (2 ^ T * L)) :
    ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 ≤
      (((Finset.range (T + 1)).sup kt : ℕ) : ℝ) * ‖f‖ ^ 2 := by
  calc
    _ ≤ ∑ t ∈ Finset.range (T + 1),
        (((Finset.range (T + 1)).sup kt : ℕ) : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast Finset.le_sup ht
    _ = _ := by rw [← Finset.mul_sum, sum_band_norm_sq L T hL]

/-- A nonnegative covariance form with the multiband envelope satisfies (18). -/
-- @node: covarianceOpNorm_le_WAllow_of_multiband
lemma covarianceOpNorm_le_WAllow_of_multiband (C : ℝ) (hC : 0 ≤ C)
    (m L T : ℕ) (hm : 1 ≤ m) (hL : Dyadic L) (kt : ℕ → ℕ)
    (sigma : Matrix (Fin (2 ^ T * L)) (Fin (2 ^ T * L)) ℝ)
    (hnon : ∀ f : Hj (2 ^ T * L), 0 ≤ covarianceForm sigma f)
    (hform : ∀ f : Hj (2 ^ T * L), covarianceForm sigma f ≤
      C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
        ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2)) :
    covarianceOpNorm sigma ≤ WAllow C m T kt := by
  have hm0 : m ≠ 0 := by omega
  have hW : 0 ≤ WAllow C m T kt := by simp only [WAllow, if_neg hm0]; positivity
  apply csSup_le
  · exact ⟨0, 0, by simp, by simp [covarianceForm]⟩
  · rintro r ⟨f, hf, rfl⟩
    rw [abs_of_nonneg (hnon f)]
    calc
      _ ≤ C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
          (((Finset.range (T + 1)).sup kt : ℕ) : ℝ) * ‖f‖ ^ 2) := by
        apply (hform f).trans
        apply mul_le_mul_of_nonneg_left _ hC
        apply add_le_add_right
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (weighted_band_norm_sq_le L T hL kt f) (by positivity : 0 ≤ (m : ℝ) ^ (-2 : ℤ))
      _ = WAllow C m T kt * ‖f‖ ^ 2 := by simp only [WAllow, if_neg hm0]; ring
      _ ≤ WAllow C m T kt := by
        apply mul_le_of_le_one_right hW
        simpa using (sq_le_sq₀ (norm_nonneg f) (by norm_num : (0 : ℝ) ≤ 1)).2 hf

end CausalSmith.Stat.DensityEffectRoughNull
