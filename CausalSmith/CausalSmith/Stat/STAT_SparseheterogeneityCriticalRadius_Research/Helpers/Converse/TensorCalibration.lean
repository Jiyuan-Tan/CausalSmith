module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.OneCellTailBound

/-! Numerical and integrability calibration for the product signed-score experiment. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped ENNReal

/-- The retained reference component also supplies the square-integrability
needed by exact iid chi-square tensorization. -/
lemma signedScoreMixtureLaw_intensityPrior_rn_sq_integrable
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J) :
    Integrable (fun z =>
      (((signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D true)).rnDeriv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) z).toReal - 1) ^ 2)
      (signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D false)) := by
  let Q := signedScoreReferenceLaw (kappa * (J : ℝ))
  let piT := signedScoreIntensityPrior kappa gamma rho a J D true
  let piF := signedScoreIntensityPrior kappa gamma rho a J D false
  let LT := signedScoreMixtureLikelihood (kappa * (J : ℝ)) piT
  let LF := signedScoreMixtureLikelihood (kappa * (J : ℝ)) piF
  let P := signedScoreMixtureLaw piT
  let N := signedScoreMixtureLaw piF
  have hrn := signedScoreMixtureLaw_intensityPrior_rnDeriv_toReal_eq
    kappa gamma rho a J D hkappa hgamma hrho ha hJ
  have hN : N = Q.withDensity (fun z => ENNReal.ofReal (LF z)) :=
    signedScoreMixtureLaw_intensityPrior_eq_withDensity
      kappa gamma rho a J D false hkappa hgamma hrho ha hJ
  have hmeasF : Measurable (fun z => ENNReal.ofReal (LF z)) :=
    (signedScoreMixtureLikelihood_measurable _ _).ennreal_ofReal
  have hfiniteF : ∀ᵐ z ∂Q, ENNReal.ofReal (LF z) < ⊤ := by
    filter_upwards [] with z
    exact ENNReal.ofReal_lt_top
  have hsq := signedScoreMixtureLikelihood_sq_sub_integrable_intensityPrior
    kappa gamma rho a J D hkappa ha hJ
  have hJpos : (0 : ℝ) < J := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hquot : Integrable (fun z => (LT z / LF z - 1) ^ 2) N := by
    rw [hN, integrable_withDensity_iff hmeasF hfiniteF]
    have hupper : Integrable (fun z =>
        (J : ℝ) * (LT z - LF z) ^ 2) Q := hsq.const_mul _
    apply hupper.mono'
    · fun_prop
    · filter_upwards [] with z
      have hF0 : 0 ≤ LF z := signedScoreMixtureLikelihood_nonneg _ _ _
        (by positivity) (signedScoreIntensityPrior_ae_nonneg
          kappa gamma rho a J D false hkappa.le hgamma hrho ha)
      have hlower := signedScoreMixtureLikelihood_intensityPrior_lower_bound
        kappa gamma rho a J D false z hkappa hgamma hrho ha hJ
      have hlower' : 1 / (J : ℝ) ≤ LF z := by
        simpa only [ENNReal.toReal_ofReal (one_div_pos.mpr hJpos).le] using hlower
      have hFpos : 0 < LF z := lt_of_lt_of_le (one_div_pos.mpr hJpos) hlower'
      have hpoint : LF z * (LT z / LF z - 1) ^ 2 ≤
          (J : ℝ) * (LT z - LF z) ^ 2 := by
        calc
          LF z * (LT z / LF z - 1) ^ 2 = (LT z - LF z) ^ 2 / LF z := by
            field_simp
          _ ≤ (J : ℝ) * (LT z - LF z) ^ 2 := by
            rw [div_le_iff₀ hFpos]
            have hone : 1 ≤ (J : ℝ) * LF z := by
              simpa only [mul_comm] using (div_le_iff₀ hJpos).mp hlower'
            nlinarith [sq_nonneg (LT z - LF z)]
      rw [ENNReal.toReal_ofReal hF0]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hF0)]
      simpa only [mul_comm] using hpoint
  exact hquot.congr (hrn.fun_comp fun x => (x - 1) ^ 2).symm

/-- The roadmap degree choice makes the tensorized one-cell chi-square
exponent fit the rational `1/200` budget. -/
lemma dualDegree_signedScore_tensor_budget (n : ℕ) (rho : ℝ)
    (hn : 3 ≤ n) (hrho : rho ∈ Icc (0 : ℝ) 2) :
    ((n - 1 : ℕ) : ℝ) *
      (rho ^ 2 * (dualDegree n rho : ℝ) ^ 3 *
        ((1 : ℝ) / 16) ^ dualDegree n rho) ≤ 1 / 200 := by
  let J := dualDegree n rho
  let H := Hrho n rho
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hHarg : 0 < Real.exp 1 + (n : ℝ) * rho ^ 2 := by positivity
  have hHexp : Real.exp H = Real.exp 1 + (n : ℝ) * rho ^ 2 := by
    dsimp [H, Hrho]
    rw [Real.exp_log hHarg]
  have hHone : 1 ≤ H := by
    dsimp [H, Hrho]
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.exp 1 + (n : ℝ) * rho ^ 2) := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact Real.exp_pos _
        · exact hHarg
        · exact le_add_of_nonneg_right (mul_nonneg hn0 (sq_nonneg rho))
  have hJceil : Nat.ceil (64 * H) ≤ J := by
    dsimp [J, dualDegree]
    exact le_max_right _ _
  have hJ64 : 64 * H ≤ (J : ℝ) := by
    exact (Nat.le_ceil (64 * H)).trans (by exact_mod_cast hJceil)
  have hJ64nat : 64 ≤ J := by
    exact_mod_cast (show (64 : ℝ) ≤ J by nlinarith)
  have hnR : ((n - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n 1
  have hnrho : ((n - 1 : ℕ) : ℝ) * rho ^ 2 ≤ Real.exp H := by
    calc
      ((n - 1 : ℕ) : ℝ) * rho ^ 2 ≤ (n : ℝ) * rho ^ 2 :=
        mul_le_mul_of_nonneg_right hnR (sq_nonneg rho)
      _ ≤ Real.exp H := by rw [hHexp]; linarith [Real.exp_pos 1]
  have hexpJ : Real.exp H ≤ (3 : ℝ) ^ J := by
    calc
      Real.exp H ≤ Real.exp ((J : ℝ) / 64) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (Real.exp ((1 : ℝ) / 64)) ^ J := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (3 : ℝ) ^ J := by
        apply pow_le_pow_left₀ (Real.exp_pos _).le
        exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) / 64 ≤ 1)).trans
          Real.exp_one_lt_three.le
  have hcube : ∀ m : ℕ, 2 ≤ m → (m : ℝ) ^ 3 ≤ (4 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
        intro hm
        by_cases hm2 : 2 ≤ m
        · rw [pow_succ]
          calc
            ((m + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * (m : ℝ) ^ 3 := by
              have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
              have hfac : 0 ≤ ((m : ℝ) - 2) *
                  (3 * (m : ℝ) ^ 2 + 3 * m + 3) := by positivity
              push_cast
              nlinarith
            _ ≤ 4 * (4 : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left (ih hm2) (by norm_num)
            _ = (4 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
        · interval_cases m <;> norm_num
  have hcubeJ : (J : ℝ) ^ 3 ≤ (4 : ℝ) ^ J := hcube J (by omega)
  change ((n - 1 : ℕ) : ℝ) *
    (rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) ≤ 1 / 200
  calc
    ((n - 1 : ℕ) : ℝ) *
        (rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) =
        (((n - 1 : ℕ) : ℝ) * rho ^ 2) * (J : ℝ) ^ 3 *
          ((1 : ℝ) / 16) ^ J := by ring
    _ ≤ (3 : ℝ) ^ J * (4 : ℝ) ^ J * ((1 : ℝ) / 16) ^ J := by
      gcongr
      exact hnrho.trans hexpJ
    _ = ((3 : ℝ) / 4) ^ J := by rw [← mul_pow, ← mul_pow]; ring_nf
    _ ≤ ((3 : ℝ) / 4) ^ 64 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ64nat
    _ ≤ 1 / 200 := by norm_num

/-- Equation (68): at the selected degree and intensity, the product count
mixtures for all rare cells have total variation below one quarter. -/
lemma signedScoreProductMixture_intensityPrior_tv_lt_one_quarter
    (n : ℕ) (rho gamma : ℝ) (hn : 3 ≤ n)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    Causalean.Stat.tvDist
      (signedScoreProductMixtureLaw (n - 1)
        (signedScoreIntensityPrior ((1 : ℝ) / 4096) gamma rho
          (dualInterval n rho) (dualDegree n rho) (radiusDual n rho) true))
      (signedScoreProductMixtureLaw (n - 1)
        (signedScoreIntensityPrior ((1 : ℝ) / 4096) gamma rho
          (dualInterval n rho) (dualDegree n rho) (radiusDual n rho) false)) <
      1 / 4 := by
  let kappa : ℝ := 1 / 4096
  let a := dualInterval n rho
  let J := dualDegree n rho
  let D := radiusDual n rho
  let piT := signedScoreIntensityPrior kappa gamma rho a J D true
  let piF := signedScoreIntensityPrior kappa gamma rho a J D false
  have hkappa : 0 < kappa := by norm_num [kappa]
  have hJ : 1 ≤ J := by
    dsimp [J, dualDegree]
    exact le_trans (by norm_num) (le_max_left _ _)
  have ha : 0 < a := by
    dsimp [a, dualInterval]
    positivity
  have hprob (h : Bool) : IsProbabilityMeasure
      (signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D h)) := by
    exact signedScoreMixtureLaw_intensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h hkappa hgamma hrho ha hJ
  letI : IsProbabilityMeasure (signedScoreMixtureLaw piT) := hprob true
  letI : IsProbabilityMeasure (signedScoreMixtureLaw piF) := hprob false
  have hac : signedScoreMixtureLaw piT ≪ signedScoreMixtureLaw piF := by
    exact signedScoreMixtureLaw_intensityPrior_absolutelyContinuous
      kappa gamma rho a J D hkappa hgamma hrho ha hJ
  have hint : Integrable (fun z =>
      (((signedScoreMixtureLaw piT).rnDeriv
        (signedScoreMixtureLaw piF) z).toReal - 1) ^ 2)
      (signedScoreMixtureLaw piF) := by
    exact signedScoreMixtureLaw_intensityPrior_rn_sq_integrable
      kappa gamma rho a J D hkappa hgamma hrho ha hJ
  have hcell : Causalean.Stat.chiSqDiv
      (signedScoreMixtureLaw piT) (signedScoreMixtureLaw piF) ≤
        rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J := by
    simpa only [piT, piF, kappa, a, J, D] using
      signedScoreMixtureLaw_intensityPrior_chiSqDiv_le_concrete
        gamma rho (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) hgamma hrho ha hJ
  have hbudget : ((n - 1 : ℕ) : ℝ) *
      ((1 : ℝ) * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) ≤
        1 / 200 := by
    simpa only [one_mul, J] using dualDegree_signedScore_tensor_budget n rho hn hrho
  have hcal : ((n - 1 : ℕ) : ℝ) *
      ((1 : ℝ) * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) <
        Real.log ((101 : ℝ) / 100) :=
    hbudget.trans_lt one_div_200_lt_log_101_div_100
  change Causalean.Stat.tvDist
      (signedScoreProductMixtureLaw (n - 1) piT)
      (signedScoreProductMixtureLaw (n - 1) piF) < 1 / 4
  exact signedScoreProductMixture_tv_lt_one_quarter
    (n - 1) J piT piF 1 rho hac hint
      (by simpa only [one_mul] using hcell) hcal

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
