module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.ConcentrationMoments
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.NormalizationEvents

/-! Bernstein control of the two coordinates defining the normalization good event. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators

/-- The two one-cell statistics are raw intensity and the hypothesis-oriented signed score. -/
@[no_expose]
noncomputable def normalizationBernsteinStatistic (h : Bool) : Bool → LatentCell → ℝ
  | false => latentIntensity
  | true => fun z => (if h then 1 else -1) * latentSignedScore z

/-- A uniform centered envelope for each normalization coordinate. -/
@[no_expose]
def normalizationBernsteinEnvelope : Bool → ℝ
  | false => 8
  | true => 2

/-- The available one-cell variance proxy for each normalization coordinate. -/
@[no_expose]
noncomputable def normalizationBernsteinVariance (n : ℕ) (rho : ℝ) : Bool → ℝ
  | false => 16 / (dualDegree n rho : ℝ) + dualInterval n rho
  | true => dualInterval n rho

/-- The coordinate sum thresholds whose simultaneous satisfaction implies normalization goodness. -/
@[no_expose]
noncomputable def normalizationBernsteinThreshold (n : ℕ) (rho : ℝ) : Bool → ℝ
  | false => selectedExpectedRawMass n rho /
      (8 * rareScale n (dualDegree n rho) converseKappa)
  | true => converseC2 * selectedExpectedRawMass n rho /
      (4 * Hrho n rho * selectedGamma n rho *
        rareScale n (dualDegree n rho) converseKappa)

/-- The explicit sum of the two Bernstein tails for the selected thresholds. -/
@[no_expose]
noncomputable def normalizationBernsteinRHS (n : ℕ) (rho : ℝ) : ℝ :=
  ∑ j : Bool, 2 * Real.exp
    (-(normalizationBernsteinThreshold n rho j) ^ 2 /
      (2 * (2 * ((n - 1 : ℕ) : ℝ) * normalizationBernsteinVariance n rho j +
        normalizationBernsteinEnvelope j * normalizationBernsteinThreshold n rho j)))

@[no_expose]
noncomputable def normalizationScoreMean (n : ℕ) (rho : ℝ) : ℝ :=
  (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho *
    |dualTargetGap (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)|

lemma dualInterval_abs_dualTargetGap_le_one (n : ℕ) (rho : ℝ) :
    |dualTargetGap (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)| ≤ 1 := by
  have hJ2 : (2 : ℝ) ≤ dualDegree n rho := by
    exact_mod_cast (show 2 ≤ dualDegree n rho by unfold dualDegree; omega)
  have ha : 0 < dualInterval n rho := by unfold dualInterval; positivity
  have ha1 : dualInterval n rho < 1 := by
    unfold dualInterval
    apply (div_lt_one (by positivity)).2
    nlinarith [sq_nonneg ((dualDegree n rho : ℝ) - 2)]
  have hcont : ContinuousOn (rationalTarget (dualInterval n rho))
      (Icc (dualInterval n rho) 1) := by
    apply continuousOn_rationalTarget
    simp only [mem_Icc, not_and]
    intro hzero
    linarith
  rw [abs_dualTargetGap]
  calc
    bestUniformApproxError (rationalTarget (dualInterval n rho))
          (dualInterval n rho) 1 (3 * dualDegree n rho)
        ≤ uniformApproxError (rationalTarget (dualInterval n rho))
            (dualInterval n rho) 1 0 :=
      bestUniformApproxError_le (by simp)
    _ ≤ 1 := by
      unfold uniformApproxError
      apply (intervalSupNorm_le_iff (by simpa using hcont) ha1.le).2
      intro x hx
      simp only [Polynomial.eval_zero, sub_zero]
      unfold rationalTarget
      have hx0 : 0 ≤ x := ha.le.trans hx.1
      have hden0 : 0 ≤ x + dualInterval n rho := add_nonneg hx0 ha.le
      rw [abs_of_nonneg (div_nonneg hx0 hden0)]
      exact (div_le_one (by linarith : 0 < x + dualInterval n rho)).2 (by linarith)

lemma normalizationScoreMean_mem_Icc (n : ℕ) (rho : ℝ) :
    normalizationScoreMean n rho ∈
      Icc (dualInterval n rho / 20000) (dualInterval n rho) := by
  have hJ2 : (2 : ℝ) ≤ dualDegree n rho := by
    exact_mod_cast (show 2 ≤ dualDegree n rho by unfold dualDegree; omega)
  have hJpos : (0 : ℝ) < dualDegree n rho := by positivity
  have ha : 0 < dualInterval n rho := by unfold dualInterval; positivity
  have hscale0 : 0 ≤ 1 - 1 / (dualDegree n rho : ℝ) := by
    rw [sub_nonneg, div_le_one hJpos]
    linarith
  have hscaleLower : (1 / 2 : ℝ) ≤ 1 - 1 / (dualDegree n rho : ℝ) := by
    have hrec : 1 / (dualDegree n rho : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ hJpos).2
      nlinarith
    linarith
  have hscaleUpper : 1 - 1 / (dualDegree n rho : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (dualDegree n rho : ℝ) := by positivity
    linarith
  have hgapLower := dualInterval_abs_dualTargetGap_lower n rho
  have hgapUpper := dualInterval_abs_dualTargetGap_le_one n rho
  unfold normalizationScoreMean
  constructor
  · calc
      dualInterval n rho / 20000 =
          (1 / 2 : ℝ) * dualInterval n rho * (1 / 10000) := by ring
      _ ≤ (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho *
          |dualTargetGap (dualInterval n rho) (dualDegree n rho)
            (radiusDual n rho)| := by gcongr
  · calc
      (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho *
            |dualTargetGap (dualInterval n rho) (dualDegree n rho)
              (radiusDual n rho)|
          ≤ 1 * dualInterval n rho * 1 := by gcongr
      _ = dualInterval n rho := by ring

lemma normalizationBernsteinThreshold_false_eq
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    normalizationBernsteinThreshold n rho false =
      1024 * (n : ℝ) * selectedExpectedRawMass n rho /
        (dualDegree n rho : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hJ0 : (dualDegree n rho : ℝ) ≠ 0 := by
    exact_mod_cast (show dualDegree n rho ≠ 0 by unfold dualDegree; omega)
  simp only [normalizationBernsteinThreshold]
  unfold rareScale converseKappa
  field_simp
  ring

lemma normalizationBernsteinThreshold_true_eq
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    normalizationBernsteinThreshold n rho true =
      ((n - 1 : ℕ) : ℝ) *
        normalizationScoreMean n rho / 16 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hJ0 : (dualDegree n rho : ℝ) ≠ 0 := by
    exact_mod_cast (show dualDegree n rho ≠ 0 by unfold dualDegree; omega)
  have hH0 : Hrho n rho ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho))
  have hm0 : selectedExpectedRawMass n rho ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (selectedExpectedRawMass_mem_Icc n rho hn).1)
  have hs0 : selectedExpectedAlignedScore n rho ≠ 0 :=
    ne_of_gt (selectedExpectedAlignedScore_pos n rho hn)
  have hc0 : converseC2 ≠ 0 := by unfold converseC2; norm_num
  simp only [normalizationBernsteinThreshold]
  unfold selectedGamma selectedExpectedAlignedScore expectedAlignedScoreTotal
    normalizationScoreMean rareScale converseKappa
  field_simp
  ring

lemma normalizationBernstein_score_exponent_lower
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    (n : ℝ) /
        (100000000000000 * (dualDegree n rho : ℝ) ^ 2) ≤
      (normalizationBernsteinThreshold n rho true) ^ 2 /
        (2 * (2 * ((n - 1 : ℕ) : ℝ) *
            normalizationBernsteinVariance n rho true +
          normalizationBernsteinEnvelope true *
            normalizationBernsteinThreshold n rho true)) := by
  let N : ℝ := ((n - 1 : ℕ) : ℝ)
  let J : ℝ := dualDegree n rho
  let a : ℝ := dualInterval n rho
  let m : ℝ := normalizationScoreMean n rho
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < n - 1 by omega)
  have hNlower : (n : ℝ) / 2 ≤ N := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    linarith
  have hJ2 : (2 : ℝ) ≤ J := by
    dsimp [J]
    exact_mod_cast (show 2 ≤ dualDegree n rho by unfold dualDegree; omega)
  have hJ0 : 0 < J := lt_of_lt_of_le (by norm_num) hJ2
  have ha : 0 < a := by dsimp [a, dualInterval]; positivity
  have haeq : a = 1 / (100 * J ^ 2) := by rfl
  have hm := normalizationScoreMean_mem_Icc n rho
  have hmLower : a / 20000 ≤ m := by simpa [a, m] using hm.1
  have hmUpper : m ≤ a := by simpa [a, m] using hm.2
  have hm0 : 0 < m := lt_of_lt_of_le (div_pos ha (by norm_num)) hmLower
  have heta : normalizationBernsteinThreshold n rho true = N * m / 16 := by
    simpa [N, m] using normalizationBernsteinThreshold_true_eq n rho hn
  have heta0 : 0 < normalizationBernsteinThreshold n rho true := by
    rw [heta]
    positivity
  have hetaUpper : normalizationBernsteinThreshold n rho true ≤ N * a / 16 := by
    rw [heta]
    gcongr
  have hden0 : 0 < 2 * (2 * N * a +
      2 * normalizationBernsteinThreshold n rho true) := by positivity
  rw [normalizationBernsteinVariance, normalizationBernsteinEnvelope]
  change (n : ℝ) / (100000000000000 * J ^ 2) ≤
    (normalizationBernsteinThreshold n rho true) ^ 2 /
      (2 * (2 * N * a + 2 * normalizationBernsteinThreshold n rho true))
  rw [le_div_iff₀ hden0]
  calc
    (n : ℝ) / (100000000000000 * J ^ 2) *
          (2 * (2 * N * a + 2 * normalizationBernsteinThreshold n rho true))
        ≤ (n : ℝ) / (100000000000000 * J ^ 2) *
            (17 * N * a / 4) := by
          gcongr
          nlinarith
    _ ≤ (N * m / 16) ^ 2 := by
      calc
        (n : ℝ) / (100000000000000 * J ^ 2) * (17 * N * a / 4)
            ≤ (N * (a / 20000) / 16) ^ 2 := by
              rw [haeq]
              field_simp
              nlinarith
        _ ≤ (N * m / 16) ^ 2 := by
          have : 0 ≤ N * (a / 20000) / 16 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hmLower hN0.le]
    _ = (normalizationBernsteinThreshold n rho true) ^ 2 := by rw [heta]

lemma normalizationBernstein_mass_exponent_lower
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    (n : ℝ) /
        (100000000000000 * (dualDegree n rho : ℝ) ^ 2) ≤
      (normalizationBernsteinThreshold n rho false) ^ 2 /
        (2 * (2 * ((n - 1 : ℕ) : ℝ) *
            normalizationBernsteinVariance n rho false +
          normalizationBernsteinEnvelope false *
            normalizationBernsteinThreshold n rho false)) := by
  let N : ℝ := ((n - 1 : ℕ) : ℝ)
  let J : ℝ := dualDegree n rho
  let a : ℝ := dualInterval n rho
  let E : ℝ := selectedExpectedRawMass n rho
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hNupper : N ≤ (n : ℝ) := by
    dsimp [N]
    exact_mod_cast Nat.sub_le n 1
  have hJ2 : (2 : ℝ) ≤ J := by
    dsimp [J]
    exact_mod_cast (show 2 ≤ dualDegree n rho by unfold dualDegree; omega)
  have hJ0 : 0 < J := lt_of_lt_of_le (by norm_num) hJ2
  have ha : 0 < a := by dsimp [a, dualInterval]; positivity
  have haeq : a = 1 / (100 * J ^ 2) := by rfl
  have hE := selectedExpectedRawMass_mem_Icc n rho hn
  have hE1 : 1 ≤ E := by simpa [E] using hE.1
  have hE2 : E ≤ 2 := by simpa [E] using hE.2
  have heta : normalizationBernsteinThreshold n rho false =
      1024 * (n : ℝ) * E / J := by
    simpa [J, E] using normalizationBernsteinThreshold_false_eq n rho hn
  have hetaLower : 1024 * (n : ℝ) / J ≤
      normalizationBernsteinThreshold n rho false := by
    rw [heta]
    apply (div_le_div_iff_of_pos_right hJ0).2
    nlinarith
  have hetaUpper : normalizationBernsteinThreshold n rho false ≤
      2048 * (n : ℝ) / J := by
    rw [heta]
    apply (div_le_div_iff_of_pos_right hJ0).2
    nlinarith
  have heta0 : 0 < normalizationBernsteinThreshold n rho false :=
    lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hnR) hJ0) hetaLower
  have hva : 16 / J + a ≤ 17 / J := by
    rw [haeq]
    field_simp
    nlinarith
  have hden0 : 0 < 2 * (2 * N * (16 / J + a) +
      8 * normalizationBernsteinThreshold n rho false) := by positivity
  rw [normalizationBernsteinVariance, normalizationBernsteinEnvelope]
  change (n : ℝ) / (100000000000000 * J ^ 2) ≤
    (normalizationBernsteinThreshold n rho false) ^ 2 /
      (2 * (2 * N * (16 / J + a) +
        8 * normalizationBernsteinThreshold n rho false))
  rw [le_div_iff₀ hden0]
  calc
    (n : ℝ) / (100000000000000 * J ^ 2) *
          (2 * (2 * N * (16 / J + a) +
            8 * normalizationBernsteinThreshold n rho false))
        ≤ (n : ℝ) / (100000000000000 * J ^ 2) *
            (32836 * (n : ℝ) / J) := by
          gcongr
          have hvar0 : 0 ≤ 16 / J + a := by positivity
          have hNv : N * (16 / J + a) ≤ (n : ℝ) * (17 / J) := by
            calc
              N * (16 / J + a) ≤ (n : ℝ) * (16 / J + a) := by gcongr
              _ ≤ (n : ℝ) * (17 / J) := by gcongr
          calc
            2 * (2 * N * (16 / J + a) +
                  8 * normalizationBernsteinThreshold n rho false)
                ≤ 2 * (2 * ((n : ℝ) * (17 / J)) +
                  8 * (2048 * (n : ℝ) / J)) := by
                    linarith
            _ = 32836 * (n : ℝ) / J := by ring
    _ ≤ (1024 * (n : ℝ) / J) ^ 2 := by
      field_simp
      nlinarith
    _ ≤ (normalizationBernsteinThreshold n rho false) ^ 2 := by
      gcongr

theorem normalizationBernsteinRHS_le_exp
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    normalizationBernsteinRHS n rho ≤
      4 * Real.exp (-(n : ℝ) /
        (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) := by
  have hfalse :
      Real.exp
          (-(normalizationBernsteinThreshold n rho false) ^ 2 /
            (2 * (2 * ((n - 1 : ℕ) : ℝ) *
                normalizationBernsteinVariance n rho false +
              normalizationBernsteinEnvelope false *
                normalizationBernsteinThreshold n rho false))) ≤
        Real.exp (-(n : ℝ) /
          (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have h := normalizationBernstein_mass_exponent_lower n rho hn
    simpa only [neg_div] using neg_le_neg h
  have htrue :
      Real.exp
          (-(normalizationBernsteinThreshold n rho true) ^ 2 /
            (2 * (2 * ((n - 1 : ℕ) : ℝ) *
                normalizationBernsteinVariance n rho true +
              normalizationBernsteinEnvelope true *
                normalizationBernsteinThreshold n rho true))) ≤
        Real.exp (-(n : ℝ) /
          (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have h := normalizationBernstein_score_exponent_lower n rho hn
    simpa only [neg_div] using neg_le_neg h
  rw [normalizationBernsteinRHS, Fintype.sum_bool]
  nlinarith

/-- Failure of normalization is contained in one of the two coordinatewise sum-deviation events. -/
lemma normalizationGood_compl_subset_bernsteinEvent
    (n : ℕ) (rho : ℝ) (h : Bool) (hn : 3 ≤ n) :
    {theta : Fin (n - 1) → LatentCell | ¬ normalizationGood n rho h theta} ⊆
      {theta | ∃ j : Bool, normalizationBernsteinThreshold n rho j ≤
        |(∑ i, normalizationBernsteinStatistic h j (theta i)) -
          ((n - 1 : ℕ) : ℝ) *
            ∫ z, normalizationBernsteinStatistic h j z
              ∂oneCellPrior (dualInterval n rho) (dualDegree n rho)
                (radiusDual n rho)
                (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
                  (radiusDual n rho) h)|} := by
  intro theta hbad
  have hnpos : 0 < n := by omega
  have hJpos : 0 < dualDegree n rho := by
    unfold dualDegree
    omega
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    positivity
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    omega
  have hr : 0 < rareScale n (dualDegree n rho) converseKappa := by
    unfold rareScale converseKappa
    positivity
  have hgamma : 0 < selectedGamma n rho := selectedGamma_pos n rho hn
  have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
  have hc : 0 < converseC2 := by unfold converseC2; norm_num
  have hmass : 0 < selectedExpectedRawMass n rho :=
    lt_of_lt_of_le zero_lt_one (selectedExpectedRawMass_mem_Icc n rho hn).1
  simp only [normalizationGood, not_and_or, not_le] at hbad
  rcases hbad with hbad | hbad
  · refine ⟨false, ?_⟩
    simp only [normalizationBernsteinThreshold, normalizationBernsteinStatistic,
      Bool.false_eq_true, ↓reduceIte]
    rw [oneCellPrior_integral_latentIntensity _ _ _ _ ha hJ]
    have hid :
        selectedRawMassTotal n rho theta - selectedExpectedRawMass n rho =
          rareScale n (dualDegree n rho) converseKappa *
            ((∑ i, latentIntensity (theta i)) -
              ((n - 1 : ℕ) : ℝ) *
                (4 / (dualDegree n rho : ℝ) +
                  (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho)) := by
      unfold selectedRawMassTotal selectedExpectedRawMass expectedRawMassTotal
      rw [rawMassTotal_eq_one_add_sum n (dualDegree n rho) converseKappa theta hnpos]
      ring
    rw [hid, abs_mul, abs_of_pos hr] at hbad
    apply (div_le_iff₀ (mul_pos (by norm_num) hr)).2
    nlinarith
  · refine ⟨true, ?_⟩
    simp only [normalizationBernsteinThreshold, normalizationBernsteinStatistic,
      ↓reduceIte]
    rw [integral_const_mul,
      oneCellPrior_integral_oriented_latentSignedScore _ _ _ h ha hJ]
    have hid :
        selectedGamma n rho * selectedAlignedScoreTotal n rho h theta -
            selectedGamma n rho * selectedExpectedAlignedScore n rho =
          (selectedGamma n rho *
              rareScale n (dualDegree n rho) converseKappa) *
            ((∑ i, (if h then 1 else -1) * latentSignedScore (theta i)) -
              ((n - 1 : ℕ) : ℝ) *
                ((if h then 1 else -1) *
                  ((if h then 1 else -1) *
                    (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho *
                      |dualTargetGap (dualInterval n rho) (dualDegree n rho)
                        (radiusDual n rho)|))) := by
      unfold selectedAlignedScoreTotal selectedExpectedAlignedScore
        expectedAlignedScoreTotal rawSignedScoreTotal
      cases h
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [neg_one_mul, Finset.sum_neg_distrib]
        ring
      · simp only [↓reduceIte]
        ring
    rw [hid, abs_mul, abs_of_pos (mul_pos hgamma hr)] at hbad
    let X : ℝ :=
      (∑ i, (if h then 1 else -1) * latentSignedScore (theta i)) -
        ((n - 1 : ℕ) : ℝ) *
          ((if h then 1 else -1) *
            ((if h then 1 else -1) *
              (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho *
                |dualTargetGap (dualInterval n rho) (dualDegree n rho)
                  (radiusDual n rho)|))
    change converseC2 * selectedExpectedRawMass n rho /
      (4 * Hrho n rho * selectedGamma n rho *
        rareScale n (dualDegree n rho) converseKappa) ≤ |X|
    change converseC2 * selectedExpectedRawMass n rho / (4 * Hrho n rho) <
      selectedGamma n rho * rareScale n (dualDegree n rho) converseKappa * |X|
      at hbad
    have hfourH : 0 < 4 * Hrho n rho := mul_pos (by norm_num) hH
    apply (div_le_iff₀
      (mul_pos (mul_pos hfourH hgamma) hr)).2
    calc
      converseC2 * selectedExpectedRawMass n rho
          ≤ (4 * Hrho n rho) *
              ((selectedGamma n rho * rareScale n (dualDegree n rho) converseKappa) * |X|) :=
            by
              simpa only [mul_assoc, mul_left_comm, mul_comm] using
                le_of_lt ((div_lt_iff₀ hfourH).mp hbad)
      _ = |X| *
              (4 * Hrho n rho * selectedGamma n rho *
                rareScale n (dualDegree n rho) converseKappa) := by ring

/-- The selected product prior obeys the exact two-coordinate Bernstein union bound. -/
theorem selectedLatentPrior_normalizationBernstein
    (n : ℕ) (rho : ℝ) (h : Bool) (hn : 3 ≤ n) :
    (selectedLatentPrior n rho h).real
        {theta | ∃ j : Bool, normalizationBernsteinThreshold n rho j ≤
          |(∑ i, normalizationBernsteinStatistic h j (theta i)) -
            ((n - 1 : ℕ) : ℝ) *
              ∫ z, normalizationBernsteinStatistic h j z
                ∂oneCellPrior (dualInterval n rho) (dualDegree n rho)
                  (radiusDual n rho)
                  (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
                    (radiusDual n rho) h)|} ≤
      normalizationBernsteinRHS n rho := by
  let a := dualInterval n rho
  let J := dualDegree n rho
  let D := radiusDual n rho
  let ho := orientedHypothesis a J D h
  let P := oneCellPrior a J D ho
  have hJpos : 0 < dualDegree n rho := by unfold dualDegree; omega
  have ha : 0 < a := by dsimp [a, dualInterval]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a, dualInterval]
    have hJ2 : (2 : ℝ) ≤ dualDegree n rho := by
      exact_mod_cast (show 2 ≤ dualDegree n rho by unfold dualDegree; omega)
    apply (div_le_one (by positivity : (0 : ℝ) < 100 * (dualDegree n rho : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((dualDegree n rho : ℝ) - 2)]
  have hJ : 1 ≤ J := by dsimp [J, dualDegree]; omega
  letI : IsProbabilityMeasure P := oneCellPrior_isProbabilityMeasure a J D ho ha hJ
  have hgmeas : ∀ j, Measurable (normalizationBernsteinStatistic h j) := by
    intro j
    cases j <;> simp only [normalizationBernsteinStatistic]
    · exact latentIntensity_stronglyMeasurable.measurable
    · exact (stronglyMeasurable_const.mul latentSignedScore_stronglyMeasurable).measurable
  have hgint : ∀ j, Integrable (normalizationBernsteinStatistic h j) P := by
    intro j
    apply Integrable.of_bound (hgmeas j).aestronglyMeasurable 4
    cases j
    · filter_upwards [oneCellPrior_ae_latentIntensity_mem_Icc a J D ho ha ha1 hJ] with z hz
      simpa only [Real.norm_eq_abs, normalizationBernsteinStatistic,
        Bool.false_eq_true, ↓reduceIte,
        abs_of_nonneg hz.1] using hz.2
    · filter_upwards [oneCellPrior_ae_abs_latentSignedScore_le a J D ho ha ha1 hJ] with z hz
      simp only [Real.norm_eq_abs, normalizationBernsteinStatistic, ↓reduceIte, abs_mul]
      have hs : |(if h then (1 : ℝ) else -1)| = 1 := by cases h <;> simp
      rw [hs, one_mul]
      linarith
  have hb : ∀ j, 0 ≤ normalizationBernsteinEnvelope j := by
    intro j; cases j <;> norm_num [normalizationBernsteinEnvelope]
  have hsigma : ∀ j, 0 ≤ normalizationBernsteinVariance n rho j := by
    intro j; cases j <;> simp only [normalizationBernsteinVariance] <;> positivity
  have heta : ∀ j, 0 < normalizationBernsteinThreshold n rho j := by
    intro j
    have hr : 0 < rareScale n (dualDegree n rho) converseKappa := by
      unfold rareScale converseKappa
      positivity
    have hm : 0 < selectedExpectedRawMass n rho :=
      lt_of_lt_of_le zero_lt_one (selectedExpectedRawMass_mem_Icc n rho hn).1
    cases j
    · simp only [normalizationBernsteinThreshold]
      positivity
    · simp only [normalizationBernsteinThreshold]
      have hc : 0 < converseC2 := by unfold converseC2; norm_num
      have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
      have hgamma := selectedGamma_pos n rho hn
      positivity
  have henvelope : ∀ j, ∀ᵐ z ∂P,
      |normalizationBernsteinStatistic h j z -
          ∫ y, normalizationBernsteinStatistic h j y ∂P| ≤
        normalizationBernsteinEnvelope j := by
    intro j
    cases j
    · simp only [normalizationBernsteinStatistic, Bool.false_eq_true, ↓reduceIte,
        normalizationBernsteinEnvelope]
      rw [show P = oneCellPrior a J D ho from rfl,
        oneCellPrior_integral_latentIntensity a J D ho ha hJ]
      filter_upwards [oneCellPrior_ae_latentIntensity_mem_Icc a J D ho ha ha1 hJ] with z hz
      have hm0 : 0 ≤ 4 / (J : ℝ) + (1 - 1 / (J : ℝ)) * a := by
        have hscale0 : 0 ≤ 1 - 1 / (J : ℝ) := by
          rw [sub_nonneg, div_le_iff₀ (by positivity)]
          simpa only [one_mul] using (show (1 : ℝ) ≤ J by exact_mod_cast hJ)
        positivity
      have hm4 : 4 / (J : ℝ) + (1 - 1 / (J : ℝ)) * a ≤ 4 := by
        have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
        have hrec : 1 / (J : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hJr
        have hscale0 : 0 ≤ 1 - 1 / (J : ℝ) := sub_nonneg.mpr hrec
        have hmul : (1 - 1 / (J : ℝ)) * a ≤
            (1 - 1 / (J : ℝ)) * 4 :=
          mul_le_mul_of_nonneg_left (ha1.trans (by norm_num)) hscale0
        calc
          4 / (J : ℝ) + (1 - 1 / (J : ℝ)) * a
              ≤ 4 / (J : ℝ) + (1 - 1 / (J : ℝ)) * 4 :=
                add_le_add_right hmul _
          _ = 4 := by ring
      exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    · have hmeanAbs : |∫ y, normalizationBernsteinStatistic h true y ∂P| ≤ 1 := by
        calc
          |∫ y, normalizationBernsteinStatistic h true y ∂P|
              ≤ ∫ y, |normalizationBernsteinStatistic h true y| ∂P :=
                abs_integral_le_integral_abs
          _ ≤ ∫ _y, (1 : ℝ) ∂P := by
            apply integral_mono_ae (hgint true).abs (integrable_const 1)
            filter_upwards [oneCellPrior_ae_abs_latentSignedScore_le a J D ho ha ha1 hJ] with z hz
            simp only [normalizationBernsteinStatistic, ↓reduceIte, abs_mul]
            have hs : |(if h then (1 : ℝ) else -1)| = 1 := by cases h <;> simp
            rw [hs, one_mul]
            exact hz
          _ = 1 := by simp
      filter_upwards [oneCellPrior_ae_abs_latentSignedScore_le a J D ho ha ha1 hJ] with z hz
      simp only [normalizationBernsteinStatistic, ↓reduceIte,
        normalizationBernsteinEnvelope]
      calc
        |(if h then 1 else -1) * latentSignedScore z -
            ∫ y, (if h then 1 else -1) * latentSignedScore y ∂P|
            ≤ |(if h then 1 else -1) * latentSignedScore z| +
                |∫ y, (if h then 1 else -1) * latentSignedScore y ∂P| :=
              abs_sub _ _
        _ ≤ 2 := by
          have hs : |(if h then (1 : ℝ) else -1)| = 1 := by cases h <;> simp
          rw [abs_mul, hs, one_mul]
          change |∫ y, (if h then (1 : ℝ) else -1) * latentSignedScore y ∂P| ≤ 1 at hmeanAbs
          linarith
  have hvariance : ∀ j,
      ∫ z, (normalizationBernsteinStatistic h j z -
        ∫ y, normalizationBernsteinStatistic h j y ∂P) ^ 2 ∂P ≤
          normalizationBernsteinVariance n rho j := by
    intro j
    cases j
    · simpa only [normalizationBernsteinStatistic, Bool.false_eq_true, ↓reduceIte,
        normalizationBernsteinVariance, P, a, J, D, ho] using
        oneCellPrior_integral_centered_latentIntensity_sq_le a J D ho ha ha1 hJ
    · have hs : (if h then (1 : ℝ) else -1) ^ 2 = 1 := by cases h <;> norm_num
      have hint :
          (∫ y, (if h then (1 : ℝ) else -1) * latentSignedScore y ∂P) =
            (if h then 1 else -1) * ∫ y, latentSignedScore y ∂P := by
        rw [integral_const_mul]
      simp only [normalizationBernsteinStatistic, ↓reduceIte,
        normalizationBernsteinVariance, hint]
      have hpoint : ∀ z,
          ((if h then (1 : ℝ) else -1) * latentSignedScore z -
              (if h then 1 else -1) * ∫ y, latentSignedScore y ∂P) ^ 2 =
            (latentSignedScore z - ∫ y, latentSignedScore y ∂P) ^ 2 := by
        intro z
        rw [← mul_sub, mul_pow, hs, one_mul]
      simp_rw [hpoint]
      simpa only [P, a, J, D, ho] using
        oneCellPrior_integral_centered_latentSignedScore_sq_le a J D ho ha ha1 hJ
  simpa only [selectedLatentPrior, latentProductPrior, normalizationBernsteinRHS,
      a, J, D, ho, P] using
    (Causalean.Stat.Concentration.iid_sum_bernstein_union_bound
      (N := n - 1) P (normalizationBernsteinStatistic h) hgmeas hgint
      normalizationBernsteinEnvelope (normalizationBernsteinVariance n rho)
      (normalizationBernsteinThreshold n rho) hb hsigma heta (by omega)
      henvelope hvariance)

/-- The probability that the selected latent draw fails normalization goodness is bounded by
the explicit two-coordinate Bernstein right-hand side. -/
theorem selectedLatentPrior_normalizationGood_compl_le_bernstein
    (n : ℕ) (rho : ℝ) (h : Bool) (hn : 3 ≤ n) :
    (selectedLatentPrior n rho h).real
        {theta | ¬ normalizationGood n rho h theta} ≤
      normalizationBernsteinRHS n rho := by
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have : 0 < dualDegree n rho := by unfold dualDegree; omega
    positivity
  have hJ : 1 ≤ dualDegree n rho := by unfold dualDegree; omega
  letI : IsProbabilityMeasure
      (oneCellPrior (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) h)) :=
    oneCellPrior_isProbabilityMeasure _ _ _ _ ha hJ
  letI : IsProbabilityMeasure (selectedLatentPrior n rho h) := by
    unfold selectedLatentPrior latentProductPrior
    infer_instance
  calc
    (selectedLatentPrior n rho h).real
          {theta | ¬ normalizationGood n rho h theta}
        ≤ (selectedLatentPrior n rho h).real
          {theta | ∃ j : Bool, normalizationBernsteinThreshold n rho j ≤
            |(∑ i, normalizationBernsteinStatistic h j (theta i)) -
              ((n - 1 : ℕ) : ℝ) *
                ∫ z, normalizationBernsteinStatistic h j z
                  ∂oneCellPrior (dualInterval n rho) (dualDegree n rho)
                    (radiusDual n rho)
                    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
                      (radiusDual n rho) h)|} :=
            measureReal_mono
              (normalizationGood_compl_subset_bernsteinEvent n rho h hn)
              (measure_ne_top _ _)
    _ ≤ normalizationBernsteinRHS n rho :=
      selectedLatentPrior_normalizationBernstein n rho h hn

theorem selectedLatentPrior_normalizationGood_compl_le_exp
    (n : ℕ) (rho : ℝ) (h : Bool) (hn : 3 ≤ n) :
    (selectedLatentPrior n rho h).real
        {theta | ¬ normalizationGood n rho h theta} ≤
      4 * Real.exp (-(n : ℝ) /
        (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) :=
  (selectedLatentPrior_normalizationGood_compl_le_bernstein n rho h hn).trans
    (normalizationBernsteinRHS_le_exp n rho hn)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
