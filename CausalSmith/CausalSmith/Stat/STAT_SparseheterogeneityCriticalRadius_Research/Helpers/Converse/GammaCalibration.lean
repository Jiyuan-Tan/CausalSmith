module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.ProductCalibration

/-! Numerical calibration of the shared-design effect multiplier. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open Set

noncomputable def converseKappa : ℝ := 1 / 4096

noncomputable def converseC2 : ℝ := 1 / 100000000000000000000

noncomputable def selectedExpectedRawMass (n : ℕ) (rho : ℝ) : ℝ :=
  expectedRawMassTotal n (dualDegree n rho) converseKappa (dualInterval n rho)

noncomputable def selectedExpectedAlignedScore (n : ℕ) (rho : ℝ) : ℝ :=
  expectedAlignedScoreTotal n (dualDegree n rho) converseKappa
    (dualInterval n rho) (radiusDual n rho)

noncomputable def selectedGamma (n : ℕ) (rho : ℝ) : ℝ :=
  4 * converseC2 * selectedExpectedRawMass n rho /
    (Hrho n rho * selectedExpectedAlignedScore n rho)

lemma Hrho_one_le (n : ℕ) (rho : ℝ) : 1 ≤ Hrho n rho := by
  unfold Hrho
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.exp 1 + (n : ℝ) * rho ^ 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Real.exp_pos _
      · exact add_pos_of_pos_of_nonneg (Real.exp_pos _)
          (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg rho))
      · exact le_add_of_nonneg_right
          (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg rho))

lemma dualDegree_le_sixtyFive_mul_Hrho (n : ℕ) (rho : ℝ) :
    (dualDegree n rho : ℝ) ≤ 65 * Hrho n rho := by
  have hH := Hrho_one_le n rho
  have hceil : (Nat.ceil (64 * Hrho n rho) : ℝ) < 64 * Hrho n rho + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  unfold dualDegree
  rw [Nat.cast_max, max_le_iff]
  constructor
  · norm_num
    linarith
  · linarith

lemma selectedExpectedRawMass_mem_Icc (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    selectedExpectedRawMass n rho ∈ Set.Icc (1 : ℝ) 2 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ : 2 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_max_left _ _
  have hJR : (2 : ℝ) ≤ dualDegree n rho := by exact_mod_cast hJ
  have hnsub : ((n - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n 1
  have hbracket_nonneg :
      0 ≤ 4 / (dualDegree n rho : ℝ) +
        (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho := by
    have : 0 ≤ 1 - 1 / (dualDegree n rho : ℝ) := by
      rw [sub_nonneg, div_le_iff₀ (by positivity)]
      linarith
    have ha : 0 ≤ dualInterval n rho := by
      unfold dualInterval
      positivity
    exact add_nonneg (by positivity) (mul_nonneg this ha)
  have hbracket_upper :
      (dualDegree n rho : ℝ) *
          (4 / (dualDegree n rho : ℝ) +
            (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho) ≤ 5 := by
    unfold dualInterval
    have hJpos : (0 : ℝ) < dualDegree n rho := by positivity
    have hunit : 0 ≤ 1 - 1 / (dualDegree n rho : ℝ) := by
      rw [sub_nonneg, div_le_iff₀ hJpos]
      linarith
    have hunit_le : 1 - 1 / (dualDegree n rho : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (dualDegree n rho : ℝ) := by positivity
      linarith
    field_simp
    nlinarith [sq_nonneg ((dualDegree n rho : ℝ) - 2)]
  unfold selectedExpectedRawMass expectedRawMassTotal
  change 1 ≤ 1 + rareScale n (dualDegree n rho) converseKappa *
        ((n - 1 : ℕ) : ℝ) *
        (4 / (dualDegree n rho : ℝ) +
          (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho) ∧
      1 + rareScale n (dualDegree n rho) converseKappa *
        ((n - 1 : ℕ) : ℝ) *
        (4 / (dualDegree n rho : ℝ) +
          (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho) ≤ 2
  constructor
  · have : 0 ≤ rareScale n (dualDegree n rho) converseKappa := by
      unfold rareScale converseKappa
      positivity
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg this (Nat.cast_nonneg _)) hbracket_nonneg)
  · unfold rareScale converseKappa
    have hnpos : (0 : ℝ) < n := by linarith
    have hnratio : ((n - 1 : ℕ) : ℝ) / n ≤ 1 :=
      (div_le_one hnpos).2 hnsub
    have hprod :
        (((n - 1 : ℕ) : ℝ) / n) *
            ((dualDegree n rho : ℝ) *
              (4 / (dualDegree n rho : ℝ) +
                (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho)) ≤ 5 := by
      calc
        (((n - 1 : ℕ) : ℝ) / n) *
              ((dualDegree n rho : ℝ) *
                (4 / (dualDegree n rho : ℝ) +
                  (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho))
            ≤ 1 * ((dualDegree n rho : ℝ) *
                (4 / (dualDegree n rho : ℝ) +
                  (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho)) := by
              gcongr
        _ ≤ 5 := by simpa using hbracket_upper
    have heq :
        (1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * n) *
              ((n - 1 : ℕ) : ℝ) *
              (4 / (dualDegree n rho : ℝ) +
                (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho) =
          (1 / 4096) / 2 *
            ((((n - 1 : ℕ) : ℝ) / n) *
              ((dualDegree n rho : ℝ) *
                (4 / (dualDegree n rho : ℝ) +
                  (1 - 1 / (dualDegree n rho : ℝ)) * dualInterval n rho))) := by
      field_simp
    rw [heq]
    nlinarith

lemma selectedExpectedAlignedScore_pos (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    0 < selectedExpectedAlignedScore n rho := by
  have hJ : 2 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_max_left _ _
  have hgap := dualInterval_abs_dualTargetGap_lower n rho
  unfold selectedExpectedAlignedScore expectedAlignedScoreTotal rareScale
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnsub : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hJpos : (0 : ℝ) < dualDegree n rho := by positivity
  have hfactor : 0 < 1 - 1 / (dualDegree n rho : ℝ) := by
    rw [sub_pos, div_lt_one hJpos]
    exact_mod_cast hJ
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    positivity
  unfold converseKappa
  positivity

lemma selectedExpectedAlignedScore_lower (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    converseKappa /
        (8000000 * (dualDegree n rho : ℝ)) ≤
      selectedExpectedAlignedScore n rho := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsub : ((n - 1 : ℕ) : ℝ) ≥ (2 / 3 : ℝ) * n := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    linarith
  have hJ : 2 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_max_left _ _
  have hJR : (2 : ℝ) ≤ dualDegree n rho := by exact_mod_cast hJ
  have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / (dualDegree n rho : ℝ) := by
    have hrecip : 1 / (dualDegree n rho : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < dualDegree n rho)).2
      nlinarith
    linarith
  have hgap := dualInterval_abs_dualTargetGap_lower n rho
  unfold selectedExpectedAlignedScore expectedAlignedScoreTotal rareScale
  unfold dualInterval converseKappa
  have hnpos : (0 : ℝ) < n := by linarith
  have hJpos : (0 : ℝ) < dualDegree n rho := by positivity
  have hgap' : (1 / 10000 : ℝ) ≤
      |dualTargetGap (1 / (100 * (dualDegree n rho : ℝ) ^ 2))
        (dualDegree n rho) (radiusDual n rho)| := by
    simpa [dualInterval] using hgap
  have hApos : 0 <
      (1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * (n : ℝ)) := by
    positivity
  have hapos : 0 < 1 / (100 * (dualDegree n rho : ℝ) ^ 2) := by
    positivity
  calc
    (1 / 4096 : ℝ) / (8000000 * (dualDegree n rho : ℝ))
        ≤ (1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * (n : ℝ)) *
            ((2 / 3 : ℝ) * n) * (1 / 2) *
            (1 / (100 * (dualDegree n rho : ℝ) ^ 2)) * (1 / 10000) := by
              field_simp
              norm_num
    _ ≤ (1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * (n : ℝ)) *
          ((n - 1 : ℕ) : ℝ) *
          ((1 - 1 / (dualDegree n rho : ℝ)) *
            (1 / (100 * (dualDegree n rho : ℝ) ^ 2)) *
            |dualTargetGap (1 / (100 * (dualDegree n rho : ℝ) ^ 2))
              (dualDegree n rho) (radiusDual n rho)|) := by
            calc
              (1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * (n : ℝ)) *
                    ((2 / 3 : ℝ) * n) * (1 / 2) *
                    (1 / (100 * (dualDegree n rho : ℝ) ^ 2)) * (1 / 10000)
                  = ((1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * (n : ℝ))) *
                      (((2 / 3 : ℝ) * n) *
                        ((1 / 2) * (1 / (100 * (dualDegree n rho : ℝ) ^ 2)) *
                          (1 / 10000))) := by ring
              _ ≤ ((1 / 4096 : ℝ) * (dualDegree n rho : ℝ) / (2 * (n : ℝ))) *
                    (((n - 1 : ℕ) : ℝ) *
                      ((1 - 1 / (dualDegree n rho : ℝ)) *
                        (1 / (100 * (dualDegree n rho : ℝ) ^ 2)) *
                        |dualTargetGap (1 / (100 * (dualDegree n rho : ℝ) ^ 2))
                          (dualDegree n rho) (radiusDual n rho)|)) := by
                    gcongr
              _ = _ := by ring

lemma selectedGamma_mem_Icc (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    selectedGamma n rho ∈ Set.Icc (0 : ℝ) 1 := by
  have hmass := selectedExpectedRawMass_mem_Icc n rho hn
  have hscore := selectedExpectedAlignedScore_pos n rho hn
  have hscoreLower := selectedExpectedAlignedScore_lower n rho hn
  have hH := Hrho_one_le n rho
  have hJupper := dualDegree_le_sixtyFive_mul_Hrho n rho
  have hJpos : (0 : ℝ) < dualDegree n rho := by
    unfold dualDegree
    positivity
  have hHpos : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one hH
  have hden : 0 < Hrho n rho * selectedExpectedAlignedScore n rho :=
    mul_pos hHpos hscore
  unfold converseKappa at hscoreLower
  constructor
  · unfold selectedGamma converseC2
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by norm_num))
        (zero_le_one.trans hmass.1)) hden.le
  · unfold selectedGamma converseC2
    rw [div_le_one hden]
    have hdenLower :
        (1 / 4096 : ℝ) / (8000000 * 65) ≤
          Hrho n rho * selectedExpectedAlignedScore n rho := by
      calc
        (1 / 4096 : ℝ) / (8000000 * 65)
            ≤ Hrho n rho *
                ((1 / 4096 : ℝ) / (8000000 * (dualDegree n rho : ℝ))) := by
              field_simp
              nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hscoreLower hHpos.le
    calc
      4 * (1 / 100000000000000000000 : ℝ) * selectedExpectedRawMass n rho
          ≤ 4 * (1 / 100000000000000000000 : ℝ) * 2 := by
            gcongr
            exact hmass.2
      _ ≤ (1 / 4096 : ℝ) / (8000000 * 65) := by norm_num
      _ ≤ _ := hdenLower

lemma selectedGamma_pos (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    0 < selectedGamma n rho := by
  unfold selectedGamma
  have hc : 0 < converseC2 := by
    unfold converseC2
    norm_num
  have hmass : 0 < selectedExpectedRawMass n rho :=
    lt_of_lt_of_le zero_lt_one (selectedExpectedRawMass_mem_Icc n rho hn).1
  have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
  have hscore : 0 < selectedExpectedAlignedScore n rho :=
    selectedExpectedAlignedScore_pos n rho hn
  positivity

-- keep: exact selected-gamma identity behind the target-separation calibration
lemma selectedGamma_calibration (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) :
    selectedGamma n rho * selectedExpectedAlignedScore n rho /
        selectedExpectedRawMass n rho =
      4 * converseC2 / Hrho n rho := by
  have hmass := (selectedExpectedRawMass_mem_Icc n rho hn).1
  have hscore := selectedExpectedAlignedScore_pos n rho hn
  have hH := Hrho_one_le n rho
  unfold selectedGamma
  field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hmass), ne_of_gt hscore,
    ne_of_gt (lt_of_lt_of_le zero_lt_one hH)]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
