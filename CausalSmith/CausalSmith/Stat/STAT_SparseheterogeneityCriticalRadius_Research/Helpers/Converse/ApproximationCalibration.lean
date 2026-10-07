module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.CalibrationMoments
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.Main

/-! Quantitative separation supplied by the reciprocal approximation dual. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open Set Polynomial
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

private lemma uniformPowLower (n : ℕ) (hn : 2 ≤ n) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hmp : (m : ℝ) + 1 ≠ 0 := by linarith
    have hd : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    have hb : 0 ≤ 1 - 1 / (m : ℝ) := by
      rw [sub_nonneg, div_le_iff₀ (by linarith : (0 : ℝ) < m)]
      linarith
    have hbern := one_add_mul_le_pow
      (a := 1 / ((m : ℝ) ^ 2 - 1)) (by
        have hx : (0 : ℝ) ≤ 1 / ((m : ℝ) ^ 2 - 1) := by positivity
        linarith) m
    have hfac : 1 ≤ (1 + (m : ℝ) / ((m : ℝ) ^ 2 - 1)) *
        (1 - 1 / ((m : ℝ) + 1)) := by
      field_simp
      nlinarith
    have hid : 1 - 1 / ((m : ℝ) + 1) =
        (1 - 1 / (m : ℝ)) * (1 + 1 / ((m : ℝ) ^ 2 - 1)) := by
      field_simp
      ring
    have hstep : (1 - 1 / (m : ℝ)) ^ m ≤
        (1 - 1 / ((m : ℝ) + 1)) ^ (m + 1) := by
      rw [pow_succ, hid, mul_pow]
      have hnew : 0 ≤ 1 - 1 / ((m : ℝ) + 1) := by
        rw [sub_nonneg, div_le_iff₀ (by linarith : (0 : ℝ) < m + 1)]
        linarith
      have hmul := mul_le_mul_of_nonneg_right hbern hnew
      have hprod : 1 ≤ (1 + 1 / ((m : ℝ) ^ 2 - 1)) ^ m *
          ((1 - 1 / (m : ℝ)) * (1 + 1 / ((m : ℝ) ^ 2 - 1))) := by
        rw [← hid]
        exact hfac.trans (by simpa only [div_eq_mul_inv, one_mul] using hmul)
      nlinarith [mul_nonneg (pow_nonneg hb m) (sub_nonneg.mpr hprod)]
    exact ih.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hstep)

/-- At the paper interval `a = 1/(100J²)` and degree `3J`, the rational
target retains a uniform numerical approximation gap. -/
lemma rationalTarget_bestUniformApproxError_lower (J : ℕ) (hJ : 2 ≤ J) :
    (1 : ℝ) / 10000 ≤
      bestUniformApproxError
        (rationalTarget (1 / (100 * (J : ℝ) ^ 2)))
        (1 / (100 * (J : ℝ) ^ 2)) 1 (3 * J) := by
  let a : ℝ := 1 / (100 * (J : ℝ) ^ 2)
  let K : ℕ := 3 * J
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one (by positivity)).2
    nlinarith [sq_nonneg ((J : ℝ) - 2)]
  have hsub : 2 * a * (K : ℝ) ^ 2 - a ≤ 1 := by
    dsimp [a, K]
    push_cast
    field_simp
    nlinarith [sq_nonneg (J : ℝ)]
  have hrecip := bestUniformApproxError_reciprocal_one_sq K hK
  have hlowerEach (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ K) :
      (((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2)) *
          (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K / 2 ≤
        uniformApproxError (rationalTarget a) a 1 Q := by
    let A : Polynomial ℝ := C (2 * a) * X - C a
    let R : Polynomial ℝ := C 2 * (C 1 - Q.comp A)
    have hA : A.natDegree ≤ 1 := by
      dsimp [A]
      exact (natDegree_sub_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
    have hR : R.natDegree ≤ K := by
      dsimp [R]
      refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans ?_)
      exact max_le (by simp) ((natDegree_comp_le.trans (by nlinarith)))
    have hrecipCont : ContinuousOn (fun z : ℝ => z⁻¹) (Icc 1 ((K : ℝ) ^ 2)) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro z hz hz0
      have : z = 0 := by simpa using hz0
      linarith [hz.1]
    have hbestR := bestUniformApproxError_le (f := fun z : ℝ => z⁻¹) (r := 1)
      (s := (K : ℝ) ^ 2) hR
    rw [hrecip] at hbestR
    have hratCont : ContinuousOn (rationalTarget a) (Icc a 1) := by
      apply continuousOn_rationalTarget
      simp only [mem_Icc, not_and]
      intro hneg
      linarith
    have hresCont : ContinuousOn
        (fun z : ℝ => z⁻¹ - R.eval z) (Icc 1 ((K : ℝ) ^ 2)) :=
      hrecipCont.sub R.continuous.continuousOn
    have hratBound : ∀ x ∈ Icc a 1,
        |rationalTarget a x - Q.eval x| ≤
          uniformApproxError (rationalTarget a) a 1 Q :=
      (intervalSupNorm_le_iff
        (hratCont.sub Q.continuous.continuousOn) ha1.le).mp le_rfl
    have hscaled : uniformApproxError (fun z : ℝ => z⁻¹) 1 ((K : ℝ) ^ 2) R ≤
        2 * uniformApproxError (rationalTarget a) a 1 Q := by
      apply (intervalSupNorm_le_iff hresCont (by nlinarith)).2
      intro z hz
      have hzpos : 0 < z := lt_of_lt_of_le (by norm_num) hz.1
      have hxmem : 2 * a * z - a ∈ Icc a 1 := by
        constructor
        · have hz1 : 2 * a ≤ 2 * a * z := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hz.1 (mul_nonneg (by norm_num) ha.le))
          linarith
        · calc
            2 * a * z - a ≤ 2 * a * (K : ℝ) ^ 2 - a := by
              exact sub_le_sub_right
                (mul_le_mul_of_nonneg_left hz.2 (mul_nonneg (by norm_num) ha.le)) a
            _ ≤ 1 := hsub
      have hiden : 2 * a * z - a + a = 2 * a * z := by ring
      have hresid : z⁻¹ - R.eval z =
          -2 * (rationalTarget a (2 * a * z - a) - Q.eval (2 * a * z - a)) := by
        dsimp [R, A]
        simp only [eval_mul, eval_C, eval_sub, eval_comp, eval_X]
        unfold rationalTarget
        rw [hiden]
        field_simp [ne_of_gt ha, ne_of_gt hzpos]
        ring
      rw [hresid, abs_mul]
      norm_num
      simpa using mul_le_mul_of_nonneg_left (hratBound _ hxmem)
        (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hbestLower :
      (((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2)) *
          (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K / 2 ≤
        bestUniformApproxError (rationalTarget a) a 1 K := by
    unfold bestUniformApproxError
    apply le_csInf
    · exact ⟨uniformApproxError (rationalTarget a) a 1 0, 0, by simp⟩
    · rintro e ⟨Q, hQ, rfl⟩
      exact hlowerEach Q hQ
  have hbase : (1 - 1 / (K : ℝ)) ^ 2 ≤
      ((K : ℝ) - 1) / ((K : ℝ) + 1) := by
    have hKpos : (0 : ℝ) < K := by positivity
    have hKplus : (0 : ℝ) < K + 1 := by positivity
    apply (le_div_iff₀ hKplus).2
    field_simp
    nlinarith
  have hbaseNonneg : 0 ≤ (1 - 1 / (K : ℝ)) ^ 2 := sq_nonneg _
  have hpowBase : ((1 - 1 / (K : ℝ)) ^ 2) ^ K ≤
      (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K :=
    pow_le_pow_left₀ hbaseNonneg hbase K
  have hu := uniformPowLower K hK
  have hpow : (1 / 16 : ℝ) ≤
      (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K := by
    rw [← pow_mul] at hpowBase
    have hsquare : (1 / 16 : ℝ) ≤ ((1 - 1 / (K : ℝ)) ^ K) ^ 2 := by
      nlinarith [sq_nonneg ((1 - 1 / (K : ℝ)) ^ K - 1 / 4)]
    rw [← pow_mul] at hsquare
    exact hsquare.trans (by simpa [Nat.mul_comm] using hpowBase)
  have hpref : (1 : ℝ) / 4 ≤ ((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (K : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((K : ℝ) - 2)]
  change (1 : ℝ) / 10000 ≤ bestUniformApproxError (rationalTarget a) a 1 K
  have hformula : (1 : ℝ) / 128 ≤
      (((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2)) *
        (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K / 2 := by
    calc
      (1 : ℝ) / 128 = (1 / 4) * (1 / 16) / 2 := by norm_num
      _ ≤ ((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2) * (1 / 16) / 2 := by
        gcongr
      _ ≤ ((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2) *
          (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K / 2 := by
        gcongr
  exact (by norm_num : (1 : ℝ) / 10000 ≤ 1 / 128) |>.trans
    (hformula.trans hbestLower)

/-- The selected finite dual therefore has a nonvanishing signed separation,
independently of its orientation. -/
lemma dualInterval_abs_dualTargetGap_lower (n : ℕ) (rho : ℝ) :
    (1 : ℝ) / 10000 ≤
      |dualTargetGap (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho)| := by
  rw [abs_dualTargetGap]
  exact rationalTarget_bestUniformApproxError_lower (dualDegree n rho) (by
    unfold dualDegree
    exact le_max_left _ _)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
