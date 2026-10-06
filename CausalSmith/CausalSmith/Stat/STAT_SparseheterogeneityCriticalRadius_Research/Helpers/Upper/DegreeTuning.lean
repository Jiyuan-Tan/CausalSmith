module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Estimator
public import Causalean.Stat.Concentration.Poisson.UpperTail

/-! Numerical degree tuning for the upper-risk proof. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

private lemma auditConstant_log : Real.log auditConstant = (1048576 : ℝ) := by
  rw [auditConstant, Real.log_exp]
  norm_num

private lemma exp_Hrho (n : ℕ) (rho : ℝ) :
    Real.exp (Hrho n rho) = Real.exp 1 + n * rho ^ 2 := by
  rw [Hrho, Real.exp_log]
  positivity

private lemma one_le_Hrho (n : ℕ) (rho : ℝ) : 1 ≤ Hrho n rho := by
  rw [← Real.exp_le_exp, exp_Hrho]
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg rho]

private lemma degree_cast_upper (n : ℕ) (rho : ℝ) :
    (degree n rho : ℝ) ≤ 2 + Hrho n rho / (16 * 1048576) := by
  have hH := one_le_Hrho n rho
  have hx : 0 ≤ Hrho n rho / (16 * (1048576 : ℝ)) := by positivity
  have hfloor := Nat.floor_le hx
  rw [degree, auditConstant_log]
  simp only [Nat.cast_max, Nat.cast_ofNat]
  exact max_le (by linarith) (hfloor.trans (by linarith))

private lemma degree_cast_lower_of_large {n : ℕ} {rho : ℝ}
    (hlarge : 48 * (1048576 : ℝ) ≤ Hrho n rho) :
    Hrho n rho / (32 * 1048576) ≤ (degree n rho : ℝ) := by
  have hx : 0 ≤ Hrho n rho / (16 * (1048576 : ℝ)) := by
    positivity
  have hfloor := Nat.lt_floor_add_one (Hrho n rho / (16 * (1048576 : ℝ)))
  have hhalf :
      Hrho n rho / (32 * 1048576) ≤
        Hrho n rho / (16 * 1048576) - 1 := by
    nlinarith
  rw [degree, auditConstant_log]
  simp only [Nat.cast_max, Nat.cast_ofNat]
  calc
    _ ≤ Hrho n rho / (16 * 1048576) - 1 := hhalf
    _ ≤ (Nat.floor (Hrho n rho / (16 * 1048576)) : ℝ) := by linarith
    _ ≤ max 2 (Nat.floor (Hrho n rho / (16 * 1048576)) : ℝ) := le_max_right _ _

private lemma auditConstant_pow_degree_le (n : ℕ) (rho : ℝ) :
    auditConstant ^ degree n rho ≤
      auditConstant ^ 2 * Real.exp (Hrho n rho / 16) := by
  have hK := degree_cast_upper n rho
  rw [auditConstant]
  simp only [← Real.exp_nat_mul]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num at hK ⊢
  nlinarith

private lemma polynomial_exponential_absorption {H : ℝ}
    (hH : 48 * (1048576 : ℝ) ≤ H) :
    H ^ 6 * Real.exp (H / 16) ≤
      92160 * (Real.exp H - Real.exp 1) := by
  have hH0 : 0 ≤ H := by positivity
  have hp := Real.pow_div_factorial_le_exp (H / 2) (by positivity) 6
  norm_num [div_pow] at hp
  have hp' : H ^ 6 ≤ 46080 * Real.exp (H / 2) := by nlinarith
  have hmul : H ^ 6 * Real.exp (H / 16) ≤
      46080 * Real.exp (H / 2) * Real.exp (H / 16) :=
    mul_le_mul_of_nonneg_right hp' (Real.exp_nonneg _)
  have hexp : Real.exp (H / 2) * Real.exp (H / 16) =
      Real.exp (9 * H / 16) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnine : Real.exp (9 * H / 16) ≤ Real.exp H := by
    rw [Real.exp_le_exp]
    nlinarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp 1 using 1
    norm_num
  have htwo : 2 * Real.exp 1 ≤ Real.exp H := by
    have h2H : (2 : ℝ) ≤ H := by linarith
    have hmono : Real.exp 2 ≤ Real.exp H := Real.exp_le_exp.mpr h2H
    rw [show Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 by
      rw [← Real.exp_add]
      norm_num] at hmono
    nlinarith [Real.exp_pos 1]
  calc
    _ ≤ 46080 * Real.exp (9 * H / 16) := by
      rw [← hexp]
      simpa only [mul_assoc] using hmul
    _ ≤ 46080 * Real.exp H := by gcongr
    _ ≤ 92160 * (Real.exp H - Real.exp 1) := by nlinarith

private lemma cap_exponential_le_inverse_sample {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(n : ℝ) / 2) ≤ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Real.mul_exp_neg_le_exp_neg_one ((n : ℝ) / 2)
  have he : Real.exp (-1) ≤ (1 : ℝ) :=
    Real.exp_le_one_iff.mpr (by norm_num)
  apply (le_div_iff₀ hn0).2
  have h' : (n : ℝ) / 2 * Real.exp (-(n : ℝ) / 2) ≤ 1 := by
    simpa only [neg_div] using h.trans he
  nlinarith

private lemma three_quarters_pow_mul (q : ℕ) :
    (q + 3 : ℝ) * ((3 : ℝ) / 4) ^ q ≤ 3 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
      rw [pow_succ]
      have hpow : 0 ≤ ((3 : ℝ) / 4) ^ q := by positivity
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      nlinarith

private lemma cap_geometric_le_inverse_sample {n : ℕ} (hn : 3 ≤ n) :
    (Real.exp 1 / 4) ^ (postPilotSize n / 2) ≤ 12 / n := by
  let q := postPilotSize n / 2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbase : Real.exp 1 / 4 ≤ (3 : ℝ) / 4 := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hpow : (Real.exp 1 / 4) ^ q ≤ ((3 : ℝ) / 4) ^ q := by gcongr
  have hgeom := three_quarters_pow_mul q
  have hqpos : (0 : ℝ) < q + 3 := by positivity
  have hqbound : (n : ℝ) ≤ 4 * (q + 3) := by
    dsimp [q, postPilotSize, pilotSize]
    exact_mod_cast (show n ≤ 4 * ((n - n / 2) / 2 + 3) by omega)
  calc
    _ ≤ ((3 : ℝ) / 4) ^ q := hpow
    _ ≤ 3 / (q + 3) := by
      apply (le_div_iff₀ hqpos).2
      simpa [mul_comm] using hgeom
    _ ≤ 12 / n := by
      apply (div_le_div_iff₀ hqpos hn0).2
      nlinarith

/-- The concrete audit variance term in equation (48) is absorbed by the
declared critical-rate expression. -/
lemma audit_degree_variance_tuning :
    ∃ C : ℝ, 0 < C ∧ ∀ n rho, 3 ≤ n → 0 ≤ rho → rho ≤ 2 →
      2000000 * auditConstant ^ degree n rho * (degree n rho : ℝ) ^ 4 / n ≤
        C * rate n rho := by
  let A : ℝ := 1048576
  let C : ℝ := 2000000 * auditConstant ^ 2 *
    (625 * Real.exp (3 * A) + 92160)
  refine ⟨C, by dsimp [C, auditConstant]; positivity, ?_⟩
  intro n rho hn hrho0 hrho2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hH := one_le_Hrho n rho
  have hrate0 : 0 ≤ rate n rho := by
    unfold rate
    positivity
  by_cases hsmall : Hrho n rho < 48 * A
  · have hK : (degree n rho : ℝ) ≤ 5 := by
      have := degree_cast_upper n rho
      dsimp [A] at hsmall ⊢
      linarith
    have hpow := auditConstant_pow_degree_le n rho
    have hexp : Real.exp (Hrho n rho / 16) ≤ Real.exp (3 * A) := by
      rw [Real.exp_le_exp]
      linarith
    have hAK : auditConstant ^ degree n rho ≤
        auditConstant ^ 2 * Real.exp (3 * A) :=
      hpow.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg auditConstant))
    have hK4 : (degree n rho : ℝ) ^ 4 ≤ 625 := by
      have hK0 : (0 : ℝ) ≤ degree n rho := by positivity
      have hsq : (degree n rho : ℝ) ^ 2 ≤ 25 := by nlinarith
      nlinarith [mul_self_le_mul_self (sq_nonneg (degree n rho : ℝ)) hsq]
    have hmain :
        2000000 * auditConstant ^ degree n rho * (degree n rho : ℝ) ^ 4 / n ≤
          (2000000 * auditConstant ^ 2 * (625 * Real.exp (3 * A))) / n := by
      calc
        _ ≤ 2000000 * (auditConstant ^ 2 * Real.exp (3 * A)) *
            (degree n rho : ℝ) ^ 4 / n := by gcongr
        _ ≤ 2000000 * (auditConstant ^ 2 * Real.exp (3 * A)) * 625 / n := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ (2000000 * auditConstant ^ 2 * (625 * Real.exp (3 * A))) / n := hmain
      _ ≤ C * (1 / n) := by
        dsimp [C]
        have hpos : 0 ≤ 2000000 * auditConstant ^ 2 := by positivity
        have hepos : 0 ≤ Real.exp (3 * A) := Real.exp_nonneg _
        apply (div_le_iff₀ hn0).2
        field_simp [hn0.ne']
        nlinarith
      _ ≤ C * rate n rho := by
        unfold rate
        apply mul_le_mul_of_nonneg_left _ (by dsimp [C, auditConstant]; positivity)
        have : 0 ≤ 1 / (n : ℝ) := by positivity
        have : 0 ≤ rho ^ 2 / Hrho n rho ^ 2 := by positivity
        linarith

  · have hlarge : 48 * A ≤ Hrho n rho := le_of_not_gt hsmall
    have hKupper : (degree n rho : ℝ) ≤ Hrho n rho := by
      have := degree_cast_upper n rho
      dsimp [A] at hlarge ⊢
      nlinarith
    have hK0 : (0 : ℝ) ≤ degree n rho := by positivity
    have hK4 : (degree n rho : ℝ) ^ 4 ≤ Hrho n rho ^ 4 := by gcongr
    have hAK := auditConstant_pow_degree_le n rho
    have habs := polynomial_exponential_absorption hlarge
    have hidentity : Real.exp (Hrho n rho) - Real.exp 1 = n * rho ^ 2 := by
      rw [exp_Hrho]
      ring
    have hscaled : auditConstant ^ degree n rho * (degree n rho : ℝ) ^ 4 *
          Hrho n rho ^ 2 ≤
        auditConstant ^ 2 * 92160 * (n * rho ^ 2) := by
      calc
        _ ≤ (auditConstant ^ 2 * Real.exp (Hrho n rho / 16)) *
            Hrho n rho ^ 4 * Hrho n rho ^ 2 := by gcongr
        _ = auditConstant ^ 2 *
            (Hrho n rho ^ 6 * Real.exp (Hrho n rho / 16)) := by ring
        _ ≤ auditConstant ^ 2 *
            (92160 * (Real.exp (Hrho n rho) - Real.exp 1)) := by gcongr
        _ = auditConstant ^ 2 * 92160 * (n * rho ^ 2) := by rw [hidentity]; ring
    have hHpos : 0 < Hrho n rho := lt_of_lt_of_le (by norm_num) hH
    have hmain :
        2000000 * auditConstant ^ degree n rho * (degree n rho : ℝ) ^ 4 / n ≤
          (2000000 * auditConstant ^ 2 * 92160) *
            (rho ^ 2 / Hrho n rho ^ 2) := by
      calc
        _ = (2000000 / ((n : ℝ) * Hrho n rho ^ 2)) *
            (auditConstant ^ degree n rho * (degree n rho : ℝ) ^ 4 *
              Hrho n rho ^ 2) := by field_simp [hn0.ne', hHpos.ne']
        _ ≤ (2000000 / ((n : ℝ) * Hrho n rho ^ 2)) *
            (auditConstant ^ 2 * 92160 * (n * rho ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hscaled (by positivity)
        _ = _ := by field_simp [hn0.ne', hHpos.ne']
    calc
      _ ≤ (2000000 * auditConstant ^ 2 * 92160) *
          (rho ^ 2 / Hrho n rho ^ 2) := hmain
      _ ≤ C * (rho ^ 2 / Hrho n rho ^ 2) := by
        gcongr
        dsimp [C]
        have hbase : 0 ≤ 2000000 * auditConstant ^ 2 := by positivity
        have hepos : 0 ≤ Real.exp (3 * A) := Real.exp_nonneg _
        nlinarith
      _ ≤ C * rate n rho := by
        unfold rate
        apply mul_le_mul_of_nonneg_left _ (by dsimp [C, auditConstant]; positivity)
        have : 0 ≤ 1 / (n : ℝ) := by positivity
        have : 0 ≤ rho ^ 2 / Hrho n rho ^ 2 := by positivity
        linarith

/-- The squared bias term in equation (48) is absorbed by the declared
critical-rate expression. -/
lemma degree_bias_tuning :
    ∃ C : ℝ, 0 < C ∧ ∀ n rho, 3 ≤ n → 0 ≤ rho → rho ≤ 2 →
      (rho ^ 2 + 1 / n) / (degree n rho : ℝ) ^ 2 ≤ C * rate n rho := by
  let A : ℝ := 1048576
  let C : ℝ := (48 * A) ^ 2 + (32 * A) ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n rho hn hrho0 hrho2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hH := one_le_Hrho n rho
  have hHpos : 0 < Hrho n rho := lt_of_lt_of_le (by norm_num) hH
  have hK : (2 : ℝ) ≤ degree n rho := by
    exact_mod_cast (show 2 ≤ degree n rho by simp [degree])
  have hKpos : 0 < (degree n rho : ℝ) := by linarith
  by_cases hsmall : Hrho n rho < 48 * A
  · have hHsq : Hrho n rho ^ 2 ≤ (48 * A) ^ 2 := by
      nlinarith [mul_self_le_mul_self (show 0 ≤ Hrho n rho by linarith)
        (le_of_lt hsmall)]
    have hrho : rho ^ 2 ≤ (48 * A) ^ 2 *
        (rho ^ 2 / Hrho n rho ^ 2) := by
      calc
        _ = (rho ^ 2 / Hrho n rho ^ 2) * Hrho n rho ^ 2 := by
          field_simp [hHpos.ne']
        _ ≤ (rho ^ 2 / Hrho n rho ^ 2) * (48 * A) ^ 2 := by gcongr
        _ = _ := by ring
    have hdiv : (rho ^ 2 + 1 / n) / (degree n rho : ℝ) ^ 2 ≤
        (rho ^ 2 + 1 / n) / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hK]
    calc
      _ ≤ (rho ^ 2 + 1 / n) / 4 := hdiv
      _ ≤ C * (1 / n + rho ^ 2 / Hrho n rho ^ 2) := by
        dsimp [C]
        have hninv : 0 ≤ 1 / (n : ℝ) := by positivity
        have hz : 0 ≤ rho ^ 2 / Hrho n rho ^ 2 := by positivity
        nlinarith
      _ = C * rate n rho := by rfl
  · have hlarge : 48 * A ≤ Hrho n rho := le_of_not_gt hsmall
    have hlower := degree_cast_lower_of_large hlarge
    have hsquares : Hrho n rho ^ 2 ≤
        (32 * A) ^ 2 * (degree n rho : ℝ) ^ 2 := by
      have hB : 0 ≤ (32 * A : ℝ) := by dsimp [A]; positivity
      have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ Hrho n rho)
        (show Hrho n rho ≤ (32 * A) * (degree n rho : ℝ) by
          dsimp [A]
          simpa [mul_comm] using
            ((div_le_iff₀ (by norm_num : (0 : ℝ) < 32 * 1048576)).mp hlower))
      nlinarith
    have hrho : rho ^ 2 ≤ (32 * A) ^ 2 *
        (rho ^ 2 / Hrho n rho ^ 2) * (degree n rho : ℝ) ^ 2 := by
      calc
        _ = (rho ^ 2 / Hrho n rho ^ 2) * Hrho n rho ^ 2 := by
          field_simp [hHpos.ne']
        _ ≤ (rho ^ 2 / Hrho n rho ^ 2) *
            ((32 * A) ^ 2 * (degree n rho : ℝ) ^ 2) := by gcongr
        _ = _ := by ring
    have hone : 1 ≤ (32 * A) ^ 2 * (degree n rho : ℝ) ^ 2 := by
      dsimp [A]
      nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hK]
    apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
    unfold rate
    dsimp [C]
    have hninv : 0 ≤ 1 / (n : ℝ) := by positivity
    have hz : 0 ≤ rho ^ 2 / Hrho n rho ^ 2 := by positivity
    nlinarith

/-- The standard quarter-mean Poisson cap remainder is at critical-rate scale. -/
lemma cap_tail_tuning :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (rho : ℝ), 3 ≤ n → 0 ≤ rho → rho ≤ 2 →
      (Real.exp 1 / 4) ^ (postPilotSize n / 2) ≤ C * rate n rho := by
  refine ⟨12, by norm_num, ?_⟩
  intro n rho hn hrho0 hrho2
  calc
    _ ≤ 12 / (n : ℝ) := cap_geometric_le_inverse_sample hn
    _ = 12 * (1 / (n : ℝ)) := by ring
    _ ≤ 12 * rate n rho := by
      unfold rate
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have : 0 ≤ rho ^ 2 / Hrho n rho ^ 2 := by positivity
      linarith

/-- Equations (48)--(49): the audit variance, squared degree bias, and cap
remainder are simultaneously bounded by one universal multiple of `rate`. -/
lemma degree_tuning_upper_terms :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (rho : ℝ), 3 ≤ n → 0 ≤ rho → rho ≤ 2 →
      1 / n +
          2000000 * auditConstant ^ degree n rho * (degree n rho : ℝ) ^ 4 / n +
          (rho ^ 2 + 1 / n) / (degree n rho : ℝ) ^ 2 +
          (Real.exp 1 / 4) ^ (postPilotSize n / 2) ≤
        C * rate n rho := by
  obtain ⟨Cv, hCv, hv⟩ := audit_degree_variance_tuning
  obtain ⟨Cb, hCb, hb⟩ := degree_bias_tuning
  obtain ⟨Cc, hCc, hc⟩ := cap_tail_tuning
  refine ⟨1 + Cv + Cb + Cc, by positivity, ?_⟩
  intro n rho hn hrho0 hrho2
  have hnbase : 1 / (n : ℝ) ≤ rate n rho := by
    unfold rate
    have : 0 ≤ rho ^ 2 / Hrho n rho ^ 2 := by positivity
    linarith
  have hv' := hv n rho hn hrho0 hrho2
  have hb' := hb n rho hn hrho0 hrho2
  have hc' := hc n rho hn hrho0 hrho2
  calc
    _ ≤ rate n rho + Cv * rate n rho + Cb * rate n rho + Cc * rate n rho := by
      gcongr
    _ = (1 + Cv + Cb + Cc) * rate n rho := by ring

/-- The precise coefficients produced by the ideal MSE and the capped-count
transport are absorbed by the common tuning bound. -/
lemma degree_tuning_concrete_risk_terms (Cp : ℝ) (hCp : 0 ≤ Cp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (M rho : ℝ), 3 ≤ n → 1 ≤ M →
      0 ≤ rho → rho ≤ 2 →
      3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
          (degree n rho : ℝ) ^ 4 / n) +
        (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
          (M ^ 2 * rho ^ 2 + Cp * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ))) +
        4 * M ^ 2 *
          (Real.exp 1 / 4) ^ (postPilotSize n / 2) ≤
        C * M ^ 2 * rate n rho := by
  obtain ⟨Ct, hCt, htune⟩ := degree_tuning_upper_terms
  let D : ℝ := 2 * 196612 ^ 2 * (1 + Cp)
  let S : ℝ := 3 + D + 4
  refine ⟨S * Ct, mul_pos ?_ hCt, ?_⟩
  · unfold S D
    positivity
  intro n M rho hn hM hrho0 hrho2
  let A := 2000000 * auditConstant ^ degree n rho *
    (degree n rho : ℝ) ^ 4 / n
  let B := (rho ^ 2 + 1 / (n : ℝ)) / (degree n rho : ℝ) ^ 2
  let T := (Real.exp 1 / 4) ^ (postPilotSize n / 2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hA : 0 ≤ A := by
    unfold A
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg
      (by unfold auditConstant; positivity) _)) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)
  have hB : 0 ≤ B := by unfold B; positivity
  have hT : 0 ≤ T := by unfold T; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  have hS : 0 ≤ S := by unfold S; positivity
  have hbias :
      (2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2) *
          (M ^ 2 * rho ^ 2 + Cp * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ))) ≤
        D * M ^ 2 * B := by
    have hinside : rho ^ 2 + Cp * (rho ^ 2 + 1 / (n : ℝ)) ≤
        (1 + Cp) * (rho ^ 2 + 1 / (n : ℝ)) := by
      have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hinside
      (sq_nonneg (degree n rho : ℝ))
    unfold D B
    calc
      _ = 2 * 196612 ^ 2 * M ^ 2 *
          ((rho ^ 2 + Cp * (rho ^ 2 + 1 / (n : ℝ))) /
            (degree n rho : ℝ) ^ 2) := by ring
      _ ≤ 2 * 196612 ^ 2 * M ^ 2 *
          (((1 + Cp) * (rho ^ 2 + 1 / (n : ℝ))) /
            (degree n rho : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have hweighted : 3 * A + D * B + 4 * T ≤
      S * (1 / (n : ℝ) + A + B + T) := by
    have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
    calc
      _ ≤ S * A + S * B + S * T := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_right (by unfold S; linarith) hA
          · exact mul_le_mul_of_nonneg_right (by unfold S; linarith) hB
        · exact mul_le_mul_of_nonneg_right (by unfold S; linarith) hT
      _ ≤ S * (1 / (n : ℝ) + A + B + T) := by
        nlinarith [mul_nonneg hS hinv]
  have ht := htune n rho hn hrho0 hrho2
  change 1 / (n : ℝ) + A + B + T ≤ Ct * rate n rho at ht
  calc
    _ ≤ 3 * (M ^ 2 * A) + D * M ^ 2 * B + 4 * M ^ 2 * T := by
      rw [show 3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
          (degree n rho : ℝ) ^ 4 / n) = 3 * (M ^ 2 * A) by
        unfold A
        ring]
      apply add_le_add
      · simpa only [add_comm] using add_le_add_left hbias (3 * (M ^ 2 * A))
      · rfl
    _ = M ^ 2 * (3 * A + D * B + 4 * T) := by ring
    _ ≤ M ^ 2 * (S * (1 / (n : ℝ) + A + B + T)) := by gcongr
    _ ≤ M ^ 2 * (S * (Ct * rate n rho)) := by gcongr
    _ = S * Ct * M ^ 2 * rate n rho := by ring


end CausalSmith.Stat.SparseheterogeneityCriticalRadius
