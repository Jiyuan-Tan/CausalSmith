module
public import Causalean.Mathlib.Probability.Birthday.Basic

/-!
# Finite birthday and binomial bounds

Pointwise collision estimates, monotonicity in the alphabet, and a finite
binomial pair bound. These are the quantitative inputs for asymptotics and
least-threshold existence.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

/-- A [positive alphabet](hyp:hm) gives [a collision probability between zero
and one](goal) for every draw count. -/
theorem repeatKernel_mem_Icc (m r : ℕ) (hm : 0 < m) :
    repeatKernel m r ∈ Set.Icc (0 : ℝ) 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : (m.descFactorial r : ℝ) ≤ (m : ℝ) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow m r
  have hq : noRepeat m r ≤ 1 := by
    unfold noRepeat
    exact (div_le_iff₀ (pow_pos hmpos _)).2 (by simpa using hfac)
  change 0 ≤ repeatKernel m r ∧ repeatKernel m r ≤ 1
  unfold repeatKernel
  constructor
  · linarith
  · have : 0 ≤ noRepeat m r := by unfold noRepeat; positivity
    linarith

/-- If the [draw count exceeds the alphabet](hyp:hr), the
[repeat probability is one](goal). -/
theorem repeatKernel_eq_one_of_lt (m r : ℕ) (hr : m < r) :
    repeatKernel m r = 1 := by
  simp [repeatKernel, noRepeat, Nat.descFactorial_eq_zero_iff_lt.mpr hr]

/-- For a [positive alphabet](hyp:hm), the [repeat probability](goal) is at
most the number of unordered draw pairs divided by the alphabet size. -/
theorem repeatKernel_le_pairs (m r : ℕ) (hm : 0 < m) :
    repeatKernel m r ≤ (r.choose 2 : ℝ) / (m : ℝ) := by
  induction r with
  | zero => simp [repeatKernel, noRepeat]
  | succ r ih =>
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hpow : 0 < (m : ℝ) ^ r := pow_pos hmpos _
    have hfac : (m.descFactorial r : ℝ) ≤ (m : ℝ) ^ r := by
      exact_mod_cast Nat.descFactorial_le_pow m r
    have hq0 : 0 ≤ (m.descFactorial r : ℝ) / (m : ℝ) ^ r := by positivity
    have hq1 : (m.descFactorial r : ℝ) / (m : ℝ) ^ r ≤ 1 := by
      exact (div_le_iff₀ hpow).2 (by simpa using hfac)
    have hsub : (m : ℝ) - r ≤ (m - r : ℕ) := by
      by_cases h : r ≤ m
      · rw [Nat.cast_sub h]
      · have : (m : ℝ) ≤ r := by
          exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
        simp only [Nat.sub_eq_zero_of_le
          (Nat.le_of_lt (Nat.lt_of_not_ge h)), Nat.cast_zero]
        linarith
    have hsub1 : ((m - r : ℕ) : ℝ) ≤ m := by
      exact_mod_cast Nat.sub_le m r
    have hrec : (m.descFactorial (r + 1) : ℝ) / (m : ℝ) ^ (r + 1) =
        ((m - r : ℕ) : ℝ) / (m : ℝ) *
          ((m.descFactorial r : ℝ) / (m : ℝ) ^ r) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      ring
    have hchoose : ((r + 1).choose 2 : ℝ) = (r.choose 2 : ℝ) + r := by
      rw [Nat.choose_succ_succ']
      simp
      ring
    unfold repeatKernel noRepeat at ih ⊢
    rw [hrec, hchoose]
    have hratio0 : 0 ≤ 1 - ((m - r : ℕ) : ℝ) / (m : ℝ) := by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hmpos).2 (by simp [hsub1])
    have hratio : 1 - ((m - r : ℕ) : ℝ) / (m : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
      apply (le_div_iff₀ hmpos).2
      have : (1 - ((m - r : ℕ) : ℝ) / (m : ℝ)) * (m : ℝ) =
          (m : ℝ) - (m - r : ℕ) := by field_simp
      rw [this]
      linarith
    have hmul : (1 - ((m - r : ℕ) : ℝ) / (m : ℝ)) *
        ((m.descFactorial r : ℝ) / (m : ℝ) ^ r) ≤ (r : ℝ) / (m : ℝ) := by
      calc
        _ ≤ 1 - ((m - r : ℕ) : ℝ) / (m : ℝ) := by nlinarith
        _ ≤ _ := hratio
    have hstep : 1 - ((m - r : ℕ) : ℝ) / (m : ℝ) *
        ((m.descFactorial r : ℝ) / (m : ℝ) ^ r) ≤
        (1 - (m.descFactorial r : ℝ) / (m : ℝ) ^ r) + r / (m : ℝ) := by
      nlinarith [hmul]
    exact hstep.trans (by
      have := add_le_add_right ih (r / (m : ℝ))
      simpa [add_div] using this)

/-- For a [positive alphabet](hyp:hm), the [no-repeat probability](goal) is at
most the exponential of minus the pair count over the alphabet size. -/
theorem noRepeat_le_exp (m r : ℕ) (hm : 0 < m) :
    noRepeat m r ≤ Real.exp (-((r.choose 2 : ℕ) : ℝ) / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  induction r with
  | zero => simp [noRepeat]
  | succ r ih =>
    by_cases h : r < m
    · have hcast : ((m - r : ℕ) : ℝ) = (m : ℝ) - r :=
        Nat.cast_sub h.le
      have hfactor : ((m - r : ℕ) : ℝ) / m ≤
          Real.exp (-(r : ℝ) / m) := by
        rw [hcast]
        have hbasic := Real.one_sub_le_exp_neg ((r : ℝ) / m)
        have heq : ((m : ℝ) - r) / m = 1 - (r : ℝ) / m := by
          field_simp
        rw [heq]
        simpa only [neg_div] using hbasic
      have hrec : noRepeat m (r + 1) =
          ((m - r : ℕ) : ℝ) / m * noRepeat m r := by
        unfold noRepeat
        rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
        ring
      have hchoose : ((r + 1).choose 2 : ℝ) = (r.choose 2 : ℝ) + r := by
        rw [Nat.choose_succ_succ']
        simp
        ring
      rw [hrec, hchoose]
      calc
        _ ≤ Real.exp (-(r : ℝ) / m) * noRepeat m r :=
          mul_le_mul_of_nonneg_right hfactor (by unfold noRepeat; positivity)
        _ ≤ Real.exp (-(r : ℝ) / m) *
            Real.exp (-((r.choose 2 : ℕ) : ℝ) / m) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp (-(((r.choose 2 : ℕ) : ℝ) + r) / m) := by
          rw [← Real.exp_add]
          congr 1
          ring
    · have hzero : m - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
      simpa [noRepeat, Nat.descFactorial_succ, hzero] using
        (Real.exp_nonneg (-(((r + 1).choose 2 : ℕ) : ℝ) / m))

/-- For a [positive alphabet](hyp:hm) and [draw count within it](hyp:hr),
the [no-repeat probability](goal) is at least the exponential pair bound with
the remaining alphabet size in its denominator. -/
theorem exp_le_noRepeat (m r : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    Real.exp (-((r.choose 2 : ℕ) : ℝ) / (m + 1 - r : ℕ)) ≤ noRepeat m r := by
  induction r with
  | zero => simp [noRepeat]
  | succ r ih =>
    have hrm : r < m := Nat.lt_of_succ_le hr
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hden_nat : m + 1 - (r + 1) = m - r := by omega
    have hden_pos_nat : 0 < m - r := Nat.sub_pos_of_lt hrm
    have hden_pos : (0 : ℝ) < (m - r : ℕ) := by exact_mod_cast hden_pos_nat
    have hfactor : Real.exp (-(r : ℝ) / (m - r : ℕ)) ≤
        ((m - r : ℕ) : ℝ) / m := by
      have hx1 : (r : ℝ) / m < 1 :=
        (div_lt_one hmpos).2 (by exact_mod_cast hrm)
      have hpos : 0 < 1 - (r : ℝ) / m := sub_pos.mpr hx1
      have hlog := Real.one_sub_inv_le_log_of_pos hpos
      have hid : 1 - (1 - (r : ℝ) / m)⁻¹ =
          -((r : ℝ) / m) / (1 - (r : ℝ) / m) := by
        have hmr : (m : ℝ) - r ≠ 0 := by
          rw [← Nat.cast_sub hrm.le]
          exact ne_of_gt hden_pos
        field_simp [ne_of_gt hmpos, ne_of_gt hpos, hmr]
        ring
      rw [hid] at hlog
      have h := (Real.exp_le_exp.mpr hlog).trans
        (le_of_eq (Real.exp_log hpos))
      have hone : 1 - (r : ℝ) / m = ((m - r : ℕ) : ℝ) / m := by
        rw [Nat.cast_sub hrm.le]
        field_simp
      have hexp : -((r : ℝ) / m) / (1 - (r : ℝ) / m) =
          -(r : ℝ) / (m - r : ℕ) := by
        rw [Nat.cast_sub hrm.le]
        field_simp
      rw [hexp, hone] at h
      exact h
    have ih' := ih (Nat.le_of_lt hrm)
    have hden_le : (m - r : ℕ) ≤ m + 1 - r := by omega
    have hchoose_nonneg : (0 : ℝ) ≤ (r.choose 2 : ℕ) := Nat.cast_nonneg _
    have hweak : Real.exp (-((r.choose 2 : ℕ) : ℝ) / (m - r : ℕ)) ≤
        Real.exp (-((r.choose 2 : ℕ) : ℝ) / (m + 1 - r : ℕ)) := by
      apply Real.exp_le_exp.mpr
      have hsmall_nat : 0 < m + 1 - r := by omega
      have hsmall : (0 : ℝ) < (m + 1 - r : ℕ) := by exact_mod_cast hsmall_nat
      have hcastle : ((m - r : ℕ) : ℝ) ≤ (m + 1 - r : ℕ) := by
        exact_mod_cast hden_le
      have := div_le_div_of_nonneg_left hchoose_nonneg hden_pos hcastle
      simpa only [neg_div] using neg_le_neg this
    have hrec : noRepeat m (r + 1) =
        (((m - r : ℕ) : ℝ) / m) * noRepeat m r := by
      unfold noRepeat
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      ring
    rw [hden_nat, hrec]
    calc
      Real.exp (-(((r + 1).choose 2 : ℕ) : ℝ) / (m - r : ℕ)) =
          Real.exp (-(r : ℝ) / (m - r : ℕ)) *
            Real.exp (-((r.choose 2 : ℕ) : ℝ) / (m - r : ℕ)) := by
        rw [← Real.exp_add, Nat.choose_succ_succ']
        simp
        ring
      _ ≤ (((m - r : ℕ) : ℝ) / m) *
          Real.exp (-((r.choose 2 : ℕ) : ℝ) / (m + 1 - r : ℕ)) :=
        mul_le_mul hfactor hweak (Real.exp_nonneg _) (by positivity)
      _ ≤ (((m - r : ℕ) : ℝ) / m) * noRepeat m r :=
        mul_le_mul_of_nonneg_left ih' (by positivity)

/-- As the [positive alphabet](hyp:hm) grows by one, the
[no-repeat probability increases](goal). -/
theorem noRepeat_mono_succ (m r : ℕ) (hm : 0 < m) :
    noRepeat m r ≤ noRepeat (m + 1) r := by
  induction r with
  | zero => simp [noRepeat]
  | succ r ih =>
    by_cases hr : r < m
    · have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      have hm1pos : (0 : ℝ) < m + 1 := by positivity
      have hfac : ((m - r : ℕ) : ℝ) / m ≤
          (((m + 1) - r : ℕ) : ℝ) / (m + 1) := by
        rw [Nat.cast_sub hr.le, Nat.cast_sub (by omega : r ≤ m + 1)]
        apply (div_le_div_iff₀ hmpos hm1pos).2
        push_cast
        nlinarith
      have hleft : 0 ≤ noRepeat m r := by unfold noRepeat; positivity
      have hright : (0 : ℝ) ≤ (((m + 1) - r : ℕ) : ℝ) / (m + 1) := by
        positivity
      have hrecL : noRepeat m (r + 1) =
          (((m - r : ℕ) : ℝ) / m) * noRepeat m r := by
        unfold noRepeat
        rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
        ring
      have hrecR : noRepeat (m + 1) (r + 1) =
          ((((m + 1) - r : ℕ) : ℝ) / (m + 1 : ℝ)) *
            noRepeat (m + 1) r := by
        unfold noRepeat
        rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
        field_simp [ne_of_gt hm1pos]
        push_cast
        ring
      rw [hrecL, hrecR]
      exact mul_le_mul hfac ih hleft hright
    · have hzero : m.descFactorial (r + 1) = 0 :=
        Nat.descFactorial_of_lt (by omega)
      rw [noRepeat, hzero, Nat.cast_zero, zero_div]
      unfold noRepeat
      positivity

/-- For a [valid success probability](hyp:heta) and [positive alphabet](hyp:hm),
[increasing the alphabet](goal) cannot raise the averaged repeat probability. -/
theorem repeat_antitone_succ (T m : ℕ) (eta : ℝ)
    (hm : 0 < m) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    birthdayRepeat T (m + 1) eta ≤ birthdayRepeat T m eta := by
  unfold birthdayRepeat binomialAverage
  apply Finset.sum_le_sum
  intro r hr
  have hw : 0 ≤ Causalean.Mathlib.Probability.binomialWeight T eta r := by
    simp only [Causalean.Mathlib.Probability.binomialWeight]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heta.1 _))
      (pow_nonneg (sub_nonneg.mpr heta.2) _)
  apply mul_le_mul_of_nonneg_left _ hw
  unfold repeatKernel
  linarith [noRepeat_mono_succ m r hm]

/-- For a [valid success probability](hyp:heta), [positive smaller
alphabet](hyp:hm), and [ordered alphabet sizes](hyp:hmn), the
[averaged repeat probability is antitone](goal). -/
theorem repeat_antitone (T : ℕ) (eta : ℝ) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    birthdayRepeat T n eta ≤ birthdayRepeat T m eta := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      exact (repeat_antitone_succ T n eta (hm.trans_le hmn) heta).trans ih

end Causalean.Mathlib.Probability.Birthday
