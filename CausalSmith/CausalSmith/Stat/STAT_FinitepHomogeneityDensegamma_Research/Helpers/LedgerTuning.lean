module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseAlgebra

/-! Finite-moment homogeneity testing: dyadic tuning bounds. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Upward dyadic rounding is monotone on positive inputs. This statement assumes [the hx condition](hyp:hx), [the hxy condition](hyp:hxy). [This is the stated conclusion](goal). -/
-- @node: dyadUp_mono
lemma dyadUp_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    dyadUp x ≤ dyadUp y := by
  unfold dyadUp
  apply (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).2
  exact Int.ceil_mono (Real.logb_le_logb_of_le (by norm_num) hx hxy)

/-- Rounding a target at least one stays above one and below twice its target. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: ledger_dyadUp_bounds
lemma ledger_dyadUp_bounds {x : ℝ} (hx : 1 ≤ x) : 1 ≤ dyadUp x ∧ dyadUp x ≤ 2*x := by
  have hlog : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hceil : (Int.ceil (Real.logb 2 x) : ℝ) ≤ Real.logb 2 x+1 :=
    (Int.ceil_lt_add_one _).le
  constructor
  · unfold dyadUp
    have hk : (0:ℤ) ≤ Int.ceil (Real.logb 2 x) := by
      exact_mod_cast hlog.trans (Int.le_ceil _)
    simpa using (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).2 hk
  · unfold dyadUp
    rw [← Real.rpow_intCast]
    calc
      (2:ℝ) ^ (Int.ceil (Real.logb 2 x) : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 x+1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = 2*x := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one,
          Real.rpow_logb (by norm_num) (by norm_num) (by linarith : 0 < x)]
        ring

/-- The public tail target is a block-size power with the positive exponent E/(p−1). This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_tail_target_bounds
lemma ledger_tail_target_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    1 ≤ ledgerA n v ^ (-1/(v.p-1)) ∧
    ledgerA n v ^ (-1/(v.p-1)) ≤ (blockSize n:ℝ) := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hphase := exponent_phase_algebra v hv
  have hE : 0 < Eexp v := hphase.2.2.1
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have hpow : ledgerA n v ^ (-1/(v.p-1)) =
      (blockSize n:ℝ) ^ (Eexp v/(v.p-1)) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    congr 1
    ring
  rw [hpow]
  constructor
  · exact Real.one_le_rpow hs (div_pos hE hm).le
  · calc
      (blockSize n:ℝ) ^ (Eexp v/(v.p-1)) ≤ (blockSize n:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs hphase.2.2.2.2.2.2.2.2.1.le
      _ = _ := Real.rpow_one _

/-- Every level cutoff lies between one and the main cutoff, which is at most twice the block size. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_cutoff_bounds
lemma ledger_cutoff_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    1 ≤ ledgerT0 n v ∧ ledgerT0 n v ≤ 2*(blockSize n:ℝ) ∧
    ∀ j : ℕ, 1 ≤ ledgerT n v j ∧ ledgerT n v j ≤ ledgerT0 n v := by
  have hn' : ¬ n < 4 := by omega
  obtain ⟨htlo, hthi⟩ := ledger_tail_target_bounds n v hn hv
  have ht := ledger_dyadUp_bounds htlo
  have hmain : ledgerT0 n v = dyadUp (ledgerA n v ^ (-1/(v.p-1))) := by
    simp only [ledgerT0, if_neg hn', max_eq_right ht.1]
  rw [hmain]
  refine ⟨ht.1, ht.2.trans (by gcongr), ?_⟩
  intro j
  simp only [ledgerT, if_neg hn']
  constructor
  · exact (ledger_dyadUp_bounds (le_max_left _ _)).1
  · apply dyadUp_mono (by positivity)
    exact max_le htlo (min_le_left _ _)

/-- Natural dyadic rank rounding agrees with real dyadic rounding above one. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: leastPow2Ge_eq_dyadUp
lemma leastPow2Ge_eq_dyadUp {x : ℝ} (hx : 1 ≤ x) :
    (leastPow2Ge x:ℝ) = dyadUp x := by
  have hl : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  simp only [leastPow2Ge, Nat.cast_pow, Nat.cast_ofNat, dyadUp]
  rw [← zpow_natCast, Int.natCast_ceil_eq_ceil hl]

/-- Dyadic rank rounding does not change an existing power of two. [This is the stated conclusion](goal). -/
-- @node: leastPow2Ge_pow
lemma leastPow2Ge_pow (k : ℕ) : leastPow2Ge ((2:ℝ)^k) = 2^k := by
  simp [leastPow2Ge, Real.logb_pow]

/-- Both tuning ranks fit the public linear and quadratic block-size budgets. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_rank_bounds
lemma ledger_rank_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerM n v ≤ 2*blockSize n ∧ ledgerK n v ≤ 2*blockSize n^2 := by
  have hn' : ¬ n < 4 := by omega
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hp := exponent_phase_algebra v hv
  have hE : 0 < Eexp v := hp.2.2.1
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hS : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have ht (r : ℝ) : ledgerA n v ^ (-1/r) = (blockSize n:ℝ) ^ (Eexp v/r) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    congr 1
    ring
  have hMtlo : 1 ≤ ledgerA n v ^ (-1/v.γ) := by
    rw [ht]; exact Real.one_le_rpow hs (div_pos hE hg).le
  have hMthi : ledgerA n v ^ (-1/v.γ) ≤ (blockSize n:ℝ) := by
    rw [ht]
    simpa using Real.rpow_le_rpow_of_exponent_le hs hp.2.2.2.2.2.2.1
  have hM : ledgerM n v ≤ 2*blockSize n := by
    have hh := (ledger_dyadUp_bounds hMtlo).2.trans (mul_le_mul_of_nonneg_left hMthi (by norm_num))
    rw [← leastPow2Ge_eq_dyadUp hMtlo] at hh
    simp only [ledgerM, if_neg hn']
    exact_mod_cast hh
  have hM2 : ledgerM n v ≤ 2*blockSize n^2 := by
    have hsN : 1 ≤ blockSize n := by unfold blockSize; omega
    nlinarith [Nat.mul_self_le_mul_self hsN]
  have hKtlo : 1 ≤ ledgerA n v ^ (-1/sumReg v) := by
    rw [ht]; exact Real.one_le_rpow hs (div_pos hE hS).le
  have hKthi : ledgerA n v ^ (-1/sumReg v) ≤ (blockSize n:ℝ)^2 := by
    rw [ht]
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hs hp.2.2.2.2.2.2.2.1.le
  refine ⟨hM, ?_⟩
  by_cases h : ledgerA n v ^ (-1/sumReg v) ≤ (ledgerM n v:ℝ)
  · have hid : leastPow2Ge (ledgerM n v:ℝ) = ledgerM n v := by
      rw [show ledgerM n v = 2^(Nat.ceil (Real.logb 2 (ledgerA n v ^ (-1/v.γ)))) by
        simp only [ledgerM, if_neg hn', leastPow2Ge]]
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact leastPow2Ge_pow _
    simpa only [ledgerK, if_neg hn', max_eq_left h, hid] using hM2
  · have hh := (ledger_dyadUp_bounds hKtlo).2.trans (mul_le_mul_of_nonneg_left hKthi (by norm_num))
    rw [← leastPow2Ge_eq_dyadUp hKtlo] at hh
    simp only [ledgerK, if_neg hn', max_eq_right (le_of_not_ge h)]
    exact_mod_cast hh

/-- Upward dyadic rounding dominates every positive target. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: le_dyadUp
lemma le_dyadUp {x : ℝ} (hx : 0 < x) : x ≤ dyadUp x := by
  unfold dyadUp
  rw [← Real.rpow_intCast]
  calc
    x = (2:ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)

/-- The chosen coarse rank makes its approximation error at most the block target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_approximation_bound
lemma ledger_approximation_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    (ledgerM n v:ℝ)^(-v.γ) ≤ ledgerA n v := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have ht : 1 ≤ ledgerA n v ^ (-1/v.γ) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    apply Real.one_le_rpow hs
    have he : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr he.le) (div_nonpos_of_nonpos_of_nonneg (by norm_num) hg.le)
  have hr : ledgerA n v ^ (-1/v.γ) ≤ (ledgerM n v:ℝ) := by
    simp only [ledgerM, if_neg (by omega : ¬n < 4)]
    rw [leastPow2Ge_eq_dyadUp ht]
    exact le_dyadUp (by positivity)
  calc
    (ledgerM n v:ℝ)^(-v.γ) ≤ (ledgerA n v ^ (-1/v.γ))^(-v.γ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
    _ = ledgerA n v := by
      rw [← Real.rpow_mul ha.le]
      have he : (-1/v.γ)*(-v.γ) = 1 := by field_simp
      rw [he, Real.rpow_one]

/-- Replacing the half-sample size by the full sample costs at most a factor three. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledgerA_le_three_rho
lemma ledgerA_le_three_rho (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerA n v ≤ 3*rho n v := by
  have hsN : 1 ≤ blockSize n := by unfold blockSize; omega
  have hs : 0 < (blockSize n:ℝ) := by exact_mod_cast (by omega : 0 < blockSize n)
  have hn3 : (n:ℝ) ≤ 3*(blockSize n:ℝ) := by
    have : n ≤ 3*blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have he : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have he1 : Eexp v ≤ 1 := by
    have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
    have h := (div_le_iff₀ hg).mp (exponent_phase_algebra v hv).2.2.2.2.2.2.1
    linarith [hv.2.2.2.2]
  have hr := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n:ℝ)) hn3 (neg_nonpos.mpr he.le)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hs.le] at hr
  have h3 : (3:ℝ)^Eexp v ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) he1
  have hid : (3:ℝ)^Eexp v * (3:ℝ)^(-Eexp v) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  unfold ledgerA rho
  calc
    (blockSize n:ℝ)^(-Eexp v) = (3:ℝ)^Eexp v*((3:ℝ)^(-Eexp v)*(blockSize n:ℝ)^(-Eexp v)) := by
      rw [← mul_assoc, hid, one_mul]
    _ ≤ (3:ℝ)^Eexp v*(n:ℝ)^(-Eexp v) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ 3*(n:ℝ)^(-Eexp v) := mul_le_mul_of_nonneg_right h3 (by positivity)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
