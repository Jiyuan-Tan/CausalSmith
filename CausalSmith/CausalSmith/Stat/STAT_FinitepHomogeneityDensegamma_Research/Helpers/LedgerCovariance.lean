module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerBias

/-! Finite-moment homogeneity testing: single-cutoff covariance rate bounds. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- In a single-cutoff branch the interaction target fits the linear block budget. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hbranch condition](hyp:hbranch). [This is the stated conclusion](goal). -/
-- @node: ledger_single_rank_bound
lemma ledger_single_rank_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid)
    (hbranch : singleBranch v) : ledgerK n v ≤ 2*blockSize n := by
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hES : Eexp v ≤ sumReg v := by
    rcases hbranch with h | h
    · have hh := (div_le_iff₀ hg).mp (exponent_phase_algebra v hv).2.2.2.2.2.2.1
      linarith
    · have h0 : E0 v ≤ qExp v := by
        unfold E0
        apply (div_le_iff₀ he).2
        nlinarith
      have hb := hv.2.2.1.1
      exact (min_le_left _ _).trans (h0.trans (by dsimp [sumReg]; linarith))
  have ht : 1 ≤ ledgerA n v^(-1/sumReg v) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ blockSize n)]
    apply Real.one_le_rpow hs
    have hE : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (div_nonpos_of_nonpos_of_nonneg (by norm_num) hS.le)
  have hu : ledgerA n v^(-1/sumReg v) ≤ (blockSize n:ℝ) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ blockSize n)]
    have hex : (-Eexp v)*(-1/sumReg v) ≤ 1 := by
      have hh : Eexp v/sumReg v ≤ 1 := (div_le_iff₀ hS).2 (by simpa using hES)
      convert hh using 1 <;> ring
    simpa using Real.rpow_le_rpow_of_exponent_le hs hex
  have hM := (ledger_rank_bounds n v hn hv).1
  have hsmall : ¬ n < 4 := by omega
  by_cases hh : ledgerA n v^(-1/sumReg v) ≤ (ledgerM n v:ℝ)
  · have hid : leastPow2Ge (ledgerM n v:ℝ) = ledgerM n v := by
      simp only [ledgerM, if_neg hsmall, leastPow2Ge, Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      simp
    simpa only [ledgerK, if_neg hsmall, max_eq_left hh, hid] using hM
  · have hh' := (ledger_dyadUp_bounds ht).2.trans (mul_le_mul_of_nonneg_left hu (by norm_num))
    rw [← leastPow2Ge_eq_dyadUp ht] at hh'
    simp only [ledgerK, if_neg hsmall, max_eq_right (le_of_not_ge hh)]
    exact_mod_cast hh'

/-- Upward rounding increases the main second moment by at most a factor two. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_main_variance_bound
lemma ledger_main_variance_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerV0 n v ≤ 64*ledgerA n v^(-tExp v) := by
  have hs : 0 < (blockSize n:ℝ) := by
    have : 0 < blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hTpos : 0 < ledgerT0 n v := lt_of_lt_of_le (by norm_num) (ledgerT0_ge_one n v)
  have hr := ledger_dyadUp_bounds (ledger_tail_target_bounds n v hn hv).1
  have ht : ledgerT0 n v ≤ 2*ledgerA n v^(-1/(v.p-1)) := by
    simpa only [ledgerT0, if_neg (by omega : ¬n < 4), max_eq_right hr.1] using hr.2
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ledgerT0 n v) ht
    (show 0 ≤ 2-v.p by linarith [hv.1.2])
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity), ← Real.rpow_mul ha.le] at hpow
  have he : (-1/(v.p-1))*(2-v.p) = -tExp v := by unfold tExp; ring
  rw [he] at hpow
  have htwo : (2:ℝ)^(2-v.p) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show 2-v.p ≤ 1 by linarith [hv.1.1])
  unfold ledgerV0
  calc
    _ ≤ 32*((2:ℝ)^(2-v.p)*ledgerA n v^(-tExp v)) := by gcongr
    _ ≤ 32*(2*ledgerA n v^(-tExp v)) := by gcongr
    _ = _ := by ring

/-- Exact block factors and the linear rank budget bound the single-cutoff covariance. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hbranch condition](hyp:hbranch). [This is the stated conclusion](goal). -/
-- @node: ledger_single_covariance_bound
lemma ledger_single_covariance_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid)
    (hbranch : singleBranch v) :
    ledgerCov n v ≤ 24576*ledgerA n v^(-tExp v)/(blockSize n:ℝ) := by
  have hsN : 2 ≤ blockSize n := by unfold blockSize; omega
  have hs : (2:ℝ) ≤ blockSize n := by exact_mod_cast hsN
  have hK : (ledgerK n v:ℝ) ≤ 2*(blockSize n:ℝ) := by
    exact_mod_cast ledger_single_rank_bound n v hn hv hbranch
  have hT : 0 ≤ ledgerT0 n v := by linarith [ledgerT0_ge_one n v]
  have hV : 0 ≤ ledgerV0 n v := by unfold ledgerV0; positivity
  have hspos : (0:ℝ) < blockSize n := by linarith
  have hsm : (0:ℝ) < (blockSize n:ℝ)-1 := by linarith
  have hKV : 0 ≤ (ledgerK n v:ℝ)*ledgerV0 n v := by positivity
  have hid : ledgerCov n v = 256*ledgerV0 n v/(blockSize n:ℝ)+
      32*((ledgerK n v:ℝ)*ledgerV0 n v)/((blockSize n:ℝ)*((blockSize n:ℝ)-1)) := by
    simp only [ledgerCov, ledgerL1, ledgerL2, if_neg (by omega : ¬n < 4), if_pos hbranch, add_zero]
    ring_nf
    rw [Real.sq_sqrt hV, Real.sq_sqrt hKV]
    ring
  rw [hid]
  have hc : 32*((ledgerK n v:ℝ)*ledgerV0 n v)/((blockSize n:ℝ)*((blockSize n:ℝ)-1)) ≤
      128*ledgerV0 n v/(blockSize n:ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (blockSize n:ℝ)*((blockSize n:ℝ)-1)) (by positivity : 0 < (blockSize n:ℝ))).2
    have hh : 32*(ledgerK n v:ℝ) ≤ 128*((blockSize n:ℝ)-1) := by nlinarith
    have hvv := mul_le_mul_of_nonneg_right hh hV
    nlinarith [mul_le_mul_of_nonneg_right hvv (by positivity : 0 ≤ (blockSize n:ℝ))]
  calc
    _ ≤ 384*ledgerV0 n v/(blockSize n:ℝ) := by
      calc
        _ ≤ 256*ledgerV0 n v/(blockSize n:ℝ)+128*ledgerV0 n v/(blockSize n:ℝ) := add_le_add_right hc _
        _ = _ := by ring
    _ ≤ 384*(64*ledgerA n v^(-tExp v))/(blockSize n:ℝ) := by
      gcongr
      exact ledger_main_variance_bound n v hn hv
    _ = _ := by ring

/-- The coarse rank is at most twice its unrounded approximation target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_coarse_target_upper
lemma ledger_coarse_target_upper (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    (ledgerM n v:ℝ) ≤ 2*ledgerA n v^(-1/v.γ) := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hE : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have ht : 1 ≤ ledgerA n v^(-1/v.γ) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ blockSize n)]
    apply Real.one_le_rpow hs
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (div_nonpos_of_nonpos_of_nonneg (by norm_num) hg.le)
  simp only [ledgerM, if_neg (by omega : ¬n < 4)]
  rw [leastPow2Ge_eq_dyadUp ht]
  exact (ledger_dyadUp_bounds ht).2

/-- The pure-tail channel identity makes the dimension-weighted main noise at most the squared target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_tail_noise_balance
lemma ledger_tail_noise_balance (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerA n v^(-1/(2*v.γ))*ledgerA n v^(-tExp v)/(blockSize n:ℝ) ≤ ledgerA n v^2 := by
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hspos : (0:ℝ) < blockSize n := by linarith
  have hbalance : E0 v*(2+tExp v+1/(2*v.γ)) = 1 := by
    have hqn : qExp v ≠ 0 := ne_of_gt hq
    unfold E0 tExp
    field_simp [ne_of_gt he, ne_of_gt hm, ne_of_gt hg]
    have hid : v.p*qExp v = v.p-1 := by unfold qExp; field_simp
    nlinarith [mul_pos hg hq]
  have hfactor : 0 < 2+tExp v+1/(2*v.γ) := by
    have ht : 0 ≤ tExp v := div_nonneg (by linarith [hv.1.2]) hm.le
    positivity
  have hbound := mul_le_mul_of_nonneg_right (show Eexp v ≤ E0 v from min_le_left _ _) hfactor.le
  rw [hbalance] at hbound
  have hex : (-Eexp v)*(-1/(2*v.γ))+(-Eexp v)*(-tExp v)-1 ≤ (-Eexp v)*2 := by
    linear_combination hbound
  unfold ledgerA
  rw [← Real.rpow_natCast, ← Real.rpow_mul hspos.le,
    ← Real.rpow_mul hspos.le, ← Real.rpow_mul hspos.le,
    ← Real.rpow_add hspos]
  conv_lhs => arg 2; rw [← Real.rpow_one (blockSize n:ℝ)]
  rw [← Real.rpow_sub hspos]
  exact Real.rpow_le_rpow_of_exponent_le hs hex

/-- The single-cutoff branch satisfies the complete declared analytic covariance rate. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hbranch condition](hyp:hbranch). [This is the stated conclusion](goal). -/
-- @node: ledger_single_covariance_rate
lemma ledger_single_covariance_rate (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid)
    (hbranch : singleBranch v) :
    Real.sqrt (ledgerM n v)*ledgerCov n v ≤ Astar v*ledgerA n v^2 := by
  have hs : 0 < (blockSize n:ℝ) := by
    have : 0 < blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hM : Real.sqrt (ledgerM n v) ≤ Real.sqrt 2*ledgerA n v^(-1/(2*v.γ)) := by
    calc
      _ ≤ Real.sqrt (2*ledgerA n v^(-1/v.γ)) := Real.sqrt_le_sqrt (ledger_coarse_target_upper n v hn hv)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow (ledgerA n v^(-1/v.γ)),
          ← Real.rpow_mul ha.le]
        congr 2
        ring
  have hcovnonneg : 0 ≤ ledgerCov n v := by
    have hh : (0:ℝ) < (blockSize n:ℝ)-1 := by
      have : 2 ≤ blockSize n := by unfold blockSize; omega
      have : (2:ℝ) ≤ blockSize n := by exact_mod_cast this
      linarith
    unfold ledgerCov
    split <;> positivity
  have hc := ledger_single_covariance_bound n v hn hv hbranch
  have hweight := ledger_tail_noise_balance n v hn hv
  have hA : 24576*Real.sqrt 2 ≤ Astar v := by
    unfold Astar
    nlinarith [Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) (sq_nonneg (Lstar v)),
      mul_nonneg (Real.sqrt_nonneg 2) (sq_nonneg (Gstar v))]
  calc
    _ ≤ (Real.sqrt 2*ledgerA n v^(-1/(2*v.γ)))*
        (24576*ledgerA n v^(-tExp v)/(blockSize n:ℝ)) :=
      mul_le_mul hM hc hcovnonneg (by positivity)
    _ = (24576*Real.sqrt 2)*(ledgerA n v^(-1/(2*v.γ))*ledgerA n v^(-tExp v)/(blockSize n:ℝ)) := by ring
    _ ≤ (24576*Real.sqrt 2)*ledgerA n v^2 := mul_le_mul_of_nonneg_left hweight (by positivity)
    _ ≤ Astar v*ledgerA n v^2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
