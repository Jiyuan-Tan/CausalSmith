module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerTuning
public import Mathlib.Algebra.Order.Field.GeomSum

/-! Finite-moment homogeneity testing: geometric sums for the public bias ledger. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The fine rank dominates the interaction approximation target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_interaction_bound
lemma ledger_interaction_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    (ledgerK n v:ℝ)^(-sumReg v) ≤ ledgerA n v := by
  have ha : 0 < ledgerA n v := by
    have hs : 0 < blockSize n := by unfold blockSize; omega
    unfold ledgerA
    positivity
  have hs : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have ht : 1 ≤ ledgerA n v ^ (-1/sumReg v) := by
    have hb : 1 ≤ (blockSize n:ℝ) := by
      have : 1 ≤ blockSize n := by unfold blockSize; omega
      exact_mod_cast this
    unfold ledgerA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    apply Real.one_le_rpow hb
    have he : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr he.le)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hs.le)
  have hr : ledgerA n v ^ (-1/sumReg v) ≤ (ledgerK n v:ℝ) := by
    simp only [ledgerK, if_neg (by omega : ¬n < 4)]
    rw [leastPow2Ge_eq_dyadUp (ht.trans (le_max_right _ _))]
    exact (le_max_right _ _).trans (le_dyadUp (by positivity))
  calc
    _ ≤ (ledgerA n v ^ (-1/sumReg v))^(-sumReg v) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
    _ = ledgerA n v := by
      rw [← Real.rpow_mul ha.le]
      have he : (-1/sumReg v)*(-sumReg v) = 1 := by field_simp
      rw [he, Real.rpow_one]

/-- The main cutoff leaves at most the target scale in negative tail power. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_main_tail_bound
lemma ledger_main_tail_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerT0 n v^(1-v.p) ≤ ledgerA n v := by
  have ha : 0 < ledgerA n v := by
    have hs : 0 < blockSize n := by unfold blockSize; omega
    unfold ledgerA
    positivity
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have hr : ledgerA n v^(-1/(v.p-1)) ≤ ledgerT0 n v := by
    simp only [ledgerT0, if_neg (by omega : ¬n < 4)]
    exact (le_dyadUp (by positivity)).trans (le_max_right _ _)
  calc
    _ ≤ (ledgerA n v^(-1/(v.p-1)))^(1-v.p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
    _ = ledgerA n v := by
      rw [← Real.rpow_mul ha.le]
      have he : (-1/(v.p-1))*(1-v.p) = 1 := by field_simp; ring
      rw [he, Real.rpow_one]

/-- Positive dyadic decay has a uniform finite geometric sum bound. This statement assumes [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: dyadic_decay_sum_bound
lemma dyadic_decay_sum_bound (r : ℝ) (hr : 0 < r) (L : ℕ) :
    (∑ j : Fin L, (2:ℝ)^(-(j.val:ℝ)*r)) ≤ Ageo r := by
  have ht : (2:ℝ)^(-r) < 1 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
      (show -r < 0 by linarith)
  have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := L)
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-r)) ht
  rw [← Finset.range_eq_Ico] at hh
  simp only [pow_zero, one_div] at hh
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (2:ℝ)^(-(j:ℝ)*r)) L]
  calc
    _ = ∑ j ∈ Finset.range L, ((2:ℝ)^(-r))^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ Ageo r := hh

/-- The increment ranks never exceed the final fine rank. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_rank_bound
lemma ledger_increment_rank_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) :
    0 < ledgerM n v ∧ ledgerM n v ≤ ledgerK n v ∧
    ledgerR n v (ledgerL n v) ≤ ledgerK n v := by
  have hm : 0 < ledgerM n v := by
    simp only [ledgerM, if_neg (by omega : ¬n < 4), leastPow2Ge]
    positivity
  have hm1 : 1 ≤ (ledgerM n v:ℝ) := by exact_mod_cast hm
  have hmk : ledgerM n v ≤ ledgerK n v := by
    have hh : (ledgerM n v:ℝ) ≤ (ledgerK n v:ℝ) := by
      simp only [ledgerK, if_neg (by omega : ¬n < 4)]
      rw [leastPow2Ge_eq_dyadUp (hm1.trans (le_max_left _ _))]
      exact (le_max_left _ _).trans (le_dyadUp (by positivity))
    exact_mod_cast hh
  refine ⟨hm, hmk, ?_⟩
  have hd : ledgerK n v / ledgerM n v ≠ 0 := by
    have := (Nat.le_div_iff_mul_le hm).2 (by simpa using hmk : 1*ledgerM n v ≤ ledgerK n v)
    omega
  exact (Nat.mul_le_mul_right (ledgerM n v) (Nat.pow_log_le_self 2 hd)).trans
    (Nat.div_mul_le_self _ _)

/-- Each increment's negative tail power is bounded by the capped target plus its local target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_tail_bound
lemma ledger_increment_tail_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) (j : ℕ) :
    ledgerT n v j^(1-v.p) ≤ ledgerA n v+
      ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v*(ledgerR n v j:ℝ)^v.α := by
  have hs : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  obtain ⟨hM, hMK, hRL⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < ledgerK n v := lt_of_lt_of_le hM hMK
  have hR : 0 < (ledgerR n v j:ℝ) := by unfold ledgerR; positivity
  let z := (ledgerR n v j:ℝ)^(-v.α)/
    (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v)
  have hz : 0 < z := by dsimp [z]; positivity
  have hlocal : (z^(1/(v.p-1)))^(1-v.p) =
      ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v*(ledgerR n v j:ℝ)^v.α := by
    rw [← Real.rpow_mul hz.le]
    have he : (1/(v.p-1))*(1-v.p) = -1 := by field_simp; ring
    rw [he, Real.rpow_neg_one]
    dsimp [z]
    rw [inv_div, Real.rpow_neg hR.le]
    field_simp
  have hmain : (ledgerA n v^(-1/(v.p-1)))^(1-v.p) = ledgerA n v := by
    rw [← Real.rpow_mul ha.le]
    have he : (-1/(v.p-1))*(1-v.p) = 1 := by field_simp; ring
    rw [he, Real.rpow_one]
  have hdom : min (ledgerA n v^(-1/(v.p-1))) (z^(1/(v.p-1))) ≤ ledgerT n v j := by
    simp only [ledgerT, if_neg (by omega : ¬n < 4)]
    exact (le_max_right _ _).trans (le_dyadUp (by positivity))
  have hpow := Real.rpow_le_rpow_of_nonpos
    (lt_min (by positivity) (by positivity)) hdom (show 1-v.p ≤ 0 by linarith)
  rcases le_total (ledgerA n v^(-1/(v.p-1))) (z^(1/(v.p-1))) with h | h
  · rw [min_eq_left h, hmain] at hpow
    exact hpow.trans (le_add_of_nonneg_right (by positivity))
  · rw [min_eq_right h, hlocal] at hpow
    exact hpow.trans (le_add_of_nonneg_left ha.le)

/-- Summing approximation tails across the dyadic refinement costs one geometric multiplier. This statement assumes [the hn condition](hyp:hn), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: ledger_rank_decay_sum_bound
lemma ledger_rank_decay_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (r : ℝ) (hr : 0 < r) :
    (∑ j : Fin (ledgerL n v), (ledgerR n v j.val:ℝ)^(-r)) ≤ Ageo r := by
  obtain ⟨hm, hmk, hlast⟩ := ledger_increment_rank_bound n v hn
  apply le_trans (Finset.sum_le_sum (fun j hj => ?_)) (dyadic_decay_sum_bound r hr _)
  have hh : (2:ℝ)^j.val ≤ (ledgerR n v j.val:ℝ) := by
    have hm1 : (1:ℝ) ≤ ledgerM n v := by exact_mod_cast hm
    simp only [ledgerR, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [show 0 ≤ (2:ℝ)^j.val by positivity]
  calc
    _ ≤ ((2:ℝ)^j.val)^(-r) := Real.rpow_le_rpow_of_nonpos (by positivity) hh (by linarith)
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring

/-- Backwards summation of the positive rank ratios also costs one geometric multiplier. This statement assumes [the hn condition](hyp:hn), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: ledger_rank_ratio_sum_bound
lemma ledger_rank_ratio_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (r : ℝ) (hr : 0 < r) :
    (∑ j : Fin (ledgerL n v), ((ledgerR n v (j.val+1):ℝ)/ledgerK n v)^r) ≤ Ageo r := by
  obtain ⟨hm, hmk, hlast⟩ := ledger_increment_rank_bound n v hn
  have hk : 0 < (ledgerK n v:ℝ) := by exact_mod_cast (lt_of_lt_of_le hm hmk)
  have hterm (j : Fin (ledgerL n v)) :
      ((ledgerR n v (j.val+1):ℝ)/ledgerK n v)^r ≤
      (2:ℝ)^(-((ledgerL n v-1-j.val:ℕ):ℝ)*r) := by
    have he : j.val+1+(ledgerL n v-1-j.val) = ledgerL n v := by omega
    have hmul : (ledgerR n v (j.val+1):ℝ)*(2:ℝ)^(ledgerL n v-1-j.val) ≤ ledgerK n v := by
      have heq : ledgerR n v (j.val+1)*2^(ledgerL n v-1-j.val) = ledgerR n v (ledgerL n v) := by
        unfold ledgerR
        rw [mul_assoc, mul_comm (ledgerM n v), ← mul_assoc, ← pow_add, he]
      exact_mod_cast heq ▸ hlast
    have hh : (ledgerR n v (j.val+1):ℝ)/ledgerK n v ≤
        ((2:ℝ)^(ledgerL n v-1-j.val))⁻¹ := by
      apply (div_le_iff₀ hk).2
      apply (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(ledgerL n v-1-j.val))).mpr at hmul
      simpa [div_eq_mul_inv, mul_comm] using hmul
    calc
      _ ≤ (((2:ℝ)^(ledgerL n v-1-j.val))⁻¹)^r :=
        Real.rpow_le_rpow (by positivity) hh hr.le
      _ = _ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hterm j)
  apply hh.trans
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (2:ℝ)^(-((ledgerL n v-1-j:ℕ):ℝ)*r))]
  rw [Finset.sum_range_reflect (fun j : ℕ => (2:ℝ)^(-(j:ℝ)*r))]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (2:ℝ)^(-(j:ℝ)*r))]
  exact dyadic_decay_sum_bound r hr _

/-- The local bias contributions are bounded by the two geometric sequences in the roadmap. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_bias_bound
lemma ledger_increment_bias_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) (j : ℕ) :
    aLev n v (j+1)*ledgerT n v (j+1)^(1-v.p) ≤
      80*ledgerA n v*((ledgerR n v j:ℝ)^(-v.α)+
        ((ledgerR n v (j+1):ℝ)/ledgerK n v)^lam0 v) := by
  obtain ⟨hm, hmk, hlast⟩ := ledger_increment_rank_bound n v hn
  have hr : 0 < (ledgerR n v j:ℝ) := by unfold ledgerR; positivity
  have hα : v.α ≤ 1 := hv.2.1.2
  have htwo : (2:ℝ)^v.α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα
  have heq : (ledgerR n v j:ℝ)^(-v.α)*(ledgerR n v (j+1):ℝ)^v.α = (2:ℝ)^v.α := by
    have hR : (ledgerR n v (j+1):ℝ) = 2*(ledgerR n v j:ℝ) := by
      simp [ledgerR, pow_succ]; ring
    rw [hR, Real.mul_rpow (by norm_num) hr.le]
    have hc : (ledgerR n v j:ℝ)^(-v.α)*(ledgerR n v j:ℝ)^v.α = 1 := by
      rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
    calc
      _ = (2:ℝ)^v.α*((ledgerR n v j:ℝ)^(-v.α)*(ledgerR n v j:ℝ)^v.α) := by ring
      _ = _ := by rw [hc, mul_one]
  have ht := mul_le_mul_of_nonneg_left (ledger_increment_tail_bound n v hn hv (j+1))
    (show 0 ≤ aLev n v (j+1) by simp only [aLev, Nat.add_sub_cancel]; positivity)
  simp only [aLev, Nat.add_sub_cancel] at ht ⊢
  have ha : 0 ≤ ledgerA n v := by unfold ledgerA; positivity
  have hq : 0 ≤ ((ledgerR n v (j+1):ℝ)/ledgerK n v)^lam0 v := by positivity
  have hmul := mul_le_mul_of_nonneg_left htwo (mul_nonneg ha hq)
  have hprod : 40*(ledgerR n v j:ℝ)^(-v.α)*
      (ledgerA n v+ledgerA n v*((ledgerR n v (j+1):ℝ)/ledgerK n v)^lam0 v*(ledgerR n v (j+1):ℝ)^v.α) =
      40*ledgerA n v*(ledgerR n v j:ℝ)^(-v.α)+
      40*(ledgerA n v*((ledgerR n v (j+1):ℝ)/ledgerK n v)^lam0 v)*(2:ℝ)^v.α := by
    calc
      _ = 40*ledgerA n v*(ledgerR n v j:ℝ)^(-v.α)+
        40*(ledgerA n v*((ledgerR n v (j+1):ℝ)/ledgerK n v)^lam0 v)*
        ((ledgerR n v j:ℝ)^(-v.α)*(ledgerR n v (j+1):ℝ)^v.α) := by ring
      _ = _ := by rw [heq]
  rw [hprod] at ht
  nlinarith [mul_nonneg ha (Real.rpow_nonneg hr.le (-v.α))]

/-- The complete bias ledger sums both decay sequences without any logarithmic loss. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_bias_bound
lemma ledger_bias_bound (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerBias n v ≤ Bstar v*ledgerA n v := by
  have hα := ledger_rank_decay_sum_bound n v hn v.α hv.2.1.1
  have hl : 0 < lam0 v := by
    have hp : 0 < v.p := by linarith [hv.1.1]
    have hm : 0 < v.p-1 := by linarith [hv.1.1]
    unfold lam0
    positivity
  have hgeom := ledger_rank_ratio_sum_bound n v hn (lam0 v) hl
  have ha : 0 ≤ ledgerA n v := by unfold ledgerA; positivity
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (ledgerL n v)) hj => ledger_increment_bias_bound n v hn hv j.val)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hs : (∑ j : Fin (ledgerL n v), aLev n v (j.val+1)*ledgerT n v (j.val+1)^(1-v.p)) ≤
      80*ledgerA n v*(Ageo v.α+Ageo (lam0 v)) := by
    have h := add_le_add hα hgeom
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 80*ledgerA n v by positivity)
    nlinarith
  have hi := ledger_interaction_bound n v hn hv
  have ht := ledger_main_tail_bound n v hn hv
  have hge : 0 ≤ Ageo v.α+Ageo (lam0 v) := by
    have h := add_le_add hα hgeom
    apply le_trans _ h
    exact add_nonneg
      (Finset.sum_nonneg (fun j hj => Real.rpow_nonneg (by positivity) _))
      (Finset.sum_nonneg (fun j hj => Real.rpow_nonneg (by positivity) _))
  simp only [ledgerBias, if_neg (by omega : ¬n < 4)]
  unfold Bstar
  split <;> nlinarith [mul_nonneg ha hge]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
