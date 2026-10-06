module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerCovariance

/-! Geometric canonical-pair noise bounds for the multilevel score ledger. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- In the multilevel branch both rounded ranks fit twice the interaction target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_fine_target_upper
lemma ledger_multilevel_fine_target_upper (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    (ledgerK n v:ℝ) ≤ 2*ledgerA n v^(-1/sumReg v) := by
  have hS : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hSg : sumReg v < v.γ := lt_of_not_ge (fun h => hb (Or.inl h))
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hE : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have ht : 1 ≤ ledgerA n v^(-1/sumReg v) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    apply Real.one_le_rpow hs
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hE.le)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hS.le)
  have htargets : ledgerA n v^(-1/v.γ) ≤ ledgerA n v^(-1/sumReg v) := by
    unfold ledgerA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n),
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    apply Real.rpow_le_rpow_of_exponent_le hs
    have hd : Eexp v/v.γ ≤ Eexp v/sumReg v :=
      div_le_div_of_nonneg_left hE.le hS hSg.le
    convert hd using 1 <;> ring
  have hsmall : ¬ n < 4 := by omega
  by_cases hh : ledgerA n v^(-1/sumReg v) ≤ (ledgerM n v:ℝ)
  · have hid : leastPow2Ge (ledgerM n v:ℝ) = ledgerM n v := by
      simp only [ledgerM, if_neg hsmall, leastPow2Ge, Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      simp
    simp only [ledgerK, if_neg hsmall, max_eq_left hh, hid]
    exact (ledger_coarse_target_upper n v hn hv).trans
      (mul_le_mul_of_nonneg_left htargets (by norm_num))
  · simp only [ledgerK, if_neg hsmall, max_eq_right (le_of_not_ge hh)]
    rw [leastPow2Ge_eq_dyadUp ht]
    exact (ledger_dyadUp_bounds ht).2

/-- The fine-rank propensity amplitude is at most two, including upward rounding. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_amplitude_bound
lemma ledger_multilevel_amplitude_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    ledgerA n v*(ledgerK n v:ℝ)^v.α ≤ 2 := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hE : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have ha1 : ledgerA n v ≤ 1 := by
    simpa [ledgerA] using Real.rpow_le_rpow_of_exponent_le hs (neg_nonpos.mpr hE.le)
  have hS : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have hK := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ledgerK n v)
    (ledger_multilevel_fine_target_upper n v hn hv hb) hv.2.1.1.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
    ← Real.rpow_mul ha.le] at hK
  have htwo : (2:ℝ)^v.α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hv.2.1.2
  have hex : 0 ≤ 1+(-1/sumReg v)*v.α := by
    apply (div_nonneg (show 0 ≤ v.β from hv.2.2.1.1.le) hS.le).trans_eq
    have heq : v.β/sumReg v = 1+(-1/sumReg v)*v.α := by
      field_simp [hS.ne']
      dsimp [sumReg]
      ring
    exact heq
  have hpow : ledgerA n v^(1+(-1/sumReg v)*v.α) ≤ 1 :=
    Real.rpow_le_one ha.le ha1 hex
  calc
    _ ≤ ledgerA n v*((2:ℝ)^v.α*ledgerA n v^((-1/sumReg v)*v.α)) :=
      mul_le_mul_of_nonneg_left hK ha.le
    _ = (2:ℝ)^v.α*ledgerA n v^(1+(-1/sumReg v)*v.α) := by
      rw [Real.rpow_add ha, Real.rpow_one]; ring
    _ ≤ 2*1 := mul_le_mul htwo hpow (by positivity) (by norm_num)
    _ = 2 := by ring

/-- The backwards geometric exponent has the positive lower bound specified by the roadmap. This statement assumes [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_eta_bound
lemma ledger_multilevel_eta_bound (v : Params) (hv : v.Valid) (hb : ¬ singleBranch v) :
    0 < eta0 v ∧ eta0 v ≤ 1-(v.α+lam0 v)*tExp v ∧
    0 ≤ v.α*tExp v ∧ v.α*tExp v < 1 := by
  have hp : 0 < v.p := by linarith [hv.1.1]
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have ht : 0 ≤ tExp v := div_nonneg (by linarith [hv.1.2]) hm.le
  have hα : v.α < qExp v := lt_of_not_ge (fun h => hb (Or.inr h))
  have hl : 0 < lam0 v := by unfold lam0; positivity
  have he : 0 < eta0 v := by unfold eta0; positivity
  have hid : 1-(qExp v+lam0 v)*tExp v = eta0 v := by
    unfold qExp lam0 tExp eta0
    field_simp
    ring
  have hle : (v.α+lam0 v)*tExp v ≤ (qExp v+lam0 v)*tExp v :=
    mul_le_mul_of_nonneg_right (by linarith) ht
  refine ⟨he, ?_, mul_nonneg hv.2.1.1.le ht, ?_⟩
  · linarith
  · nlinarith [mul_nonneg hl.le ht]

/-- The interaction exponent balances the dimension-weighted canonical noise. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_canonical_noise_balance
lemma ledger_canonical_noise_balance (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerA n v^(-1/(2*v.γ))*ledgerA n v^(-(1+v.β*tExp v)/sumReg v)/(blockSize n:ℝ)^2 ≤
      ledgerA n v^2 := by
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hspos : (0:ℝ) < blockSize n := by linarith
  have hbalance : E4 v*(2+(1+v.β*tExp v)/sumReg v+1/(2*v.γ)) = 2 := by
    have htq : 2+tExp v = 1/qExp v := by
      unfold tExp qExp
      field_simp [hm.ne', hp.ne']
      ring
    have hid : 2*sumReg v+(1+v.β*tExp v)+sumReg v/(2*v.γ) = Dp v := by
      unfold Dp
      rw [show v.β/qExp v = v.β*(2+tExp v) by rw [htq]; ring]
      dsimp [sumReg]
      ring
    unfold E4
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hd.ne').2
    field_simp [hS.ne', hg.ne'] at hid ⊢
    nlinarith [hid]
  have ht : 0 ≤ tExp v := div_nonneg (by linarith [hv.1.2]) hm.le
  have hβ : 0 < v.β := hv.2.2.1.1
  have hfactor : 0 < 2+(1+v.β*tExp v)/sumReg v+1/(2*v.γ) := by positivity
  have hbound := mul_le_mul_of_nonneg_right (show Eexp v ≤ E4 v from min_le_right _ _) hfactor.le
  rw [hbalance] at hbound
  have hex : (-Eexp v)*(-1/(2*v.γ))+(-Eexp v)*(-(1+v.β*tExp v)/sumReg v)-2 ≤ (-Eexp v)*2 := by
    linear_combination hbound
  unfold ledgerA
  simp only [← Real.rpow_two]
  rw [← Real.rpow_mul hspos.le, ← Real.rpow_mul hspos.le,
    ← Real.rpow_mul hspos.le, ← Real.rpow_add hspos, ← Real.rpow_sub hspos]
  exact Real.rpow_le_rpow_of_exponent_le hs hex

/-- Dyadic rounding and the positive-power guard bound every increment second moment. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_variance_guard
lemma ledger_increment_variance_guard (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (j : ℕ) :
    ledgerV n v j ≤ 64*max 1
      (((ledgerR n v j:ℝ)^(-v.α)/
        (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v))^tExp v) := by
  obtain ⟨hM, hMK, hRL⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < ledgerK n v := lt_of_lt_of_le hM hMK
  have hR : 0 < (ledgerR n v j:ℝ) := by unfold ledgerR; positivity
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have hp : 0 ≤ 2-v.p := by linarith [hv.1.2]
  let z := (ledgerR n v j:ℝ)^(-v.α)/
    (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v)
  have hz : 0 < z := by dsimp [z]; positivity
  have hT : ledgerT n v j ≤ 2*max 1 (z^(1/(v.p-1))) := by
    simp only [ledgerT, if_neg (by omega : ¬n < 4)]
    apply (ledger_dyadUp_bounds (le_max_left _ _)).2.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le_max_left 1 (min_le_right _ _)
  have hpow := Real.rpow_le_rpow (by
    simp only [ledgerT, if_neg (by omega : ¬n < 4)]
    exact (le_dyadUp (by positivity)).trans' (by positivity)) hT hp
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
    Real.rpow_max (by norm_num) (by positivity) hp,
    Real.one_rpow, ← Real.rpow_mul hz.le] at hpow
  have hid : (1/(v.p-1))*(2-v.p) = tExp v := by unfold tExp; ring
  rw [hid] at hpow
  have htwo : (2:ℝ)^(2-v.p) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show 2-v.p ≤ 1 by linarith [hv.1.1])
  change 32*ledgerT n v j^(2-v.p) ≤ 64*max 1 (z^tExp v)
  calc
    _ ≤ 32*((2:ℝ)^(2-v.p)*max 1 (z^tExp v)) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ 32*(2*max 1 (z^tExp v)) := by gcongr
    _ = _ := by ring

/-- Taking square roots of the guarded second moment separates the guard from the local target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_sqrt_variance_guard
lemma ledger_increment_sqrt_variance_guard (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (j : ℕ) :
    Real.sqrt (ledgerV n v j) ≤ Real.sqrt 64*(1+
      ((ledgerR n v j:ℝ)^(-v.α)/
        (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v))^(tExp v/2)) := by
  obtain ⟨hM, hMK, hRL⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < ledgerK n v := lt_of_lt_of_le hM hMK
  have hR : 0 < (ledgerR n v j:ℝ) := by unfold ledgerR; positivity
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  let z := (ledgerR n v j:ℝ)^(-v.α)/
    (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v)
  have hz : 0 < z := by dsimp [z]; positivity
  calc
    _ ≤ Real.sqrt (64*max 1 (z^tExp v)) :=
      Real.sqrt_le_sqrt (ledger_increment_variance_guard n v hn hv j)
    _ = Real.sqrt 64*max 1 (z^(tExp v/2)) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64)]
      congr 1
      rw [Real.sqrt_eq_rpow,
        Real.rpow_max (by norm_num) (by positivity) (by norm_num), Real.one_rpow,
        ← Real.rpow_mul hz.le]
      congr 2
      ring
    _ ≤ Real.sqrt 64*(1+z^(tExp v/2)) := by
      exact mul_le_mul_of_nonneg_left (max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by norm_num)))
        (Real.sqrt_nonneg 64)

/-- The guarded increment splits into its rank term and the positive-exponent tail term. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_sqrt_rank_bound
lemma ledger_increment_sqrt_rank_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (j : ℕ) :
    Real.sqrt ((ledgerR n v j:ℝ)*ledgerV n v j) ≤ Real.sqrt 64*
      (Real.sqrt (ledgerR n v j)+ledgerA n v^(-tExp v/2)*
        (ledgerK n v:ℝ)^(lam0 v*tExp v/2)*
        (ledgerR n v j:ℝ)^((1-(v.α+lam0 v)*tExp v)/2)) := by
  obtain ⟨hM, hMK, hRL⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < (ledgerK n v:ℝ) := by exact_mod_cast lt_of_lt_of_le hM hMK
  have hR : 0 < (ledgerR n v j:ℝ) := by unfold ledgerR; positivity
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hid : Real.sqrt (ledgerR n v j)*
      ((ledgerR n v j:ℝ)^(-v.α)/
        (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v))^(tExp v/2) =
      ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^(lam0 v*tExp v/2)*
        (ledgerR n v j:ℝ)^((1-(v.α+lam0 v)*tExp v)/2) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hR.le hK.le,
      Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow ha.le (by positivity), Real.div_rpow (by positivity) (by positivity)]
    simp only [← Real.rpow_mul ha.le, ← Real.rpow_mul hR.le, ← Real.rpow_mul hK.le]
    have he : (1-(v.α+lam0 v)*tExp v)/2 =
        1/2+(-v.α*(tExp v/2))-lam0 v*(tExp v/2) := by ring
    rw [he, Real.rpow_sub hR, Real.rpow_add hR,
      show -tExp v/2 = -(tExp v/2) by ring, Real.rpow_neg ha.le]
    have hkexp : lam0 v*tExp v/2 = lam0 v*(tExp v/2) := by ring
    rw [hkexp]
    field_simp

  rw [Real.sqrt_mul hR.le]
  calc
    _ ≤ Real.sqrt (ledgerR n v j)*(Real.sqrt 64*(1+
        ((ledgerR n v j:ℝ)^(-v.α)/
          (ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v))^(tExp v/2))) :=
      mul_le_mul_of_nonneg_left (ledger_increment_sqrt_variance_guard n v hn hv j) (Real.sqrt_nonneg _)
    _ = _ := by rw [mul_add, mul_one]; rw [← hid]; ring

/-- Positive geometric multipliers decrease as their decay exponent increases. This statement assumes [the hx condition](hyp:hx), [the hxy condition](hyp:hxy). [This is the stated conclusion](goal). -/
-- @node: Ageo_antitone_positive
lemma Ageo_antitone_positive (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ Ageo y ∧ Ageo y ≤ Ageo x := by
  have hp : (2:ℝ)^(-x) < 1 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
      (show -x < 0 by linarith)
  have hpow : (2:ℝ)^(-y) ≤ (2:ℝ)^(-x) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hden : 0 < 1-(2:ℝ)^(-x) := by linarith
  unfold Ageo
  constructor
  · exact inv_nonneg.mpr (by linarith)
  · simpa only [one_div] using one_div_le_one_div_of_le hden (by linarith)

/-- Positive powers of increment ranks sum geometrically backwards from the final rank. This statement assumes [the hn condition](hyp:hn), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: ledger_rank_growth_sum_bound
lemma ledger_rank_growth_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (r : ℝ) (hr : 0 < r) :
    (∑ j : Fin (ledgerL n v), (ledgerR n v (j.val+1):ℝ)^r) ≤
      (ledgerK n v:ℝ)^r*Ageo r := by
  obtain ⟨hm, hmk, hlast⟩ := ledger_increment_rank_bound n v hn
  have hk : 0 < (ledgerK n v:ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmk
  have he (j : Fin (ledgerL n v)) :
      (ledgerR n v (j.val+1):ℝ)^r =
        (ledgerK n v:ℝ)^r*((ledgerR n v (j.val+1):ℝ)/ledgerK n v)^r := by
    rw [Real.div_rpow (by positivity) hk.le]
    field_simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (ledger_rank_ratio_sum_bound n v hn r hr) (by positivity)

/-- All rank-weighted increment second moments sum to the declared canonical multiplier. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_canonical_sum_bound
lemma ledger_multilevel_canonical_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    (∑ j : Fin (ledgerL n v), Real.sqrt ((ledgerR n v (j.val+1):ℝ)*ledgerV n v (j.val+1))) ≤
      Gstar v*ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2) := by
  obtain ⟨hM, hMK, hRL⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < (ledgerK n v:ℝ) := by exact_mod_cast lt_of_lt_of_le hM hMK
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  obtain ⟨heta, hetale, hat, hatlt⟩ := ledger_multilevel_eta_bound v hv hb
  have ht : 0 ≤ tExp v := div_nonneg (by linarith [hv.1.2]) (by linarith [hv.1.1])
  have hr : 0 < (1-(v.α+lam0 v)*tExp v)/2 := by linarith
  have hgeo := ledger_rank_growth_sum_bound n v hn ((1-(v.α+lam0 v)*tExp v)/2) hr
  have hAgeo := (Ageo_antitone_positive (eta0 v/2) ((1-(v.α+lam0 v)*tExp v)/2)
    (by linarith) (by linarith)).2
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin (ledgerL n v)) hj => ledger_increment_sqrt_rank_bound n v hn hv (j.val+1))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hsqrt : (∑ j : Fin (ledgerL n v), Real.sqrt (ledgerR n v (j.val+1))) ≤
      Real.sqrt (ledgerK n v)*Ageo (1/2) := by
    simp only [Real.sqrt_eq_rpow]
    exact ledger_rank_growth_sum_bound n v hn (1/2) (by norm_num)
  have htail : ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^(lam0 v*tExp v/2)*
      (∑ j : Fin (ledgerL n v), (ledgerR n v (j.val+1):ℝ)^((1-(v.α+lam0 v)*tExp v)/2)) ≤
      ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2)*Ageo (eta0 v/2) := by
    calc
      _ ≤ ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^(lam0 v*tExp v/2)*
          ((ledgerK n v:ℝ)^((1-(v.α+lam0 v)*tExp v)/2)*Ageo (eta0 v/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hgeo.trans (mul_le_mul_of_nonneg_left hAgeo (by positivity))
      _ = _ := by
        have he : (ledgerK n v:ℝ)^(lam0 v*tExp v/2)*
            (ledgerK n v:ℝ)^((1-(v.α+lam0 v)*tExp v)/2) =
            (ledgerK n v:ℝ)^((1-v.α*tExp v)/2) := by
          rw [← Real.rpow_add hK]
          congr 1
          ring
        calc
          _ = ledgerA n v^(-tExp v/2)*
              ((ledgerK n v:ℝ)^(lam0 v*tExp v/2)*
               (ledgerK n v:ℝ)^((1-(v.α+lam0 v)*tExp v)/2))*Ageo (eta0 v/2) := by ring
          _ = _ := by rw [he]
  have hamp := ledger_multilevel_amplitude_bound n v hn hv hb
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ledgerA n v*(ledgerK n v:ℝ)^v.α) hamp (show 0 ≤ tExp v/2 by linarith)
  have hroot : Real.sqrt (ledgerK n v) ≤
      (2:ℝ)^(tExp v/2)*ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2) := by
    rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul hK.le] at hpow
    have hh := mul_le_mul_of_nonneg_right hpow
      (show 0 ≤ ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2) by positivity)
    have heq : (ledgerA n v^(tExp v/2)*(ledgerK n v:ℝ)^(v.α*(tExp v/2)))*
        (ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2)) = Real.sqrt (ledgerK n v) := by
      calc
        _ = (ledgerA n v^(tExp v/2)*ledgerA n v^(-tExp v/2))*
          ((ledgerK n v:ℝ)^(v.α*(tExp v/2))*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add ha, ← Real.rpow_add hK]
          simp only [show tExp v/2+ -tExp v/2 = 0 by ring, Real.rpow_zero, one_mul]
          rw [show v.α*(tExp v/2)+(1-v.α*tExp v)/2 = 1/2 by ring, Real.sqrt_eq_rpow]
    rw [heq] at hh
    simpa only [mul_assoc] using hh
  have hA0 : 0 ≤ Ageo (1/2) := (Ageo_antitone_positive (1/2) (1/2) (by norm_num) le_rfl).1
  have hsqrt' := hsqrt.trans (mul_le_mul_of_nonneg_right hroot hA0)
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hsqrt' (Real.sqrt_nonneg 64))
    (mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg 64))
  unfold Gstar
  calc
    _ ≤ Real.sqrt 64*((2:ℝ)^(tExp v/2)*ledgerA n v^(-tExp v/2)*
          (ledgerK n v:ℝ)^((1-v.α*tExp v)/2)*Ageo (1/2))+
        Real.sqrt 64*(ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2)*Ageo (eta0 v/2)) := by
      exact hsum.trans (by nlinarith [hh])
    _ = _ := by ring

/-- Rounding the fine rank converts the geometric sum into its unrounded interaction power. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_canonical_sum_rate
lemma ledger_multilevel_canonical_sum_rate (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    (∑ j : Fin (ledgerL n v), Real.sqrt ((ledgerR n v (j.val+1):ℝ)*ledgerV n v (j.val+1))) ≤
      Real.sqrt 2*Gstar v*ledgerA n v^(-(1+v.β*tExp v)/(2*sumReg v)) := by
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hS : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  obtain ⟨heta, hetale, hat, hatlt⟩ := ledger_multilevel_eta_bound v hv hb
  have hr : 0 ≤ (1-v.α*tExp v)/2 := by linarith
  have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ledgerK n v)
    (ledger_multilevel_fine_target_upper n v hn hv hb) hr
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity), ← Real.rpow_mul ha.le] at hpow
  have htwo : (2:ℝ)^((1-v.α*tExp v)/2) ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hG : 0 ≤ Gstar v := by
    have h1 := (Ageo_antitone_positive (1/2) (1/2) (by norm_num) le_rfl).1
    have h2 := (Ageo_antitone_positive (eta0 v/2) (eta0 v/2) (by linarith) le_rfl).1
    unfold Gstar
    positivity
  calc
    _ ≤ Gstar v*ledgerA n v^(-tExp v/2)*(ledgerK n v:ℝ)^((1-v.α*tExp v)/2) :=
      ledger_multilevel_canonical_sum_bound n v hn hv hb
    _ ≤ Gstar v*ledgerA n v^(-tExp v/2)*
        (Real.sqrt 2*ledgerA n v^((-1/sumReg v)*((1-v.α*tExp v)/2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hpow.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
    _ = _ := by
      have he : -tExp v/2+(-1/sumReg v)*((1-v.α*tExp v)/2) =
          -(1+v.β*tExp v)/(2*sumReg v) := by
        field_simp [hS.ne']
        dsimp [sumReg]
        ring
      calc
        _ = Real.sqrt 2*Gstar v*(ledgerA n v^(-tExp v/2)*
              ledgerA n v^((-1/sumReg v)*((1-v.α*tExp v)/2))) := by ring
        _ = _ := by rw [← Real.rpow_add ha, he]

/-- Squaring the main and increment contributions gives the two canonical-pair noise channels. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_canonical_square_bound
lemma ledger_multilevel_canonical_square_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    ledgerL2 n v^2 ≤ 4096*(blockSize n:ℝ)*ledgerA n v^(-tExp v)+
      64*Gstar v^2*ledgerA n v^(-(1+v.β*tExp v)/sumReg v) := by
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hT : 0 < ledgerT0 n v := lt_of_lt_of_le (by norm_num) (ledgerT0_ge_one n v)
  have hsum := ledger_multilevel_canonical_sum_rate n v hn hv hb
  let x := Real.sqrt ((ledgerM n v:ℝ)*ledgerV0 n v)
  let y := ∑ j : Fin (ledgerL n v), Real.sqrt ((ledgerR n v (j.val+1):ℝ)*ledgerV n v (j.val+1))
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hx2 : x^2 ≤ 128*(blockSize n:ℝ)*ledgerA n v^(-tExp v) := by
    dsimp [x]
    rw [Real.sq_sqrt (by unfold ledgerV0; positivity)]
    have hM : (ledgerM n v:ℝ) ≤ 2*(blockSize n:ℝ) := by exact_mod_cast (ledger_rank_bounds n v hn hv).1
    have hV := ledger_main_variance_bound n v hn hv
    have hh := mul_le_mul hM hV (by unfold ledgerV0; positivity) (by positivity : 0 ≤ 2*(blockSize n:ℝ))
    nlinarith
  have hy2 : y^2 ≤ 2*Gstar v^2*ledgerA n v^(-(1+v.β*tExp v)/sumReg v) := by
    have hh := pow_le_pow_left₀ hy hsum 2
    have he : (ledgerA n v^(-(1+v.β*tExp v)/(2*sumReg v)))^2 =
        ledgerA n v^(-(1+v.β*tExp v)/sumReg v) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      congr 1
      ring
    simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), he] using hh
  have hid : ledgerL2 n v = 4*(x+y) := by
    simp only [ledgerL2, if_neg (by omega : ¬ n < 4), if_neg hb, x, y]
  rw [hid]
  nlinarith [sq_nonneg (x-y)]

/-- Exact block normalization turns the canonical square bound into the stated two rates. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_canonical_covariance_bound
lemma ledger_multilevel_canonical_covariance_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    2*ledgerL2 n v^2/((blockSize n:ℝ)*((blockSize n:ℝ)-1)) ≤
      16384*ledgerA n v^(-tExp v)/(blockSize n:ℝ)+
      256*Gstar v^2*ledgerA n v^(-(1+v.β*tExp v)/sumReg v)/(blockSize n:ℝ)^2 := by
  have hs : (2:ℝ) ≤ blockSize n := by
    have : 2 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hspos : (0:ℝ) < blockSize n := by linarith
  have hsm : (0:ℝ) < (blockSize n:ℝ)-1 := by linarith
  have hden : (blockSize n:ℝ)^2 ≤ 2*((blockSize n:ℝ)*((blockSize n:ℝ)-1)) := by nlinarith
  have hbound := ledger_multilevel_canonical_square_bound n v hn hv hb
  calc
    _ ≤ 4*ledgerL2 n v^2/(blockSize n:ℝ)^2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg (ledgerL2 n v))]
    _ ≤ 4*(4096*(blockSize n:ℝ)*ledgerA n v^(-tExp v)+
        64*Gstar v^2*ledgerA n v^(-(1+v.β*tExp v)/sumReg v))/(blockSize n:ℝ)^2 := by gcongr
    _ = _ := by field_simp; ring

/-- Dimension weighting preserves the squared target for the complete canonical-pair contribution. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_canonical_covariance_rate
lemma ledger_multilevel_canonical_covariance_rate (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    Real.sqrt (ledgerM n v)*(2*ledgerL2 n v^2/((blockSize n:ℝ)*((blockSize n:ℝ)-1))) ≤
      Real.sqrt 2*(16384+256*Gstar v^2)*ledgerA n v^2 := by
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have hs : (0:ℝ) < blockSize n := by exact_mod_cast hsN
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hM : Real.sqrt (ledgerM n v) ≤ Real.sqrt 2*ledgerA n v^(-1/(2*v.γ)) := by
    calc
      _ ≤ Real.sqrt (2*ledgerA n v^(-1/v.γ)) := Real.sqrt_le_sqrt (ledger_coarse_target_upper n v hn hv)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow (ledgerA n v^(-1/v.γ)),
          ← Real.rpow_mul ha.le]
        congr 2
        ring
  have hsm : (0:ℝ) < (blockSize n:ℝ)-1 := by
    have : 2 ≤ blockSize n := by unfold blockSize; omega
    have : (2:ℝ) ≤ blockSize n := by exact_mod_cast this
    linarith
  have hc := ledger_multilevel_canonical_covariance_bound n v hn hv hb
  have ht := ledger_tail_noise_balance n v hn hv
  have hi := ledger_canonical_noise_balance n v hn hv
  calc
    _ ≤ (Real.sqrt 2*ledgerA n v^(-1/(2*v.γ)))*
        (16384*ledgerA n v^(-tExp v)/(blockSize n:ℝ)+
         256*Gstar v^2*ledgerA n v^(-(1+v.β*tExp v)/sumReg v)/(blockSize n:ℝ)^2) :=
      mul_le_mul hM hc (by positivity) (by positivity)
    _ = (16384*Real.sqrt 2)*(ledgerA n v^(-1/(2*v.γ))*ledgerA n v^(-tExp v)/(blockSize n:ℝ))+
        (256*Real.sqrt 2*Gstar v^2)*(ledgerA n v^(-1/(2*v.γ))*ledgerA n v^(-(1+v.β*tExp v)/sumReg v)/(blockSize n:ℝ)^2) := by ring
    _ ≤ (16384*Real.sqrt 2)*ledgerA n v^2+(256*Real.sqrt 2*Gstar v^2)*ledgerA n v^2 :=
      add_le_add (mul_le_mul_of_nonneg_left ht (by positivity)) (mul_le_mul_of_nonneg_left hi (by positivity))
    _ = _ := by ring

/-- A singleton square bound gives its dimension-weighted tail-noise contribution. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hlinear condition](hyp:hlinear). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_singleton_covariance_rate
lemma ledger_multilevel_singleton_covariance_rate (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid)
    (hlinear : ledgerL1 n v^2 ≤ 64*Lstar v^2*ledgerA n v^(-tExp v)) :
    Real.sqrt (ledgerM n v)*(ledgerL1 n v^2/(blockSize n:ℝ)) ≤
      Real.sqrt 2*(64*Lstar v^2)*ledgerA n v^2 := by
  have hsN : 0 < blockSize n := by unfold blockSize; omega
  have hs : (0:ℝ) < blockSize n := by exact_mod_cast hsN
  have ha : 0 < ledgerA n v := by unfold ledgerA; positivity
  have hM : Real.sqrt (ledgerM n v) ≤ Real.sqrt 2*ledgerA n v^(-1/(2*v.γ)) := by
    calc
      _ ≤ Real.sqrt (2*ledgerA n v^(-1/v.γ)) := Real.sqrt_le_sqrt (ledger_coarse_target_upper n v hn hv)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow (ledgerA n v^(-1/v.γ)),
          ← Real.rpow_mul ha.le]
        congr 2
        ring
  have hc := div_le_div_of_nonneg_right hlinear hs.le
  calc
    _ ≤ (Real.sqrt 2*ledgerA n v^(-1/(2*v.γ)))*
        ((64*Lstar v^2*ledgerA n v^(-tExp v))/(blockSize n:ℝ)) :=
      mul_le_mul hM hc (by positivity) (by positivity)
    _ = (Real.sqrt 2*(64*Lstar v^2))*(ledgerA n v^(-1/(2*v.γ))*
        ledgerA n v^(-tExp v)/(blockSize n:ℝ)) := by ring
    _ ≤ (Real.sqrt 2*(64*Lstar v^2))*ledgerA n v^2 :=
      mul_le_mul_of_nonneg_left (ledger_tail_noise_balance n v hn hv) (by positivity)

/-- The proved canonical contribution and the singleton square estimate assemble the full covariance rate. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb), [the hlinear condition](hyp:hlinear). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_covariance_rate_of_singleton
lemma ledger_multilevel_covariance_rate_of_singleton (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v)
    (hlinear : ledgerL1 n v^2 ≤ 64*Lstar v^2*ledgerA n v^(-tExp v)) :
    Real.sqrt (ledgerM n v)*ledgerCov n v ≤ Astar v*ledgerA n v^2 := by
  have hsingle := ledger_multilevel_singleton_covariance_rate n v hn hv hlinear
  have hpair := ledger_multilevel_canonical_covariance_rate n v hn hv hb
  have htotal := add_le_add hsingle hpair
  have hA : Real.sqrt 2*(64*Lstar v^2+16384+256*Gstar v^2) ≤ Astar v := by
    unfold Astar
    nlinarith [Real.sqrt_nonneg 2]
  calc
    _ ≤ Real.sqrt 2*(64*Lstar v^2+16384+256*Gstar v^2)*ledgerA n v^2 := by
      simp only [ledgerCov, if_neg (by omega : ¬n < 4), mul_add]
      nlinarith [htotal]
    _ ≤ Astar v*ledgerA n v^2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
