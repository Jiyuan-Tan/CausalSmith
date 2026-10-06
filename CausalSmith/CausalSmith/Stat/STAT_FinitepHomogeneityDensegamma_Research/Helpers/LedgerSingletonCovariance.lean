module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerMultilevelCovariance

/-! Singleton-projection geometric and logarithmic budgets for the multilevel ledger. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The target scale is positive and at most one. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledgerA_unit_bounds
lemma ledgerA_unit_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    0 < ledgerA n v ∧ ledgerA n v ≤ 1 := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    have : 1 ≤ blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hE := (exponent_phase_algebra v hv).2.2.1
  constructor
  · unfold ledgerA; positivity
  · simpa [ledgerA] using Real.rpow_le_rpow_of_exponent_le hs (neg_nonpos.mpr hE.le)

/-- The tangent inequality for the exponential bounds the logarithmic interpolation loss. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: singleton_log_interpolation_bound
lemma singleton_log_interpolation_bound (a : ℝ) (ha : 0 < a) :
    -a*Real.log a ≤ (Real.exp 1)⁻¹ := by
  have h := Real.add_one_le_exp (-Real.log a-1)
  have he : Real.exp (-Real.log a-1) = a⁻¹*(Real.exp 1)⁻¹ := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log ha]
    simp [div_eq_mul_inv]
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  simp only [sub_add_cancel] at hh
  have hid : a*(a⁻¹*(Real.exp 1)⁻¹) = (Real.exp 1)⁻¹ := by field_simp
  rw [hid] at hh
  nlinarith

/-- Refinement depth costs only the logarithm of the interaction target. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_depth_bound
lemma ledger_multilevel_depth_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    (ledgerL n v:ℝ)*Real.log 2 ≤ Real.log 2-Real.log (ledgerA n v)/sumReg v := by
  obtain ⟨hM, hMK, hlast⟩ := ledger_increment_rank_bound n v hn
  have hpow : (2:ℝ)^(ledgerL n v) ≤ (ledgerK n v:ℝ) := by
    have hm : (1:ℝ) ≤ ledgerM n v := by exact_mod_cast hM
    have hh : (2:ℝ)^(ledgerL n v)*(ledgerM n v:ℝ) ≤ ledgerK n v := by
      exact_mod_cast hlast
    nlinarith [show 0 ≤ (2:ℝ)^(ledgerL n v) by positivity]
  have ha := (ledgerA_unit_bounds n v hn hv).1
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(ledgerL n v))
    (hpow.trans (ledger_multilevel_fine_target_upper n v hn hv hb))
  rw [Real.log_pow, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity), Real.log_rpow ha] at hh
  convert hh using 1 <;> ring

/-- Multiplying refinement depth by the target scale removes the sample-size logarithm. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_scaled_depth_bound
lemma ledger_multilevel_scaled_depth_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    ledgerA n v*(ledgerL n v:ℝ) ≤ Dstar v := by
  obtain ⟨ha, ha1⟩ := ledgerA_unit_bounds n v hn hv
  have hS : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdepth := mul_le_mul_of_nonneg_left (ledger_multilevel_depth_bound n v hn hv hb) ha.le
  have hinter := singleton_log_interpolation_bound _ ha
  have hdiv := (div_le_div_of_nonneg_right hinter (mul_pos hS hlog).le)
  have hid : ledgerA n v*(Real.log 2-Real.log (ledgerA n v)/sumReg v) =
      (ledgerA n v+(-ledgerA n v*Real.log (ledgerA n v))/(sumReg v*Real.log 2))*Real.log 2 := by
    field_simp
    ring
  rw [← mul_assoc, hid] at hdepth
  have h := (mul_le_mul_iff_left₀ hlog).mp hdepth
  unfold Dstar
  have he : (Real.exp 1)⁻¹/(sumReg v*Real.log 2) = (Real.exp 1*sumReg v*Real.log 2)⁻¹ := by
    field_simp
  rw [he] at hdiv
  linarith

/-- Summing the local tail targets uses the fine-rank amplitude and one geometric multiplier. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_tail_sum_bound
lemma ledger_multilevel_tail_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    (∑ j : Fin (ledgerL n v), ledgerT n v (j.val+1)^(1-v.p)) ≤
      Dstar v+2*Ageo v.α := by
  have ha := (ledgerA_unit_bounds n v hn hv).1
  have hl : 0 < lam0 v := by
    have hp : 0 < v.p := by linarith [hv.1.1]
    have hm : 0 < v.p-1 := by linarith [hv.1.1]
    unfold lam0; positivity
  obtain ⟨hm, hmk, hlast⟩ := ledger_increment_rank_bound n v hn
  have hk : 0 < (ledgerK n v:ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmk
  have he (j : Fin (ledgerL n v)) :
      ledgerA n v*((ledgerR n v (j.val+1):ℝ)/ledgerK n v)^lam0 v*(ledgerR n v (j.val+1):ℝ)^v.α =
      (ledgerA n v*(ledgerK n v:ℝ)^v.α)*((ledgerR n v (j.val+1):ℝ)/ledgerK n v)^(v.α+lam0 v) := by
    rw [Real.rpow_add (by unfold ledgerR; positivity)]
    simp_rw [Real.div_rpow (by positivity : (0:ℝ) ≤ ledgerR n v (j.val+1)) hk.le]
    field_simp
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin (ledgerL n v)) hj => ledger_increment_tail_bound n v hn hv (j.val+1))
  simp_rw [he] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hgeom := ledger_rank_ratio_sum_bound n v hn (v.α+lam0 v) (add_pos hv.2.1.1 hl)
  have hanti := (Ageo_antitone_positive v.α (v.α+lam0 v) hv.2.1.1 (by linarith)).2
  have hmul := mul_le_mul_of_nonneg_left (hgeom.trans hanti)
    (show 0 ≤ ledgerA n v*(ledgerK n v:ℝ)^v.α by positivity)
  have hge : 0 ≤ Ageo v.α := (Ageo_antitone_positive v.α v.α hv.2.1.1 le_rfl).1
  have hcap := mul_le_mul_of_nonneg_right (ledger_multilevel_amplitude_bound n v hn hv hb) hge
  have hdepth := ledger_multilevel_scaled_depth_bound n v hn hv hb
  nlinarith

/-- The primitive approximation part of the singleton ledger is a geometric series. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_amplitude_sum_bound
lemma ledger_multilevel_amplitude_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) :
    (∑ j : Fin (ledgerL n v), aLev n v (j.val+1)) ≤ 80*Ageo v.α := by
  have h := ledger_rank_decay_sum_bound n v hn v.α hv.2.1.1
  have hg : 0 ≤ Ageo v.α := (Ageo_antitone_positive v.α v.α hv.2.1.1 le_rfl).1
  simp only [aLev, Nat.add_sub_cancel, ← Finset.mul_sum]
  nlinarith

/-- Both primitive smoothness and clipped-mean tails fit the singleton mean budget. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_d_sum_bound
lemma ledger_multilevel_d_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    (∑ j : Fin (ledgerL n v), dLev n v (j.val+1)) ≤
      110*Ageo (s0 v)+20*Dstar v+40*Ageo v.α := by
  have hs : 0 < s0 v := by
    unfold s0
    exact lt_min hv.2.1.1 (lt_min hv.2.2.1.1 (by linarith [hv.2.2.2.1]))
  have hgeom := ledger_rank_decay_sum_bound n v hn (s0 v) hs
  have htail := ledger_multilevel_tail_sum_bound n v hn hv hb
  simp only [dLev, Nat.add_sub_cancel, Finset.sum_add_distrib, ← Finset.mul_sum]
  change 110*(∑ j : Fin (ledgerL n v), (ledgerR n v j.val:ℝ)^(-s0 v))+
    20*(∑ j : Fin (ledgerL n v), ledgerT n v (j.val+1)^(1-v.p)) ≤ _
  linarith

/-- Capping the increment cutoffs caps every increment's standard deviation. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_increment_sqrt_variance_le_main
lemma ledger_increment_sqrt_variance_le_main (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (j : ℕ) :
    Real.sqrt (ledgerV n v j) ≤ Real.sqrt (ledgerV0 n v) := by
  have hcut := (ledger_cutoff_bounds n v hn hv).2.2 j
  apply Real.sqrt_le_sqrt
  unfold ledgerV ledgerV0
  gcongr
  · exact hcut.1.trans' (by norm_num)
  · linarith [hv.1.2]
  · exact hcut.2

/-- All increment variances can be summed against the geometric propensity amplitudes. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_weighted_variance_sum_bound
lemma ledger_multilevel_weighted_variance_sum_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) :
    (∑ j : Fin (ledgerL n v), aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1))) ≤
      80*Ageo v.α*Real.sqrt (ledgerV0 n v) := by
  calc
    _ ≤ ∑ j : Fin (ledgerL n v), aLev n v (j.val+1)*Real.sqrt (ledgerV0 n v) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left (ledger_increment_sqrt_variance_le_main n v hn hv _)
      unfold aLev; positivity
    _ = (∑ j : Fin (ledgerL n v), aLev n v (j.val+1))*Real.sqrt (ledgerV0 n v) := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (ledger_multilevel_amplitude_sum_bound n v hn hv)
      (Real.sqrt_nonneg _)

/-- The main variance budget is large enough to absorb deterministic singleton contributions. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_main_sqrt_variance_ge_one
lemma ledger_main_sqrt_variance_ge_one (n : ℕ) (v : Params) (hv : v.Valid) :
    1 ≤ Real.sqrt (ledgerV0 n v) := by
  have hpow : 1 ≤ ledgerT0 n v^(2-v.p) :=
    Real.one_le_rpow (ledgerT0_ge_one n v) (by linarith [hv.1.2])
  have hV : 1 ≤ ledgerV0 n v := by unfold ledgerV0; linarith
  simpa using Real.sqrt_le_sqrt hV

/-- The geometric mean and variance sums assemble the unsquared singleton bound. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_linear_bound
lemma ledger_multilevel_linear_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    ledgerL1 n v ≤ Lstar v*Real.sqrt (ledgerV0 n v) := by
  have hd := ledger_multilevel_d_sum_bound n v hn hv hb
  have hw := ledger_multilevel_weighted_variance_sum_bound n v hn hv
  have hroot := ledger_main_sqrt_variance_ge_one n v hv
  have hd0 : 0 ≤ 110*Ageo (s0 v)+20*Dstar v+40*Ageo v.α := by
    apply le_trans _ hd
    apply Finset.sum_nonneg
    intro j hj
    have hT := ((ledger_cutoff_bounds n v hn hv).2.2 (j.val+1)).1
    unfold dLev; positivity
  have hscale := mul_le_mul_of_nonneg_left hroot hd0
  simp only [mul_one] at hscale
  simp only [ledgerL1, if_neg (by omega : ¬n < 4), if_neg hb, Finset.sum_add_distrib]
  unfold Lstar
  nlinarith

/-- Squaring the assembled singleton bound and inserting the main moment rate closes its ledger. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledger_multilevel_linear_square_bound
lemma ledger_multilevel_linear_square_bound (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (hv : v.Valid) (hb : ¬ singleBranch v) :
    ledgerL1 n v^2 ≤ 64*Lstar v^2*ledgerA n v^(-tExp v) := by
  have hlinear := ledger_multilevel_linear_bound n v hn hv hb
  have h0 : 0 ≤ ledgerL1 n v := by
    simp only [ledgerL1, if_neg (by omega : ¬n < 4), if_neg hb]
    apply add_nonneg (by positivity)
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    have hT := ((ledger_cutoff_bounds n v hn hv).2.2 (j.val+1)).1
    unfold dLev aLev; positivity
  have hsquare := sq_le_sq₀ h0 (h0.trans hlinear) |>.mpr hlinear
  have hT0 := ledgerT0_ge_one n v
  rw [mul_pow, Real.sq_sqrt (by unfold ledgerV0; positivity)] at hsquare
  have hV := mul_le_mul_of_nonneg_left (ledger_main_variance_bound n v hn hv) (sq_nonneg (Lstar v))
  nlinarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
