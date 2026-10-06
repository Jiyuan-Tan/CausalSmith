module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerSingletonCovariance

/-! Finite-moment homogeneity testing: assembled rate bounds and public tuning grids. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The two analytic ledger bounds imply the declared full-sample separation constant. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hb condition](hyp:hb), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: Ratt_le_of_ledger_bounds
lemma Ratt_le_of_ledger_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid)
    (hb : ledgerBias n v ≤ Bstar v*ledgerA n v)
    (hc : Real.sqrt (ledgerM n v)*ledgerCov n v ≤ Astar v*ledgerA n v^2) :
    Ratt n v ≤ CAtt v*rho n v := by
  have ha : 0 ≤ ledgerA n v := by unfold ledgerA; positivity
  have hquarter : (ledgerM n v:ℝ)^(1/4:ℝ) = Real.sqrt (Real.sqrt (ledgerM n v)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ledgerM n v)]
    norm_num
  have hnoise : (ledgerM n v:ℝ)^(1/4:ℝ)*Real.sqrt (ledgerCov n v) ≤
      Real.sqrt (Astar v)*ledgerA n v := by
    rw [hquarter, ← Real.sqrt_mul (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (Astar v*ledgerA n v^2) := Real.sqrt_le_sqrt hc
      _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq ha]
  have hb0 : 0 ≤ Bstar v := by
    have hα : 0 ≤ Ageo v.α := by
      unfold Ageo
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (neg_nonpos.mpr hv.2.1.1.le)
      simp only [Real.rpow_zero] at h
      positivity
    have hl : 0 ≤ Ageo (lam0 v) := by
      have hp : 0 < v.p := by linarith [hv.1.1]
      have hlam : 0 ≤ lam0 v := by unfold lam0; positivity
      unfold Ageo
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (neg_nonpos.mpr hlam)
      simp only [Real.rpow_zero] at h
      positivity
    unfold Bstar
    positivity
  have hcoef : 0 ≤ 16+5*Bstar v+1024*Real.sqrt (Astar v) := by positivity
  unfold Ratt CAtt
  calc
    _ ≤ (16/3)*((16+5*Bstar v+1024*Real.sqrt (Astar v))*ledgerA n v) := by
      have happrox := ledger_approximation_bound n v hn hv
      nlinarith
    _ ≤ (16/3)*((16+5*Bstar v+1024*Real.sqrt (Astar v))*(3*rho n v)) := by
      gcongr
      exact ledgerA_le_three_rho n v hn hv
    _ = _ := by ring

/-- Ledger rate bounds: the displayed mathematical construction or bound. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_rate_bounds
lemma ledger_rate_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerBias n v ≤ Bstar v*ledgerA n v ∧
    Real.sqrt (ledgerM n v)*ledgerCov n v ≤ Astar v*ledgerA n v^2 ∧
    Ratt n v ≤ CAtt v*rho n v ∧
    ledgerM n v ≤ 2*blockSize n ∧ ledgerK n v ≤ 2*blockSize n^2 ∧
    1 ≤ ledgerT0 n v ∧ ledgerT0 n v ≤ 2*blockSize n ∧
    ∀ j : Fin (ledgerL n v), 1 ≤ ledgerT n v (j.val+1) ∧ ledgerT n v (j.val+1) ≤ ledgerT0 n v := by
  have hcut := ledger_cutoff_bounds n v hn hv
  have hrank := ledger_rank_bounds n v hn hv
  have hbias : ledgerBias n v ≤ Bstar v*ledgerA n v := by
    exact ledger_bias_bound n v hn hv
  have hcov : Real.sqrt (ledgerM n v)*ledgerCov n v ≤ Astar v*ledgerA n v^2 := by
    by_cases hbranch : singleBranch v
    · exact ledger_single_covariance_rate n v hn hv hbranch
    · exact ledger_multilevel_covariance_rate_of_singleton n v hn hv hbranch
        (ledger_multilevel_linear_square_bound n v hn hv hbranch)
  exact ⟨hbias, hcov, Ratt_le_of_ledger_bounds n v hn hv hbias hcov, hrank.1, hrank.2,
    hcut.1, hcut.2.1, fun j => hcut.2.2 (j.val+1)⟩

/-- A dyadic exponent bounded by a positive real endpoint fits its logarithmic grid. This statement assumes [the hB condition](hyp:hB). [This is the stated conclusion](goal). -/
-- @node: dyadic_exponent_le_grid
lemma dyadic_exponent_le_grid (j : ℕ) (B : ℝ) (hB : (2:ℝ)^j ≤ B) :
    j ≤ Nat.ceil (Real.logb 2 B) := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (by positivity : (0:ℝ) < 2^j) hB
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at hlog
  exact_mod_cast hlog.trans (Nat.le_ceil _)

/-- A dyadic outcome cutoff between one and the public endpoint has a natural grid index. This statement assumes [the hlo condition](hyp:hlo), [the hhi condition](hyp:hhi). [This is the stated conclusion](goal). -/
-- @node: dyadic_outcome_mem_grid
lemma dyadic_outcome_mem_grid (n : ℕ) (k : ℤ)
    (hlo : 1 ≤ (2:ℝ)^k) (hhi : (2:ℝ)^k ≤ 2*(blockSize n:ℝ)) :
    (2:ℝ)^k ∈ publicOutcomeGrid n := by
  have hk : 0 ≤ k := by
    have hh : (2:ℝ)^(0:ℤ) ≤ (2:ℝ)^k := by simpa using hlo
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hh
  have heq : (2:ℝ)^k = (2:ℝ)^k.toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hk]
  rw [heq]
  apply Finset.mem_image.mpr
  refine ⟨k.toNat, Finset.mem_range.mpr ?_, rfl⟩
  exact Nat.lt_succ_of_le (dyadic_exponent_le_grid _ _ (heq ▸ hhi))

/-- Public tuning uses only the specified finite grids. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledger_public_grids
lemma ledger_public_grids (n : ℕ) (v : Params) (hn : 4 ≤ n) (hv : v.Valid) :
    ledgerM n v ∈ publicRankGrid n ∧ ledgerK n v ∈ publicRankGrid n ∧
    ledgerT0 n v ∈ publicOutcomeGrid n ∧ ledgerCutoff n v ∈ publicCutoffGrid n v ∧
    ∀ j : Fin (ledgerL n v), ledgerT n v (j.val+1) ∈ publicOutcomeGrid n := by
  have hsmall : ¬ n < 4 := by omega
  obtain ⟨hM, hK⟩ := ledger_rank_bounds n v hn hv
  obtain ⟨hT0lo, hT0hi, hTnat⟩ := ledger_cutoff_bounds n v hn hv
  have hT (j : Fin (ledgerL n v)) := hTnat (j.val+1)
  have hs : 1 ≤ blockSize n := by unfold blockSize; omega
  have hMhi : ledgerM n v ≤ 2*blockSize n^2 := by
    nlinarith [Nat.mul_self_le_mul_self hs]
  have hrank (r : ℕ) (heq : ∃ j : ℕ, r=2^j) (hhi : r ≤ 2*blockSize n^2) :
      r ∈ publicRankGrid n := by
    obtain ⟨j, rfl⟩ := heq
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_range.mpr ?_, rfl⟩
    apply Nat.lt_succ_of_le
    apply dyadic_exponent_le_grid
    exact_mod_cast hhi
  refine ⟨hrank _ ?_ hMhi, hrank _ ?_ hK, ?_, ?_, ?_⟩
  · simp only [ledgerM, if_neg hsmall, leastPow2Ge]
    exact ⟨_, rfl⟩
  · simp only [ledgerK, if_neg hsmall, leastPow2Ge]
    exact ⟨_, rfl⟩
  · unfold ledgerT0 at hT0lo hT0hi ⊢
    simp only [if_neg hsmall] at hT0lo hT0hi ⊢
    rcases le_total (dyadUp (ledgerA n v ^ (-1/(v.p-1)))) 1 with h | h
    · rw [max_eq_left h]
      exact dyadic_outcome_mem_grid n 0 (by norm_num) (by simpa only [max_eq_left h, zpow_zero] using hT0hi)
    · rw [max_eq_right h]
      exact dyadic_outcome_mem_grid n _ h ((le_max_right _ _).trans hT0hi)
  · simp [ledgerCutoff, publicCutoffGrid, hsmall]
  · intro j
    simp only [ledgerT, if_neg hsmall, dyadUp]
    apply dyadic_outcome_mem_grid n _
    · simpa only [ledgerT, if_neg hsmall, dyadUp] using (hT j).1
    · have hh := ((hT j).2).trans hT0hi
      simpa only [ledgerT, if_neg hsmall, dyadUp] using hh

end CausalSmith.Stat.FinitepHomogeneityDensegamma
