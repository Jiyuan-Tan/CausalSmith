module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFilterMass

/-! # Observed-word Bayes recursion for sparse terminal depth

Forced terminal windows and observed reward likelihood lower bounds give the
finite-product posterior recursion, including the stationary initial prefix.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

section Filter

variable {M d Q : Nat} (hd : 0 < d) (t0 zeta C : ℝ)
  (code : Fin M → Fin d → Bool) (v : Fin M)
  (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)

local notation "F" => sparseHiddenFilter hd t0 zeta C code v x a r
local notation "D" => (fun n : Nat ↦ ∑ h, F n h)
local notation "U" => (fun n : Nat ↦ ∑ u, F n (depthSignEquiv Q (Fin.last Q, u)))
local notation "Z" => (fun n : Nat ↦ U n / D n)
local notation "κ" => (((d * hdepth Q : Nat) : ℝ)⁻¹)

/-- The initial filter total is the common uniform context mass. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta), and
[the latent-overlap radius assumption](hyp:hC), this establishes
[the sparse hidden filter initial total result](goal). -/
-- @node: sparse_hidden_filter_initial_total
lemma sparse_hidden_filter_initial_total (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) : D 0 = κ := by
  simp only [sparseHiddenFilter,
    sparse_init_eq_signed_density hd t0 zeta C ht0 hzeta hC code v]
  exact sparse_signed_density_context_mass d Q t0 C _ ht0 (x 0)

/-- Every posterior-dependent reward denominator is strictly positive. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter bayes factor positivity result](goal). -/
-- @node: sparse_hidden_filter_bayes_factor_pos
lemma sparse_hidden_filter_bayes_factor_pos (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) : 0 < 1 - sparseSignal t0 * Z n := by
  have hc := sparse_signal_bounds t0 ht0
  have hz := sparse_hidden_filter_depth_ratio_bounds hd t0 zeta C code v x a r
    ht0 hzeta hC n (Fin.last Q)
  have hmul := mul_le_mul_of_nonneg_left hz.2 hc.1.le
  dsimp at hmul ⊢
  linarith

/-- The observed filter total has the posterior-dependent one-step lower bound from equation
(9), including its common context likelihood. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter total bayes lower result](goal). -/
-- @node: sparse_hidden_filter_total_bayes_lower
lemma sparse_hidden_filter_total_bayes_lower (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) :
    κ / 2 * (1 - sparseSignal t0 * Z n) * D n ≤ D (n + 1) := by
  have hp := sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC n
  have hl := sparse_hidden_filter_normalized_reward_lower hd t0 zeta C code v x a r
    ht0 hzeta hC n (r n)
  have hm := (le_div_iff₀ hp).mp hl
  dsimp only at ⊢
  rw [sparse_hidden_filter_total_update hd t0 zeta C code v x a r]
  convert mul_le_mul_of_nonneg_left hm (show 0 ≤ κ by positivity) using 1 <;> first | rfl | ring

/-- Multiplying the one-step Bayes lower bounds controls a whole observed reward window, without
revealing resets. For the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the start](hyp:start), and
[the block index](hyp:ell), this establishes
[the sparse hidden filter total window lower result](goal). -/
-- @node: sparse_hidden_filter_total_window_lower
lemma sparse_hidden_filter_total_window_lower (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (start ell : Nat) :
    (κ / 2) ^ ell * D start *
      (∏ i ∈ Finset.range ell, (1 - sparseSignal t0 * Z (start + i))) ≤
        D (start + ell) := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    have hf := sparse_hidden_filter_bayes_factor_pos hd t0 zeta C code v x a r
      ht0 hzeta hC (start + ell)
    have hstep := sparse_hidden_filter_total_bayes_lower hd t0 zeta C code v x a r
      ht0 hzeta hC (start + ell)
    have hm := mul_le_mul_of_nonneg_left ih
      (mul_nonneg (show 0 ≤ κ / 2 by positivity) hf.le)
    rw [Finset.prod_range_succ, pow_succ]
    calc
      _ = (κ / 2 * (1 - sparseSignal t0 * Z (start + ell))) *
          ((κ / 2) ^ ell * D start *
            ∏ i ∈ Finset.range ell, (1 - sparseSignal t0 * Z (start + i))) := by ring
      _ ≤ κ / 2 * (1 - sparseSignal t0 * Z (start + ell)) * D (start + ell) := hm
      _ ≤ D (start + (ell + 1)) := by simpa [Nat.add_assoc] using hstep

/-- The terminal numerator is bounded by the structural advance probability and fair reward
likelihood, for both stationary and complete windows. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter terminal window upper result](goal). -/
-- @node: sparse_hidden_filter_terminal_window_upper
lemma sparse_hidden_filter_terminal_window_upper (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) :
    U n ≤ (κ / 2) ^ (min Q n) * mixingAlpha t0 ^ Q * D (n - min Q n) := by
  dsimp only at ⊢
  by_cases hn : n ≤ Q
  · have hinit : (∑ h, F 0 h) = κ :=
      sparse_hidden_filter_initial_total hd t0 zeta C code v x a r ht0 hzeta hC
    rw [min_eq_right hn, Nat.sub_self, hinit,
      sparse_hidden_filter_early_terminal_mass hd t0 zeta C code v x a r ht0 hzeta hC n hn]
    have hm := mul_le_mul_of_nonneg_left (sparse_terminal_depth_mass_upper t0 ht0 Q)
      (show 0 ≤ κ ^ (n + 1) / (2 : ℝ) ^ n by positivity)
    convert hm using 1 <;> first | rfl | (simp only [div_pow, pow_succ]; ring)
  · have hQn : Q ≤ n := by omega
    rw [min_eq_left hQn,
      sparse_hidden_filter_complete_terminal_mass hd t0 zeta C code v x a r n hQn]
    have hm := mul_le_mul_of_nonneg_left
      (sparse_hidden_filter_depth_le_total hd t0 zeta C code v x a r ht0 hC (n - Q) 0)
      (show 0 ≤ (κ * mixingAlpha t0 / 2) ^ Q by
        apply pow_nonneg; exact div_nonneg (mul_nonneg (by positivity) (mixingAlpha_pos ht0).le) (by norm_num))
    convert hm using 1 <;> first | rfl | (simp only [div_pow, mul_pow]; ring)

/-- Bayes normalization gives equation (12) for every realized observed context, action and
reward word, including all stationary initial windows. For the candidate-policy count,
the code dimension, the hidden-depth scale,
the code dimension assumption, the mixing scale,
the policy-overlap scale, the latent-overlap radius,
the binary code, the codeword index, the observed state,
the action, the reward symbol, [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter posterior recursion result](goal). -/
-- @node: sparse_hidden_filter_posterior_recursion
lemma sparse_hidden_filter_posterior_recursion (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) :
    Z n ≤ mixingAlpha t0 ^ Q *
      ∏ i ∈ Finset.range (min Q n), (1 - sparseSignal t0 * Z (n - min Q n + i))⁻¹ := by
  let ell := min Q n
  let P := ∏ i ∈ Finset.range ell, (1 - sparseSignal t0 * Z (n - ell + i))
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro i hi
    exact sparse_hidden_filter_bayes_factor_pos hd t0 zeta C code v x a r ht0 hzeta hC _
  have hD := sparse_hidden_filter_total_pos hd t0 zeta C code v x a r ht0 hzeta hC n
  have hnum := sparse_hidden_filter_terminal_window_upper hd t0 zeta C code v x a r ht0 hzeta hC n
  have hden := sparse_hidden_filter_total_window_lower hd t0 zeta C code v x a r
    ht0 hzeta hC (n - ell) ell
  have hn : n - ell + ell = n := Nat.sub_add_cancel (min_le_right Q n)
  rw [hn] at hden
  have hscale : 0 ≤ mixingAlpha t0 ^ Q / P := div_nonneg (pow_nonneg (mixingAlpha_pos ht0).le _) hP.le
  have hm := mul_le_mul_of_nonneg_left hden hscale
  have heq : (mixingAlpha t0 ^ Q / P) * ((κ / 2) ^ ell * D (n - ell) * P) =
      (κ / 2) ^ ell * mixingAlpha t0 ^ Q * D (n - ell) := by
    field_simp
  rw [heq] at hm
  have hratio : Z n ≤ mixingAlpha t0 ^ Q / P := (div_le_iff₀ hD).2 (hnum.trans (by simpa [ell, mul_comm] using hm))
  simpa [P, div_eq_mul_inv, Finset.prod_inv_distrib] using hratio

/-- Express the Bayes recursion on the actual chronological epoch interval. For
the candidate-policy count, the code dimension,
the hidden-depth scale, the code dimension assumption,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the binary code, the codeword index,
the observed state, the action, the reward symbol,
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), and [the sample size](hyp:n), this establishes
[the sparse hidden filter posterior recursion ico result](goal). -/
-- @node: sparse_hidden_filter_posterior_recursion_Ico
lemma sparse_hidden_filter_posterior_recursion_Ico (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (n : Nat) :
    Z n ≤ mixingAlpha t0 ^ Q *
      ∏ i ∈ Finset.Ico (n - min Q n) n, (1 - sparseSignal t0 * Z i)⁻¹ := by
  rw [Finset.prod_Ico_eq_prod_range]
  have hlen : n - (n - min Q n) = min Q n := by omega
  simp only [hlen, Nat.add_comm]
  simpa only [Nat.add_comm] using
    sparse_hidden_filter_posterior_recursion hd t0 zeta C code v x a r ht0 hzeta hC n

end Filter

end CausalSmith.Stat.PomdpPolicyclassRegret
