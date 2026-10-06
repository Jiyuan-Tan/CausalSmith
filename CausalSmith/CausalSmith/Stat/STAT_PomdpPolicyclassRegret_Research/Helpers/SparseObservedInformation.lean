module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseObservedLikelihood

/-! # Averaging the full observed likelihood

The full observed KL is the expected sum of reward log likelihoods. The
logarithmic inequality reduces it to a signed reward expectation, and the
squared filter means have the uniform retention-window budget from (18)--(20).
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Extend a finite observed word with a fixed dummy epoch. Recorded epochs
are unchanged; the extension is used only to feed the chronological filter. -/
-- @node: sparseObservedWordExtension
def sparseObservedWordExtension {T d Q : Nat} (hd : 0 < d)
    (w : FiniteObsView T (d * hdepth Q) 2) (k : Nat) :
    Fin (d * hdepth Q) × Bool × Fin 2 :=
  if h : k < T then w ⟨k, h⟩ else
    (⟨0, Nat.mul_pos hd (by simp [hdepth])⟩, false, 0)

/-- The chronological filter's conditional reward mean, evaluated using
only the recorded observed word and stationary padding. -/
-- @node: sparseObservedRewardMean
noncomputable def sparseObservedRewardMean {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  let x := fun k ↦ (sparseObservedWordExtension hd w k).1
  let a := fun k ↦ (sparseObservedWordExtension hd w k).2.1
  let r := fun k ↦ (sparseObservedWordExtension hd w k).2.2
  sparseSignal t0 * sparseFilterBias hd zeta C code v x a t.val Q *
    ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r t.val
      (depthSignEquiv Q (Fin.last Q, u))) /
      (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r t.val h))

/-- The full observed log likelihood expands into the finite sum of reward log ratios from (16);
no hidden coordinate or reset is revealed. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), [the v0](hyp:v0), and
[the observed word](hyp:w), this establishes
[the sparse observed log ratio equality reward sum result](goal). -/
-- @node: sparse_observed_log_ratio_eq_reward_sum
lemma sparse_observed_log_ratio_eq_reward_sum {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 0 < T) (code : Fin M → Fin d → Bool) (v v0 : Fin M)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    Real.log ((sparseObservedPMF hd t0 zeta C code v false w).toReal /
      (sparseObservedPMF hd t0 zeta C code v0 true w).toReal) =
      ∑ t : Fin T, Real.log (1 + (if (w t).2.2 = 0 then -1 else 1 : ℝ) *
        sparseObservedRewardMean hd t0 zeta C code v t w) := by
  let x := fun k ↦ (sparseObservedWordExtension hd w k).1
  let a := fun k ↦ (sparseObservedWordExtension hd w k).2.1
  let r := fun k ↦ (sparseObservedWordExtension hd w k).2.2
  have hw : (fun k : Fin T ↦ (x k.val, a k.val, r k.val)) = w := by
    funext k
    simp [x, a, r, sparseObservedWordExtension, k.isLt]
  have h := sparse_observed_full_log_likelihood_ratio hd t0 zeta C ht0 hzeta hC hT
    code v v0 x a r
  rw [hw] at h
  rw [h, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp [sparseObservedRewardMean, x, a, r, sparseObservedWordExtension, k.isLt]

/-- Taking the actual alternative expectation of (16) gives the full finite-word KL, expanded
into chronological reward contributions. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), and [the v0](hyp:v0), this establishes
[the sparse observed KL div equality reward sum result](goal). -/
-- @node: sparse_observed_klDiv_eq_reward_sum
lemma sparse_observed_klDiv_eq_reward_sum {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 0 < T) (code : Fin M → Fin d → Bool) (v v0 : Fin M) :
    (klDiv (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false).toMeasure
      (sparseObservedPMF hd t0 zeta C code v0 true).toMeasure).toReal =
      ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          Real.log (1 + (if (w t).2.2 = 0 then -1 else 1 : ℝ) *
            sparseObservedRewardMean hd t0 zeta C code v t w) := by
  rw [finitePMF_klDiv_eq_sum _ _ (by
    intro w hw
    have hp := sparse_fair_observed_pmf_pos hd t0 zeta C ht0 hzeta hC code v0 w
    simp [hw] at hp)]
  simp_rw [sparse_observed_log_ratio_eq_reward_sum hd t0 zeta C ht0 hzeta hC hT
    code v v0, Finset.mul_sum]
  exact Finset.sum_comm

/-- Every observed reward mean is a nonnegative number strictly below one, so both realized
reward likelihood factors are positive. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the sparse observed reward mean bounds result](goal). -/
-- @node: sparse_observed_reward_mean_bounds
lemma sparse_observed_reward_mean_bounds {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    0 ≤ sparseObservedRewardMean hd t0 zeta C code v t w ∧
      sparseObservedRewardMean hd t0 zeta C code v t w < 1 := by
  exact sparse_hidden_filter_reward_mean_bounds hd t0 zeta C code v
    (fun k ↦ (sparseObservedWordExtension hd w k).1)
    (fun k ↦ (sparseObservedWordExtension hd w k).2.1)
    (fun k ↦ (sparseObservedWordExtension hd w k).2.2) ht0 hzeta hC t.val

/-- The logarithmic inequality from (17), before conditioning, reduces the actual observed KL to
the expectation of the signed reward times its filter mean. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), and [the v0](hyp:v0), this establishes
[the sparse observed KL div bound signed reward sum result](goal). -/
-- @node: sparse_observed_klDiv_le_signed_reward_sum
lemma sparse_observed_klDiv_le_signed_reward_sum {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 0 < T) (code : Fin M → Fin d → Bool) (v v0 : Fin M) :
    (klDiv (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false).toMeasure
      (sparseObservedPMF hd t0 zeta C code v0 true).toMeasure).toReal ≤
      ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          ((if (w t).2.2 = 0 then -1 else 1 : ℝ) *
            sparseObservedRewardMean hd t0 zeta C code v t w) := by
  rw [sparse_observed_klDiv_eq_reward_sum hd t0 zeta C ht0 hzeta hC hT code v v0]
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have hb := sparse_observed_reward_mean_bounds hd t0 zeta C ht0 hzeta hC code v t w
  have hp : 0 < 1 + (if (w t).2.2 = 0 then -1 else 1 : ℝ) *
      sparseObservedRewardMean hd t0 zeta C code v t w := by
    split_ifs <;> nlinarith [hb.1, hb.2]
  simpa using Real.log_le_sub_one_of_pos hp

/-- The pointwise squared mean has exactly the observed retention factor appearing in (18),
including the deterministic stationary prefix. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the observed word](hyp:w), this
establishes [the sparse observed reward mean sq bound window result](goal). -/
-- @node: sparse_observed_reward_mean_sq_le_window
lemma sparse_observed_reward_mean_sq_le_window {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (w : FiniteObsView T (d * hdepth Q) 2) :
    sparseObservedRewardMean hd t0 zeta C code v t w ^ 2 ≤
      sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
        mixingAlpha t0 ^ (2 * Q) * retentionFactor hd zeta code v t w ^ 2 := by
  have h := sparse_hidden_filter_reward_mean_sq_le hd t0 zeta C code v
    (fun k ↦ (sparseObservedWordExtension hd w k).1)
    (fun k ↦ (sparseObservedWordExtension hd w k).2.1)
    (fun k ↦ (sparseObservedWordExtension hd w k).2.2) ht0 hzeta hC t.val
  have hset : (Finset.range T).filter
      (fun k ↦ t.val - min Q t.val ≤ k ∧ k < t.val) =
      Finset.Ico (t.val - min Q t.val) t.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hret : retentionFactor hd zeta code v t w =
      sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
        ∏ k ∈ Finset.Ico (t.val - min Q t.val) t.val,
          retentionIndicator hd code v (sparseObservedWordExtension hd w k).1
            (sparseObservedWordExtension hd w k).2.1 := by
    dsimp only [retentionFactor]
    rw [hset]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have hkT : k < T := lt_trans (Finset.mem_Ico.mp hk).2 t.isLt
    simp [sparseObservedWordExtension, hkT]
  rw [hret]
  exact h

/-- Averaging the squared filter means under the actual observed law gives the uniform budget in
(18)--(19), using the independent context-action moments. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code), and
[the codeword index](hyp:v), this establishes
[the sparse observed reward mean sq sum bound result](goal). -/
-- @node: sparse_observed_reward_mean_sq_sum_le
lemma sparse_observed_reward_mean_sq_sum_le {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) :
    (∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        sparseObservedRewardMean hd t0 zeta C code v t w ^ 2) ≤
      sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
        mixingAlpha t0 ^ (2 * Q) * T * sparseRetentionProbability Q zeta ^ Q := by
  let A := sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
    mixingAlpha t0 ^ (2 * Q)
  have hA : 0 ≤ A := by dsimp [A]; unfold mixingAlpha; positivity
  calc
    _ ≤ ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          (A * retentionFactor hd zeta code v t w ^ 2) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left
        (sparse_observed_reward_mean_sq_le_window hd t0 zeta C ht0 hzeta hC code v t w)
        ENNReal.toReal_nonneg
    _ = A * (∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          retentionFactor hd zeta code v t w ^ 2) := by
      simp_rw [← mul_assoc, mul_comm _ A, mul_assoc]
      simp only [Finset.mul_sum]
    _ ≤ A * ((T : ℝ) * sparseRetentionProbability Q zeta ^ Q) :=
      mul_le_mul_of_nonneg_left
        (sparse_observed_total_retention_second_moment_le hd t0 zeta C
          ht0 hzeta hC code v) hA
    _ = _ := by dsimp [A]; ring

/-- The numerical substitution (20) transfers the actual squared-mean budget to the constant and
factors of the contextual observed KL theorem. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code), and
[the codeword index](hyp:v), this establishes
[the sparse observed reward mean sq sum bound frontier budget result](goal). -/
-- @node: sparse_observed_reward_mean_sq_sum_le_frontier_budget
lemma sparse_observed_reward_mean_sq_sum_le_frontier_budget {T M d Q : Nat}
    (hd : 0 < d) (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) :
    (∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        sparseObservedRewardMean hd t0 zeta C code v t w ^ 2) ≤
      klConstant t0 zeta * T * overlapRadius C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ)) := by
  exact kl_from_retention_window_bound t0 zeta C hzeta T Q _
    (sparse_observed_reward_mean_sq_sum_le hd t0 zeta C ht0 hzeta hC code v)

end CausalSmith.Stat.PomdpPolicyclassRegret
