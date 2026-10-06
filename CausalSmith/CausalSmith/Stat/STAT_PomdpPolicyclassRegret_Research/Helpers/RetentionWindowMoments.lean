module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.KLHandle
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseRetention

/-! # Independent context-action retention-window second moments

Finite product sums implement steps (1) and (19) of the observed KL roadmap.
The stationary prefix contributes a deterministic power of the retention mean.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- An indicator retains its value when squared. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), and [the action](hyp:a), this
establishes [the retention indicator sq result](goal). -/
-- @node: retentionIndicator_sq
lemma retentionIndicator_sq {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (a : Bool) :
    retentionIndicator hd code v x a ^ 2 = retentionIndicator hd code v x a := by
  classical
  unfold retentionIndicator
  split_ifs <;> norm_num

/-- The uniform context and behavior action weights have unit total mass. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), and [the policy-overlap scale](hyp:zeta), this
establishes [the sparse context action weight sum result](goal). -/
-- @node: sparse_context_action_weight_sum
lemma sparse_context_action_weight_sum (d Q : Nat) (hd : 0 < d) (zeta : ℝ) :
    (∑ xa : Fin (d * hdepth Q) × Bool,
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta xa.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [sparseBehaviorWeight, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    add_sub_cancel]
  simp only [mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  exact inv_mul_cancel₀ hn

/-- The one-epoch second moment equals the behavior retention mean, because retention is an
indicator and precisely one context slot per coordinate retains. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the binary code](hyp:code), and
[the codeword index](hyp:v), this establishes [the sparse retention second moment result](goal). -/
-- @node: sparse_retention_second_moment
lemma sparse_retention_second_moment {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) :
    (∑ xa : Fin (d * hdepth Q) × Bool,
      (((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta xa.2) *
        retentionIndicator hd code v xa.1 xa.2 ^ 2) =
      sparseRetentionProbability Q zeta := by
  simp_rw [retentionIndicator_sq hd code v]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  exact sparse_behavior_retention_average hd zeta code v

/-- Under independent finite coordinates, the squared product of indicators on any window has
expectation equal to the retention mean to its window size. For [the ι](hyp:ι),
[the contraction coefficient](hyp:α), [the weight](hyp:weight), [the indicator](hyp:indicator),
[the policy](hyp:p), [the state](hyp:s), [the mass assumption](hyp:hmass), and
[the moment assumption](hyp:hmoment), this establishes
[the finite product indicator second moment result](goal). -/
-- @node: finite_product_indicator_second_moment
lemma finite_product_indicator_second_moment {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (weight indicator : α → ℝ) (p : ℝ) (s : Finset ι)
    (hmass : ∑ x, weight x = 1)
    (hmoment : ∑ x, weight x * indicator x ^ 2 = p) :
    (∑ w : ι → α, (∏ i, weight (w i)) * (∏ i ∈ s, indicator (w i)) ^ 2) =
      p ^ s.card := by
  classical
  have hterm (w : ι → α) :
      (∏ i, weight (w i)) * (∏ i ∈ s, indicator (w i)) ^ 2 =
        ∏ i, weight (w i) * (if i ∈ s then indicator (w i) ^ 2 else 1) := by
    rw [Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_filter]
    simp
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i x ↦
    weight x * (if i ∈ s then indicator x ^ 2 else 1))]
  have hsum (i : ι) :
      (∑ x, weight x * (if i ∈ s then indicator x ^ 2 else 1)) =
        if i ∈ s then p else 1 := by
    by_cases hi : i ∈ s <;> simp [hi, hmass, hmoment]
  simp_rw [hsum]
  rw [← Finset.prod_filter]
  simp

/-- The unrecorded stationary prefix and recorded independent window combine into the exact
exponent in step (19). For [the ι](hyp:ι), [the contraction coefficient](hyp:α),
[the weight](hyp:weight), [the indicator](hyp:indicator), [the policy](hyp:p),
[the hidden-depth scale](hyp:Q), [the state](hyp:s), [the mass assumption](hyp:hmass), and
[the moment assumption](hyp:hmoment), this establishes
[the finite retention prefix second moment result](goal). -/
-- @node: finite_retention_prefix_second_moment
lemma finite_retention_prefix_second_moment {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq ι]
    (weight indicator : α → ℝ) (p : ℝ) (Q : Nat) (s : Finset ι)
    (hmass : ∑ x, weight x = 1)
    (hmoment : ∑ x, weight x * indicator x ^ 2 = p) :
    (∑ w : ι → α, (∏ i, weight (w i)) *
      (p ^ (Q - s.card) * ∏ i ∈ s, indicator (w i)) ^ 2) =
      p ^ (2 * (Q - s.card) + s.card) := by
  classical
  simp_rw [mul_pow]
  calc
    _ = (p ^ (Q - s.card)) ^ 2 *
        ∑ w : ι → α, (∏ i, weight (w i)) * (∏ i ∈ s, indicator (w i)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = (p ^ (Q - s.card)) ^ 2 * p ^ s.card := by
      rw [finite_product_indicator_second_moment weight indicator p s hmass hmoment]
    _ = p ^ (2 * (Q - s.card) + s.card) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- Every early or complete retention window has second moment at most p^Q. For [the ι](hyp:ι),
[the contraction coefficient](hyp:α), [the weight](hyp:weight), [the indicator](hyp:indicator),
[the policy](hyp:p), [the hidden-depth scale](hyp:Q), [the state](hyp:s),
[the mass assumption](hyp:hmass), [the moment assumption](hyp:hmoment),
[the p0 assumption](hyp:hp0), [the p1 assumption](hyp:hp1), and
[the card assumption](hyp:hcard), this establishes
[the finite retention prefix second moment bound result](goal). -/
-- @node: finite_retention_prefix_second_moment_le
lemma finite_retention_prefix_second_moment_le {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq ι]
    (weight indicator : α → ℝ) (p : ℝ) (Q : Nat) (s : Finset ι)
    (hmass : ∑ x, weight x = 1)
    (hmoment : ∑ x, weight x * indicator x ^ 2 = p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hcard : s.card ≤ Q) :
    (∑ w : ι → α, (∏ i, weight (w i)) *
      (p ^ (Q - s.card) * ∏ i ∈ s, indicator (w i)) ^ 2) ≤ p ^ Q := by
  rw [finite_retention_prefix_second_moment weight indicator p Q s hmass hmoment]
  exact pow_le_pow_of_le_one hp0 hp1 (by omega)

/-- The recorded retention window contains exactly min(Q,t) epochs. For
[the time horizon](hyp:T), [the hidden-depth scale](hyp:Q), and [the epoch index](hyp:t), this
establishes [the retention window card result](goal). -/
-- @node: retention_window_card
lemma retention_window_card {T : Nat} (Q : Nat) (t : Fin T) :
    ((Finset.univ : Finset (Fin T)).filter
      (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val)).card = min Q t.val := by
  classical
  let s := (Finset.univ : Finset (Fin T)).filter
    (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val)
  have hm : s.map ⟨Fin.val, Fin.val_injective⟩ =
      Finset.Ico (t.val - min Q t.val) t.val := by
    ext r
    simp only [Finset.mem_map, s, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hr
      exact ⟨⟨r, by omega⟩, hr, rfl⟩
  have hc := congrArg Finset.card hm
  simp only [Finset.card_map, Nat.card_Ico] at hc
  change s.card = min Q t.val
  rw [hc]
  omega

/-- The retention factor uses precisely the preceding min(Q,t) recorded coordinates; the reward
symbols do not enter it. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the policy-overlap scale](hyp:zeta),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the observed word](hyp:w), this establishes
[the retention factor equality fin window result](goal). -/
-- @node: retentionFactor_eq_fin_window
lemma retentionFactor_eq_fin_window {T M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    retentionFactor hd zeta code v t w =
      sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
        ∏ r ∈ (Finset.univ : Finset (Fin T)).filter
          (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val),
            retentionIndicator hd code v (w r).1 (w r).2.1 := by
  classical
  dsimp only [retentionFactor]
  congr 1
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro r hr
  have h : r < T := Finset.mem_range.mp hr
  simp only [h, ↓reduceDIte]

/-- The exact retention-window moment under the common independent context-action law, for any
fixed reward word. This includes every stationary initial window and gives the equality in step
(19). For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the policy-overlap scale](hyp:zeta),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the reward](hyp:reward), this establishes
[the retention factor context action second moment result](goal). -/
-- @node: retentionFactor_context_action_second_moment
lemma retentionFactor_context_action_second_moment {T M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (reward : Fin T → Fin 2) :
    (∑ w : Fin T → Fin (d * hdepth Q) × Bool,
      (∏ r, ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (w r).2) *
        retentionFactor hd zeta code v t
          (fun r ↦ ((w r).1, (w r).2, reward r)) ^ 2) =
      sparseRetentionProbability Q zeta ^ (2 * Q - min Q t.val) := by
  classical
  let s := (Finset.univ : Finset (Fin T)).filter
    (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val)
  have hc : s.card = min Q t.val := retention_window_card Q t
  simp_rw [retentionFactor_eq_fin_window hd zeta code v]
  change (∑ w : Fin T → Fin (d * hdepth Q) × Bool,
    (∏ r, ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (w r).2) *
      (sparseRetentionProbability Q zeta ^ (Q - min Q t.val) *
        ∏ r ∈ s, retentionIndicator hd code v (w r).1 (w r).2) ^ 2) = _
  rw [← hc]
  rw [finite_retention_prefix_second_moment
    (fun xa : Fin (d * hdepth Q) × Bool ↦
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta xa.2)
    (fun xa ↦ retentionIndicator hd code v xa.1 xa.2)
    (sparseRetentionProbability Q zeta) Q s
    (sparse_context_action_weight_sum d Q hd zeta)
    (sparse_retention_second_moment hd zeta code v)]
  rw [hc]
  congr 1
  omega

/-- Uniform second-moment bound for early and complete retention windows under the common
context-action product law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the policy-overlap scale](hyp:zeta),
[the policy-overlap scale assumption](hyp:hzeta), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the reward](hyp:reward), this
establishes [the retention factor context action second moment bound result](goal). -/
-- @node: retentionFactor_context_action_second_moment_le
lemma retentionFactor_context_action_second_moment_le {T M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (hzeta : 0 < zeta) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (reward : Fin T → Fin 2) :
    (∑ w : Fin T → Fin (d * hdepth Q) × Bool,
      (∏ r, ((d * hdepth Q : Nat) : ℝ)⁻¹ * sparseBehaviorWeight zeta (w r).2) *
        retentionFactor hd zeta code v t
          (fun r ↦ ((w r).1, (w r).2, reward r)) ^ 2) ≤
      sparseRetentionProbability Q zeta ^ Q := by
  rw [retentionFactor_context_action_second_moment hd zeta code v t reward]
  obtain ⟨hp0, hp1⟩ := sparseRetentionProbability_mem_unitInterval Q zeta hzeta
  exact pow_le_pow_of_le_one hp0 hp1 (by omega)

end CausalSmith.Stat.PomdpPolicyclassRegret
