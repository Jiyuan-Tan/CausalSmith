module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseDensityInvariance

/-! # Mean retention in the sparse context experiment

Counting the exceptional context slots gives the behavior and target retention
factors in equation (19), which identify the stationary signed densities.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Flattening a coordinate and slot recovers the coordinate index. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the i](hyp:i), and [the reward symbol](hyp:r), this
establishes [the sparse context index prod result](goal). -/
-- @node: sparse_context_index_prod
lemma sparse_context_index_prod {d Q : Nat} (hd : 0 < d)
    (i : Fin d) (r : Fin (hdepth Q)) :
    contextIndex hd (finProdFinEquiv (i, r)) = i := by
  apply Fin.ext
  dsimp [contextIndex, finProdFinEquiv]
  rw [Nat.add_mul_div_left _ _ (by simp [hdepth]), Nat.div_eq_of_lt r.isLt]
  simp

/-- In product coordinates, exceptionality means matching the code-selected slot. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), [the i](hyp:i), and
[the reward symbol](hyp:r), this establishes [the sparse exceptional context prod result](goal). -/
-- @node: sparse_exceptional_context_prod
lemma sparse_exceptional_context_prod {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (i : Fin d) (r : Fin (hdepth Q)) :
    exceptionalContext hd code v (finProdFinEquiv (i, r)) ↔
      r.val = if code v i then 1 else 0 := by
  unfold exceptionalContext
  rw [sparse_context_index_prod]
  simp [finProdFinEquiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]

/-- Exactly one slot is exceptional in each coordinate. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the i](hyp:i), this establishes
[the sparse exceptional slot sum result](goal). -/
-- @node: sparse_exceptional_slot_sum
lemma sparse_exceptional_slot_sum {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M) (i : Fin d) :
    (∑ r : Fin (hdepth Q),
      if exceptionalContext hd code v (finProdFinEquiv (i, r)) then (1 : ℝ) else 0) = 1 := by
  classical
  simp_rw [sparse_exceptional_context_prod]
  have hzero (r : Fin (hdepth Q)) :
      (r.val = 0) = (r = ⟨0, by simp [hdepth]⟩) := by
    apply propext; simp [Fin.ext_iff]
  have hone (r : Fin (hdepth Q)) :
      (r.val = 1) = (r = ⟨1, by simp [hdepth]⟩) := by
    apply propext; simp [Fin.ext_iff]
  cases code v i <;> simp only [Bool.false_eq_true,
    ↓reduceIte, hzero, hone] <;> simp

/-- There are precisely d exceptional contexts in a word's exceptional set. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), and [the codeword index](hyp:v), this establishes
[the sparse exceptional context sum result](goal). -/
-- @node: sparse_exceptional_context_sum
lemma sparse_exceptional_context_sum {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M) :
    (∑ x : Fin (d * hdepth Q), if exceptionalContext hd code v x then (1 : ℝ) else 0) = d := by
  classical
  rw [Fintype.sum_equiv finProdFinEquiv.symm
    (fun x ↦ if exceptionalContext hd code v x then (1 : ℝ) else 0)
    (fun z ↦ if exceptionalContext hd code v (finProdFinEquiv z) then (1 : ℝ) else 0)
    (fun x ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [sparse_exceptional_slot_sum hd code v]
  simp

/-- Under behavior, an advance keeps the sign always on the exceptional set, and otherwise only
when action one is drawn. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the binary code](hyp:code), [the codeword index](hyp:v),
and [the observed state](hyp:x), this establishes
[the sparse behavior retention context result](goal). -/
-- @node: sparse_behavior_retention_context
lemma sparse_behavior_retention_context {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) :
    (∑ a : Bool, sparseBehaviorWeight zeta a * retentionIndicator hd code v x a) =
      (policyFactor zeta)⁻¹ + (1 - (policyFactor zeta)⁻¹) *
        (if exceptionalContext hd code v x then 1 else 0) := by
  classical
  by_cases hx : exceptionalContext hd code v x <;>
    simp [sparseBehaviorWeight, retentionIndicator, hx]

/-- Behavior retention averaged over uniform contexts is p + (1-p)/h. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the binary code](hyp:code), and
[the codeword index](hyp:v), this establishes
[the sparse behavior retention average result](goal). -/
-- @node: sparse_behavior_retention_average
lemma sparse_behavior_retention_average {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) :
    ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      (∑ x : Fin (d * hdepth Q), ∑ a : Bool,
        sparseBehaviorWeight zeta a * retentionIndicator hd code v x a) =
      (policyFactor zeta)⁻¹ + (1 - (policyFactor zeta)⁻¹) / (hdepth Q : ℝ) := by
  classical
  simp_rw [sparse_behavior_retention_context]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sparse_exceptional_context_sum hd code v]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hh0 : (hdepth Q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < hdepth Q by simp [hdepth]))
  field_simp

/-- A target loses retention only on its own exceptional contexts outside the environment's
exceptional set, with probability 1-p. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the policy-overlap scale](hyp:zeta),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed word](hyp:w), and
[the observed state](hyp:x), this establishes
[the sparse target retention context result](goal). -/
-- @node: sparse_target_retention_context
lemma sparse_target_retention_context {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v w : Fin M)
    (x : Fin (d * hdepth Q)) :
    (∑ a : Bool, sparseTargetWeight hd zeta code w x a * retentionIndicator hd code v x a) =
      1 - (1 - (policyFactor zeta)⁻¹) *
        (if exceptionalContext hd code w x ∧ ¬ exceptionalContext hd code v x then 1 else 0) := by
  classical
  by_cases hv : exceptionalContext hd code v x <;>
    by_cases hw : exceptionalContext hd code w x <;>
    simp [sparseTargetWeight, sparseBehaviorWeight, retentionIndicator, hv, hw]

/-- The exceptional-set difference contains one slot for each differing bit. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed word](hyp:w), and
[the i](hyp:i), this establishes [the sparse exceptional difference slot sum result](goal). -/
-- @node: sparse_exceptional_difference_slot_sum
lemma sparse_exceptional_difference_slot_sum {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v w : Fin M) (i : Fin d) :
    (∑ r : Fin (hdepth Q),
      if exceptionalContext hd code w (finProdFinEquiv (i, r)) ∧
        ¬ exceptionalContext hd code v (finProdFinEquiv (i, r)) then (1 : ℝ) else 0) =
      if code v i ≠ code w i then 1 else 0 := by
  classical
  simp_rw [sparse_exceptional_context_prod]
  have hzero (r : Fin (hdepth Q)) :
      (r.val = 0) = (r = ⟨0, by simp [hdepth]⟩) := by
    apply propext; simp [Fin.ext_iff]
  have hone (r : Fin (hdepth Q)) :
      (r.val = 1) = (r = ⟨1, by simp [hdepth]⟩) := by
    apply propext; simp [Fin.ext_iff]
  have h10 (r : Fin (hdepth Q)) :
      (r.val = 1 ∧ ¬ r.val = 0) = (r.val = 1) := by
    apply propext; omega
  have h01 (r : Fin (hdepth Q)) :
      (r.val = 0 ∧ ¬ r.val = 1) = (r.val = 0) := by
    apply propext; omega
  cases code v i <;> cases code w i <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_true_eq_false, not_false_eq_true,
      ↓reduceIte] <;>
    (try simp only [h10, h01]) <;> simp only [hzero, hone] <;> simp

/-- Summing the exceptional-set difference gives the Hamming distance. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), and [the observed word](hyp:w), this
establishes [the sparse exceptional difference sum result](goal). -/
-- @node: sparse_exceptional_difference_sum
lemma sparse_exceptional_difference_sum {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v w : Fin M) :
    (∑ x : Fin (d * hdepth Q),
      if exceptionalContext hd code w x ∧ ¬ exceptionalContext hd code v x then (1 : ℝ) else 0) =
      hammingDistance code v w := by
  classical
  rw [Fintype.sum_equiv finProdFinEquiv.symm
    (fun x ↦ if exceptionalContext hd code w x ∧
      ¬ exceptionalContext hd code v x then (1 : ℝ) else 0)
    (fun z ↦ if exceptionalContext hd code w (finProdFinEquiv z) ∧
      ¬ exceptionalContext hd code v (finProdFinEquiv z) then (1 : ℝ) else 0)
    (fun x ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [sparse_exceptional_difference_slot_sum hd code v w]
  rw [← Finset.sum_filter]
  simp [hammingDistance]

/-- Target retention averaged over uniform contexts is exactly lambda_vw. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the binary code](hyp:code), [the codeword index](hyp:v),
and [the observed word](hyp:w), this establishes
[the sparse target retention average result](goal). -/
-- @node: sparse_target_retention_average
lemma sparse_target_retention_average {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v w : Fin M) :
    ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      (∑ x : Fin (d * hdepth Q), ∑ a : Bool,
        sparseTargetWeight hd zeta code w x a * retentionIndicator hd code v x a) =
      1 - (1 - (policyFactor zeta)⁻¹) * (hammingDistance code v w : ℝ) /
        ((d : ℝ) * hdepth Q) := by
  classical
  simp_rw [sparse_target_retention_context]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sparse_exceptional_difference_sum hd code v w]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, mul_one]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hh0 : (hdepth Q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < hdepth Q by simp [hdepth]))
  field_simp

/-- Both retention factors lie in the unit interval, and target retention is at least behavior
retention because at most d code bits differ. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed word](hyp:w), [the policy](hyp:p),
[the p0 assumption](hyp:hp0), and [the p1 assumption](hyp:hp1), this establishes
[the sparse retention factor bounds result](goal). -/
-- @node: sparse_retention_factor_bounds
lemma sparse_retention_factor_bounds {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v w : Fin M)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p + (1 - p) / (hdepth Q : ℝ) ∧
    p + (1 - p) / (hdepth Q : ℝ) ≤
      1 - (1 - p) * (hammingDistance code v w : ℝ) / ((d : ℝ) * hdepth Q) ∧
    1 - (1 - p) * (hammingDistance code v w : ℝ) / ((d : ℝ) * hdepth Q) ≤ 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : (2 : ℝ) ≤ hdepth Q := by
    exact_mod_cast (show 2 ≤ hdepth Q by simp [hdepth])
  have hhpos : (0 : ℝ) < hdepth Q := by linarith
  have hD : (hammingDistance code v w : ℝ) ≤ d := by
    exact_mod_cast (show hammingDistance code v w ≤ d by
      unfold hammingDistance
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i : Fin d ↦ code v i ≠ code w i) Finset.univ))
  have hratio : (hammingDistance code v w : ℝ) / d ≤ 1 :=
    (div_le_one hdpos).mpr hD
  have hsmall : (1 - p) * (hammingDistance code v w : ℝ) /
      ((d : ℝ) * hdepth Q) ≤ (1 - p) / (hdepth Q : ℝ) := by
    calc
      _ = ((1 - p) * ((hammingDistance code v w : ℝ) / d)) / hdepth Q := by ring
      _ ≤ (1 - p) / (hdepth Q : ℝ) := by
        apply div_le_div_of_nonneg_right _ hhpos.le
        simpa using mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hp1)
  have hhalf : (1 - p) / (hdepth Q : ℝ) ≤ (1 - p) / 2 :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hp1) (by norm_num) hh
  refine ⟨add_nonneg hp0 (div_nonneg (sub_nonneg.mpr hp1) hhpos.le), ?_, ?_⟩
  · linarith
  · exact sub_le_self _ (by positivity)

/-- The raw behavior weights are a probability policy. For [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the policy-overlap scale](hyp:zeta), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the sparse behavior weight policy vector result](goal). -/
-- @node: sparse_behavior_weight_policyVector
lemma sparse_behavior_weight_policyVector (d Q : Nat) (zeta : ℝ)
    (hzeta : 0 < zeta) :
    PolicyVector (fun (_ : Fin (d * hdepth Q)) a ↦ sparseBehaviorWeight zeta a) := by
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  intro x
  refine ⟨?_, ?_⟩
  · intro a
    cases a <;> simp [sparseBehaviorWeight] <;> linarith
  · simp [sparseBehaviorWeight]

/-- The raw target weights are probability policies on every context. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), and [the observed word](hyp:w), this establishes
[the sparse target weight policy vector result](goal). -/
-- @node: sparse_target_weight_policyVector
lemma sparse_target_weight_policyVector {M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (hzeta : 0 < zeta) (code : Fin M → Fin d → Bool) (w : Fin M) :
    PolicyVector (sparseTargetWeight (Q := Q) hd zeta code w) := by
  intro x
  by_cases hx : exceptionalContext hd code w x
  · simpa only [sparseTargetWeight, hx, if_true] using
      sparse_behavior_weight_policyVector d Q zeta hzeta x
  · constructor
    · intro a
      cases a <;> simp [sparseTargetWeight, hx]
    · simp [sparseTargetWeight, hx]

/-- The behavior stationary law has retention p + (1-p)/h in its signed density. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code), and
[the codeword index](hyp:v), this establishes
[the sparse behavior weight stationary density result](goal). -/
-- @node: sparse_behavior_weight_stationary_density
lemma sparse_behavior_weight_stationary_density {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) :
    stationaryLaw (fun s s' ↦ ∑ a : Bool,
      sparseBehaviorWeight zeta a * sparseStateWeight hd t0 C code v false s s' a) =
      sparseSignedDensity d Q t0 C
        ((policyFactor zeta)⁻¹ + (1 - (policyFactor zeta)⁻¹) / (hdepth Q : ℝ)) := by
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  have hb := sparse_retention_factor_bounds (Q := Q) hd code v v
    (policyFactor zeta)⁻¹ hp0 hp1
  exact sparse_signed_density_stationaryLaw hd t0 C _ ht0 hC hb.1
    (hb.2.1.trans hb.2.2) code v _
    (sparse_behavior_weight_policyVector d Q zeta hzeta)
    (sparse_behavior_retention_average hd zeta code v)

/-- Each target stationary law has the Hamming-distance retention factor in its signed density.
For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed word](hyp:w), this establishes
[the sparse target weight stationary density result](goal). -/
-- @node: sparse_target_weight_stationary_density
lemma sparse_target_weight_stationary_density {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v w : Fin M) :
    stationaryLaw (fun s s' ↦ ∑ a : Bool,
      sparseTargetWeight hd zeta code w s.1 a *
        sparseStateWeight hd t0 C code v false s s' a) =
      sparseSignedDensity d Q t0 C
        (1 - (1 - (policyFactor zeta)⁻¹) * (hammingDistance code v w : ℝ) /
          ((d : ℝ) * hdepth Q)) := by
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  have hb := sparse_retention_factor_bounds (Q := Q) hd code v w
    (policyFactor zeta)⁻¹ hp0 hp1
  exact sparse_signed_density_stationaryLaw hd t0 C _ ht0 hC
    (hb.1.trans hb.2.1) hb.2.2 code v _
    (sparse_target_weight_policyVector hd zeta hzeta code w)
    (sparse_target_retention_average hd zeta code v w)

/-- The target law of the decoded packing is the signed density in (20). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), and [the observed word](hyp:w),
this establishes [the sparse packing target stationary density result](goal). -/
-- @node: sparse_packing_target_stationary_density
lemma sparse_packing_target_stationary_density (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v w : Fin M) :
    listStationaryLaw (sparsePackingExperiment T M d Q hd hDim hM
      t0 zeta C code hCode v)
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E w) =
      sparseSignedDensity d Q t0 C
        (1 - (1 - (policyFactor zeta)⁻¹) * (hammingDistance code v w : ℝ) /
          ((d : ℝ) * hdepth Q)) := by
  unfold listStationaryLaw
  have hk := funext fun s ↦ funext fun s' ↦
    sparse_packing_policy_kernel T M d Q hd hDim hM t0 zeta C
      ht0 hzeta hC code hCode v w s s'
  rw [hk]
  exact sparse_target_weight_stationary_density hd t0 zeta C ht0 hzeta hC code v w

/-- The behavior law of the decoded packing is the signed density in (20). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse packing behavior stationary density result](goal). -/
-- @node: sparse_packing_behavior_stationary_density
lemma sparse_packing_behavior_stationary_density (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    listStationaryLaw (sparsePackingExperiment T M d Q hd hDim hM
      t0 zeta C code hCode v)
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.b) =
      sparseSignedDensity d Q t0 C
        ((policyFactor zeta)⁻¹ + (1 - (policyFactor zeta)⁻¹) / (hdepth Q : ℝ)) := by
  unfold listStationaryLaw
  have hk := funext fun s ↦ funext fun s' ↦
    sparse_packing_policy_kernel_weight T M d Q hd hDim hM t0 zeta C
      ht0 hC code hCode v
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.b) s s'
  rw [hk]
  change stationaryLaw (fun s s' ↦ ∑ a : Bool,
    (sparseBehaviorPMF zeta d Q s.1 a).toReal *
      sparseStateWeight hd t0 C code v false s s' a) = _
  simp_rw [sparse_behavior_pmf_toReal zeta hzeta]
  exact sparse_behavior_weight_stationary_density hd t0 zeta C ht0 hzeta hC code v

/-- The exact stationary densities yield simultaneous latent overlap for all policies in the
revealed list. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the dim assumption](hyp:hDim),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the sparse packing latent stationary overlap result](goal). -/
-- @node: sparse_packing_latent_stationary_overlap
lemma sparse_packing_latent_stationary_overlap (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    ListLatentStationaryOverlap
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v) C := by
  refine ⟨hC.le, ?_⟩
  intro w
  refine ⟨hC.le, ?_⟩
  intro s
  change listStationaryLaw _
    ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E w) s ≤
    C * listStationaryLaw _
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.b) s
  rw [sparse_packing_target_stationary_density T M d Q hd hDim hM
      t0 zeta C ht0 hzeta hC.le code hCode v w,
    sparse_packing_behavior_stationary_density T M d Q hd hDim hM
      t0 zeta C ht0 hzeta hC.le code hCode v]
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  have hb := sparse_retention_factor_bounds (Q := Q) hd code v w
    (policyFactor zeta)⁻¹ hp0 hp1
  exact sparse_signed_density_overlap d Q t0 C _ _ ht0 hC hb.1 hb.2.1 hb.2.2 s

/-- The stationary reward formula is exactly (22), with the target's Hamming-distance retention
factor. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the dim assumption](hyp:hDim),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), and [the observed word](hyp:w),
this establishes [the sparse packing policy value formula result](goal). -/
-- @node: sparse_packing_policy_value_formula
lemma sparse_packing_policy_value_formula (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v w : Fin M) :
    policyValue (sparsePackingExperiment T M d Q hd hDim hM
      t0 zeta C code hCode v) w =
      1 / 2 + sparseSignal t0 * sparseEpsilon C / 2 * depthMass t0 Q Q *
        (1 - (1 - (policyFactor zeta)⁻¹) * (hammingDistance code v w : ℝ) /
          ((d : ℝ) * hdepth Q)) ^ Q := by
  change (∑ s : JointState (d * hdepth Q) (2 * (Q + 1)), listStationaryLaw _
    ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E w) s *
    listRewardRegression _
      ((sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E w) s) = _
  rw [sparse_packing_target_stationary_density T M d Q hd hDim hM
    t0 zeta C ht0 hzeta hC code hCode v w]
  simp_rw [sparse_packing_reward_regression T M d Q hd hDim hM
    t0 zeta C ht0 hzeta hC code hCode v w]
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
  have hp1 : (policyFactor zeta)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hL.le
  have hb := sparse_retention_factor_bounds (Q := Q) hd code v w
    (policyFactor zeta)⁻¹ hp0 hp1
  exact sparse_signed_density_reward_mean d Q hd t0 C _ ht0 hC
    (hb.1.trans hb.2.1) hb.2.2

end CausalSmith.Stat.PomdpPolicyclassRegret
