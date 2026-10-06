module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseStationaryStart

/-! # Explicit signed densities for the sparse packing

These are the candidate densities in equation (20) of the membership roadmap.
Normalization, pointwise overlap, and their terminal reward means are verified
here. Identifying them with the selected stationary laws remains a separate
transition-invariance calculation.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- The candidate joint density has a uniform context, geometric depth,
and a sign whose mean is the reset bias times the retention power. -/
-- @node: sparseSignedDensity
noncomputable def sparseSignedDensity (d Q : Nat) (t0 C retention : ℝ)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) : ℝ :=
  ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q (hiddenDepth Q s.2) *
    (1 + signValue (hiddenSign Q s.2) * sparseEpsilon C *
      retention ^ hiddenDepth Q s.2) / 2

/-- Summing the two signs removes the bias at each fixed depth and context. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the retention](hyp:retention), [the observed state](hyp:x),
and [the candidate index](hyp:j), this establishes
[the sparse signed density sum sign result](goal). -/
-- @node: sparse_signed_density_sum_sign
lemma sparse_signed_density_sum_sign (d Q : Nat) (t0 C retention : ℝ)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1)) :
    (∑ u : Fin 2, sparseSignedDensity d Q t0 C retention
      (x, depthSignEquiv Q (j, u))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q j.val := by
  rw [Fin.sum_univ_two]
  simp only [sparseSignedDensity, sparse_hidden_depth_enumeration,
    sparse_hidden_sign_enumeration, signValue, Bool.false_eq_true, if_false, if_true]
  ring

/-- The candidate density is nonnegative for every retention in the unit interval. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the retention](hyp:retention),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1), and [the state](hyp:s), this
establishes [the sparse signed density nonnegativity result](goal). -/
-- @node: sparse_signed_density_nonneg
lemma sparse_signed_density_nonneg (d Q : Nat) (t0 C retention : ℝ)
    (ht0 : 0 < t0) (hC : 1 ≤ C) (hr0 : 0 ≤ retention) (hr1 : retention ≤ 1)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) :
    0 ≤ sparseSignedDensity d Q t0 C retention s := by
  have he := sparse_epsilon_bounds C hC
  have hp0 := pow_nonneg hr0 (hiddenDepth Q s.2)
  have hp1 : retention ^ hiddenDepth Q s.2 ≤ 1 := pow_le_one₀ hr0 hr1
  have hf : 0 ≤ 1 + signValue (hiddenSign Q s.2) * sparseEpsilon C *
      retention ^ hiddenDepth Q s.2 := by
    cases hs : hiddenSign Q s.2 <;> simp only [signValue, Bool.false_eq_true,
      if_false, if_true, one_mul, neg_one_mul]
    · nlinarith [mul_le_mul_of_nonneg_left hp1 he.1]
    · nlinarith [mul_nonneg he.1 hp0]
  unfold sparseSignedDensity
  exact div_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (depthMass_nonneg ht0 Q _)) hf) (by norm_num)

/-- Summing all hidden coordinates gives the uniform context mass. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the retention](hyp:retention),
[the mixing scale assumption](hyp:ht0), and [the observed state](hyp:x), this establishes
[the sparse signed density context mass result](goal). -/
-- @node: sparse_signed_density_context_mass
lemma sparse_signed_density_context_mass (d Q : Nat) (t0 C retention : ℝ)
    (ht0 : 0 < t0) (x : Fin (d * hdepth Q)) :
    (∑ h : Fin (2 * (Q + 1)), sparseSignedDensity d Q t0 C retention (x, h)) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ sparseSignedDensity d Q t0 C retention (x, h))
    (fun z ↦ sparseSignedDensity d Q t0 C retention (x, depthSignEquiv Q z))
    (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [sparse_signed_density_sum_sign]
  rw [← Finset.mul_sum, sum_depthMass ht0 Q, mul_one]

/-- The explicit candidate density is a probability vector. For [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the retention](hyp:retention),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the r0 assumption](hyp:hr0), and [the r1 assumption](hyp:hr1), this establishes
[the sparse signed density probability result](goal). -/
-- @node: sparse_signed_density_probability
lemma sparse_signed_density_probability (d Q : Nat) (hd : 0 < d)
    (t0 C retention : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (hr0 : 0 ≤ retention) (hr1 : retention ≤ 1) :
    ProbabilityVector (sparseSignedDensity d Q t0 C retention) := by
  refine ⟨sparse_signed_density_nonneg d Q t0 C retention ht0 hC hr0 hr1, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [sparse_signed_density_context_mass d Q t0 C retention ht0]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hn

/-- Greater target retention preserves the radius-C pointwise density bound. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the policy](hyp:p), [the retention](hyp:retention),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the policy assumption](hyp:hp), [the pr assumption](hyp:hpr),
[the reward symbol assumption](hyp:hr), and [the state](hyp:s), this establishes
[the sparse signed density overlap result](goal). -/
-- @node: sparse_signed_density_overlap
lemma sparse_signed_density_overlap (d Q : Nat) (t0 C p retention : ℝ)
    (ht0 : 0 < t0) (hC : 1 < C) (hp : 0 ≤ p)
    (hpr : p ≤ retention) (hr : retention ≤ 1)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) :
    sparseSignedDensity d Q t0 C retention s ≤
      C * sparseSignedDensity d Q t0 C p s := by
  have hb : 0 ≤ ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      depthMass t0 Q (hiddenDepth Q s.2) / 2 := by
    exact div_nonneg (mul_nonneg (by positivity) (depthMass_nonneg ht0 Q _))
      (by norm_num)
  have h := mul_le_mul_of_nonneg_left
    (sparse_sign_weight_overlap C p retention (hiddenDepth Q s.2)
      hC hp hpr hr (hiddenSign Q s.2)) hb
  dsimp only [sparseSignedDensity]
  nlinarith only [h]

/-- The signed first moment at a fixed depth retains exactly the bias power. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the retention](hyp:retention), [the observed state](hyp:x),
and [the candidate index](hyp:j), this establishes
[the sparse signed density sign moment result](goal). -/
-- @node: sparse_signed_density_sign_moment
lemma sparse_signed_density_sign_moment (d Q : Nat) (t0 C retention : ℝ)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1)) :
    (∑ u : Fin 2, sparseSignedDensity d Q t0 C retention
      (x, depthSignEquiv Q (j, u)) *
        signValue (hiddenSign Q (depthSignEquiv Q (j, u)))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q j.val *
        sparseEpsilon C * retention ^ j.val := by
  rw [Fin.sum_univ_two]
  simp only [sparseSignedDensity, sparse_hidden_depth_enumeration,
    sparse_hidden_sign_enumeration, signValue, Bool.false_eq_true, if_false, if_true]
  ring

/-- Only terminal depth contributes to the reward signal in the explicit density. For
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), and [the retention](hyp:retention), this establishes
[the sparse signed density terminal moment result](goal). -/
-- @node: sparse_signed_density_terminal_moment
lemma sparse_signed_density_terminal_moment (d Q : Nat) (hd : 0 < d)
    (t0 C retention : ℝ) :
    (∑ s : JointState (d * hdepth Q) (2 * (Q + 1)),
      sparseSignedDensity d Q t0 C retention s * signValue (hiddenSign Q s.2) *
        (if hiddenDepth Q s.2 = Q then 1 else 0)) =
      depthMass t0 Q Q * sparseEpsilon C * retention ^ Q := by
  classical
  rw [Fintype.sum_prod_type]
  have hhidden (x : Fin (d * hdepth Q)) :
      (∑ h : Fin (2 * (Q + 1)), sparseSignedDensity d Q t0 C retention (x, h) *
        signValue (hiddenSign Q h) * (if hiddenDepth Q h = Q then 1 else 0)) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q Q *
        sparseEpsilon C * retention ^ Q := by
    rw [Fintype.sum_equiv (depthSignEquiv Q).symm
      (fun h ↦ sparseSignedDensity d Q t0 C retention (x, h) *
        signValue (hiddenSign Q h) * (if hiddenDepth Q h = Q then 1 else 0))
      (fun z ↦ sparseSignedDensity d Q t0 C retention (x, depthSignEquiv Q z) *
        signValue (hiddenSign Q (depthSignEquiv Q z)) *
          (if hiddenDepth Q (depthSignEquiv Q z) = Q then 1 else 0))
      (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
    simp_rw [sparse_hidden_depth_enumeration, ← Finset.sum_mul,
      sparse_signed_density_sign_moment]
    have hind (j : Fin (Q + 1)) : (j.val = Q) = (j = Fin.last Q) := by
      apply propext
      simp [Fin.ext_iff]
    simp_rw [hind]
    simp
  simp_rw [hhidden]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = (((d * hdepth Q : Nat) : ℝ) * ((d * hdepth Q : Nat) : ℝ)⁻¹) *
        (depthMass t0 Q Q * sparseEpsilon C * retention ^ Q) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hn, one_mul]

/-- Averaging the terminal reward regression gives equation (22) for the candidate density,
before its identification with the stationary law. For [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the retention](hyp:retention),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the r0 assumption](hyp:hr0), and [the r1 assumption](hyp:hr1), this establishes
[the sparse signed density reward mean result](goal). -/
-- @node: sparse_signed_density_reward_mean
lemma sparse_signed_density_reward_mean (d Q : Nat) (hd : 0 < d)
    (t0 C retention : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C)
    (hr0 : 0 ≤ retention) (hr1 : retention ≤ 1) :
    (∑ s : JointState (d * hdepth Q) (2 * (Q + 1)),
      sparseSignedDensity d Q t0 C retention s *
        (1 / 2 + sparseSignal t0 * signValue (hiddenSign Q s.2) *
          (if hiddenDepth Q s.2 = Q then 1 else 0) / 2)) =
      1 / 2 + sparseSignal t0 * sparseEpsilon C / 2 *
        depthMass t0 Q Q * retention ^ Q := by
  have hmass := (sparse_signed_density_probability d Q hd t0 C retention
    ht0 hC hr0 hr1).2
  have hterm := sparse_signed_density_terminal_moment d Q hd t0 C retention
  calc
    _ = (∑ s, sparseSignedDensity d Q t0 C retention s) / 2 +
        sparseSignal t0 / 2 * (∑ s, sparseSignedDensity d Q t0 C retention s *
          signValue (hiddenSign Q s.2) * (if hiddenDepth Q s.2 = Q then 1 else 0)) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [hmass, hterm]; ring

end CausalSmith.Stat.PomdpPolicyclassRegret
