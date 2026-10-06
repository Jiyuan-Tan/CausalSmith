module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthStationarity
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseStationaryDensity

/-! # Transition invariance of the sparse signed density

The two-sign calculation transports the reset bias through retained advances.
Averaging over uniform contexts then yields the candidate stationary density
for any observed-state policy with its corresponding mean retention.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Every action and context either retains the old sign or redraws it fairly. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x), and
[the action](hyp:a), this establishes [the sparse retention indicator cases result](goal). -/
-- @node: sparse_retention_indicator_cases
lemma sparse_retention_indicator_cases {M d Q : Nat} (hd : 0 < d)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (a : Bool) :
    retentionIndicator hd code v x a = 0 ∨ retentionIndicator hd code v x a = 1 := by
  classical
  unfold retentionIndicator
  split_ifs <;> simp

/-- At a fixed old depth and context, summing the old sign gives the reset mass or an advance
with its bias multiplied by the retention indicator. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the reward symbol](hyp:r), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the candidate index](hyp:j),
[the successor state](hyp:s'), and [the action](hyp:a), this establishes
[the sparse signed density step sign sum result](goal). -/
-- @node: sparse_signed_density_step_sign_sum
lemma sparse_signed_density_step_sign_sum {M d Q : Nat} (hd : 0 < d)
    (t0 C r : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1))
    (s' : JointState (d * hdepth Q) (2 * (Q + 1))) (a : Bool) :
    (∑ u : Fin 2, sparseSignedDensity d Q t0 C r (x, depthSignEquiv Q (j, u)) *
      sparseStateWeight hd t0 C code v false (x, depthSignEquiv Q (j, u)) s' a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ ^ 2 * depthMass t0 Q j.val *
        (if j.val = Q then
          if hiddenDepth Q s'.2 = 0 then resetSignWeight C false (hiddenSign Q s'.2)
          else 0
        else
          (if hiddenDepth Q s'.2 = 0 then
            (1 - mixingAlpha t0) * resetSignWeight C false (hiddenSign Q s'.2)
            else 0) +
          (if hiddenDepth Q s'.2 = j.val + 1 then
            mixingAlpha t0 * (1 + signValue (hiddenSign Q s'.2) * sparseEpsilon C *
              r ^ j.val * retentionIndicator hd code v x a) / 2 else 0)) := by
  classical
  rw [Fin.sum_univ_two]
  rcases sparse_retention_indicator_cases hd code v x a with hr | hr <;>
    by_cases hj : j.val = Q <;>
    by_cases hz : hiddenDepth Q s'.2 = 0 <;>
    by_cases hn : hiddenDepth Q s'.2 = j.val + 1 <;>
    cases hs : hiddenSign Q s'.2 <;>
    simp [sparseSignedDensity, sparseStateWeight, sparse_hidden_depth_enumeration,
      (sparse_hidden_sign_enumeration Q j).1, (sparse_hidden_sign_enumeration Q j).2,
      hr, hj, hz, hn, hs, signValue] <;> ring

/-- Averaging over the two actions preserves reset mass and replaces the advance indicator with
its probability under the observed-state policy. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the reward symbol](hyp:r), [the binary code](hyp:code),
[the codeword index](hyp:v), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the observed state](hyp:x), [the candidate index](hyp:j), and [the successor state](hyp:s'),
this establishes [the sparse signed density step policy sum result](goal). -/
-- @node: sparse_signed_density_step_policy_sum
lemma sparse_signed_density_step_policy_sum {M d Q : Nat} (hd : 0 < d)
    (t0 C r : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1))
    (s' : JointState (d * hdepth Q) (2 * (Q + 1))) :
    (∑ u : Fin 2, sparseSignedDensity d Q t0 C r (x, depthSignEquiv Q (j, u)) *
      ∑ a : Bool, p x a *
        sparseStateWeight hd t0 C code v false (x, depthSignEquiv Q (j, u)) s' a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ ^ 2 * depthMass t0 Q j.val *
        (if j.val = Q then
          if hiddenDepth Q s'.2 = 0 then resetSignWeight C false (hiddenSign Q s'.2)
          else 0
        else
          (if hiddenDepth Q s'.2 = 0 then
            (1 - mixingAlpha t0) * resetSignWeight C false (hiddenSign Q s'.2)
            else 0) +
          (if hiddenDepth Q s'.2 = j.val + 1 then
            mixingAlpha t0 * (1 + signValue (hiddenSign Q s'.2) * sparseEpsilon C *
              r ^ j.val * (∑ a : Bool, p x a * retentionIndicator hd code v x a)) / 2
            else 0)) := by
  classical
  calc
    _ = ∑ a : Bool, p x a *
        (∑ u : Fin 2, sparseSignedDensity d Q t0 C r (x, depthSignEquiv Q (j, u)) *
          sparseStateWeight hd t0 C code v false (x, depthSignEquiv Q (j, u)) s' a) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp_rw [sparse_signed_density_step_sign_sum]
      have hmass := (hp x).2
      simp only [Fintype.sum_bool] at hmass ⊢
      have hfalse : p x false = 1 - p x true := by linarith only [hmass]
      rw [hfalse]
      split_ifs <;> ring

/-- Uniform-context averaging of an affine function replaces its variable by its uniform mean,
retaining one context factor for the next state. For [the sample size](hyp:n),
[the sample size assumption](hyp:hn), [the observed word](hyp:w), [the action](hyp:a),
[the behavior policy](hyp:b), and [the f](hyp:f), this establishes
[the sparse context affine sum result](goal). -/
-- @node: sparse_context_affine_sum
lemma sparse_context_affine_sum (n : Nat) (hn : 0 < n) (w a b : ℝ)
    (f : Fin n → ℝ) :
    (∑ x : Fin n, (n : ℝ)⁻¹ ^ 2 * w * (a + b * f x)) =
      (n : ℝ)⁻¹ * w * (a + b * ((n : ℝ)⁻¹ * ∑ x, f x)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn']

/-- After summing the old context and sign, a fixed depth contributes its reset mass or an
advance with the policy's mean retention. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the reward symbol](hyp:r), [the binary code](hyp:code),
[the codeword index](hyp:v), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the ret assumption](hyp:hret), [the candidate index](hyp:j), and [the successor state](hyp:s'),
this establishes [the sparse signed density step context sum result](goal). -/
-- @node: sparse_signed_density_step_context_sum
lemma sparse_signed_density_step_context_sum {M d Q : Nat} (hd : 0 < d)
    (t0 C r : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p)
    (hret : ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      (∑ x, ∑ a : Bool, p x a * retentionIndicator hd code v x a) = r)
    (j : Fin (Q + 1)) (s' : JointState (d * hdepth Q) (2 * (Q + 1))) :
    (∑ x, ∑ u : Fin 2,
      sparseSignedDensity d Q t0 C r (x, depthSignEquiv Q (j, u)) *
        ∑ a : Bool, p x a *
          sparseStateWeight hd t0 C code v false (x, depthSignEquiv Q (j, u)) s' a) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q j.val *
        (if j.val = Q then
          if hiddenDepth Q s'.2 = 0 then resetSignWeight C false (hiddenSign Q s'.2)
          else 0
        else
          (if hiddenDepth Q s'.2 = 0 then
            (1 - mixingAlpha t0) * resetSignWeight C false (hiddenSign Q s'.2)
            else 0) +
          (if hiddenDepth Q s'.2 = j.val + 1 then
            mixingAlpha t0 * (1 + signValue (hiddenSign Q s'.2) * sparseEpsilon C *
              r ^ (j.val + 1)) / 2 else 0)) := by
  classical
  simp_rw [sparse_signed_density_step_policy_sum hd t0 C r code v p hp]
  let f := fun x ↦ ∑ a : Bool, p x a * retentionIndicator hd code v x a
  have hn : 0 < d * hdepth Q := Nat.mul_pos hd (by simp [hdepth])
  let A : ℝ := if j.val = Q then
    if hiddenDepth Q s'.2 = 0 then resetSignWeight C false (hiddenSign Q s'.2) else 0
    else (if hiddenDepth Q s'.2 = 0 then
      (1 - mixingAlpha t0) * resetSignWeight C false (hiddenSign Q s'.2) else 0) +
      (if hiddenDepth Q s'.2 = j.val + 1 then mixingAlpha t0 / 2 else 0)
  let B : ℝ := if j.val = Q then 0 else
    if hiddenDepth Q s'.2 = j.val + 1 then
      mixingAlpha t0 * signValue (hiddenSign Q s'.2) * sparseEpsilon C * r ^ j.val / 2
    else 0
  calc
    _ = ∑ x, ((d * hdepth Q : Nat) : ℝ)⁻¹ ^ 2 * depthMass t0 Q j.val *
        (A + B * f x) := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [A, B, f]
      split_ifs <;> ring
    _ = ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q j.val * (A + B * r) := by
      rw [sparse_context_affine_sum _ hn, show
        ((d * hdepth Q : Nat) : ℝ)⁻¹ * ∑ x, f x = r from hret]
    _ = _ := by
      dsimp [A, B]
      simp only [pow_succ]
      split_ifs <;> ring

/-- The candidate signed density is stationary when its retention parameter is the
uniform-context average of the policy's retention probabilities. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the latent-overlap radius](hyp:C), [the reward symbol](hyp:r),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1), [the binary code](hyp:code),
[the codeword index](hyp:v), [the policy](hyp:p), [the policy assumption](hyp:hp), and
[the ret assumption](hyp:hret), this establishes
[the sparse signed density is stationary result](goal). -/
-- @node: sparse_signed_density_isStationary
lemma sparse_signed_density_isStationary {M d Q : Nat} (hd : 0 < d)
    (t0 C r : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p)
    (hret : ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      (∑ x, ∑ a : Bool, p x a * retentionIndicator hd code v x a) = r) :
    IsStationary (fun s s' ↦ ∑ a : Bool,
      p s.1 a * sparseStateWeight hd t0 C code v false s s' a)
      (sparseSignedDensity d Q t0 C r) := by
  classical
  refine ⟨sparse_signed_density_probability d Q hd t0 C r ht0 hC hr0 hr1, ?_⟩
  intro s'
  rw [Fintype.sum_prod_type]
  have hhidden (x : Fin (d * hdepth Q)) :
      (∑ h, sparseSignedDensity d Q t0 C r (x, h) *
        ∑ a : Bool, p x a * sparseStateWeight hd t0 C code v false (x, h) s' a) =
      ∑ j : Fin (Q + 1), ∑ u : Fin 2,
        sparseSignedDensity d Q t0 C r (x, depthSignEquiv Q (j, u)) *
          ∑ a : Bool, p x a *
            sparseStateWeight hd t0 C code v false (x, depthSignEquiv Q (j, u)) s' a := by
    rw [Fintype.sum_equiv (depthSignEquiv Q).symm
      (fun h ↦ sparseSignedDensity d Q t0 C r (x, h) *
        ∑ a : Bool, p x a * sparseStateWeight hd t0 C code v false (x, h) s' a)
      (fun z ↦ sparseSignedDensity d Q t0 C r (x, depthSignEquiv Q z) *
        ∑ a : Bool, p x a *
          sparseStateWeight hd t0 C code v false (x, depthSignEquiv Q z) s' a)
      (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [hhidden]
  rw [Finset.sum_comm]
  simp_rw [sparse_signed_density_step_context_sum hd t0 C r code v p hp hret]
  by_cases hz : hiddenDepth Q s'.2 = 0
  · have hn (j : Fin (Q + 1)) : hiddenDepth Q s'.2 ≠ j.val + 1 := by omega
    simp_rw [if_neg (hn _), hz, if_true, add_zero]
    calc
      _ = ((d * hdepth Q : Nat) : ℝ)⁻¹ *
          (∑ j : Fin (Q + 1), if j.val = Q then depthMass t0 Q j.val
            else (1 - mixingAlpha t0) * depthMass t0 Q j.val) *
          resetSignWeight C false (hiddenSign Q s'.2) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by
        rw [depthMass_reset_balance ht0]
        simp only [sparseSignedDensity, hz, pow_zero, mul_one, resetSignWeight,
          Bool.false_eq_true, if_false]
        ring
  · let j : Fin (Q + 1) := ⟨hiddenDepth Q s'.2 - 1, by
      have hh := s'.2.isLt
      unfold hiddenDepth
      omega⟩
    have hjnext : hiddenDepth Q s'.2 = j.val + 1 := by dsimp [j]; omega
    have hjterm : j.val ≠ Q := by
      have hh := s'.2.isLt
      dsimp [j]
      unfold hiddenDepth at *
      omega
    rw [Fintype.sum_eq_single j]
    · simp only [hjterm, hjnext, Nat.add_one_ne_zero, ↓reduceIte, zero_add]
      simp only [sparseSignedDensity, hjnext, depthMass_succ]
      ring
    · intro i hij
      have hine : hiddenDepth Q s'.2 ≠ i.val + 1 := by
        intro he
        apply hij
        apply Fin.ext
        dsimp [j]
        omega
      simp only [hz, hine, ↓reduceIte, add_zero, mul_zero, ite_self]

/-- Common-reset contraction identifies the selected stationary law with the explicit signed
density once the mean retention has been computed. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the latent-overlap radius](hyp:C), [the reward symbol](hyp:r),
[the mixing scale assumption](hyp:ht0), [the latent-overlap radius assumption](hyp:hC),
[the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1), [the binary code](hyp:code),
[the codeword index](hyp:v), [the policy](hyp:p), [the policy assumption](hyp:hp), and
[the ret assumption](hyp:hret), this establishes
[the sparse signed density stationary law result](goal). -/
-- @node: sparse_signed_density_stationaryLaw
lemma sparse_signed_density_stationaryLaw {M d Q : Nat} (hd : 0 < d)
    (t0 C r : ℝ) (ht0 : 0 < t0) (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (p : Fin (d * hdepth Q) → Bool → ℝ) (hp : PolicyVector p)
    (hret : ((d * hdepth Q : Nat) : ℝ)⁻¹ *
      (∑ x, ∑ a : Bool, p x a * retentionIndicator hd code v x a) = r) :
    stationaryLaw (fun s s' ↦ ∑ a : Bool,
      p s.1 a * sparseStateWeight hd t0 C code v false s s' a) =
      sparseSignedDensity d Q t0 C r := by
  exact stationary_unique_of_contraction _ (mixingAlpha t0) (mixingAlpha_lt_one ht0)
    (sparse_policy_weight_contraction hd t0 C ht0 hC code v false p hp)
    (sparse_policy_weight_stationary hd t0 C ht0 hC code v false p hp)
    (sparse_signed_density_isStationary hd t0 C r ht0 hC hr0 hr1 code v p hp hret)

end CausalSmith.Stat.PomdpPolicyclassRegret
