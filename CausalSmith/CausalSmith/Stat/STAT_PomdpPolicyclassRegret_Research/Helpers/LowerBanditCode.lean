module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BinaryCode
public import Causalean.Stat.Minimax.Mixture.SignOverlap

/-! # Sign-code algebra for the fully observed lower experiment

Equations (40)--(43) express the contextual-bandit target values in terms of
sign overlaps. The separated Boolean code gives a unique best target with a
uniform value gap. These algebraic facts are separate from constructing the
common reward-transition kernel and proving its observed information bound.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open Causalean.Stat.Minimax.Mixture.SignOverlap
open scoped BigOperators

/-- The action-one probability in equation (40). -/
-- @node: lowerBanditActionProb
noncomputable def lowerBanditActionProb (eta : ℝ) (bit : Bool) : ℝ :=
  (1 + eta * (if bit then 1 else -1)) / 2

/-- Averaging equation (41) under the target action rule gives its sign product. For
[the signal parameter](hyp:eta), [the rate parameter](hyp:gamma), [the codeword index](hyp:v),
and [the observed word](hyp:w), this establishes [the lower bandit action mean result](goal). -/
-- @node: lower_bandit_action_mean
lemma lower_bandit_action_mean (eta gamma : ℝ) (v w : Bool) :
    lowerBanditActionProb eta w * (1 / 2 + gamma * (if v then 1 else -1)) +
      (1 - lowerBanditActionProb eta w) * (1 / 2 - gamma * (if v then 1 else -1)) =
    1 / 2 + gamma * eta * (if v then 1 else -1) * (if w then 1 else -1) := by
  cases v <;> cases w <;> simp [lowerBanditActionProb] <;> ring

/-- The target action rule is a probability for every code bit. For
[the signal parameter](hyp:eta), [the eta0 assumption](hyp:heta0),
[the eta1 assumption](hyp:heta1), and [the bit](hyp:bit), this establishes
[the lower bandit action probability unit result](goal). -/
-- @node: lower_bandit_action_prob_unit
lemma lower_bandit_action_prob_unit (eta : ℝ) (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1) (bit : Bool) :
    lowerBanditActionProb eta bit ∈ Set.Icc (0 : ℝ) 1 := by
  cases bit <;> simp only [lowerBanditActionProb, Bool.false_eq_true,
    if_false, if_true, mul_neg_one, mul_one] <;> constructor <;> linarith

/-- Both action ratios against fair behavior satisfy the equation (40) bound. For
[the signal parameter](hyp:eta), [the action-overlap factor](hyp:L),
[the eta0 assumption](hyp:heta0), [the action-overlap factor assumption](hyp:hL), and
[the bit](hyp:bit), this establishes [the lower bandit action overlap result](goal). -/
-- @node: lower_bandit_action_overlap
lemma lower_bandit_action_overlap (eta L : ℝ) (heta0 : 0 ≤ eta)
    (hL : 1 + eta ≤ L) (bit : Bool) :
    lowerBanditActionProb eta bit / (1 / 2) ≤ L ∧
      (1 - lowerBanditActionProb eta bit) / (1 / 2) ≤ L := by
  cases bit <;> simp only [lowerBanditActionProb, Bool.false_eq_true,
    if_false, if_true, mul_neg_one, mul_one] <;> constructor <;> linarith

/-- Positive policy amplitude preserves the distinction between Boolean words. For
[the code dimension](hyp:d), [the signal parameter](hyp:eta), and
[the signal parameter assumption](hyp:heta), this establishes
[the lower bandit policy injective result](goal). -/
-- @node: lower_bandit_policy_injective
lemma lower_bandit_policy_injective {d : Nat} (eta : ℝ) (heta : 0 < eta) :
    Function.Injective (fun word : Fin d → Bool ↦
      fun i ↦ lowerBanditActionProb eta (word i)) := by
  intro v w h
  funext i
  have hi := congrFun h i
  cases hv : v i <;> cases hw : w i <;>
    simp [lowerBanditActionProb, hv, hw] at hi ⊢ <;> linarith

/-- The sign overlap counts agreements minus disagreements. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed word](hyp:w), this establishes
[the lower bandit inner sign hamming result](goal). -/
-- @node: lower_bandit_innerSign_hamming
lemma lower_bandit_innerSign_hamming {M d : Nat}
    (code : Fin M → Fin d → Bool) (v w : Fin M) :
    innerSign (code v) (code w) = (d : ℝ) - 2 * hammingDistance code v w := by
  classical
  have hpoint (i : Fin d) :
      (if code v i then (1 : ℝ) else -1) * (if code w i then (1 : ℝ) else -1) =
      1 - 2 * (if code v i ≠ code w i then (1 : ℝ) else 0) := by
    cases code v i <;> cases code w i <;> norm_num
  unfold innerSign hammingDistance
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.cast_card, Finset.sum_filter]
  simp

/-- The uniform-context target value in equation (42). -/
-- @node: lowerBanditCodeValue
noncomputable def lowerBanditCodeValue {d : Nat} (eta gamma : ℝ)
    (v w : Fin d → Bool) : ℝ :=
  1 / 2 + gamma * eta / d * innerSign v w

/-- Averaging the conditional action means yields equation (42). For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd),
[the signal parameter](hyp:eta), [the rate parameter](hyp:gamma), [the codeword index](hyp:v),
and [the observed word](hyp:w), this establishes
[the lower bandit code value mean result](goal). -/
-- @node: lower_bandit_code_value_mean
lemma lower_bandit_code_value_mean {d : Nat} (hd : 0 < d) (eta gamma : ℝ)
    (v w : Fin d → Bool) :
    (d : ℝ)⁻¹ * ∑ i : Fin d,
      (lowerBanditActionProb eta (w i) * (1 / 2 + gamma * (if v i then 1 else -1)) +
        (1 - lowerBanditActionProb eta (w i)) *
          (1 / 2 - gamma * (if v i then 1 else -1))) =
    lowerBanditCodeValue eta gamma v w := by
  simp_rw [lower_bandit_action_mean]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hs : (∑ i : Fin d, gamma * eta * (if v i then 1 else -1) *
      (if w i then 1 else -1)) = gamma * eta * innerSign v w := by
    unfold innerSign
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  unfold lowerBanditCodeValue
  field_simp

/-- A wrong codeword loses twice the normalized Hamming distance, equation (43). For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d), [the binary code](hyp:code),
[the signal parameter](hyp:eta), [the rate parameter](hyp:gamma), [the codeword index](hyp:v),
and [the observed word](hyp:w), this establishes [the lower bandit code value gap result](goal). -/
-- @node: lower_bandit_code_value_gap
lemma lower_bandit_code_value_gap {M d : Nat}
    (code : Fin M → Fin d → Bool) (eta gamma : ℝ) (v w : Fin M) :
    lowerBanditCodeValue eta gamma (code v) (code v) -
      lowerBanditCodeValue eta gamma (code v) (code w) =
    2 * gamma * eta / d * hammingDistance code v w := by
  unfold lowerBanditCodeValue
  rw [lower_bandit_innerSign_hamming, lower_bandit_innerSign_hamming]
  have hself : hammingDistance code v v = 0 := by simp [hammingDistance]
  rw [hself, Nat.cast_zero]
  ring

/-- The separated code supplies the uniform policy gap required by testing. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d), [the binary code](hyp:code),
[the binary code assumption](hyp:hcode), [the code dimension assumption](hyp:hd),
[the signal parameter](hyp:eta), [the rate parameter](hyp:gamma),
[the signal parameter assumption](hyp:heta), [the rate parameter assumption](hyp:hgamma),
[the codeword index](hyp:v), [the observed word](hyp:w), and [the vw assumption](hyp:hvw), this
establishes [the lower bandit separated gap result](goal). -/
-- @node: lower_bandit_separated_gap
lemma lower_bandit_separated_gap {M d : Nat}
    (code : Fin M → Fin d → Bool) (hcode : CodeSeparated code) (hd : 0 < d)
    (eta gamma : ℝ) (heta : 0 ≤ eta) (hgamma : 0 ≤ gamma)
    (v w : Fin M) (hvw : v ≠ w) :
    gamma * eta / 2 ≤ lowerBanditCodeValue eta gamma (code v) (code v) -
      lowerBanditCodeValue eta gamma (code v) (code w) := by
  rw [lower_bandit_code_value_gap]
  have hdist := hcode.2 v w hvw
  have hscale := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ 2 * gamma * eta / d by positivity)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    gamma * eta / 2 = (2 * gamma * eta / d) * ((d : ℝ) / 4) := by field_simp; ring
    _ ≤ _ := hscale

/-- The policy amplitude in equation (40) is positive and enforces overlap. For
[the action-overlap factor](hyp:L) and [the action-overlap factor assumption](hyp:hL), this
establishes [the lower bandit amplitude bounds result](goal). -/
-- @node: lower_bandit_amplitude_bounds
lemma lower_bandit_amplitude_bounds (L : ℝ) (hL : 1 < L) :
    0 < min ((L - 1) / 2) (1 / 2) ∧
      min ((L - 1) / 2) (1 / 2) ≤ 1 / 2 ∧
      1 + min ((L - 1) / 2) (1 / 2) ≤ L := by
  refine ⟨lt_min (by linarith) (by norm_num), min_le_right _ _, ?_⟩
  have := min_le_left ((L - 1) / 2) (1 / 2)
  linarith

/-- Equation (41) supplies a valid reward probability for both environment signs. For
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0),
[the gamma1 assumption](hyp:hgamma1), [the bit](hyp:bit), and [the action](hyp:action), this
establishes [the lower bandit reward probability unit result](goal). -/
-- @node: lower_bandit_reward_prob_unit
lemma lower_bandit_reward_prob_unit (gamma : ℝ) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1 / 16) (bit action : Bool) :
    1 / 2 + gamma * (if bit then 1 else -1) * (if action then 1 else -1)
      ∈ Set.Icc (0 : ℝ) 1 := by
  cases bit <;> cases action <;> simp <;> constructor <;> linarith

/-- The code gap is strictly positive, so its own word is the unique best target. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d), [the binary code](hyp:code),
[the binary code assumption](hyp:hcode), [the code dimension assumption](hyp:hd),
[the signal parameter](hyp:eta), [the rate parameter](hyp:gamma),
[the signal parameter assumption](hyp:heta), [the rate parameter assumption](hyp:hgamma),
[the codeword index](hyp:v), [the observed word](hyp:w), and [the vw assumption](hyp:hvw), this
establishes [the lower bandit code unique optimum result](goal). -/
-- @node: lower_bandit_code_unique_optimum
lemma lower_bandit_code_unique_optimum {M d : Nat}
    (code : Fin M → Fin d → Bool) (hcode : CodeSeparated code) (hd : 0 < d)
    (eta gamma : ℝ) (heta : 0 < eta) (hgamma : 0 < gamma)
    (v w : Fin M) (hvw : v ≠ w) :
    lowerBanditCodeValue eta gamma (code v) (code w) <
      lowerBanditCodeValue eta gamma (code v) (code v) := by
  have hgap := lower_bandit_separated_gap code hcode hd eta gamma heta.le hgamma.le v w hvw
  have hpos : 0 < gamma * eta / 2 := by positivity
  linarith

end CausalSmith.Stat.PomdpPolicyclassRegret
