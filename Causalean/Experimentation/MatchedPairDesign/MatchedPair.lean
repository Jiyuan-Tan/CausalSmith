/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.Designs.Bernoulli
public import Mathlib.Tactic.NormNum

/-! # Matched-pair designs

Bai's fixed matched-pair design organizes units into pairs and treats exactly one of each pair's
two positions, selected by an independent fair coin. It is therefore a product across pairs, not
independent assignment across all units.

This file defines the pair-level coin, the product design, and its treatment indicator. The main
inclusion results give treatment probability `1/2`, perfect negative dependence within a pair,
and independence across pairs with joint treatment probability `1/4`. The file fixes the pairing;
it does not compare pairings or prove an optimal matching theorem.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace MatchedPairDesign

open DesignBased

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The [per-pair fair-coin randomization design](goal) assigns probability one half to each of
the two positions: one outcome selects the first position for treatment and the other selects the
second position. -/
noncomputable def pairCoinDesign : FiniteDesign Bool :=
  coinDesign ((1 : ℝ) / 2) (by norm_num) (by norm_num)

/-- For [a finite collection of pair labels with decidable identity](hyp:P), the
[matched-pair randomization design](goal) independently draws a fair coin for every pair and
treats the position selected by that coin, leaving the other position as control.  This is a
size-two stratified design with one treated unit in each pair rather than independent assignment
over all units. -/
noncomputable def matchedPairDesign : FiniteDesign (P → Bool) :=
  prodDesign (fun _ : P => pairCoinDesign)

/-- The matched-pair design is the product of the independent pair-level fair coins. -/
lemma matchedPairDesign_eq_prod_pairCoin :
    matchedPairDesign (P := P) = prodDesign (fun _ : P => pairCoinDesign) := rfl

/-- For [a pair label](hyp:P,p), [one of its two positions](hyp:b), and [an assignment selecting a
treated position in every pair](hyp:z), the [treatment indicator for that unit](goal) equals one
when the assignment selects that position and zero otherwise. -/
def mpTreatInd (p : P) (b : Bool) (z : P → Bool) : ℝ := if z p = b then 1 else 0

omit [Fintype P] [DecidableEq P] in
/-- **Within-pair exclusivity.** Exactly one position of each pair is treated: the two units'
indicators sum to one on every assignment. -/
lemma mpTreatInd_within (p : P) (z : P → Bool) :
    mpTreatInd p true z + mpTreatInd p false z = 1 := by
  unfold mpTreatInd
  cases z p <;> simp

/-- **First-order inclusion probability.** [Under the matched-pair design, the unit occupying
position `b` of pair `p` is treated with probability `1/2`](goal). -/
lemma matchedPairDesign_E_mpTreatInd (p : P) (b : Bool) :
    (matchedPairDesign (P := P)).E (mpTreatInd p b) = 1 / 2 := by
  change (prodDesign (fun _ : P => pairCoinDesign)).E
      (fun z => (fun c : Bool => if c = b then (1 : ℝ) else 0) (z p)) = 1 / 2
  rw [FiniteDesign.E_prod_apply (fun _ : P => pairCoinDesign) p
      (fun c : Bool => if c = b then (1 : ℝ) else 0)]
  unfold pairCoinDesign
  rw [coinDesign_E]
  cases b <;> norm_num

/-- **Within-pair negative dependence.** [Under the matched-pair design, the two units of pair `p`
are never treated together, so the expectation of the product of their treatment indicators is
zero](goal) — perfect negative dependence. -/
lemma matchedPairDesign_E_mpTreatInd_within (p : P) :
    (matchedPairDesign (P := P)).E (fun z => mpTreatInd p true z * mpTreatInd p false z) = 0 := by
  have hzero : ∀ z : P → Bool, mpTreatInd p true z * mpTreatInd p false z = 0 := by
    intro z
    unfold mpTreatInd
    cases z p <;> simp
  rw [(matchedPairDesign (P := P)).E_congr hzero]
  exact (matchedPairDesign (P := P)).E_const 0

/-- **Cross-pair independence.** For [pairs `p` and `p'` that are distinct](hyp:h), [the
probability that position `b` of `p` and position `b'` of `p'` are treated simultaneously equals
`¼`](goal) — units in distinct pairs are treated independently, and each position is treated with
probability `½`, so the joint probability factors as `½ · ½`. -/
lemma matchedPairDesign_E_mpTreatInd_cross (p p' : P) (h : p ≠ p') (b b' : Bool) :
    (matchedPairDesign (P := P)).E (fun z => mpTreatInd p b z * mpTreatInd p' b' z) = 1 / 4 := by
  change (prodDesign (fun _ : P => pairCoinDesign)).E
      (fun z => (fun c : Bool => if c = b then (1 : ℝ) else 0) (z p) *
        (fun c : Bool => if c = b' then (1 : ℝ) else 0) (z p')) = 1 / 4
  rw [FiniteDesign.E_prod_apply₂
      (fun _ : P => pairCoinDesign) h
      (fun c : Bool => if c = b then (1 : ℝ) else 0)
      (fun c : Bool => if c = b' then (1 : ℝ) else 0)]
  unfold pairCoinDesign
  rw [coinDesign_E, coinDesign_E]
  cases b <;> cases b' <;> norm_num

end MatchedPairDesign
end Experimentation
end Causalean
