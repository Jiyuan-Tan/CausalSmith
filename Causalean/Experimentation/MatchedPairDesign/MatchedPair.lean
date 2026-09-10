/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bai (2022): the matched-pair design

This file formalizes the fixed-pair matched-pair randomization design from Bai (2022), "Optimality
of Matched-Pair Designs in Randomized Controlled Trials" (American Economic Review).  Units are
organized into pairs indexed by `P`; within each pair the two members occupy the two positions
`Bool`, and the experiment treats exactly one position per pair, chosen by an independent fair coin.
This is a product of pair-level fair-coin designs, read so that the coin selects the treated
position.  It is not independent assignment over the `2|P|` units: within each size-two stratum
exactly one unit is treated.

This file records the matched-pair design and its **inclusion structure**: each unit is treated with
probability `½`; the two units of a pair are *perfectly negatively dependent* (exactly one is
treated); and units in different pairs are treated independently.  It does not compare alternative
pairings or prove an optimal matching theorem.
-/

import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Matched-pair designs

Matched-pair designs organize units into pairs indexed by `P`, with the two members of each pair
represented by positions `Bool`.  The assignment `z p` is a pair-level fair coin selecting the
treated position, so this is not independent assignment over the `2|P|` units: each size-two stratum
treats exactly one unit.

This file defines the fair coin `pairCoinDesign`, the product design `matchedPairDesign`, and the
treatment indicator `mpTreatInd`.  The main inclusion results prove within-pair exclusivity,
first-order inclusion probability `1/2`, perfect within-pair negative dependence, and cross-pair
independence with joint probability `1/4`.
-/

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
