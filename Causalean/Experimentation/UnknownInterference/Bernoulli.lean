/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.Designs.Bernoulli
public import Causalean.Experimentation.UnknownInterference.Basic

/-! # Bernoulli design under unknown interference

Independent Bernoulli assignment supplies the product-design independence used for
Sävje-Aronow-Hudgens unknown-interference results.

Each unit is treated by an independent coin with its own probability. Consequently, one unit's
assignment is independent of all other assignment coordinates, and its treatment indicator has
expectation equal to its treatment probability. This file provides deprecated compatibility names
for the canonical design and these one-coordinate marginal identities. New code should use the
corresponding declarations in `DesignBased` directly.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The legacy unknown-interference spelling of the [canonical Bernoulli randomization
design](goal) for [unit-specific probabilities](hyp:p) [between zero and one](hyp:hp0,hp1). -/
@[deprecated DesignBased.bernoulliDesign (since := "2026-09-19")]
noncomputable abbrev bernoulliDesign
    (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) : FiniteDesign (U → Bool) :=
  DesignBased.bernoulliDesign p hp0 hp1

/-- Under [independent Bernoulli assignment for a finite unit population](hyp:U) with
[unit-specific treatment probabilities](hyp:p) [between zero and one](hyp:hp0,hp1), [the expected
value of any transformation](hyp:g) of [one unit's assignment](hyp:i) [equals its expectation under
that unit's Bernoulli coin](goal). -/
@[deprecated DesignBased.bernoulliDesign_E_eval (since := "2026-09-19")]
lemma bernoulliDesign_E_eval (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : U) (g : Bool → ℝ) :
    (bernoulliDesign p hp0 hp1).E (fun z => g (z i))
      = (coinDesign (p i) (hp0 i) (hp1 i)).E g :=
  DesignBased.bernoulliDesign_E_eval p hp0 hp1 i g

/-- The legacy unknown-interference wrapper for the canonical treatment-indicator expectation. -/
@[deprecated DesignBased.bernoulliDesign_E_treat (since := "2026-09-19")]
lemma bernoulliDesign_E_treat (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (fun z => if z i then (1 : ℝ) else 0) = p i := by
  exact DesignBased.bernoulliDesign_E_treat p hp0 hp1 i

/-- The legacy unknown-interference wrapper for the canonical control-indicator expectation. -/
@[deprecated DesignBased.bernoulliDesign_E_ctrl (since := "2026-09-19")]
lemma bernoulliDesign_E_ctrl (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (fun z => if z i then (0 : ℝ) else 1) = 1 - p i := by
  exact DesignBased.bernoulliDesign_E_ctrl p hp0 hp1 i

end UnknownInterference
end Experimentation
end Causalean
