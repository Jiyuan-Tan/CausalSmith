/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Basic

/-!
# Finite raw-moment equality transfers to finite cumulant equality

The set-partition formula for the cumulant of order `k` only uses moments whose
orders are at most `k`.  This module packages that finite-dependence fact and its
measure-theoretic consequence.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory

/-- When [two abstract moment sequences agree through a cutoff](hyp:hm) and [the requested
cumulant order lies below that cutoff](hyp:hk), [their combinatorial cumulants at that order
agree](goal). -/
theorem cumFromMom_congr_up_to {m₁ m₂ : ℕ → ℝ} {K k : ℕ}
    (hm : ∀ j, j ≤ K → m₁ j = m₂ j) (hk : k ≤ K) :
    cumFromMom k m₁ = cumFromMom k m₂ := by
  unfold cumFromMom
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  apply hm
  exact (Finset.card_le_card (π.le hB)).trans (by simpa using hk)

/-- Given [two real measures](hyp:μ,ν), [a finite cutoff](hyp:K), and [equality of their raw
moments through that cutoff](hyp:hm), [the source cumulants of the identity statistic agree at
every order through the cutoff](goal). -/
theorem sourceCumulant_eq_of_rawMoment_eq_up_to
    (μ ν : Measure ℝ) (K : ℕ)
    (hm : ∀ j, j ≤ K → rawMoment μ j = rawMoment ν j) :
    ∀ k, k ≤ K →
      sourceCumulant μ (id : ℝ → ℝ) k = sourceCumulant ν (id : ℝ → ℝ) k := by
  intro k hk
  rw [sourceCumulant_eq_cumFromMom, sourceCumulant_eq_cumFromMom]
  exact cumFromMom_congr_up_to hm hk

end Causalean.Stat.MomentProblems
