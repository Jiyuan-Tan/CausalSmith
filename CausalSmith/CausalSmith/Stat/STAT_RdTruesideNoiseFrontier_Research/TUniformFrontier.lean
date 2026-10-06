module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.FrontierComparison
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.FrontierSequences

/-!
# True-side Gaussian measurement-error endpoint frontier

Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Complete theorem conclusion: constants are outside the sample-size and noise binders. Given [the displayed inputs and assumptions](hyp:β), [this definition specifies the stated object](goal). -/
def UniformFrontierConclusion (β : ℝ) : Prop :=
  (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
    UniqueRateRoot β n σ ∧ MatchedFrontier β n σ c C ∧ FrontierBranches β n σ c C) ∧
  FrontierSequences β ∧ BetaOneFrontier
/-- A comparison with a nonnegative target survives decreasing its lower constant
and increasing its positive upper constant. Given [the displayed inputs and assumptions](hyp:x,y,c,C,c',C',h,hy,hC,hc,hC'), [the stated mathematical conclusion holds](goal). -/
lemma frontier_comparison_weaken {x y c C c' C' : ℝ}
    (h : c * x ≤ y ∧ y ≤ C * x) (hy : 0 ≤ y) (hC : 0 < C)
    (hc : c' ≤ c) (hC' : C ≤ C') : c' * x ≤ y ∧ y ≤ C' * x := by
  have hx : 0 ≤ x := by
    by_contra! hx
    have := mul_neg_of_pos_of_neg hC hx
    linarith [h.2]
  exact ⟨(mul_le_mul_of_nonneg_right hc hx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hC' hx)⟩

/-- The minimax chains permit a common smaller lower and larger upper constant. Given [the displayed inputs and assumptions](hyp:β,σ,c,C,c',C',n,h,hr,hc,hC), [the stated mathematical conclusion holds](goal). -/
lemma matched_frontier_weaken {β σ c C c' C' : ℝ} {n : ℕ}
    (h : MatchedFrontier β n σ c C) (hr : 0 ≤ frontierRate β n σ)
    (hc : c' ≤ c) (hC : C ≤ C') : MatchedFrontier β n σ c' C' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨(mul_le_mul_of_nonneg_right hc hr).trans h1, h2, h3,
    h4.trans (mul_le_mul_of_nonneg_right hC hr),
    (mul_le_mul_of_nonneg_right hc hr).trans h5, h6, h7,
    h8.trans (mul_le_mul_of_nonneg_right hC hr), h9⟩

/-- Exact branches and interfaces survive a common widening of their comparison constants. Given [the displayed inputs and assumptions](hyp:β,σ,c,C,c',C',n,h,hh,hσ,hC,hc,hC'), [the stated mathematical conclusion holds](goal). -/
lemma frontier_branches_weaken {β σ c C c' C' : ℝ} {n : ℕ}
    (h : FrontierBranches β n σ c C) (hh : 0 ≤ rateResolution β n σ)
    (hσ : 0 ≤ σ) (hC : 0 < C) (hc : c' ≤ c) (hC' : C ≤ C') :
    FrontierBranches β n σ c' C' := by
  rcases h with ⟨hd, hn, hi, he⟩
  refine ⟨hd, ?_, hi, he⟩
  intro hnoisy
  rcases hn hnoisy with ⟨h0, hs, hiff, hm, hk⟩
  refine ⟨h0, hs, hiff, ?_, ?_⟩
  · intro hmid
    rcases hm hmid with ⟨z, hz, hzσ, heq, hres, huniq, hlo, hhi⟩
    obtain ⟨hlo', hhi'⟩ := frontier_comparison_weaken ⟨hlo, hhi⟩ hh hC hc hC'
    exact ⟨z, hz, hzσ, heq, hres, huniq, hlo', hhi'⟩
  · intro hcompact
    rcases hk hcompact with ⟨τ, hτ, heq, hres, huniq, hlo, hhi, hrlo, hrhi⟩
    have hτ0 : 0 ≤ τ := (Real.rpow_nonneg hσ _).trans hτ.le
    have hr0 : 0 ≤ frontierRate β n σ := Real.rpow_nonneg hh _
    obtain ⟨hlo', hhi'⟩ := frontier_comparison_weaken ⟨hlo, hhi⟩ hτ0 hC hc hC'
    obtain ⟨hrlo', hrhi'⟩ := frontier_comparison_weaken ⟨hrlo, hrhi⟩ hr0 hC hc hC'
    exact ⟨τ, hτ, heq, hres, huniq, hlo', hhi', hrlo', hrhi'⟩

/-- All-sample, all-noise endpoint frontier, with exhaustive branches, interfaces and sequence comparisons. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
-- @node: thm:uniform-frontier
theorem uniform_frontier (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    UniformFrontierConclusion β := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  let hermite_of_gate : ClassicalHermiteFacts := classicalHermiteFacts
  obtain ⟨c₁, C₁, hc₁, hC₁, hmatched⟩ :=
    matched_frontier legendre_of_gate hermite_of_gate β hβ
  obtain ⟨c₂, C₂, hc₂, hC₂, hbranches⟩ := frontier_branches β hβ
  refine ⟨⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂,
    lt_max_of_lt_left hC₁, ?_⟩, frontier_sequences β hβ, beta_one_frontier⟩
  intro n hn σ hσ
  have hroot := unique_rate_root β n σ hβ hn hσ
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hh : 0 ≤ rateResolution β n σ :=
    (le_of_lt (Real.rpow_pos_of_pos hn0 _)).trans hroot.1.1
  refine ⟨hroot, matched_frontier_weaken (hmatched n hn σ hσ)
    (Real.rpow_nonneg hh _) (min_le_left _ _) (le_max_left _ _), ?_⟩
  exact frontier_branches_weaken (hbranches n hn σ hσ) hh hσ.1 hC₂
    (min_le_right _ _) (le_max_right _ _)

end CausalSmith.Stat.RdTruesideNoiseFrontier
