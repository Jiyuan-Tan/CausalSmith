module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorTuning

/-!
# Deterministic median witnesses

A majority of accurate block scores controls the subset-minimum median.
Consequently a median error supplies a half-size subset of bad blocks,
the deterministic input to the chronological union bound in equation (11).
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open MeasureTheory
open scoped BigOperators ENNReal

/-- The minimum over members of a finite subset is at most each member's score. For
[the second event](hyp:B), [the candidate score](hyp:score), [the index subset](hyp:S),
[the i](hyp:i), and [the i assumption](hyp:hi), this establishes
[the selector subset min bound result](goal). -/
-- @node: selector_subset_min_le
lemma selector_subset_min_le {B : Nat} (score : Fin B → ℝ)
    (S : Finset (Fin B)) (i : Fin B) (hi : i ∈ S) :
    (⨅ ell : S, score ell.1) ≤ score i := by
  exact ciInf_le (Finite.bddBelow_range (fun ell : S ↦ score ell.1)) ⟨i, hi⟩

/-- A nonempty subset of scores above a threshold has its minimum above it. For
[the second event](hyp:B), [the candidate score](hyp:score), [the index subset](hyp:S),
[the index subset assumption](hyp:hS), [the action](hyp:a), and [the action assumption](hyp:ha),
this establishes [the selector subset min ge result](goal). -/
-- @node: selector_subset_min_ge
lemma selector_subset_min_ge {B : Nat} (score : Fin B → ℝ)
    (S : Finset (Fin B)) (hS : S.Nonempty) (a : ℝ)
    (ha : ∀ i ∈ S, a ≤ score i) :
    a ≤ ⨅ ell : S, score ell.1 := by
  let : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  exact le_ciInf fun i ↦ ha i.1 i.2

/-- Two subsets each containing a majority of an odd list must intersect. For
[the second event](hyp:B), [the odd assumption](hyp:hodd), [the index subset](hyp:S),
[the g](hyp:G), [the index subset assumption](hyp:hS), and [the g assumption](hyp:hG), this
establishes [the selector majority intersects result](goal). -/
-- @node: selector_majority_intersects
lemma selector_majority_intersects {B : Nat} (hodd : B % 2 = 1)
    (S G : Finset (Fin B)) (hS : S.card = (B + 1) / 2)
    (hG : (B + 1) / 2 ≤ G.card) : (S ∩ G).Nonempty := by
  apply Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ S) (Finset.subset_univ G)
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- A majority of scores in an interval puts the subset-minimum median in that interval. For
[the second event](hyp:B), [the odd assumption](hyp:hodd), [the candidate score](hyp:score),
[the g](hyp:G), [the g assumption](hyp:hG), [the action](hyp:a), [the behavior policy](hyp:b),
and [the good assumption](hyp:hgood), this establishes
[the selector median interval result](goal). -/
-- @node: selector_median_interval
lemma selector_median_interval {B : Nat} (hodd : B % 2 = 1)
    (score : Fin B → ℝ) (G : Finset (Fin B))
    (hG : (B + 1) / 2 ≤ G.card) (a b : ℝ)
    (hgood : ∀ i ∈ G, score i ∈ Set.Icc a b) :
    (⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1) ∈ Set.Icc a b := by
  classical
  obtain ⟨S, hSG, hS⟩ := Finset.exists_subset_card_eq hG
  let s : {S : Finset (Fin B) // S.card = (B + 1) / 2} := ⟨S, hS⟩
  let : Nonempty {S : Finset (Fin B) // S.card = (B + 1) / 2} := ⟨s⟩
  have hSpos : S.Nonempty := Finset.card_pos.mp (by omega)
  constructor
  · exact (selector_subset_min_ge score S hSpos a
      (fun i hi ↦ (hgood i (hSG hi)).1)).trans
      (le_ciSup (Finite.bddAbove_range (fun R :
        {R : Finset (Fin B) // R.card = (B + 1) / 2} ↦
          ⨅ ell : R.1, score ell.1)) s)
  · apply ciSup_le
    intro R
    obtain ⟨i, hi⟩ := selector_majority_intersects hodd R.1 G R.2 hG
    obtain ⟨hiR, hiG⟩ := Finset.mem_inter.mp hi
    exact (selector_subset_min_le score R.1 i hiR).trans (hgood i hiG).2

/-- A large median error forces at least half the odd list to have large coordinate error. For
[the second event](hyp:B), [the odd assumption](hyp:hodd), [the candidate score](hyp:score),
[the parameter](hyp:θ), [the δ](hyp:δ), and [the err assumption](hyp:herr), this establishes
[the selector median bad card result](goal). -/
-- @node: selector_median_bad_card
lemma selector_median_bad_card {B : Nat} (hodd : B % 2 = 1)
    (score : Fin B → ℝ) (θ δ : ℝ)
    (herr : δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1) - θ|) :
    (B + 1) / 2 ≤ (Finset.univ.filter fun i ↦ δ < |score i - θ|).card := by
  classical
  by_contra hsmall
  let G := Finset.univ.filter fun i ↦ ¬ δ < |score i - θ|
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ (α := Fin B)) (p := fun i ↦ δ < |score i - θ|)
  have hG : (B + 1) / 2 ≤ G.card := by
    dsimp only [G]
    simp only [Finset.card_univ, Fintype.card_fin] at hpartition
    omega
  have hmed := selector_median_interval hodd score G hG (θ - δ) (θ + δ) (by
    intro i hi
    have he := le_of_not_gt (Finset.mem_filter.mp hi).2
    obtain ⟨hl, hu⟩ := abs_le.mp he
    exact ⟨by linarith, by linarith⟩)
  have hle : |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1) - θ| ≤ δ :=
    abs_le.mpr ⟨by linarith [hmed.1], by linarith [hmed.2]⟩
  exact (not_lt_of_ge hle) herr

/-- A large median error supplies a specified half-size subset consisting entirely of bad
blocks. For [the second event](hyp:B), [the odd assumption](hyp:hodd),
[the candidate score](hyp:score), [the parameter](hyp:θ), [the δ](hyp:δ), and
[the err assumption](hyp:herr), this establishes [the selector median bad witness result](goal). -/
-- @node: selector_median_bad_witness
lemma selector_median_bad_witness {B : Nat} (hodd : B % 2 = 1)
    (score : Fin B → ℝ) (θ δ : ℝ)
    (herr : δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1) - θ|) :
    ∃ S : Finset (Fin B), S.card = (B + 1) / 2 ∧
      ∀ i ∈ S, δ < |score i - θ| := by
  classical
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq
    (selector_median_bad_card hodd score θ δ herr)
  exact ⟨S, hcard, fun i hi ↦ (Finset.mem_filter.mp (hsub hi)).2⟩

/-- The observable block median has the bad-subset witness used in equation (11). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the target policy](hyp:e), [the observed word](hyp:w), [the parameter](hyp:θ), [the δ](hyp:δ),
and [the err assumption](hyp:herr), this establishes
[the selector block median bad witness result](goal). -/
-- @node: selector_blockMedian_bad_witness
lemma selector_blockMedian_bad_witness (T M nX k : Nat) (b e : Policy nX)
    (w : ObsView T nX) (θ δ : ℝ)
    (herr : δ < |blockMedian T M nX k b e w - θ|) :
    ∃ S : Finset (Fin (numBlocks M)), S.card = (numBlocks M + 1) / 2 ∧
      ∀ ell ∈ S, δ < |blockScore T M nX k b e ell w - θ| := by
  exact selector_median_bad_witness (selector_numBlocks_odd M)
    (fun ell ↦ blockScore T M nX k b e ell w) θ δ herr

/-- The median tail is bounded by the sum of joint bad events over half-size subsets. This union
bound requires no independence and no measurability side condition. For
[the sample space](hyp:Ω), [the measure](hyp:μ), [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the candidate score](hyp:score), [the parameter](hyp:θ), and
[the δ](hyp:δ), this establishes [the selector median tail union result](goal). -/
-- @node: selector_median_tail_union
lemma selector_median_tail_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : Nat} (hodd : B % 2 = 1)
    (score : Fin B → Ω → ℝ) (θ δ : ℝ) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤
      ∑ S ∈ Finset.univ.powersetCard ((B + 1) / 2),
        μ {w | ∀ i ∈ S, δ < |score i w - θ|} := by
  classical
  apply le_trans (measure_mono ?_) (measure_biUnion_finset_le _ _)
  intro w hw
  obtain ⟨S, hS, hbad⟩ := selector_median_bad_witness hodd (fun i ↦ score i w) θ δ hw
  exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
    ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩, hbad⟩⟩

/-- Any bound on the specified joint bad events gives the corresponding binomial median bound.
The chronological argument must supply these joint-event bounds separately. For
[the sample space](hyp:Ω), [the measure](hyp:μ), [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the candidate score](hyp:score), [the parameter](hyp:θ),
[the δ](hyp:δ), [the policy](hyp:p), and [the joint assumption](hyp:hjoint), this establishes
[the selector median tail choose result](goal). -/
-- @node: selector_median_tail_choose
lemma selector_median_tail_choose {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : Nat} (hodd : B % 2 = 1)
    (score : Fin B → Ω → ℝ) (θ δ : ℝ) (p : ℝ≥0∞)
    (hjoint : ∀ S : Finset (Fin B), S.card = (B + 1) / 2 →
      μ {w | ∀ i ∈ S, δ < |score i w - θ|} ≤ p ^ ((B + 1) / 2)) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤
      (B.choose ((B + 1) / 2) : ℝ≥0∞) * p ^ ((B + 1) / 2) := by
  classical
  calc
    _ ≤ ∑ S ∈ Finset.univ.powersetCard ((B + 1) / 2),
        μ {w | ∀ i ∈ S, δ < |score i w - θ|} :=
      selector_median_tail_union μ hodd score θ δ
    _ ≤ ∑ S ∈ Finset.univ.powersetCard ((B + 1) / 2), p ^ ((B + 1) / 2) :=
      Finset.sum_le_sum fun S hS ↦ hjoint S (Finset.mem_powersetCard.mp hS).2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

/-- There are at most two to the number of blocks half-size subsets. For
[the second event](hyp:B), this establishes [the selector half subsets card bound result](goal). -/
-- @node: selector_half_subsets_card_le
lemma selector_half_subsets_card_le (B : Nat) :
    B.choose ((B + 1) / 2) ≤ 2 ^ B := by
  have hsub : (Finset.univ (α := Fin B)).powersetCard ((B + 1) / 2) ⊆
      Finset.univ.powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1
  simpa only [Finset.card_powersetCard, Finset.card_powerset, Finset.card_univ,
    Fintype.card_fin] using Finset.card_le_card hsub

/-- The combinatorial part of the dependent-block median bound is exponential in block count.
For [the sample space](hyp:Ω), [the measure](hyp:μ), [the second event](hyp:B),
[the odd assumption](hyp:hodd), [the candidate score](hyp:score), [the parameter](hyp:θ),
[the δ](hyp:δ), [the policy](hyp:p), and [the joint assumption](hyp:hjoint), this establishes
[the selector median tail two pow result](goal). -/
-- @node: selector_median_tail_two_pow
lemma selector_median_tail_two_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : Nat} (hodd : B % 2 = 1)
    (score : Fin B → Ω → ℝ) (θ δ : ℝ) (p : ℝ≥0∞)
    (hjoint : ∀ S : Finset (Fin B), S.card = (B + 1) / 2 →
      μ {w | ∀ i ∈ S, δ < |score i w - θ|} ≤ p ^ ((B + 1) / 2)) :
    μ {w | δ < |(⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
      ⨅ ell : S.1, score ell.1 w) - θ|} ≤
      (2 : ℝ≥0∞) ^ B * p ^ ((B + 1) / 2) := by
  apply (selector_median_tail_choose μ hodd score θ δ p hjoint).trans
  gcongr
  exact_mod_cast selector_half_subsets_card_le B

/-- The actual observable block median obeys the finite union bound over bad block subsets. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the target policy](hyp:e), [the measure](hyp:μ), [the parameter](hyp:θ), and [the δ](hyp:δ),
this establishes [the selector block median tail union result](goal). -/
-- @node: selector_blockMedian_tail_union
lemma selector_blockMedian_tail_union (T M nX k : Nat) (b e : Policy nX)
    (μ : Measure (ObsView T nX)) (θ δ : ℝ) :
    μ {w | δ < |blockMedian T M nX k b e w - θ|} ≤
      ∑ S ∈ Finset.univ.powersetCard ((numBlocks M + 1) / 2),
        μ {w | ∀ ell ∈ S, δ < |blockScore T M nX k b e ell w - θ|} := by
  exact selector_median_tail_union μ (selector_numBlocks_odd M)
    (blockScore T M nX k b e) θ δ

end CausalSmith.Stat.PomdpPolicyclassRegret
