module

public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.THonestUpperFullElbow
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.THonestLowerFullElbow

/-! # Sharp no-logarithm equal-sample length frontier -/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: thm:sharp-length-frontier-full-elbow
/-- Given [the supplied inputs](hyp:α,c_f,C_f,L,hα,hf,hF,hL), [the stated result about sharp length frontier full elbow holds](goal). -/
theorem sharp_length_frontier_full_elbow (α c_f C_f L : ℝ)
    (hα : 0 < α ∧ α < 1) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < C0 ∧
      (∀ n : ℕ, 0 < n →
        scoreInterval α c_f C_f L ∈ HonestIntervals α c_f C_f L n) ∧
      (∀ n : ℕ, threshold ≤ n →
        ∀ a : ℝ, 0 < a → a ≤ 1 / 4 → -- @realizes a(domain (0,1/4])
          c0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) ≤
            lengthFrontier α c_f C_f L a n ∧
          lengthFrontier α c_f C_f L a n ≤
            C0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a)) ∧
      (∀ n : ℕ, threshold ≤ n →
        ∀ P : TransportLaw, ModelClass c_f C_f L P n →
          expectedLength P n n (scoreInterval α c_f C_f L) ≤
            C0 * min 1
              ((n : ℝ) ^ (-(1 / 3 : ℝ)) / firstStage P)) := by
  obtain ⟨hHonest, C0, hC0, hExpected, hUpper⟩ :=
    honest_upper_full_elbow α c_f C_f L hα hf hF hL
  obtain ⟨cLower, hcLower, hLower⟩ :=
    honest_lower_full_elbow α c_f C_f L hα hf hF hL
  refine ⟨min cLower (C0 / 2), C0, ?_, ?_, hHonest, ?_, hExpected⟩
  · exact lt_min hcLower (by linarith)
  · have hHalf : min cLower (C0 / 2) ≤ C0 / 2 := min_le_right _ _
    linarith
  · intro n hn a ha haBound
    have hx : 0 ≤ min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) := by positivity
    constructor
    · calc
        min cLower (C0 / 2) * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) ≤
            cLower * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hx
        _ ≤ lengthFrontier α c_f C_f L a n :=
          (hLower n hn a ha haBound).2
    · exact hUpper n hn a ha haBound

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
