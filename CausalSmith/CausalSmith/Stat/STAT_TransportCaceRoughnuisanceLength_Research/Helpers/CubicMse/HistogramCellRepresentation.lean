module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.IidBlockAverage

/-! # Histogram cell heights as iid block averages -/

public section

open Set
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:K,hK,l), [the stated result about midpoint mem cell holds](goal). -/

lemma midpoint_mem_cell {K : ℕ} (hK : 0 < K) (l : Fin K) : midpoint K l ∈ cell K l := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold midpoint cell
  split_ifs with hlast
  · constructor
    · apply (div_le_div_iff_of_pos_right hKr).2
      norm_num
    · apply (div_le_one hKr).2
      have hl : (l.val : ℝ) + 1 = K := by exact_mod_cast hlast
      linarith
  · constructor
    · apply (div_le_div_iff_of_pos_right hKr).2
      norm_num
    · apply (div_lt_div_iff_of_pos_right hKr).2
      norm_num
/-- Given [the supplied inputs](hyp:K,hK,l,r), [the stated result about midpoint mem cell iff holds](goal). -/

lemma midpoint_mem_cell_iff {K : ℕ} (hK : 0 < K) (l r : Fin K) :
    midpoint K l ∈ cell K r ↔ r = l := by
  constructor
  · intro hmem
    by_contra hne
    exact Set.disjoint_left.mp (cell_disjoint hK hne) hmem (midpoint_mem_cell hK l)
  · intro hrl
    simpa [hrl] using midpoint_mem_cell hK l
/-- Given [the supplied inputs](hyp:n,w,i,hi,r), [the stated result about source cell mark eq channel mark holds](goal). -/

lemma sourceCellMark_eq_channelMark {n : ℕ} (w : TwoSample n n) (i : Fin 7)
    (hi : i ≠ 0) (r : Fin n) : sourceCellMark i (w.1 r) = channelMark w i r := by
  fin_cases i <;> simp_all [sourceCellMark, channelMark, boolReal]
/-- Given [the supplied inputs](hyp:n,K,hn,hK,w,b,l), [the stated result about marked histogram midpoint target holds](goal). -/

lemma markedHistogram_midpoint_target {n K : ℕ} (hn : threshold ≤ n)
    (hK : 0 < K) (w : TwoSample n n) (b : Fin 4) (l : Fin K) :
    markedHistogram w 0 K b (midpoint K l) =
      iidBlockHeight K (blockIdx n b) (targetCellScore K l) w.2 := by
  classical
  unfold markedHistogram iidBlockHeight
  simp only [if_neg (Nat.not_lt_of_ge hn)]
  rw [Finset.sum_eq_single l]
  · rw [if_pos (midpoint_mem_cell hK l)]
    rw [block_card]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    simp [channelMark, channelX, sourceChannel, targetCellScore]
  · intro r _ hrl
    rw [if_neg]
    exact fun hmem => hrl (midpoint_mem_cell_iff hK l r |>.mp hmem)
  · exact fun hl => (hl (Finset.mem_univ l)).elim
/-- Given [the supplied inputs](hyp:n,K,hn,hK,w,i,hi,b,l), [the stated result about marked histogram midpoint source holds](goal). -/

lemma markedHistogram_midpoint_source {n K : ℕ} (hn : threshold ≤ n)
    (hK : 0 < K) (w : TwoSample n n) (i : Fin 7) (hi : i ≠ 0)
    (b : Fin 4) (l : Fin K) :
    markedHistogram w i K b (midpoint K l) =
      iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) w.1 := by
  classical
  unfold markedHistogram iidBlockHeight
  simp only [if_neg (Nat.not_lt_of_ge hn)]
  rw [Finset.sum_eq_single l]
  · rw [if_pos (midpoint_mem_cell hK l)]
    rw [block_card]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [← sourceCellMark_eq_channelMark w i hi r]
    have hsource : sourceChannel i = true := by simp [sourceChannel, hi]
    simp [channelX, hsource, sourceCellScore]
  · intro r _ hrl
    rw [if_neg]
    exact fun hmem => hrl (midpoint_mem_cell_iff hK l r |>.mp hmem)
  · exact fun hl => (hl (Finset.mem_univ l)).elim

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
