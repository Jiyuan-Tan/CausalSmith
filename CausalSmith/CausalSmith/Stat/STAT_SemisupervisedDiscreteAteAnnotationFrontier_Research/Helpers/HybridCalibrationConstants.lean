module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.Estimator
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Existence and readback facts for the paper's least calibration constants. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

/-- The dyadic search set is inhabited for every admissible overlap.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma dyadicIndex_set_nonempty {eps : Real} (heps : 0 < eps)
    (heps2 : eps < 1 / 2) :
    Set.Nonempty {j : Nat | 1 ≤ j ∧ (2 : Real) ^ (-(j : Int)) ≤ eps} := by
  obtain ⟨j, hj, _⟩ := exists_nat_pow_near_of_lt_one heps (by linarith)
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 : Real) / 2 < 1)
  refine ⟨j + 1, by omega, ?_⟩
  have heq : (2 : Real) ^ (-((j + 1 : Nat) : Int)) =
      ((1 : Real) / 2) ^ (j + 1) := by
    rw [zpow_neg, zpow_natCast, one_div_pow]
    simp [one_div]
  rw [heq]
  exact hj.le

/-- The least dyadic index satisfies its defining inequalities.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma dyadicIndex_spec {eps : Real} (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    1 ≤ dyadicIndex eps ∧ barEps eps ≤ eps := by
  simpa [dyadicIndex, barEps] using
    Nat.sInf_mem (dyadicIndex_set_nonempty heps heps2)
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma barEps_pos (eps : Real) : 0 < barEps eps := by
  unfold barEps
  positivity

/-- The integer search defining `Hconst` is inhabited.  [the stated conditions](hyp:heps) [the stated conclusion](goal). -/
lemma Hconst_set_nonempty {eps : Real} (heps : 0 < eps) :
    Set.Nonempty {H : Nat | 4 ≤ H ∧
      15 + 24 / cCirc ≤ (H : Real) / 4 ∧
      672 ≤ (H : Real) * cCirc * barEps eps ∧
      24 ≤ (H : Real) * cCirc * barEps eps} := by
  let R : Real := max 4 (max (4 * (15 + 24 / cCirc))
    (max (672 / (cCirc * barEps eps)) (24 / (cCirc * barEps eps))))
  obtain ⟨H, hH⟩ := exists_nat_ge R
  refine ⟨H, ?_⟩
  have hc : 0 < cCirc := by norm_num [cCirc]
  have hb : 0 < barEps eps := barEps_pos eps
  have h4 : (4 : Real) ≤ H := (le_max_left _ _).trans hH
  have hfirst : 4 * (15 + 24 / cCirc) ≤ (H : Real) :=
    (le_max_left _ _).trans (le_max_right 4 _ |>.trans hH)
  have h672 : 672 / (cCirc * barEps eps) ≤ (H : Real) :=
    (le_max_left _ _).trans
      (le_max_right (4 * (15 + 24 / cCirc)) _ |>.trans
        (le_max_right 4 _ |>.trans hH))
  have h24 : 24 / (cCirc * barEps eps) ≤ (H : Real) :=
    (le_max_right _ _).trans
      (le_max_right (4 * (15 + 24 / cCirc)) _ |>.trans
        (le_max_right 4 _ |>.trans hH))
  constructor
  · exact_mod_cast h4
  constructor
  · linarith
  constructor
  · simpa [mul_assoc] using (div_le_iff₀ (mul_pos hc hb)).mp h672
  · simpa [mul_assoc] using (div_le_iff₀ (mul_pos hc hb)).mp h24

/-- All four numerical properties can be read back from the least integer.  [the stated conditions](hyp:heps) [the stated conclusion](goal). -/
lemma Hconst_spec {eps : Real} (heps : 0 < eps) :
    4 ≤ Hconst eps ∧
      15 + 24 / cCirc ≤ (Hconst eps : Real) / 4 ∧
      672 ≤ (Hconst eps : Real) * cCirc * barEps eps ∧
      24 ≤ (Hconst eps : Real) * cCirc * barEps eps := by
  simpa [Hconst] using Nat.sInf_mem (Hconst_set_nonempty heps)

/-- [Every sample size](hyp:n) has [polynomial degree proxy at least two](goal). -/
@[simp] lemma Ldeg_ge_two (n : Nat) : 2 ≤ Ldeg n := by
  simp [Ldeg]

/-- Positivity facts needed by every probabilistic leaf follow directly from
the finite calibration predicate.  [the stated conditions](hyp:hcal) [the stated conclusion](goal). -/
lemma calibrationPredicate_positive_parameters {n m : Nat} {eps : Real}
    (hcal : calibrationPredicate n m eps) :
    let bs := blockSizes n m
    let N : Nat := n + m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let B := Bscale n m eps
    0 < u ∧ 0 < tp ∧ 0 < t ∧ 0 < B := by
  dsimp only
  simp only [calibrationPredicate] at hcal
  rcases hcal with ⟨hn, hu0, _hu1, htp0, _htp1, ht0, _ht1,
    _hr0, _hr1, _hL, htpB, _hLB, _hm4, _hm6, _htail1, _htail2, _htail3⟩
  have hnR : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hNR : (0 : Real) < n + m := by positivity
  have hu : 0 < ((blockSizes n m).M0 : Real) / 8 := by
    have : 0 < (((blockSizes n m).M0 : Real) / 8) / n :=
      lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 32) hu0
    rcases (div_pos_iff.mp this) with h | h
    · exact h.1
    · linarith
  have htp : 0 < (((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 := by
    have : 0 < ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8) /
        (n + m : Nat) := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 32) htp0
    rcases (div_pos_iff.mp this) with h | h
    · exact h.1
    · linarith
  have ht : 0 < (((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8 := by
    have : 0 < ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) /
        (n + m : Nat) := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 32) ht0
    rcases (div_pos_iff.mp this) with h | h
    · exact h.1
    · linarith
  have hB : 0 < Bscale n m eps := by
    have : 0 <
        ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8) *
          Bscale n m eps := lt_of_lt_of_le (by norm_num : (0 : Real) < 8) htpB
    rcases (mul_pos_iff.mp this) with h | h
    · exact h.2
    · linarith
  exact ⟨hu, htp, ht, hB⟩

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
