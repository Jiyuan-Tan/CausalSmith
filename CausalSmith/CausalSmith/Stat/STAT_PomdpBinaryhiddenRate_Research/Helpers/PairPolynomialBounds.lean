module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Root-based polynomial stability estimates

Coefficient and evaluation bounds for a monic degree-six polynomial whose complex
roots lie in a disk of radius less than one, counted with algebraic multiplicity.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators

/-- Bounded complex roots control the sum of the seven real coefficients. [Under the listed formal conditions](hyp:hm,hd,hr), [the stated conclusion holds](goal).-/
-- @node: degreeSix_coeff_sum_le_of_roots_le
lemma degreeSix_coeff_sum_le_of_roots_le (p : Polynomial ℝ) (alpha : ℝ)
    (hm : p.Monic) (hd : p.natDegree = 6)
    (hr : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ alpha) :
    (∑ k : Fin 7, |p.coeff k.val|) ≤ (1 + alpha) ^ 6 := by
  have hc (k : Fin 7) : |p.coeff k.val| ≤
      alpha ^ (6 - k.val) * (Nat.choose 6 k.val : ℝ) := by
    have h := Polynomial.coeff_le_of_roots_le k.val hm
      (IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))) hr
    simpa [hd] using h
  calc
    _ ≤ ∑ k : Fin 7, alpha ^ (6 - k.val) * (Nat.choose 6 k.val : ℝ) :=
      Finset.sum_le_sum fun k _ => hc k
    _ = (1 + alpha) ^ 6 := by
      simp [Fin.sum_univ_succ, Nat.choose]
      ring

/-- A root disk below one gives a lower bound on a product of distances to one. [Under the listed formal conditions](hyp:hα,hr), [the stated conclusion holds](goal).-/
-- @node: roots_distance_prod_lower
lemma roots_distance_prod_lower (s : Multiset ℂ) (alpha : ℝ)
    (hα : alpha < 1) (hr : ∀ z ∈ s, ‖z‖ ≤ alpha) :
    (1 - alpha) ^ s.card ≤ ‖(s.map (fun z => 1 - z)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    have hz := hr z (by simp)
    have hs := ih (fun w hw => hr w (by simp [hw]))
    have hdist : 1 - alpha ≤ ‖(1 : ℂ) - z‖ := by
      have h := norm_sub_norm_le (1 : ℂ) z
      simp only [norm_one] at h
      linarith
    simpa [pow_succ, mul_comm] using
      mul_le_mul hdist hs (by positivity) (norm_nonneg _)

/-- The degree-six monic factor is bounded away from zero at one. [Under the listed formal conditions](hyp:hm,hd,hα,hr), [the stated conclusion holds](goal).-/
-- @node: degreeSix_eval_one_lower_of_roots_le
lemma degreeSix_eval_one_lower_of_roots_le (p : Polynomial ℝ) (alpha : ℝ)
    (hm : p.Monic) (hd : p.natDegree = 6) (hα : alpha < 1)
    (hr : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ alpha) :
    (1 - alpha) ^ 6 ≤ |p.eval 1| := by
  let q := p.map (algebraMap ℝ ℂ)
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hcard : q.roots.card = 6 := by
    rw [← hsplit.natDegree_eq_card_roots, hm.natDegree_map, hd]
  have h := roots_distance_prod_lower q.roots alpha hα hr
  rw [hcard, ← hsplit.eval_eq_prod_roots_of_monic (hm.map _) 1] at h
  simpa [q, Polynomial.eval_map] using h

/-- The two root estimates yield the sharp seven-coefficient stability ratio. [Under the listed formal conditions](hyp:hm,hd,hα,hr), [the stated conclusion holds](goal).-/
-- @node: degreeSix_coefficient_ratio_le_of_roots_le
lemma degreeSix_coefficient_ratio_le_of_roots_le (p : Polynomial ℝ) (alpha : ℝ)
    (hm : p.Monic) (hd : p.natDegree = 6) (hα : alpha < 1)
    (hr : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ alpha) :
    (∑ k : Fin 7, |p.coeff k.val|) / |p.eval 1| ≤ stabilityFactor alpha := by
  have hnum := degreeSix_coeff_sum_le_of_roots_le p alpha hm hd hr
  have hden := degreeSix_eval_one_lower_of_roots_le p alpha hm hd hα hr
  have hpos : 0 < (1 - alpha) ^ 6 := pow_pos (by linarith) _
  calc
    _ ≤ (1 + alpha) ^ 6 / (1 - alpha) ^ 6 :=
      div_le_div₀ (by positivity) hnum hpos hden
    _ = stabilityFactor alpha := by rw [stabilityFactor, div_pow]

end CausalSmith.Stat.PomdpBinaryhiddenRate
