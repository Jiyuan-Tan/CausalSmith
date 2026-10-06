module
public import Causalean.Tactic.Attr
public import Causalean.Tactic.CondexpLinearity
public import Causalean.Tactic.IndicatorSimps
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Tactic.SumAlgebraSimps
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic

/-!
# Finite product moment identities

Finite sums under normalized product weights factor into one-coordinate moments.
-/

public section

namespace Causalean.Mathlib.Algebra.BigOperators

/-- For [a finite coordinate type and finite state type](hyp:I,A), a [normalized
weight](hyp:w,hwsum), and a [one-cell statistic](hyp:X), the weighted mean of
the sum over the product space equals the number of coordinates times the
one-cell weighted mean. The result is [the product-space mean identity for the coordinate sum](goal). -/
lemma finiteProduct_sum_mean {I A : Type*}
    [Fintype I] [DecidableEq I] [Fintype A]
    (w X : A → ℝ) (hwsum : ∑ a : A, w a = 1) :
    (∑ u : I → A, (∏ i : I, w (u i)) * ∑ i : I, X (u i)) =
      (Fintype.card I : ℝ) * ∑ a : A, w a * X a := by
  have hmarg (j : I) :
      ∑ u : I → A, (∏ i : I, w (u i)) * X (u j) =
        ∑ a : A, w a * X a := by
    have hfactor (u : I → A) :
        (∏ i : I, w (u i)) * X (u j) =
          ∏ i : I, if i = j then w (u i) * X (u i) else w (u i) := by
      calc
        _ = (∏ i : I, w (u i)) *
            ∏ i : I, if i = j then X (u i) else 1 := by simp
        _ = ∏ i : I, w (u i) * (if i = j then X (u i) else 1) := by
          rw [Finset.prod_mul_distrib]
        _ = _ := by simp
    calc
      _ = ∑ u : I → A,
          ∏ i : I, if i = j then w (u i) * X (u i) else w (u i) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hfactor u
      _ = ∏ i : I,
          ∑ a : A, if i = j then w a * X a else w a := by
        exact (Fintype.prod_sum (fun i : I => fun a : A =>
          if i = j then w a * X a else w a)).symm
      _ = ∑ a : A, w a * X a := by
        simp [hwsum, Finset.prod_ite_eq']
  calc
    _ = ∑ i : I, ∑ u : I → A, (∏ j : I, w (u j)) * X (u i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _i : I, ∑ a : A, w a * X a := by
      apply Finset.sum_congr rfl
      intro i _
      exact hmarg i
    _ = _ := by simp


/-- For [a finite coordinate type and finite state type](hyp:I,A), a [normalized
weight](hyp:w,hwsum), and a [centered one-cell statistic](hyp:c,hcenter), the
weighted second moment of the coordinate sum equals the number of coordinates
times the one-cell weighted second moment. The result is [the product-space second-moment identity for the centered coordinate sum](goal). -/
lemma finiteProduct_centered_sum_sq {I A : Type*}
    [Fintype I] [DecidableEq I] [Fintype A]
    (w c : A → ℝ) (hwsum : ∑ a : A, w a = 1)
    (hcenter : ∑ a : A, w a * c a = 0) :
    (∑ u : I → A, (∏ i : I, w (u i)) * (∑ i : I, c (u i)) ^ 2) =
      (Fintype.card I : ℝ) * ∑ a : A, w a * c a ^ 2 := by
  have hpair (j k : I) (hjk : j ≠ k) :
      ∑ u : I → A, (∏ i : I, w (u i)) * c (u j) * c (u k) = 0 := by
    let f : I → A → ℝ := fun l a =>
      w a * (if l = j then c a else 1) * (if l = k then c a else 1)
    have hf (u : I → A) :
        (∏ i : I, w (u i)) * c (u j) * c (u k) =
          ∏ l : I, f l (u l) := by
      simp only [f, Finset.prod_mul_distrib]
      simp [Finset.prod_ite_eq', mul_assoc]
    calc
      _ = ∑ u : I → A, ∏ l : I, f l (u l) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hf u
      _ = ∏ l : I, ∑ a : A, f l a := by
        exact (Fintype.prod_sum f).symm
      _ = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [f, hjk, hcenter]
  have hdiag (j : I) :
      ∑ u : I → A, (∏ i : I, w (u i)) * c (u j) ^ 2 =
        ∑ a : A, w a * c a ^ 2 := by
    have hfactor (u : I → A) :
        (∏ i : I, w (u i)) * c (u j) ^ 2 =
          ∏ i : I, if i = j then w (u i) * c (u i) ^ 2 else w (u i) := by
      calc
        _ = (∏ i : I, w (u i)) *
            ∏ i : I, if i = j then c (u i) ^ 2 else 1 := by simp
        _ = ∏ i : I, w (u i) *
            (if i = j then c (u i) ^ 2 else 1) := by
          rw [Finset.prod_mul_distrib]
        _ = _ := by simp
    calc
      _ = ∑ u : I → A,
          ∏ i : I, if i = j then w (u i) * c (u i) ^ 2 else w (u i) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hfactor u
      _ = ∏ i : I,
          ∑ a : A, if i = j then w a * c a ^ 2 else w a := by
        exact (Fintype.prod_sum (fun i : I => fun a : A =>
          if i = j then w a * c a ^ 2 else w a)).symm
      _ = ∑ a : A, w a * c a ^ 2 := by
        simp [hwsum, Finset.prod_ite_eq']
  calc
    _ = ∑ j : I, ∑ k : I,
        ∑ u : I → A, (∏ i : I, w (u i)) * c (u j) * c (u k) := by
      simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ j : I, ∑ k : I,
        if k = j then (∑ a : A, w a * c a ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      split_ifs with h
      · subst k
        convert hdiag j using 1
        · apply Finset.sum_congr rfl
          intro u _
          ring
      · exact hpair j k (Ne.symm h)
    _ = _ := by simp

end Causalean.Mathlib.Algebra.BigOperators
