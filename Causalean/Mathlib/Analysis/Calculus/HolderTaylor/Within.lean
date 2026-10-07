/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-!
# Hölder–Taylor remainder for a function smooth only on an interval

`holder_taylor_remainder_within` is the counterpart of `holder_taylor_remainder` for a function
that is `p` times continuously differentiable on a closed interval only, with `p`-th
within-interval derivative Hölder of order `β − p`: its within-interval Taylor polynomial at a
point `t` of the interval has error at most `(M / p!) |a − t|^β` at every point `a` of the
interval. The proof applies the Lagrange form of the remainder on the segment between `t` and
`a` and identifies the derivatives within that segment with those within the interval.
-/

public section

namespace Causalean.Mathlib.Analysis.HolderTaylor

open scoped BigOperators

/-- Let [a set `s` be contained in a set `t`](hyp:st), where [`s`](hyp:hs) and [`t`](hyp:ht) are
sets within which derivatives are unique, and let [`f` be `n` times continuously differentiable
on `t`](hyp:h). Then at [every point of `s`](hyp:hx), [the `n`-th derivative of `f` taken
within `s` equals the one taken within `t`](goal). -/
theorem iteratedDerivWithin_eq_of_subset {f : ℝ → ℝ} {s t : Set ℝ} {n : ℕ} {x : ℝ} (st : s ⊆ t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t) (h : ContDiffOn ℝ n f t) (hx : x ∈ s) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n f t x := by
  rw [iteratedDerivWithin, iteratedDerivWithin, iteratedFDerivWithin_subset st hs ht h hx]

/-- Hölder–Taylor remainder within an interval for a derivative order `n + 1 ≤ β` and an
evaluation point different from the base point. -/
private lemma holder_taylor_remainder_within_succ {f : ℝ → ℝ} {M β lo hi t a : ℝ} {n : ℕ}
    (hM : 0 ≤ M) (ht : t ∈ Set.Icc lo hi) (ha : a ∈ Set.Icc lo hi)
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Icc lo hi))
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDerivWithin (n + 1) f (Set.Icc lo hi) x -
              iteratedDerivWithin (n + 1) f (Set.Icc lo hi) y|
              ≤ M * |x - y| ^ (β - ((n + 1 : ℕ) : ℝ)))
    (hle : ((n + 1 : ℕ) : ℝ) ≤ β) (hne : a ≠ t) :
    |f a - taylorWithinEval f (n + 1) (Set.Icc lo hi) t a|
      ≤ M / ((n + 1).factorial : ℝ) * |a - t| ^ β := by
  have hlohi : lo < hi := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact lt_of_le_of_lt ha.1 (lt_of_lt_of_le h ht.2)
    · exact lt_of_le_of_lt ht.1 (lt_of_lt_of_le h ha.2)
  have hIu : UniqueDiffOn ℝ (Set.Icc lo hi) := uniqueDiffOn_Icc hlohi
  have hJI : Set.uIcc t a ⊆ Set.Icc lo hi := Set.uIcc_subset_Icc ht ha
  have hJu : UniqueDiffOn ℝ (Set.uIcc t a) := uniqueDiffOn_Icc (min_lt_max.mpr hne.symm)
  have hexp_nonneg : 0 ≤ β - ((n + 1 : ℕ) : ℝ) := sub_nonneg.mpr hle
  have habs_pos : 0 < |a - t| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hfJ : ContDiffOn ℝ (n + 1 : ℕ) f (Set.uIcc t a) := hf.mono hJI
  have hsame : ∀ k ≤ n + 1, ∀ y ∈ Set.uIcc t a,
      iteratedDerivWithin k f (Set.uIcc t a) y = iteratedDerivWithin k f (Set.Icc lo hi) y :=
    fun k hk y hy =>
      iteratedDerivWithin_eq_of_subset hJI hJu hIu (hf.of_le (by exact_mod_cast hk)) hy
  have hfJn : ContDiffOn ℝ n f (Set.uIcc t a) :=
    hfJ.of_le (by exact_mod_cast Nat.le_succ n)
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.uIcc t a)) (Set.uIoo t a) :=
    (hfJ.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) hJu).mono
      Set.uIoo_subset_uIcc_self
  obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_lagrange hne.symm hfJn hdiff
  have hξJ : ξ ∈ Set.uIcc t a := Set.uIoo_subset_uIcc_self hξ
  have htJ : t ∈ Set.uIcc t a := Set.left_mem_uIcc
  have hpolyJ : taylorWithinEval f (n + 1) (Set.Icc lo hi) t a =
      taylorWithinEval f (n + 1) (Set.uIcc t a) t a := by
    rw [taylor_within_apply, taylor_within_apply]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hsame k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) t htJ]
  have hfac : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiffeq : f a - taylorWithinEval f (n + 1) (Set.Icc lo hi) t a =
      (iteratedDerivWithin (n + 1) f (Set.Icc lo hi) ξ -
        iteratedDerivWithin (n + 1) f (Set.Icc lo hi) t) / ((n + 1).factorial : ℝ)
        * (a - t) ^ (n + 1) := by
    rw [hpolyJ, ← hsame (n + 1) le_rfl ξ hξJ, ← hsame (n + 1) le_rfl t htJ,
      taylorWithinEval_succ, ← sub_sub, hrem, smul_eq_mul, Nat.factorial_succ]
    push_cast
    field_simp
  have hdist : |ξ - t| ≤ |a - t| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Set.uIoo_of_ge h.le] at hξ
      rw [abs_of_nonpos (by linarith [hξ.2]), abs_of_nonpos (by linarith)]
      linarith [hξ.1]
    · rw [Set.uIoo_of_le h.le] at hξ
      rw [abs_of_nonneg (by linarith [hξ.1]), abs_of_nonneg (by linarith)]
      linarith [hξ.2]
  have htop := (hb ξ (hJI hξJ) t ht).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hdist hexp_nonneg) hM)
  rw [hdiffeq, abs_mul, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1).factorial)]
  have hcombine : |a - t| ^ (β - ((n + 1 : ℕ) : ℝ)) * |a - t| ^ (n + 1) = |a - t| ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_add habs_pos]
    congr 1
    ring
  calc _ ≤ (M * |a - t| ^ (β - ((n + 1 : ℕ) : ℝ))) / ((n + 1).factorial : ℝ) * |a - t| ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htop (by positivity)) (by positivity)
    _ = M / ((n + 1).factorial : ℝ) * |a - t| ^ β := by
        rw [← hcombine]
        ring

/-- **Hölder–Taylor remainder for a function that is smooth only on an interval.** Let `p` be the
largest integer strictly below the smoothness index `β`. If [`β` is positive](hyp:hβ), [the
Hölder constant `M` is nonnegative](hyp:hM), [the expansion point `t`](hyp:ht) and [the
evaluation point `a`](hyp:ha) lie in an interval `[lo, hi]`, [`f` is `p` times continuously
differentiable on that interval](hyp:hf), and [its `p`-th derivative within the interval is
`(β − p)`-Hölder there with constant `M`](hyp:hb), then [the degree-`p` Taylor polynomial of
`f` at `t`, built from derivatives within the interval, approximates `f(a)` with error at most
`(M / p!) · |a − t|^β`](goal).

Nothing is assumed about `f` outside `[lo, hi]`; at an endpoint the derivatives are one-sided.
The constant is the same as in the version for functions smooth on the whole line. -/
theorem holder_taylor_remainder_within {f : ℝ → ℝ} {M β lo hi t a : ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M)
    (ht : t ∈ Set.Icc lo hi) (ha : a ∈ Set.Icc lo hi)
    (hf : ContDiffOn ℝ (holderDerivOrder β) f (Set.Icc lo hi))
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDerivWithin (holderDerivOrder β) f (Set.Icc lo hi) x -
              iteratedDerivWithin (holderDerivOrder β) f (Set.Icc lo hi) y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ))) :
    |f a - taylorWithinEval f (holderDerivOrder β) (Set.Icc lo hi) t a|
      ≤ M / ((holderDerivOrder β)).factorial * |a - t| ^ β := by
  rcases eq_or_ne a t with rfl | hne
  · rw [taylorWithinEval_self, sub_self, abs_zero]
    exact mul_nonneg (div_nonneg hM (by positivity)) (Real.rpow_nonneg (abs_nonneg _) _)
  have hlt := (holderDerivOrder_lt hβ).le
  generalize holderDerivOrder β = p at hf hb hlt ⊢
  cases p with
  | zero =>
    have hbb := hb a ha t ht
    simpa [taylor_within_zero_eval, iteratedDerivWithin_zero] using hbb
  | succ n => exact holder_taylor_remainder_within_succ hM ht ha hf hb hlt hne

end Causalean.Mathlib.Analysis.HolderTaylor
