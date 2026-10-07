module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hölder control of a lower within-interval jet

A bound on one more derivative gives a Lipschitz estimate on a compact
interval and hence a Hölder estimate at every exponent up to one.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- If [a function f](hyp:f) is [j + 1 times continuously differentiable](hyp:j,hf) on [the
closed interval from a to a + d](hyp:a,d) of [positive length](hyp:hd), and [its within-interval
derivative of order j + 1 is bounded in absolute value by B on that interval](hyp:hbound), with
[B nonnegative](hyp:B,hB), then for [every exponent α](hyp:α) that is [positive](hyp:hα) and
[at most one](hyp:hα1), [the order-j within-interval derivative is Hölder with exponent α and
constant B·d^(1 − α): at any two points x, y of the interval its values differ by at most
B·d^(1 − α)·|x − y|^α](goal). Pairs involving either endpoint are included. -/
theorem lower_jet_holder_of_next_bound
    (j : ℕ) (α a d B : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : 0 < d) (hB : 0 ≤ B) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (j + 1) f (Set.Icc a (a + d)))
    (hbound : ∀ t ∈ Set.Icc a (a + d),
      |iteratedDerivWithin (j + 1) f (Set.Icc a (a + d)) t| ≤ B) :
    ∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
      |iteratedDerivWithin j f (Set.Icc a (a + d)) x -
        iteratedDerivWithin j f (Set.Icc a (a + d)) y| ≤
          (B * d ^ (1 - α)) * |x - y| ^ α := by
  let s := Set.Icc a (a + d)
  have hu : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by linarith)
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin j f s) s :=
    hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr (Nat.lt_succ_self j)) hu
  intro x hx y hy
  have hmv : |iteratedDerivWithin j f s x - iteratedDerivWithin j f s y| ≤
      B * |x - y| := by
    have h := (convex_Icc a (a + d)).norm_image_sub_le_of_norm_derivWithin_le
      hdiff (fun t ht => by
        rw [← iteratedDerivWithin_succ, Real.norm_eq_abs]
        exact hbound t ht) hy hx
    simpa only [Real.norm_eq_abs] using h
  have hxy : |x - y| ≤ d := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hnonneg : 0 ≤ |x - y| := abs_nonneg _
  have hexp : 0 ≤ 1 - α := by linarith
  have hpow : |x - y| ^ (1 - α) ≤ d ^ (1 - α) :=
    Real.rpow_le_rpow hnonneg hxy hexp
  have hfactor : |x - y| = |x - y| ^ α * |x - y| ^ (1 - α) := by
    conv_lhs => rw [← Real.rpow_one |x - y|]
    rw [← Real.rpow_add_of_nonneg hnonneg hα.le hexp]
    congr 1
    ring
  calc
    |iteratedDerivWithin j f s x - iteratedDerivWithin j f s y| ≤
        B * |x - y| := hmv
    _ = B * (|x - y| ^ α * |x - y| ^ (1 - α)) :=
      congrArg (B * ·) hfactor
    _ ≤ B * (|x - y| ^ α * d ^ (1 - α)) := by
      gcongr
    _ = (B * d ^ (1 - α)) * |x - y| ^ α := by ring

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
