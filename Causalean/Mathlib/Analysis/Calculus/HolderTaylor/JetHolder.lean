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

/-- On an interval of fixed length, a uniform bound on the order-`j+1`
within derivative gives a uniform Hölder-`α` bound on the order-`j` within
derivative. The conclusion includes pairs involving either endpoint.
[The jet order, exponent, interval, bound, function, and regularity assumptions](hyp:j,α,a,d,B,hα,hα1,hd,hB,f,hf,hbound) yield [the stated lower-jet Hölder bound](goal). -/
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
