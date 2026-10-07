module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.Endpoint
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.Product

/-!
# Endpoint Taylor expansion of exp(−∫h)·g with a uniform constant

For functions h and g that are k times continuously differentiable on an interval, bounded there,
and whose k-th derivatives are Hölder with exponent α ∈ (0, 1], the survival-weighted product
t ↦ exp(−∫_a^t h)·g(t) is approximated by a polynomial of degree at most k in the distance to the
right endpoint b, with error at most C·(b − t)^(k + α) on the whole interval. The constant C
depends only on k, α, the interval length and the sup and Hölder bounds on h and g, not on the
functions themselves. The functional form is that of a survival function (the exponential of minus
a cumulative hazard) times a second factor.

## Main results

* `survival_product_endpoint_taylor` — the expansion on [a, a + d], with C also independent of
  the location a of the interval.
* `survival_product_endpoint_taylor_Icc` — the same statement on a fixed interval [a, b].
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα) and
[at most one](hyp:hα1), [an interval length d](hyp:d) that is [positive](hyp:hd), and nonnegative
[value envelopes Mh and Mg](hyp:Mh,Mg,hMh,hMg) and [Hölder constants Lh and Lg](hyp:Lh,Lg,hLh,hLg).
Then [there is one nonnegative constant C such that, for every interval from a to a + d and every
integrand h and second factor g that are k times continuously differentiable on it, bounded there
by Mh and Mg, and whose k-th within-interval derivatives are Hölder with exponent α and constants
Lh and Lg there, the survival-weighted product exp(−∫ from a to t of h)·g(t) has a polynomial of
degree at most k in the distance a + d − t to the right endpoint whose error at every point t of
the interval is at most C times that distance to the power k + α](goal). The constant depends
only on the shared input bounds and interval length, not on the functions or interval location.
-/
theorem survival_product_endpoint_taylor
    (k : ℕ) (α d Mh Lh Mg Lg : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hd : 0 < d)
    (hMh : 0 ≤ Mh) (hLh : 0 ≤ Lh) (hMg : 0 ≤ Mg) (hLg : 0 ≤ Lg) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ) (h g : ℝ → ℝ),
        ContDiffOn ℝ k h (Set.Icc a (a + d)) →
        ContDiffOn ℝ k g (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |h x| ≤ Mh) →
        (∀ x ∈ Set.Icc a (a + d), |g x| ≤ Mg) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k h (Set.Icc a (a + d)) x -
            iteratedDerivWithin k h (Set.Icc a (a + d)) y| ≤
              Lh * |x - y| ^ α) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k g (Set.Icc a (a + d)) x -
            iteratedDerivWithin k g (Set.Icc a (a + d)) y| ≤
              Lg * |x - y| ^ α) →
        ∃ coeff : Fin (k + 1) → ℝ,
          ∀ t ∈ Set.Icc a (a + d),
            |Real.exp (-(∫ x in a..t, h x)) * g t -
              ∑ j : Fin (k + 1), coeff j * (a + d - t) ^ j.val| ≤
                C * (a + d - t) ^ ((k : ℝ) + α) := by
  /- Strategy: obtain the product's `ContDiffOn` and top Hölder bound from
  `survival_product_holder_closure`, then apply `endpoint_holder_taylor`.
  The resulting coefficients can be chosen from the endpoint within jet. -/
  obtain ⟨B, hB, hclosure⟩ :=
    survival_product_holder_closure k α d Mh Lh Mg Lg
      hα hα1 hd hMh hLh hMg hLg
  obtain ⟨C, hC, htaylor⟩ :=
    endpoint_holder_taylor k α d B hα hd hB
  refine ⟨C, hC, ?_⟩
  intro a h g hh hg hMh' hMg' hLh' hLg'
  obtain ⟨hfc, _, hfh⟩ :=
    hclosure a h g hh hg hMh' hMg' hLh' hLg'
  exact htaylor a (fun t : ℝ => Real.exp (-(∫ x in a..t, h x)) * g t) hfc hfh

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα) and
[at most one](hyp:hα1), [endpoints a and b](hyp:a,b) with [a < b](hyp:hab), and nonnegative
[value envelopes Mh and Mg](hyp:Mh,Mg,hMh,hMg) and [Hölder constants Lh and Lg](hyp:Lh,Lg,hLh,hLg).
Then [there is one nonnegative constant C such that, for every integrand h and second factor g that
are k times continuously differentiable on the interval from a to b, bounded there by Mh and Mg,
and whose k-th within-interval derivatives are Hölder with exponent α and constants Lh and Lg
there, the survival-weighted product exp(−∫ from a to t of h)·g(t) has a polynomial of degree at
most k in b − t whose error at every point t of the interval is at most C·(b − t)^(k + α)](goal).
No product seminorm is an input. -/
theorem survival_product_endpoint_taylor_Icc
    (k : ℕ) (α a b Mh Lh Mg Lg : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hab : a < b)
    (hMh : 0 ≤ Mh) (hLh : 0 ≤ Lh) (hMg : 0 ≤ Mg) (hLg : 0 ≤ Lg) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h g : ℝ → ℝ),
        ContDiffOn ℝ k h (Set.Icc a b) →
        ContDiffOn ℝ k g (Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, |h x| ≤ Mh) →
        (∀ x ∈ Set.Icc a b, |g x| ≤ Mg) →
        (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |iteratedDerivWithin k h (Set.Icc a b) x -
            iteratedDerivWithin k h (Set.Icc a b) y| ≤
              Lh * |x - y| ^ α) →
        (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |iteratedDerivWithin k g (Set.Icc a b) x -
            iteratedDerivWithin k g (Set.Icc a b) y| ≤
              Lg * |x - y| ^ α) →
        ∃ coeff : Fin (k + 1) → ℝ,
          ∀ t ∈ Set.Icc a b,
            |Real.exp (-(∫ x in a..t, h x)) * g t -
              ∑ j : Fin (k + 1), coeff j * (b - t) ^ j.val| ≤
                C * (b - t) ^ ((k : ℝ) + α) := by
  obtain ⟨C, hC, hbound⟩ :=
    survival_product_endpoint_taylor k α (b - a) Mh Lh Mg Lg
      hα hα1 (sub_pos.mpr hab) hMh hLh hMg hLg
  refine ⟨C, hC, ?_⟩
  intro h g hh hg hMh' hMg' hLh' hLg'
  have heq : a + (b - a) = b := by ring
  simpa [heq] using
    (hbound a h g (by simpa [heq] using hh) (by simpa [heq] using hg)
      (by simpa [heq] using hMh') (by simpa [heq] using hMg')
      (by simpa [heq] using hLh') (by simpa [heq] using hLg'))

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
