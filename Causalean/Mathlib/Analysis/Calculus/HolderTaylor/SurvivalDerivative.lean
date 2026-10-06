module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.PrimitiveJet
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# First within derivative of an exponential primitive

The survival-type exponential satisfies a first-order derivative identity
on a nondegenerate closed interval, including both endpoints.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- If [an integrand h](hyp:h) is [continuous](hyp:hh) on [the closed interval from a to
a + d](hyp:a,d) of [positive length](hyp:hd), then [at every point t of the interval, endpoints
included, the within-interval derivative of the survival function exp(−∫ from a to t of h) equals
−h(t) times that survival function at t](goal). -/
theorem survival_derivWithin
    (a d : ℝ) (hd : 0 < d) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 0 h (Set.Icc a (a + d))) :
    ∀ t ∈ Set.Icc a (a + d),
      derivWithin (fun u : ℝ => Real.exp (-(∫ x in a..u, h x)))
        (Set.Icc a (a + d)) t =
      -h t * Real.exp (-(∫ x in a..t, h x)) := by
  /- Combine interval_primitive_derivWithin with the within-set chain
  rule for negation and Real.exp. -/
  intro t ht
  let s := Set.Icc a (a + d)
  let H := fun u : ℝ => ∫ x in a..u, h x
  have hHdiff : DifferentiableWithinAt ℝ H s t :=
    (interval_primitive_contDiffOn 0 a d hd h hh).differentiableOn
      (by norm_num) t ht
  have hHderiv : derivWithin H s t = h t :=
    interval_primitive_derivWithin a d hd h hh t ht
  have hHas : HasDerivWithinAt H (h t) s t := by
    simpa [hHderiv] using hHdiff.hasDerivWithinAt
  have hsurv := hHas.neg.exp.derivWithin
    ((uniqueDiffOn_Icc (lt_add_of_pos_right a hd)) t ht)
  simpa [H, s, mul_comm] using hsurv

/-- If [an integrand h](hyp:h) is [k times continuously differentiable](hyp:k,hh) on [the closed
interval from a to a + d](hyp:a,d) of [positive length](hyp:hd), then [for every order j at most
k and every point t of the interval, the (j + 1)-th within-interval derivative of the survival
function S(t) = exp(−∫ from a to t of h) equals minus the Leibniz sum over i from 0 to j of
(j choose i) times the i-th within-interval derivative of h times the (j − i)-th within-interval
derivative of S](goal), as obtained from the differential equation S′ = −h·S. -/
theorem survival_iteratedDerivWithin_succ
    (k : ℕ) (a d : ℝ) (hd : 0 < d) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ k h (Set.Icc a (a + d))) :
    ∀ j ≤ k, ∀ t ∈ Set.Icc a (a + d),
      iteratedDerivWithin (j + 1)
        (fun u : ℝ => Real.exp (-(∫ x in a..u, h x)))
        (Set.Icc a (a + d)) t =
      -(∑ i ∈ Finset.range (j + 1),
          (Nat.choose j i : ℝ) *
            iteratedDerivWithin i h (Set.Icc a (a + d)) t *
            iteratedDerivWithin (j - i)
              (fun u : ℝ => Real.exp (-(∫ x in a..u, h x)))
              (Set.Icc a (a + d)) t) := by
  /- First identify S' with -h*S on the entire interval using
  `survival_derivWithin`. Rewrite the successor derivative as the j-th
  derivative of S', then use `iteratedDerivWithin_congr` and Mathlib's
  `iteratedDerivWithin_mul`. The hypotheses supply C^j for both factors. -/
  intro j hj t ht
  let s := Set.Icc a (a + d)
  let S := fun u : ℝ => Real.exp (-(∫ x in a..u, h x))
  have hS : ContDiffOn ℝ j S s :=
    ((interval_primitive_contDiffOn k a d hd h hh).neg.exp).of_le (by
      exact_mod_cast Nat.le_trans hj (Nat.le_succ k))
  have hhj : ContDiffOn ℝ j h s := hh.of_le (by exact_mod_cast hj)
  have hderiv : Set.EqOn (derivWithin S s) (fun u => -(h u * S u)) s := by
    intro u hu
    simpa only [S, s, neg_mul] using
      survival_derivWithin a d hd h (hh.of_le (by norm_num)) u hu
  change iteratedDerivWithin (j + 1) S s t =
    -(∑ i ∈ Finset.range (j + 1),
      (Nat.choose j i : ℝ) * iteratedDerivWithin i h s t *
        iteratedDerivWithin (j - i) S s t)
  rw [iteratedDerivWithin_succ', (iteratedDerivWithin_congr (n := j) hderiv) ht]
  rw [iteratedDerivWithin_fun_neg]
  exact congrArg Neg.neg
    (iteratedDerivWithin_mul ht (uniqueDiffOn_Icc (lt_add_of_pos_right a hd))
      (hhj t ht) (hS t ht))

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
