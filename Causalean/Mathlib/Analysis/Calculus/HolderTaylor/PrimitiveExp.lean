module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.Interpolation
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.JetHolder
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.PrimitiveJet
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.SurvivalDerivative
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.SurvivalJetBound
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Primitive and exponential closure on an interval

Quantitative regularity of an interval primitive and of its survival-type
exponential, using only a value bound and a top derivative Hölder bound for the
integrand. All constants are uniform under translation of the interval.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα),
[an interval length d](hyp:d) that is [positive](hyp:hd), and
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative Hölder constant L](hyp:L,hL). Then
[there is one nonnegative constant B such that, for every interval from a to a + d and every
integrand h that is k times continuously differentiable on it, bounded by M there, and whose k-th
within-interval derivative is Hölder with constant L and exponent α there, the primitive of h from
a is k + 1 times continuously differentiable on the interval, all its within-interval derivatives
up to order k + 1 are bounded by B there, and its (k + 1)-th within-interval derivative is Hölder
with constant B and exponent α](goal). -/
theorem primitive_quantitative_closure
    (k : ℕ) (α d M L : ℝ) (hα : 0 < α)
    (hd : 0 < d) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (h : ℝ → ℝ),
        ContDiffOn ℝ k h (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |h x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k h (Set.Icc a (a + d)) x -
            iteratedDerivWithin k h (Set.Icc a (a + d)) y| ≤
              L * |x - y| ^ α) →
        let H := fun t : ℝ => ∫ x in a..t, h x
        ContDiffOn ℝ (k + 1) H (Set.Icc a (a + d)) ∧
        (∀ j ≤ k + 1, ∀ x ∈ Set.Icc a (a + d),
          |iteratedDerivWithin j H (Set.Icc a (a + d)) x| ≤ B) ∧
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin (k + 1) H (Set.Icc a (a + d)) x -
            iteratedDerivWithin (k + 1) H (Set.Icc a (a + d)) y| ≤
              B * |x - y| ^ α) := by
  obtain ⟨C, hC, hbound⟩ :=
    uniform_iteratedDerivWithin_bound k α d M L hα hd hM hL
  refine ⟨d * M + C + L, by positivity, ?_⟩
  intro a h hh hval hholder
  let s := Set.Icc a (a + d)
  let H := fun t : ℝ => ∫ x in a..t, h x
  have hjet := interval_primitive_iteratedDerivWithin_succ k a d hd h hh
  have hCb := hbound a h hh hval hholder
  refine ⟨interval_primitive_contDiffOn k a d hd h hh, ?_, ?_⟩
  · intro j hj x hx
    cases j with
    | zero =>
      have hsub : ∀ t ∈ Set.uIoc a x, ‖h t‖ ≤ M := by
        intro t ht
        have ht' : t ∈ Set.Ioc a x := by simpa [Set.uIoc_of_le hx.1] using ht
        simpa [Real.norm_eq_abs] using hval t ⟨ht'.1.le, ht'.2.trans hx.2⟩
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const hsub
      have hlen : |x - a| ≤ d := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
        linarith [hx.2]
      have hmul : M * |x - a| ≤ M * d := mul_le_mul_of_nonneg_left hlen hM
      simpa only [iteratedDerivWithin_zero, Real.norm_eq_abs] using
        (hi.trans (hmul.trans (by linarith [hC, hL])))
    | succ j =>
      have hjk : j ≤ k := by omega
      rw [hjet j hjk x hx]
      exact (hCb j hjk x hx).trans (by linarith [mul_nonneg hd.le hM, hL])
  · intro x hx y hy
    rw [hjet k (le_refl k) x hx, hjet k (le_refl k) y hy]
    exact (hholder x hx y hy).trans (by
      have hp : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
      nlinarith [mul_nonneg (add_nonneg (mul_nonneg hd.le hM) hC) hp])

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα) and
[at most one](hyp:hα1), [an interval length d](hyp:d) that is [positive](hyp:hd), and
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative Hölder constant L](hyp:L,hL). Then
[there is one nonnegative constant B such that, for every interval from a to a + d and every
integrand h that is k times continuously differentiable on it, bounded by M there, and whose k-th
within-interval derivative is Hölder with constant L and exponent α there, the survival-type
function exp(−∫ from a to t of h) is k times continuously differentiable on the interval, bounded
by B there, and has k-th within-interval derivative Hölder with constant B and exponent
α](goal). The constant depends only on the order, exponent, length, and the two envelopes. -/
theorem survival_holder_closure
    (k : ℕ) (α d M L : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : 0 < d) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (h : ℝ → ℝ),
        ContDiffOn ℝ k h (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |h x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k h (Set.Icc a (a + d)) x -
            iteratedDerivWithin k h (Set.Icc a (a + d)) y| ≤
              L * |x - y| ^ α) →
        let S := fun t : ℝ => Real.exp (-(∫ x in a..t, h x))
        ContDiffOn ℝ k S (Set.Icc a (a + d)) ∧
        (∀ x ∈ Set.Icc a (a + d), |S x| ≤ B) ∧
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k S (Set.Icc a (a + d)) x -
            iteratedDerivWithin k S (Set.Icc a (a + d)) y| ≤
              B * |x - y| ^ α) := by
  /- First use `uniform_iteratedDerivWithin_bound` to bound the integrand's
  whole jet, and use its value bound to bound the primitive and hence `S`.
  `survival_jet_bound_of_integrand_jet_bound` then bounds `S` through order
  `k+1`. Apply `lower_jet_holder_of_next_bound` at order `k`; this also
  covers `k=0`. Differentiability follows from `interval_primitive_contDiffOn`
  and composition with `Real.exp`. -/
  obtain ⟨C, hC, hjet⟩ :=
    uniform_iteratedDerivWithin_bound k α d M L hα hd hM hL
  obtain ⟨P, hP, hprim⟩ :=
    primitive_quantitative_closure k α d M L hα hd hM hL
  have hE : 0 ≤ Real.exp P := (Real.exp_pos P).le
  obtain ⟨J, hJ, hsurvjet⟩ :=
    survival_jet_bound_of_integrand_jet_bound k d C (Real.exp P) hd hC hE
  refine ⟨Real.exp P + J * d ^ (1 - α),
    add_nonneg hE (mul_nonneg hJ (Real.rpow_nonneg hd.le _)), ?_⟩
  intro a h hh hval hholder
  let s := Set.Icc a (a + d)
  let H := fun t : ℝ => ∫ x in a..t, h x
  let S := fun t : ℝ => Real.exp (-H t)
  obtain ⟨hH, hHjet, _⟩ := hprim a h hh hval hholder
  have hS : ContDiffOn ℝ (k + 1) S s := hH.neg.exp
  have hSvalue : ∀ t ∈ s, |S t| ≤ Real.exp P := by
    intro t ht
    have hHval := hHjet 0 (Nat.zero_le _) t ht
    have hHabs : |H t| ≤ P := by simpa only [iteratedDerivWithin_zero] using hHval
    have hneg : -H t ≤ P := by rcases abs_le.mp hHabs with ⟨hlo, _⟩; linarith
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hneg
  have hSj : ∀ j ≤ k + 1, ∀ t ∈ s,
      |iteratedDerivWithin j S s t| ≤ J :=
    hsurvjet a h hh (hjet a h hh hval hholder) hSvalue
  refine ⟨hS.of_le (by exact_mod_cast Nat.le_succ k), ?_, ?_⟩
  · intro t ht
    exact (hSvalue t ht).trans (le_add_of_nonneg_right
      (mul_nonneg hJ (Real.rpow_nonneg hd.le _)))
  · intro x hx y hy
    have hhold := lower_jet_holder_of_next_bound k α a d J hα hα1 hd hJ S hS
      (hSj (k + 1) le_rfl)
    have hpow : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
    calc
      |iteratedDerivWithin k S s x - iteratedDerivWithin k S s y| ≤
          (J * d ^ (1 - α)) * |x - y| ^ α := hhold x hx y hy
      _ ≤ (Real.exp P + J * d ^ (1 - α)) * |x - y| ^ α := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hE) hpow

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
