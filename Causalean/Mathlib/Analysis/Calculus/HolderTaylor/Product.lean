module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.JetHolder
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.PrimitiveExp

/-!
# Quantitative product closure for interval Hölder jets

The product estimate uses only the two factors' value and top-derivative
Hölder bounds. A specialization covers an exponential primitive times a
second Hölder-smooth function.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα) and
[at most one](hyp:hα1), [an interval length d](hyp:d) that is [positive](hyp:hd), and nonnegative
[value envelopes Mf and Mg](hyp:Mf,Mg,hMf,hMg) and [Hölder constants Lf and Lg](hyp:Lf,Lg,hLf,hLg)
for two factors. Then [there is one nonnegative constant B such that, for every interval from a to
a + d and all functions f and g that are k times continuously differentiable on it, bounded there
by Mf and Mg, and whose k-th within-interval derivatives are Hölder with exponent α and constants
Lf and Lg there, the product f·g is k times continuously differentiable on the interval, bounded
by B there, and has k-th within-interval derivative Hölder with constant B and exponent
α](goal). -/
theorem product_holder_closure
    (k : ℕ) (α d Mf Lf Mg Lg : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hd : 0 < d)
    (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf) (hMg : 0 ≤ Mg) (hLg : 0 ≤ Lg) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (f g : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        ContDiffOn ℝ k g (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ Mf) →
        (∀ x ∈ Set.Icc a (a + d), |g x| ≤ Mg) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x -
            iteratedDerivWithin k f (Set.Icc a (a + d)) y| ≤
              Lf * |x - y| ^ α) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k g (Set.Icc a (a + d)) x -
            iteratedDerivWithin k g (Set.Icc a (a + d)) y| ≤
              Lg * |x - y| ^ α) →
        ContDiffOn ℝ k (fun t => f t * g t) (Set.Icc a (a + d)) ∧
        (∀ x ∈ Set.Icc a (a + d), |f x * g x| ≤ B) ∧
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k (fun t => f t * g t) (Set.Icc a (a + d)) x -
            iteratedDerivWithin k (fun t => f t * g t) (Set.Icc a (a + d)) y| ≤
              B * |x - y| ^ α) := by
  obtain ⟨Cf, hCf, hCf_bound⟩ :=
    uniform_iteratedDerivWithin_bound k α d Mf Lf hα hα1 hd hMf hLf
  obtain ⟨Cg, hCg, hCg_bound⟩ :=
    uniform_iteratedDerivWithin_bound k α d Mg Lg hα hα1 hd hMg hLg
  let Hf := Lf + Cf * d ^ (1 - α)
  let Hg := Lg + Cg * d ^ (1 - α)
  have hHf : 0 ≤ Hf := by dsimp [Hf]; positivity
  have hHg : 0 ≤ Hg := by dsimp [Hg]; positivity
  have hLf_le : Lf ≤ Hf := by
    dsimp [Hf]
    exact le_add_of_nonneg_right (mul_nonneg hCf (Real.rpow_nonneg hd.le _))
  have hCf_le : Cf * d ^ (1 - α) ≤ Hf := by
    dsimp [Hf]
    exact le_add_of_nonneg_left hLf
  have hLg_le : Lg ≤ Hg := by
    dsimp [Hg]
    exact le_add_of_nonneg_right (mul_nonneg hCg (Real.rpow_nonneg hd.le _))
  have hCg_le : Cg * d ^ (1 - α) ≤ Hg := by
    dsimp [Hg]
    exact le_add_of_nonneg_left hLg
  let C := Cf * Hg + Cg * Hf
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let B := Mf * Mg + ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ) * C
  have hB : 0 ≤ B := by
    dsimp [B]
    apply add_nonneg (mul_nonneg hMf hMg)
    exact Finset.sum_nonneg fun i hi => mul_nonneg (Nat.cast_nonneg _) hC
  refine ⟨B, hB, ?_⟩
  intro a f g hf hg hfv hgv hfh hgh
  let s := Set.Icc a (a + d)
  have hu : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by linarith)
  have hfb := hCf_bound a f hf hfv hfh
  have hgb := hCg_bound a g hg hgv hgh
  have hfh_all (j : ℕ) (hj : j ≤ k) (x : ℝ) (hx : x ∈ s)
      (y : ℝ) (hy : y ∈ s) :
      |iteratedDerivWithin j f s x - iteratedDerivWithin j f s y| ≤
        Hf * |x - y| ^ α := by
    by_cases hk0 : k = 0
    · have hj0 : j = 0 := by omega
      subst k
      subst j
      exact (hfh x hx y hy).trans (mul_le_mul_of_nonneg_right
        hLf_le (Real.rpow_nonneg (abs_nonneg _) _))
    by_cases heq : j = k
    · subst j
      exact (hfh x hx y hy).trans (mul_le_mul_of_nonneg_right
        hLf_le (Real.rpow_nonneg (abs_nonneg _) _))
    · have hj1 : j + 1 ≤ k := by omega
      have h := lower_jet_holder_of_next_bound j α a d Cf hα hα1 hd hCf f
        (hf.of_le (by exact_mod_cast hj1)) (fun t ht => hfb (j + 1) hj1 t ht)
        x hx y hy
      exact h.trans (mul_le_mul_of_nonneg_right
        hCf_le (Real.rpow_nonneg (abs_nonneg _) _))
  have hgh_all (j : ℕ) (hj : j ≤ k) (x : ℝ) (hx : x ∈ s)
      (y : ℝ) (hy : y ∈ s) :
      |iteratedDerivWithin j g s x - iteratedDerivWithin j g s y| ≤
        Hg * |x - y| ^ α := by
    by_cases hk0 : k = 0
    · have hj0 : j = 0 := by omega
      subst k
      subst j
      exact (hgh x hx y hy).trans (mul_le_mul_of_nonneg_right
        hLg_le (Real.rpow_nonneg (abs_nonneg _) _))
    by_cases heq : j = k
    · subst j
      exact (hgh x hx y hy).trans (mul_le_mul_of_nonneg_right
        hLg_le (Real.rpow_nonneg (abs_nonneg _) _))
    · have hj1 : j + 1 ≤ k := by omega
      have h := lower_jet_holder_of_next_bound j α a d Cg hα hα1 hd hCg g
        (hg.of_le (by exact_mod_cast hj1)) (fun t ht => hgb (j + 1) hj1 t ht)
        x hx y hy
      exact h.trans (mul_le_mul_of_nonneg_right
        hCg_le (Real.rpow_nonneg (abs_nonneg _) _))
  refine ⟨hf.mul hg, ?_, ?_⟩
  · intro x hx
    calc
      |f x * g x| = |f x| * |g x| := abs_mul _ _
      _ ≤ Mf * Mg := mul_le_mul (hfv x hx) (hgv x hx) (abs_nonneg _) hMf
      _ ≤ B := by
        dsimp [B]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi =>
          mul_nonneg (Nat.cast_nonneg _) hC)
  · intro x hx y hy
    have hpow : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
    have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
        |(Nat.choose k i : ℝ) * iteratedDerivWithin i f s x *
             iteratedDerivWithin (k - i) g s x -
           (Nat.choose k i : ℝ) * iteratedDerivWithin i f s y *
             iteratedDerivWithin (k - i) g s y| ≤
          ((Nat.choose k i : ℝ) * C) * |x - y| ^ α := by
      have hik : i ≤ k := by
        have hi' := Finset.mem_range.mp hi
        omega
      have hki : k - i ≤ k := Nat.sub_le _ _
      let u := iteratedDerivWithin i f s x
      let u' := iteratedDerivWithin i f s y
      let v := iteratedDerivWithin (k - i) g s x
      let v' := iteratedDerivWithin (k - i) g s y
      have huv : |u * v - u' * v'| ≤ C * |x - y| ^ α := by
        have heq : u * v - u' * v' = (u - u') * v + u' * (v - v') := by ring
        rw [heq]
        calc
          |(u - u') * v + u' * (v - v')| ≤
              |u - u'| * |v| + |u'| * |v - v'| := by
                simpa only [abs_mul] using abs_add_le ((u - u') * v) (u' * (v - v'))
          _ ≤ (Hf * |x - y| ^ α) * Cg + Cf * (Hg * |x - y| ^ α) := by
                apply add_le_add
                · exact mul_le_mul (hfh_all i hik x hx y hy)
                    (hgb (k - i) hki x hx) (abs_nonneg _) (mul_nonneg hHf hpow)
                · exact mul_le_mul (hfb i hik y hy)
                    (hgh_all (k - i) hki x hx y hy) (abs_nonneg _) hCf
          _ = C * |x - y| ^ α := by dsimp [C]; ring
      have hc : 0 ≤ (Nat.choose k i : ℝ) := Nat.cast_nonneg _
      calc
        _ = (Nat.choose k i : ℝ) * |u * v - u' * v'| := by
          have heq : (Nat.choose k i : ℝ) * iteratedDerivWithin i f s x *
              iteratedDerivWithin (k - i) g s x -
              (Nat.choose k i : ℝ) * iteratedDerivWithin i f s y *
                iteratedDerivWithin (k - i) g s y =
              (Nat.choose k i : ℝ) * (u * v - u' * v') := by
            dsimp [u, u', v, v']; ring
          rw [heq, abs_mul, abs_of_nonneg hc]
        _ ≤ (Nat.choose k i : ℝ) * (C * |x - y| ^ α) :=
          mul_le_mul_of_nonneg_left huv hc
        _ = ((Nat.choose k i : ℝ) * C) * |x - y| ^ α := by ring
    have hsum :
        |(∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℝ) * iteratedDerivWithin i f s x *
              iteratedDerivWithin (k - i) g s x) -
          (∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℝ) * iteratedDerivWithin i f s y *
              iteratedDerivWithin (k - i) g s y)| ≤
          (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ) * C) *
            |x - y| ^ α := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i hi => hterm i hi)
    change |iteratedDerivWithin k (f * g) s x -
      iteratedDerivWithin k (f * g) s y| ≤ B * |x - y| ^ α
    rw [iteratedDerivWithin_mul hx hu (hf x hx) (hg x hx),
      iteratedDerivWithin_mul hy hu (hf y hy) (hg y hy)]
    exact hsum.trans (mul_le_mul_of_nonneg_right
      (by dsimp [B]; exact le_add_of_nonneg_left (mul_nonneg hMf hMg)) hpow)

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα) and
[at most one](hyp:hα1), [an interval length d](hyp:d) that is [positive](hyp:hd), and nonnegative
[value envelopes Mh and Mg](hyp:Mh,Mg,hMh,hMg) and [Hölder constants Lh and Lg](hyp:Lh,Lg,hLh,hLg).
Then [there is one nonnegative constant B such that, for every interval from a to a + d and every
integrand h and second factor g that are k times continuously differentiable on it, bounded there
by Mh and Mg, and whose k-th within-interval derivatives are Hölder with exponent α and constants
Lh and Lg there, the survival-weighted product t ↦ exp(−∫ from a to t of h)·g(t) is k times
continuously differentiable on the interval, bounded by B there, and has k-th within-interval
derivative Hölder with constant B and exponent α](goal). No product seminorm is an input. -/
theorem survival_product_holder_closure
    (k : ℕ) (α d Mh Lh Mg Lg : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hd : 0 < d)
    (hMh : 0 ≤ Mh) (hLh : 0 ≤ Lh) (hMg : 0 ≤ Mg) (hLg : 0 ≤ Lg) :
    ∃ B : ℝ, 0 ≤ B ∧
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
        let f := fun t : ℝ => Real.exp (-(∫ x in a..t, h x)) * g t
        ContDiffOn ℝ k f (Set.Icc a (a + d)) ∧
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ B) ∧
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x -
            iteratedDerivWithin k f (Set.Icc a (a + d)) y| ≤
              B * |x - y| ^ α) := by
  /- Strategy: take the uniform constant from `survival_holder_closure`,
  then feed its three conclusions and the assumptions on g into
  `product_holder_closure`. -/
  obtain ⟨Bs, hBs, hs⟩ :=
    survival_holder_closure k α d Mh Lh hα hα1 hd hMh hLh
  obtain ⟨B, hB, hp⟩ :=
    product_holder_closure k α d Bs Bs Mg Lg
      hα hα1 hd hBs hBs hMg hLg
  refine ⟨B, hB, ?_⟩
  intro a h g hh hg hMh' hMg' hLh' hLg'
  obtain ⟨hSc, hSb, hSh⟩ := hs a h hh hMh' hLh'
  exact hp a (fun t : ℝ => Real.exp (-(∫ x in a..t, h x))) g
    hSc hg hSb hMg' hSh hLg'

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
