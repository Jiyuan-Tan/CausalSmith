module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Within-interval jets of an interval primitive

These identities isolate the fundamental theorem of calculus and its
finite-order within-interval consequences, including both endpoints.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- If [an integrand h](hyp:h) is [continuous](hyp:hh) on [the closed interval from a to
a + d](hyp:a,d) of [positive length](hyp:hd), then [at every point t of the interval, endpoints
included, the within-interval derivative of the primitive of h from a equals h(t)](goal). -/
theorem interval_primitive_derivWithin
    (a d : ℝ) (hd : 0 < d) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 0 h (Set.Icc a (a + d))) :
    ∀ t ∈ Set.Icc a (a + d),
      derivWithin (fun u : ℝ => ∫ x in a..u, h x)
        (Set.Icc a (a + d)) t = h t := by
  /- Apply the interval FTC at interior points and transfer the derivative
  identity to each endpoint through the one-sided within derivative. -/
  have hab : a < a + d := lt_add_of_pos_right a hd
  have hcont : ContinuousOn h (Set.Icc a (a + d)) := hh.continuousOn
  intro t ht
  have : Fact (t ∈ Set.Icc a (a + d)) := ⟨ht⟩
  have hint : IntervalIntegrable h MeasureTheory.volume a t :=
    (hcont.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1
  have hmeas : StronglyMeasurableAtFilter h
      (nhdsWithin t (Set.Icc a (a + d))) :=
    hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  exact (intervalIntegral.integral_hasDerivWithinAt_right
    (s := Set.Icc a (a + d)) (t := Set.Icc a (a + d))
    hint hmeas (hcont t ht)).derivWithin ((uniqueDiffOn_Icc hab) t ht)

/-- If [an integrand h](hyp:h) is [k times continuously differentiable](hyp:k,hh) on [the closed
interval from a to a + d](hyp:a,d) of [positive length](hyp:hd), then [its primitive from a is
k + 1 times continuously differentiable on that same interval](goal). -/
theorem interval_primitive_contDiffOn
    (k : ℕ) (a d : ℝ) (hd : 0 < d) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ k h (Set.Icc a (a + d))) :
    ContDiffOn ℝ (k + 1) (fun t : ℝ => ∫ x in a..t, h x)
      (Set.Icc a (a + d)) := by
  /- Use interval_primitive_derivWithin for the base derivative and the
  local derivative characterization of ContDiffOn for the higher orders. -/
  let s := Set.Icc a (a + d)
  let H := fun t : ℝ => ∫ x in a..t, h x
  have hab : a < a + d := lt_add_of_pos_right a hd
  have hcont : ContinuousOn h s := hh.continuousOn
  have hdiff : DifferentiableOn ℝ H s := by
    intro t ht
    have : Fact (t ∈ s) := ⟨ht⟩
    have hint : IntervalIntegrable h MeasureTheory.volume a t :=
      (hcont.mono (by
        intro x hx
        exact ⟨hx.1, hx.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1
    have hmeas : StronglyMeasurableAtFilter h (nhdsWithin t s) :=
      hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    exact (intervalIntegral.integral_hasDerivWithinAt_right
      (s := s) (t := s) hint hmeas (hcont t ht)).differentiableWithinAt
  have hderiv : Set.EqOn (derivWithin H s) h s :=
    interval_primitive_derivWithin a d hd h (hh.of_le (by norm_num))
  have hjet : ContDiffOn ℝ k (derivWithin H s) s :=
    hh.congr (fun t ht => hderiv ht)
  exact (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)).2
    ⟨hdiff, by simp, hjet⟩

/-- If [an integrand h](hyp:h) is [k times continuously differentiable](hyp:k,hh) on [the closed
interval from a to a + d](hyp:a,d) of [positive length](hyp:hd), then [for every order j at most
k and every point t of the interval, endpoints included, the (j + 1)-th within-interval derivative
of the primitive of h from a equals the j-th within-interval derivative of h](goal). -/
theorem interval_primitive_iteratedDerivWithin_succ
    (k : ℕ) (a d : ℝ) (hd : 0 < d) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ k h (Set.Icc a (a + d))) :
    ∀ j ≤ k, ∀ t ∈ Set.Icc a (a + d),
      iteratedDerivWithin (j + 1) (fun u : ℝ => ∫ x in a..u, h x)
        (Set.Icc a (a + d)) t =
      iteratedDerivWithin j h (Set.Icc a (a + d)) t := by
  /- Rewrite the successor iterated derivative as the derivative of the
  preceding jet and use the base FTC identity inductively. -/
  intro j hj t ht
  rw [iteratedDerivWithin_succ']
  exact (iteratedDerivWithin_congr
    (n := j) (interval_primitive_derivWithin a d hd h
      (hh.of_le (by norm_num)))) ht

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
