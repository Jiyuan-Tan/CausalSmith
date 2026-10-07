module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Approximation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.ConstrainedDuality

/-!
# Scalar inverse and ordinary moment priors

The interval is `[a,1]`, where `a = c₀/K²`.  The extra inverse moment
allows a change of measure by `a/x`; the separated target is `x/(x+qa)`.
The coefficient `q` will be `1-2ε`, which handles every `0 < ε < 1/2`.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- A [scale constant](hyp:c₀) and [matching degree](hyp:K) determine [the endpoint scale](goal) by [dividing the constant by the squared degree](step:1); it is positive when the constant is positive and the degree is at least one. -/
noncomputable def endpointScale (c₀ : ℝ) (K : ℕ) : ℝ := c₀ / (K : ℝ) ^ 2

/-- A [matching degree](hyp:K), [support endpoint and inverse coefficient](hyp:a,q), and [target gap](hyp:gap) specify a pair of scalar priors, for a matching degree K ≥ 1: both are probability measures carried by finitely many points and put all their mass on the interval from a to 1, they give the same mean to 1/x and to every power xᵐ with m ≤ 3K, and their means of the rational target x/(x + q·a) differ in absolute value by at least the target gap. -/
structure ScalarPriors (K : ℕ) (a q gap : ℝ) where
  positive_degree : 1 ≤ K
  ω₀ : Measure ℝ
  ω₁ : Measure ℝ
  probability₀ : IsProbabilityMeasure ω₀
  probability₁ : IsProbabilityMeasure ω₁
  finite₀ : ∃ s : Finset ℝ, ω₀ (s : Set ℝ) = 1
  finite₁ : ∃ s : Finset ℝ, ω₁ (s : Set ℝ) = 1
  supported₀ : ω₀ (Set.Icc a 1) = 1
  supported₁ : ω₁ (Set.Icc a 1) = 1
  inverse_match : (∫ x, x⁻¹ ∂ω₀) = ∫ x, x⁻¹ ∂ω₁
  ordinary_match : ∀ m : ℕ, m ≤ 3 * K →
    (∫ x, x ^ m ∂ω₀) = ∫ x, x ^ m ∂ω₁
  target_gap : gap ≤
    |(∫ x, x / (x + q * a) ∂ω₀) - ∫ x, x / (x + q * a) ∂ω₁|

/- Use Hahn–Banach duality in the finite-dimensional subspace
  `span {x⁻¹, 1, ..., x^(3K)}` on the compact interval.  Its norm-one
  annihilator is a signed measure; split into positive and negative
  parts and normalize to probability measures.  Tchakaloff/Carathéodory
  reduction makes both supports finite while preserving the inverse,
  ordinary, and target integrals.  The existing `FiniteMomentDual`
  annihilates only ordinary powers, so it is not enough by itself. -/

/-- A [positive inverse coefficient](hyp:hq₀), [positive scale and gap constants](hyp:hc₀,hδ), and [a uniform inverse-rational approximation gap](hyp:happrox) yield [finite scalar probability priors with matched inverse and degree-`3K` moments](goal). -/
theorem exists_scalarPriors_of_inverseGap {q c₀ δ : ℝ}
    (hq₀ : 0 < q)
    (hc₀ : 0 < c₀) (hδ : 0 < δ)
    (happrox : ∀ K : ℕ, 1 ≤ K → ∀ α : ℝ, ∀ P : Polynomial ℝ,
      P.natDegree ≤ 3 * K →
        ∃ x ∈ Set.Icc (endpointScale c₀ K) 1,
          δ ≤ |x / (x + q * endpointScale c₀ K) -
            (α / x + P.eval x)|) :
    ∀ K : ℕ, 1 ≤ K →
      Nonempty (ScalarPriors K (endpointScale c₀ K) q δ) := by
  intro K hK
  classical
  let a := endpointScale c₀ K
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have ha : 0 < a := by
    dsimp [a, endpointScale]
    positivity
  let f : ℝ → ℝ := fun x => x / (x + q * a)
  let g : Fin (3 * K + 2) → ℝ → ℝ :=
    fun i x => if i = 0 then x⁻¹ else x ^ (i.val - 1)
  have hf : ContinuousOn f (Set.Icc a 1) := by
    apply continuousOn_id.div (continuousOn_id.add continuousOn_const)
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hqa : 0 ≤ q * a := mul_nonneg hq₀.le ha.le
    change x + q * a ≠ 0
    positivity
  have hg : ∀ i, ContinuousOn (g i) (Set.Icc a 1) := by
    intro i
    by_cases hi : i = 0
    · subst i
      change ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc a 1)
      apply continuousOn_id.inv₀
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    · simp only [g, if_neg hi]
      exact continuousOn_id.pow _
  have hgap : ∀ α : ℝ, ∀ c : Fin (3 * K + 2) → ℝ,
      ∃ x ∈ Set.Icc a 1,
        δ ≤ |f x - (α + ∑ i, c i * g i x)| := by
    intro α c
    let P : Polynomial ℝ := Polynomial.C α +
      ∑ j : Fin (3 * K + 1), Polynomial.C (c j.succ) * Polynomial.X ^ j.val
    have hP : P.natDegree ≤ 3 * K := by
      dsimp [P]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro j hj
        exact (Polynomial.natDegree_C_mul_X_pow_le (c j.succ) j.val).trans
          (Nat.le_of_lt_succ j.isLt)
    obtain ⟨x, hx, hδx⟩ := happrox K hK (c 0) P hP
    refine ⟨x, hx, ?_⟩
    have hsum : (∑ i : Fin (3 * K + 2), c i * g i x) =
        c 0 / x + ∑ j : Fin (3 * K + 1), c j.succ * x ^ j.val := by
      rw [Fin.sum_univ_succ]
      simp [g, div_eq_mul_inv]
    have hPeval : P.eval x = α +
        ∑ j : Fin (3 * K + 1), c j.succ * x ^ j.val := by
      simp [P, Polynomial.eval_finsetSum]
    rw [hsum]
    rw [hPeval] at hδx
    have hform : α + (c 0 / x + ∑ j : Fin (3 * K + 1), c j.succ * x ^ j.val) =
        c 0 / x + (α + ∑ j : Fin (3 * K + 1), c j.succ * x ^ j.val) := by ring
    rw [hform]
    simpa only [f, a] using hδx
  obtain ⟨ω₀, ω₁, hp₀, hp₁, hfin₀, hfin₁, hs₀, hs₁, hmatch, htarget⟩ :=
    exists_finitePriors_of_constrainedApproxGap hδ f g hf hg hgap
  refine ⟨{ positive_degree := hK,
             ω₀ := ω₀, ω₁ := ω₁,
             probability₀ := hp₀, probability₁ := hp₁,
             finite₀ := hfin₀, finite₁ := hfin₁,
             supported₀ := hs₀, supported₁ := hs₁,
             inverse_match := ?_,
             ordinary_match := ?_,
             target_gap := htarget }⟩
  · exact hmatch 0
  · intro m hm
    let j : Fin (3 * K + 1) := ⟨m, by omega⟩
    have h := hmatch j.succ
    simpa [g, j] using h

/-- A [positive inverse coefficient no larger than one](hyp:q,hq₀,hq₁) q admits [constants 0 < c₀ < 1 and gap > 0, not depending on the degree, such that for every degree K ≥ 1 there is a pair of finitely supported probability priors on the interval from c₀/K² to 1 that give the same mean to 1/x and to every power xᵐ with m ≤ 3K, while their means of x/(x + q·c₀/K²) differ in absolute value by at least gap](goal). -/
theorem exists_scalarPriors (q : ℝ) (hq₀ : 0 < q) (hq₁ : q ≤ 1) :
    ∃ c₀ gap : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 0 < gap ∧
      ∀ K : ℕ, 1 ≤ K →
        Nonempty (ScalarPriors K (endpointScale c₀ K) q gap) := by
  obtain ⟨c₀, δ, hc₀, hc₁, hδ, happrox⟩ :=
    exists_inverseRationalApproxGap q hq₀ hq₁
  refine ⟨c₀, δ, hc₀, hc₁, hδ, ?_⟩
  exact exists_scalarPriors_of_inverseGap hq₀ hc₀ hδ
    (by simpa only [endpointScale] using happrox)

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
