module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Four-rate exponential tails

The absolute Taylor coefficients for three marked Poisson counts and the
arrival-mass exponential form a four-rate exponential series. Grouping by
total degree bounds its unmatched terms by a one-dimensional factorial tail.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- A [matching degree](hyp:K) and [four rates](hyp:r) determine [the four-rate factorial tail](goal) by [summing, over all four-tuples of nonnegative integer exponents whose total exceeds three times the matching degree, the product over the four rates of the rate raised to its exponent divided by the factorial of that exponent](step:1). -/
noncomputable def fourRateFactorialTail (K : ℕ) (r : Fin 4 → ℝ) : ℝ :=
  ∑' q : Fin 4 → ℕ,
    if 3 * K < ∑ i, q i then
      ∏ i, r i ^ q i / (Nat.factorial (q i) : ℝ)
    else 0

/- Group the fourfold exponential series by `∑ i, q i` using
  `Finset.sum_pow_eq_sum_piAntidiag` and the factorial formula for
  `Nat.multinomial`. For nonnegative rates, the degree-m coefficient
  is `(∑ i, r i)^m / m!`; compare with `x^m / m!` termwise. -/

/-- A [positive degree](hyp:K,hK), [four nonnegative rates](hyp:r,hr), and [an upper bound on their total rate](hyp:x,hx) give [a four-rate factorial tail no larger than the one-dimensional tail, the sum over all integers exceeding three times the degree of the bound raised to that integer divided by its factorial](goal). -/
theorem fourRateFactorialTail_le (K : ℕ) (hK : 1 ≤ K)
    (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (x : ℝ) (hx : ∑ i, r i ≤ x) :
    fourRateFactorialTail K r ≤
      ∑' m : ℕ, if 3 * K < m then x ^ m / (Nat.factorial m : ℝ) else 0 := by
  classical
  have _hK : 1 ≤ K := hK
  let s (m : ℕ) : Finset (Fin 4 → ℕ) := Finset.piAntidiag Finset.univ m
  let a (q : Fin 4 → ℕ) : ℝ := ∏ i, r i ^ q i / (Nat.factorial (q i) : ℝ)
  let f (q : Fin 4 → ℕ) : ℝ :=
    if 3 * K < ∑ i, q i then a q else 0
  have ha (q : Fin 4 → ℕ) : 0 ≤ a q := by
    dsimp [a]
    apply Finset.prod_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (hr i) _) (by positivity)
  have hf (q : Fin 4 → ℕ) : 0 ≤ f q := by
    dsimp [f]
    split_ifs with h
    · exact ha q
    · exact le_refl 0
  have hs_mem (m : ℕ) (q : Fin 4 → ℕ) :
      q ∈ s m ↔ (∑ i, q i) = m := by
    simp [s, Finset.mem_piAntidiag]
  have hfactor (q : Fin 4 → ℕ) :
      a q = (Nat.multinomial Finset.univ q : ℝ) *
        (∏ i, r i ^ q i) / (Nat.factorial (∑ i, q i) : ℝ) := by
    have hn := Nat.multinomial_spec (Finset.univ : Finset (Fin 4)) q
    have hn' : (∏ i, (Nat.factorial (q i) : ℝ)) *
        (Nat.multinomial Finset.univ q : ℝ) =
        (Nat.factorial (∑ i, q i) : ℝ) := by exact_mod_cast hn
    dsimp [a]
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [← hn']
    ring
  have hdegree (m : ℕ) :
      ∑ q ∈ s m, a q = (∑ i, r i) ^ m / (Nat.factorial m : ℝ) := by
    calc
      ∑ q ∈ s m, a q =
          ∑ q ∈ s m, (Nat.multinomial Finset.univ q : ℝ) *
            (∏ i, r i ^ q i) / (Nat.factorial m : ℝ) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [hfactor q, (hs_mem m q).mp hq]
      _ = (∑ i, r i) ^ m / (Nat.factorial m : ℝ) := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul]
            rw [Finset.sum_pow_eq_sum_piAntidiag]
  have hfiber (m : ℕ) :
      ∑' q : {q // q ∈ s m}, f q =
        if 3 * K < m then (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0 := by
    rw [Finset.tsum_subtype (s m) f]
    by_cases hm : 3 * K < m
    · simp only [if_pos hm]
      rw [← hdegree m]
      apply Finset.sum_congr rfl
      intro q hq
      simp [f, (hs_mem m q).mp hq, hm]
    · simp only [if_neg hm]
      apply Finset.sum_eq_zero
      intro q hq
      simp [f, (hs_mem m q).mp hq, hm]
  have hbase : Summable (fun m : ℕ =>
      if 3 * K < m then (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0) :=
    by
      have heq : (fun m : ℕ =>
          if 3 * K < m then (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0) =
          ({m : ℕ | 3 * K < m}.indicator fun m =>
            (∑ i, r i) ^ m / (Nat.factorial m : ℝ)) := by
        funext m
        simp [Set.indicator_apply]
      rw [heq]
      exact (Real.summable_pow_div_factorial (∑ i, r i)).indicator
        {m : ℕ | 3 * K < m}
  have houter : Summable (fun m : ℕ => ∑' q : {q // q ∈ s m}, f q) := by
    simpa only [hfiber] using hbase
  have hsum : Summable f := by
    apply (summable_partition hf (s := fun m => (s m : Set (Fin 4 → ℕ))) (by
      intro q
      refine ⟨∑ i, q i, ?_, ?_⟩
      · exact (hs_mem _ _).2 rfl
      · intro m hm
        exact (hs_mem _ _).1 hm |>.symm)).2
    constructor
    · intro m
      haveI : Finite (s m : Set (Fin 4 → ℕ)) := (s m).finite_toSet.to_subtype
      exact Summable.of_finite
    · simpa only [Finset.coe_sort_coe] using houter
  have hgroup :
      fourRateFactorialTail K r =
        ∑' m : ℕ, if 3 * K < m then
          (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0 := by
    change (∑' q, f q) = _
    have hF := hsum.hasSum.tsum_fiberwise (fun q => ∑ i, q i)
    rw [← hF.tsum_eq]
    apply tsum_congr
    intro m
    rw [show (fun q : Fin 4 → ℕ => ∑ i, q i) ⁻¹' {m} =
        (s m : Set (Fin 4 → ℕ)) by ext q; simp [hs_mem]]
    exact hfiber m
  rw [hgroup]
  apply hbase.tsum_le_tsum
  · intro m
    by_cases hm : 3 * K < m
    · simp only [if_pos hm]
      apply div_le_div_of_nonneg_right
      · exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hr i) hx m
      · positivity
    · simp [hm]
  · have heq : (fun m : ℕ =>
        if 3 * K < m then x ^ m / (Nat.factorial m : ℝ) else 0) =
        ({m : ℕ | 3 * K < m}.indicator fun m =>
          x ^ m / (Nat.factorial m : ℝ)) := by
        funext m
        simp [Set.indicator_apply]
    rw [heq]
    exact (Real.summable_pow_div_factorial x).indicator {m : ℕ | 3 * K < m}

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
