module
public import Causalean.Tactic.Attr
public import Causalean.Tactic.CondexpLinearity
public import Causalean.Tactic.IndicatorSimps
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Tactic.SumAlgebraSimps
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic

/-!
# Multinomial count-vector identities

Factorial-normalized weights over a fixed count degree collapse by the multinomial theorem.
-/

public section

namespace Causalean.Mathlib.Data.Nat.Choose

/-- For [a finite coordinate type](hyp:I), [real coordinate rates](hyp:rate), and
a [total degree](hyp:r), the sum of factorial-normalized monomials over count
vectors of that degree is the corresponding multinomial coefficient. The result is [the fixed-degree multinomial identity](goal). -/
lemma factorial_countVector_fixed_degree_sum {I : Type*} [Fintype I] [DecidableEq I]
    (rate : I → ℝ) (r : ℕ) :
    (∑ counts ∈ (Finset.univ : Finset I).piAntidiag r,
      ∏ i : I, rate i ^ counts i / (counts i).factorial) =
      (∑ i : I, rate i) ^ r / (r.factorial : ℝ) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro counts hc
  have hsum : ∑ i : I, counts i = r := (Finset.mem_piAntidiag.mp hc).1
  have hspec : (∏ i : I, ((counts i).factorial : ℝ)) *
      (Nat.multinomial Finset.univ counts : ℝ) = (r.factorial : ℝ) := by
    exact_mod_cast (hsum ▸ Nat.multinomial_spec Finset.univ counts)
  have hprod : (∏ i : I, ((counts i).factorial : ℝ)) ≠ 0 := by positivity
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hprod (by positivity)).mpr
  rw [← hspec]
  ring



end Causalean.Mathlib.Data.Nat.Choose
