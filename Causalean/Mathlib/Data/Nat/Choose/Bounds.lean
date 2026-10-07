module
public import Causalean.Tactic.Attr
public import Causalean.Tactic.CondexpLinearity
public import Causalean.Tactic.IndicatorSimps
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Tactic.SumAlgebraSimps
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# A power bound for ratios of binomial coefficients

For natural numbers k ≤ U ≤ M, the ratio of binomial coefficients C(U, k) / C(M, k) is at most
(U/M)^k, in any linearly ordered field. Equivalently, the probability that k draws without
replacement from M items all land in a fixed subset of size U is at most the corresponding
probability for draws with replacement.

## Main results

* `choose_div_choose_le_div_pow` — C(U, k) / C(M, k) ≤ (U/M)^k for k ≤ U ≤ M.
-/

public section

namespace Causalean.Mathlib.Data.Nat.Choose

/-- In [an ordered field](hyp:K), for [natural numbers `U`, `M`, and `k`](hyp:U,M,k)
with [`U ≤ M` and `k ≤ U`](hyp:hUM,hk), [the ratio of their `k`th binomial
coefficients is at most the `k`th power of `U / M`](goal). -/
lemma choose_div_choose_le_div_pow {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (U M k : ℕ) (hUM : U ≤ M) (hk : k ≤ U) :
    (U.choose k : K) / (M.choose k : K) ≤ ((U : K) / M) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkU : k < U := by omega
    have hkM : k < M := by omega
    have hMc : (0 : K) < (M.choose k : K) := by
      exact_mod_cast Nat.choose_pos hkM.le
    have hMcs : (0 : K) < (M.choose (k + 1) : K) := by
      exact_mod_cast Nat.choose_pos (by omega : k + 1 ≤ M)
    have hMk : (0 : K) < ((M - k : ℕ) : K) := by
      exact_mod_cast (by omega : 0 < M - k)
    have hMr : (0 : K) < M := by exact_mod_cast (by omega : 0 < M)
    have hUr : (U : K) ≤ M := by exact_mod_cast hUM
    have hrecU : (U.choose (k + 1) : K) * (k + 1 : K) =
        (U.choose k : K) * ((U - k : ℕ) : K) := by
      exact_mod_cast Nat.choose_succ_right_eq U k
    have hrecM : (M.choose (k + 1) : K) * (k + 1 : K) =
        (M.choose k : K) * ((M - k : ℕ) : K) := by
      exact_mod_cast Nat.choose_succ_right_eq M k
    have hratio : (U.choose (k + 1) : K) / (M.choose (k + 1) : K) =
        ((U.choose k : K) / (M.choose k : K)) *
          (((U - k : ℕ) : K) / ((M - k : ℕ) : K)) := by
      apply (div_eq_iff hMcs.ne').mpr
      field_simp
      nlinarith [hrecU, hrecM]
    have hfrac : ((U - k : ℕ) : K) / ((M - k : ℕ) : K) ≤ (U : K) / M := by
      rw [div_le_div_iff₀ hMk hMr, Nat.cast_sub hkU.le, Nat.cast_sub hkM.le]
      nlinarith
    rw [hratio, pow_succ]
    exact mul_le_mul (ih hkU.le) hfrac (by positivity) (by positivity)

end Causalean.Mathlib.Data.Nat.Choose
