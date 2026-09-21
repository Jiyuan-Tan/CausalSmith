/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite product-remainder algebra

This file supplies the product-remainder algebra for a higher-order influence function (HOIF)
estimator whose remainder is a *finite sum of products of `m+1` nonnegative factors*.
Writing `δ` for the largest factor, every term of the
remainder is a product of `m+1` factors each `≤ δ`, so the whole remainder is bounded by
`|T|·δ^{m+1}` (with `|T|` the fixed number of terms), and its squared contribution by

  `R² ≤ |T|²·δ^{2(m+1)}`.

The final theorem is a separate generic power-law fact: `K n^{κ-a}` tends to zero whenever
`κ < a`. Connecting its exponent `a` to an order `m`, nuisance rates, or a product remainder
requires an additional argument not supplied here.

This file is purely elementary (finite products of bounded reals + a power-law limit);
it carries no measure theory and is a reusable risk-algebra building block.
-/

public section

namespace Causalean.Stat.Nonparametric.HigherOrderInfluence

open scoped BigOperators
open Filter Topology

/-- **A product of `m+1` factors each in `[0, δ]` is at most `δ^{m+1}`.**
Each factor of a remainder term is nonnegative and bounded by the largest factor `δ`;
multiplying `m+1` of them keeps the product below `δ^{m+1}`. -/
theorem prod_le_pow_of_factors_le {ι : Type*} (e : ι → ℝ) (m : ℕ) (δ : ℝ)
    (s : Finset ℕ) (idx : ℕ → ι)
    (hcard : s.card = m + 1)
    (hnn : ∀ k ∈ s, 0 ≤ e (idx k)) (hle : ∀ k ∈ s, e (idx k) ≤ δ) :
    ∏ k ∈ s, e (idx k) ≤ δ ^ (m + 1) := by
  calc ∏ k ∈ s, e (idx k) ≤ ∏ _k ∈ s, δ :=
        Finset.prod_le_prod (fun k hk => hnn k hk) (fun k hk => hle k hk)
    _ = δ ^ (m + 1) := by rw [Finset.prod_const, hcard]

/-- **Squared finite-product remainder bound.**
The order-`m` remainder `R` is dominated by a sum, over a finite index
set `T` of terms, of products of `m+1` nuisance-error factors `e t k`; every factor lies in
`[0, δ]`, where `δ` is the largest nuisance `L²`-error.  Then the remainder's squared
contribution obeys `R² ≤ |T|²·δ^{2(m+1)}`.  This is the order-`m` doubly-robust bound: the
higher the order, the higher the power of `δ`. -/
theorem productRemainder_sq_le {ι : Type*} (T : Finset ι) (e : ι → ℕ → ℝ)
    (m : ℕ) (δ : ℝ) (R : ℝ)
    (hnn : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), 0 ≤ e t k)
    (hle : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), e t k ≤ δ)
    (hbound : |R| ≤ ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k) :
    R ^ 2 ≤ (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) := by
  -- Each term ≤ δ^{m+1}.
  have hterm : ∀ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k ≤ δ ^ (m + 1) := by
    intro t ht
    calc ∏ k ∈ Finset.range (m + 1), e t k ≤ ∏ _k ∈ Finset.range (m + 1), δ :=
          Finset.prod_le_prod (fun k hk => hnn t ht k hk) (fun k hk => hle t ht k hk)
      _ = δ ^ (m + 1) := by rw [Finset.prod_const, Finset.card_range]
  -- Sum ≤ |T|·δ^{m+1}.
  have hsum_le : ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k
      ≤ (T.card : ℝ) * δ ^ (m + 1) := by
    calc ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k
          ≤ ∑ _t ∈ T, δ ^ (m + 1) := Finset.sum_le_sum hterm
      _ = (T.card : ℝ) * δ ^ (m + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- The sum is nonnegative (sum of products of nonnegatives).
  have hsum_nn : 0 ≤ ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k :=
    Finset.sum_nonneg (fun t ht =>
      Finset.prod_nonneg (fun k hk => hnn t ht k hk))
  -- Square the chain |R| ≤ sum ≤ |T|·δ^{m+1}.
  have hRabs : |R| ≤ (T.card : ℝ) * δ ^ (m + 1) := le_trans hbound hsum_le
  have hR2 : R ^ 2 ≤ ((T.card : ℝ) * δ ^ (m + 1)) ^ 2 := by
    rw [← sq_abs R]
    exact pow_le_pow_left₀ (abs_nonneg R) hRabs 2
  calc R ^ 2 ≤ ((T.card : ℝ) * δ ^ (m + 1)) ^ 2 := hR2
    _ = (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (m + 1) 2]

/-- **A negative power vanishes asymptotically.** For [a real constant `K`](hyp:K) and
[real exponents `a` and `κ`](hyp:a,κ), if [`κ < a`](hyp:haκ), then [`K n^{κ-a}` tends to zero
as `n` tends to infinity](goal). The statement does not choose a remainder order or connect `a`
to the product-remainder bound above. -/
theorem const_mul_natCast_rpow_sub_tendsto_zero {K a κ : ℝ} (haκ : κ < a) :
    Tendsto (fun n : ℕ => K * (n : ℝ) ^ (κ - a)) atTop (𝓝 0) := by
  have hpos : 0 < a - κ := by linarith
  have hbase : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun x : ℝ => x ^ (-(a - κ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hpos
  have hcomp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(a - κ))) atTop (𝓝 0) :=
    hpow.comp hbase
  have := hcomp.const_mul K
  simpa [neg_sub] using this

end Causalean.Stat.Nonparametric.HigherOrderInfluence
