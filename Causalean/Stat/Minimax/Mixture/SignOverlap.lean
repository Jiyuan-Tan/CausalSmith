module
public import Causalean.Stat.Concentration.BoundedVariation.SignMGF

/-!
# Exponential bounds for averages over pairs of sign vectors

When two hypotheses are drawn independently and uniformly from the `2^K` sign vectors in
`{−1, +1}^K`, the chi-square (second-moment) computation for the resulting mixture reduces to an
average of powers of `1 + ρ ⟨s, t⟩ / K` over all pairs `(s, t)`. This module bounds such averages:
for two sample sizes `n₁`, `n₂` and overlap coefficients `ρ₁`, `ρ₂` with nonnegative bases,

    average over (s, t) of (1 + ρ₁⟨s,t⟩/K)^n₁ (1 + ρ₂⟨s,t⟩/K)^n₂ ≤ exp((n₁ρ₁ + n₂ρ₂)² / (2K)).

## Main definitions and results

* `innerSign` — the inner product `⟨s, t⟩` of two Boolean vectors read as ±1 signs.
* `uniform_innerSign_exp_le` — the average of `exp(t ⟨s,u⟩ / K)` over pairs is at most
  `exp(t² / (2K))`.
* `sign_twoPower_pointwise_le_exp` — `(1 + ρ₁x)^n₁ (1 + ρ₂x)^n₂ ≤ exp((n₁ρ₁ + n₂ρ₂) x)`.
* `uniform_sign_twoPower_le_exp` — the displayed two-sample bound.
-/
@[expose] public section
namespace Causalean.Stat.Minimax.Mixture.SignOverlap
open scoped BigOperators
/-- Given [a sign-vector length](hyp:K) and [two Boolean sign vectors](hyp:s,t),
[the inner sign product](goal) is given by [summing coordinatewise products after
interpreting Boolean values as plus or minus one](step:1). -/
def innerSign {K : ℕ} (s t : Fin K → Bool) : ℝ :=
  ∑ j : Fin K, (if s j then (1 : ℝ) else -1) * (if t j then (1 : ℝ) else -1)
/-- Given [two sample sizes](hyp:n₁,n₂), [two overlap coefficients](hyp:ρ₁,ρ₂),
[an overlap coordinate](hyp:x), and [nonnegative overlap bases](hyp:hbase₁,hbase₂),
[the product of two overlap powers is bounded by its linearized exponential](goal). -/
theorem sign_twoPower_pointwise_le_exp (n₁ n₂ : ℕ) (ρ₁ ρ₂ x : ℝ) (hbase₁ : 0 ≤ 1 + ρ₁ * x) (hbase₂ : 0 ≤ 1 + ρ₂ * x) :
    (1 + ρ₁ * x) ^ n₁ * (1 + ρ₂ * x) ^ n₂ ≤ Real.exp (((n₁ : ℝ) * ρ₁ + (n₂ : ℝ) * ρ₂) * x) := by
  have h₁ : (1 + ρ₁ * x) ^ n₁ ≤ (Real.exp (ρ₁ * x)) ^ n₁ :=
    pow_le_pow_left₀ hbase₁ (by simpa [add_comm] using Real.add_one_le_exp (ρ₁ * x)) _
  have h₂ : (1 + ρ₂ * x) ^ n₂ ≤ (Real.exp (ρ₂ * x)) ^ n₂ :=
    pow_le_pow_left₀ hbase₂ (by simpa [add_comm] using Real.add_one_le_exp (ρ₂ * x)) _
  calc
    (1 + ρ₁ * x) ^ n₁ * (1 + ρ₂ * x) ^ n₂ ≤
        (Real.exp (ρ₁ * x)) ^ n₁ * (Real.exp (ρ₂ * x)) ^ n₂ :=
      mul_le_mul h₁ h₂ (pow_nonneg hbase₂ _) (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp (((n₁ : ℝ) * ρ₁ + (n₂ : ℝ) * ρ₂) * x) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
/-- Given [a positive sign-vector length](hyp:K) and [an exponential coefficient](hyp:t),
[the uniform double average of the scaled inner-sign exponential is bounded by
its Gaussian moment expression](goal). -/
theorem uniform_innerSign_exp_le (K : ℕ) [NeZero K] (t : ℝ) : (∑ s : Fin K → Bool, ∑ u : Fin K → Bool, Real.exp (t *
    innerSign s u / (K : ℝ))) / (Fintype.card (Fin K → Bool) : ℝ) ^ 2 ≤ Real.exp (t ^ 2 / (2 * (K : ℝ))) := by
  classical
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
  have hcard : (Fintype.card (Fin K → Bool) : ℝ) = (2 : ℝ) ^ K := by
    simp [Fintype.card_bool]
  have hinner (s : Fin K → Bool) :
      (∑ u : Fin K → Bool, Real.exp (t * innerSign s u / (K : ℝ))) /
          (Fintype.card (Fin K → Bool) : ℝ) ≤
        Real.exp (t ^ 2 / (2 * (K : ℝ))) := by
    have hswap (u : Fin K → Bool) :
        innerSign s u = ∑ j : Fin K,
          (if u j then (1 : ℝ) else -1) * (if s j then (1 : ℝ) else -1) := by
      unfold innerSign
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hsquares :
        (∑ j : Fin K, (if s j then (1 : ℝ) else -1) ^ 2) = (K : ℝ) := by
      simp
    have hm := Causalean.Stat.Concentration.BoundedVariation.signMGF_le
      (fun j : Fin K => if s j then (1 : ℝ) else -1) (t / (K : ℝ))
    convert hm using 1
    · rw [hcard]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      rw [hswap]
      ring
    · rw [hsquares]
      field_simp
  calc
    (∑ s : Fin K → Bool, ∑ u : Fin K → Bool,
        Real.exp (t * innerSign s u / (K : ℝ))) /
        (Fintype.card (Fin K → Bool) : ℝ) ^ 2 =
        (∑ s : Fin K → Bool,
          (∑ u : Fin K → Bool, Real.exp (t * innerSign s u / (K : ℝ))) /
            (Fintype.card (Fin K → Bool) : ℝ)) /
          (Fintype.card (Fin K → Bool) : ℝ) := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ ≤ (∑ _s : Fin K → Bool, Real.exp (t ^ 2 / (2 * (K : ℝ)))) /
          (Fintype.card (Fin K → Bool) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum fun s _ => hinner s
      · rw [hcard]
        positivity
    _ = Real.exp (t ^ 2 / (2 * (K : ℝ))) := by
      simp [Fintype.card_bool]
/-- Given [a positive sign-vector length and two sample sizes](hyp:K,n₁,n₂),
[two overlap coefficients](hyp:ρ₁,ρ₂), and [bases 1 + ρ₁⟨s,t⟩/K and 1 + ρ₂⟨s,t⟩/K that
are nonnegative for every pair of sign vectors](hyp:hbase₁,hbase₂), where ⟨s,t⟩ is the
inner sign product, [the average over all pairs of sign vectors of
(1 + ρ₁⟨s,t⟩/K)^n₁ · (1 + ρ₂⟨s,t⟩/K)^n₂ is at most exp((n₁ρ₁ + n₂ρ₂)² / (2K))](goal). -/
theorem uniform_sign_twoPower_le_exp (K n₁ n₂ : ℕ) [NeZero K] (ρ₁ ρ₂ : ℝ) (hbase₁ : ∀ s t : Fin K → Bool, 0 ≤ 1 + ρ₁ *
    innerSign s t / (K : ℝ)) (hbase₂ : ∀ s t : Fin K → Bool, 0 ≤ 1 + ρ₂ * innerSign s t / (K : ℝ)) : (∑ s : Fin K →
    Bool, ∑ t : Fin K → Bool, (1 + ρ₁ * innerSign s t / (K : ℝ)) ^ n₁ * (1 + ρ₂ * innerSign s t / (K : ℝ)) ^ n₂) /
    (Fintype.card (Fin K → Bool) : ℝ) ^ 2 ≤ Real.exp (((n₁ : ℝ) * ρ₁ + (n₂ : ℝ) * ρ₂) ^ 2 / (2 * (K : ℝ))) := by
  classical
  have hcard : 0 ≤ (Fintype.card (Fin K → Bool) : ℝ) ^ 2 := by positivity
  calc
    _ ≤ (∑ s : Fin K → Bool, ∑ t : Fin K → Bool,
        Real.exp (((n₁ : ℝ) * ρ₁ + (n₂ : ℝ) * ρ₂) * innerSign s t / (K : ℝ))) /
        (Fintype.card (Fin K → Bool) : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hcard
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      have hb₁ : 0 ≤ 1 + ρ₁ * (innerSign s t / (K : ℝ)) := by
        simpa only [mul_div_assoc] using hbase₁ s t
      have hb₂ : 0 ≤ 1 + ρ₂ * (innerSign s t / (K : ℝ)) := by
        simpa only [mul_div_assoc] using hbase₂ s t
      simpa only [mul_div_assoc] using
        sign_twoPower_pointwise_le_exp n₁ n₂ ρ₁ ρ₂
          (innerSign s t / (K : ℝ)) hb₁ hb₂
    _ ≤ _ := uniform_innerSign_exp_le K ((n₁ : ℝ) * ρ₁ + (n₂ : ℝ) * ρ₂)
end Causalean.Stat.Minimax.Mixture.SignOverlap
