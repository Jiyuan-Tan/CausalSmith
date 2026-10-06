module
public import Causalean.Stat.Concentration.BoundedVariation.SignMGF

/-!
# Tail bound for a finite signed sum

An exponential-moment estimate gives a Gaussian tail for the uniform law on
Boolean sign vectors. This is the first step toward a finite-class squared
maximum estimate.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The sign-tail mass](goal) of [a coefficient vector in ℝ^n](hyp:a) at
[a threshold u](hyp:u) is [the fraction of the 2^n sign vectors whose
signed sum has absolute value at least u](step:1).
-/
noncomputable def signTailMass {n : ℕ} (a : Fin n → ℝ) (u : ℝ) : ℝ :=
  (∑ σ : Fin n → Bool,
    if u ≤ |∑ j, (if σ j then (1 : ℝ) else -1) * a j| then (1 : ℝ) else 0) /
    (2 ^ n : ℝ)

/-- For [a nonnegative threshold u](hyp:hu) and a coefficient vector with
[positive sum of squares](hyp:hvar), [the fraction of sign vectors whose
signed sum has absolute value at least u is at most
2·exp(−u^2/(2 times the sum of squared coefficients))](goal), uniformly in
the number of signs.
-/
theorem signTailMass_le {n : ℕ} (a : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hvar : 0 < ∑ j, (a j) ^ 2) :
    signTailMass a u ≤
      2 * Real.exp (-(u ^ 2 / (2 * ∑ j, (a j) ^ 2))) := by
  classical
  let V : ℝ := ∑ j, (a j) ^ 2
  let X : (Fin n → Bool) → ℝ := fun σ =>
    ∑ j, (if σ j then (1 : ℝ) else -1) * a j
  have hV : 0 < V := hvar
  have hVne : V ≠ 0 := ne_of_gt hV
  have hden : 0 ≤ (2 ^ n : ℝ) := by positivity
  have hmarkov (Y : (Fin n → Bool) → ℝ) (t : ℝ) (ht : 0 ≤ t)
      (hmgf : (∑ σ, Real.exp (t * Y σ)) / (2 ^ n : ℝ) ≤
        Real.exp (t ^ 2 / 2 * V)) :
      (∑ σ, if u ≤ Y σ then (1 : ℝ) else 0) / (2 ^ n : ℝ) ≤
        Real.exp (-t * u + t ^ 2 / 2 * V) := by
    calc
      (∑ σ, if u ≤ Y σ then (1 : ℝ) else 0) / (2 ^ n : ℝ) ≤
          (∑ σ, Real.exp (-t * u) * Real.exp (t * Y σ)) / (2 ^ n : ℝ) := by
            apply div_le_div_of_nonneg_right _ hden
            apply Finset.sum_le_sum
            intro σ _
            by_cases hσ : u ≤ Y σ
            · simp only [if_pos hσ]
              calc
                (1 : ℝ) = Real.exp (-t * u) * Real.exp (t * u) := by
                  rw [← Real.exp_add]
                  simp
                _ ≤ Real.exp (-t * u) * Real.exp (t * Y σ) := by
                  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
                  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ ht)
            · simp only [if_neg hσ]
              positivity
      _ = Real.exp (-t * u) * ((∑ σ, Real.exp (t * Y σ)) / (2 ^ n : ℝ)) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ Real.exp (-t * u) * Real.exp (t ^ 2 / 2 * V) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = Real.exp (-t * u + t ^ 2 / 2 * V) := by rw [Real.exp_add]
  let t : ℝ := u / V
  have ht : 0 ≤ t := div_nonneg hu hV.le
  have hopt : -t * u + t ^ 2 / 2 * V = -(u ^ 2 / (2 * V)) := by
    dsimp [t]
    field_simp; ring
  have hpos :
      (∑ σ, if u ≤ X σ then (1 : ℝ) else 0) / (2 ^ n : ℝ) ≤
        Real.exp (-(u ^ 2 / (2 * V))) := by
    rw [← hopt]
    exact hmarkov X t ht (signMGF_le a t)
  have hneg :
      (∑ σ, if u ≤ -X σ then (1 : ℝ) else 0) / (2 ^ n : ℝ) ≤
        Real.exp (-(u ^ 2 / (2 * V))) := by
    rw [← hopt]
    apply hmarkov (fun σ => -X σ) t ht
    simpa only [X, V, mul_neg, neg_mul, neg_sq] using signMGF_le a (-t)
  have hsplit (σ : Fin n → Bool) :
      (if u ≤ |X σ| then (1 : ℝ) else 0) ≤
        (if u ≤ X σ then (1 : ℝ) else 0) +
          (if u ≤ -X σ then (1 : ℝ) else 0) := by
    by_cases hσ : u ≤ |X σ|
    · rcases (le_abs.mp hσ) with hp | hn
      · by_cases hn' : u ≤ -X σ <;> simp [hσ, hp, hn']
      · by_cases hp' : u ≤ X σ <;> simp [hσ, hn, hp']
    · simp only [if_neg hσ]
      positivity
  calc
    signTailMass a u =
        (∑ σ, if u ≤ |X σ| then (1 : ℝ) else 0) / (2 ^ n : ℝ) := rfl
    _ ≤ (∑ σ, ((if u ≤ X σ then (1 : ℝ) else 0) +
          (if u ≤ -X σ then (1 : ℝ) else 0))) / (2 ^ n : ℝ) := by
        apply div_le_div_of_nonneg_right _ hden
        exact Finset.sum_le_sum (fun σ _ => hsplit σ)
    _ = (∑ σ, if u ≤ X σ then (1 : ℝ) else 0) / (2 ^ n : ℝ) +
          (∑ σ, if u ≤ -X σ then (1 : ℝ) else 0) / (2 ^ n : ℝ) := by
        rw [Finset.sum_add_distrib, add_div]
    _ ≤ Real.exp (-(u ^ 2 / (2 * V))) +
          Real.exp (-(u ^ 2 / (2 * V))) := add_le_add hpos hneg
    _ = 2 * Real.exp (-(u ^ 2 / (2 * ∑ j, (a j) ^ 2))) := by
        dsimp [V]
        ring

end Causalean.Stat.Concentration.BoundedVariation
