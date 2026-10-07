/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.Envelope

/-!
# Affine envelopes for population-localized finite-VC classes

With q = (d·log(n+1) + 1)/n, the envelope of a class of VC dimension at most d
bounded by b, localized in L²(P), is the affine function

    ψ(r) = 2·√q·r + 16·b·q.

An affine function with nonnegative slope and intercept is a star-shaped
envelope (nonnegative, nondecreasing, ψ(r)/r nonincreasing), and its critical
radius r*, the infimum of r > 0 with ψ(r) ≤ r², satisfies r*² ≤ 8·(s² + a).

Remark (not proved in Lean): under population localization no envelope of the
form s·r can hold. For the class of indicators of intervals under an atomless
law, every radius r > 0 admits intervals of L²(P) norm below r that contain
exactly one sample point, so the localized Rademacher complexity is at least of
order 1/n however small r is.

## Main definitions

* `vcPopulationLocalizedPsi` — the affine envelope ψ.

## Main results

* `affine_isStarShapedEnvelope`, `criticalRadius_affine_sq_le` — affine envelopes.
* `criticalRadius_vcPopulationLocalizedPsi_sq_le_rate` — r*² ≤ (32 + 128·b)·q.
-/

@[expose] public section

namespace Causalean.Stat.Concentration


/-- [The population-localized finite-VC envelope](goal) for [uniform bound b](hyp:b),
[VC dimension d and sample size n](hyp:d,n) is the affine function
ψ(r) = 2·√q·r + 16·b·q of the radius r, where q = (d·log(n+1) + 1)/n. -/
noncomputable def vcPopulationLocalizedPsi (b : ℝ) (d n : ℕ) : ℝ → ℝ :=
  fun r => 2 * Real.sqrt (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) * r +
    16 * b * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n)

/-- For [a slope s ≥ 0](hyp:hs) and [an intercept a ≥ 0](hyp:ha), [the affine function
ψ(r) = s·r + a is a star-shaped envelope: it is nonnegative and nondecreasing on r ≥ 0, and
ψ(r)/r is nonincreasing on r > 0](goal). -/
lemma affine_isStarShapedEnvelope {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    IsStarShapedEnvelope (fun r => s * r + a) := by
  refine ⟨fun r hr => by positivity, ?_, ?_⟩
  · intro r₁ r₂ _ h
    linarith [mul_le_mul_of_nonneg_left h hs]
  · intro r₁ r₂ h₁ h₁₂
    have h₂ : 0 < r₂ := h₁.trans_le h₁₂
    apply (div_le_div_iff₀ h₂ h₁).2
    nlinarith [mul_le_mul_of_nonneg_left h₁₂ ha]

/-- For [a uniform bound b ≥ 0](hyp:hb) and [every VC dimension d and sample size n](hyp:d,n),
[the envelope ψ(r) = 2·√q·r + 16·b·q, with q = (d·log(n+1) + 1)/n, is star-shaped: it is
nonnegative and nondecreasing on r ≥ 0, and ψ(r)/r is nonincreasing on r > 0](goal). -/
lemma vcPopulationLocalizedPsi_isStarShapedEnvelope {b : ℝ} (hb : 0 ≤ b)
    (d n : ℕ) : IsStarShapedEnvelope (vcPopulationLocalizedPsi b d n) := by
  unfold vcPopulationLocalizedPsi
  apply affine_isStarShapedEnvelope
  · positivity
  · apply mul_nonneg (mul_nonneg (by norm_num) hb)
    simpa using vcLocalizedRate_nonneg (K := 1) (d := d) (n := n) (by norm_num)

/-- For [a slope s ≥ 0](hyp:hs) and [an intercept a ≥ 0](hyp:ha), [the critical radius r* of
ψ(r) = s·r + a, the infimum of r > 0 with ψ(r) ≤ r², satisfies r*² ≤ 8·(s² + a)](goal). -/
lemma criticalRadius_affine_sq_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    criticalRadius (fun r => s * r + a) ^ 2 ≤ 8 * (s ^ 2 + a) := by
  have ht : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have ht_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hc : 0 ≤ criticalRadius (fun r => s * r + a) := criticalRadius_nonneg _
  by_cases hpos : 0 < 2 * s + 2 * Real.sqrt a
  · have hle : criticalRadius (fun r => s * r + a) ≤
        2 * s + 2 * Real.sqrt a := by
      apply criticalRadius_le hpos
      nlinarith [mul_nonneg hs ht]
    have hw : (2 * s + 2 * Real.sqrt a) ^ 2 ≤ 8 * (s ^ 2 + a) := by
      nlinarith [sq_nonneg (s - Real.sqrt a)]
    nlinarith
  · have hs0 : s = 0 := by linarith
    have ht0 : Real.sqrt a = 0 := by linarith
    have ha0 : a = 0 := by nlinarith
    have hzero : criticalRadius (fun r => s * r + a) ≤ 0 := by
      by_contra h
      have hδ : 0 < criticalRadius (fun r => s * r + a) / 2 := by linarith
      have hle := criticalRadius_le (ψ := fun r => s * r + a) hδ
        (by simp only [hs0, ha0, zero_mul, zero_add]; positivity)
      linarith
    rw [le_antisymm hzero hc]
    simp [hs0, ha0]

/-- For [a uniform bound b ≥ 0](hyp:hb) and [every VC dimension d and sample size n](hyp:d,n),
[the critical radius r* of the envelope ψ(r) = 2·√q·r + 16·b·q, the infimum of r > 0 with
ψ(r) ≤ r², satisfies r*² ≤ (32 + 128·b)·q, where q = (d·log(n+1) + 1)/n](goal).

For b = 1 the constant is 160. -/
theorem criticalRadius_vcPopulationLocalizedPsi_sq_le_rate {b : ℝ} (hb : 0 ≤ b)
    (d n : ℕ) :
    criticalRadius (vcPopulationLocalizedPsi b d n) ^ 2 ≤
      (32 + 128 * b) * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) := by
  let q : ℝ := ((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n
  have hq : 0 ≤ q := by
    simpa [q] using vcLocalizedRate_nonneg (K := 1) (d := d) (n := n) (by norm_num)
  have hle := criticalRadius_affine_sq_le
    (s := 2 * Real.sqrt q) (a := 16 * b * q)
    (by positivity) (by positivity)
  change criticalRadius (fun r => 2 * Real.sqrt q * r + 16 * b * q) ^ 2 ≤
    (32 + 128 * b) * q
  calc
    _ ≤ 8 * ((2 * Real.sqrt q) ^ 2 + 16 * b * q) := hle
    _ = (32 + 128 * b) * q := by rw [mul_pow, Real.sq_sqrt hq]; ring

end Causalean.Stat.Concentration
