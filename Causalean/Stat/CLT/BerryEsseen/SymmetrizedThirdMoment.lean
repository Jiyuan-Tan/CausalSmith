module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Basic

/-! # Cubic moment control for an independent difference

This leaf isolates the moment ingredient of Prawitz's modulus estimate.
The independent difference is integrated against the product law explicitly.
The polynomial majorant needs only third moments and products of second
moments; it does not require a fourth moment of either marginal.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

private theorem nonneg_cube_bound (a b : ℝ) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b ≤ a) :
    |a - b| ^ 3 ≤ a ^ 3 + b ^ 3 - 2 * a * b * (a + b) +
      a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have hd : 0 ≤ a - b := sub_nonneg.mpr hab
  have hmargin : 0 ≤ a ^ 3 + b ^ 3 - 2 * a * b * (a + b) +
      a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) / 2 - (a - b) ^ 3 := by
    by_cases hb1 : b ≤ 1
    · rw [show a ^ 3 + b ^ 3 - 2 * a * b * (a + b) +
          a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) / 2 - (a - b) ^ 3 =
          (a * b - b) ^ 2 + b * (a - b) * (1 - b) +
            (a - b) ^ 2 * (b + 1 / 2) by ring]
      exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg
        (mul_nonneg hb hd) (sub_nonneg.mpr hb1)))
        (mul_nonneg (sq_nonneg _) (by linarith))
    · have hb1' : 0 ≤ b - 1 := by linarith
      rw [show a ^ 3 + b ^ 3 - 2 * a * b * (a + b) +
          a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) / 2 - (a - b) ^ 3 =
          b ^ 2 * (b - 1) ^ 2 + b * (a - b) * (2 * b - 1) * (b - 1) +
            (a - b) ^ 2 * (b ^ 2 + b + 1 / 2) by ring]
      exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (mul_nonneg hb hd) (by linarith)) hb1'))
        (mul_nonneg (sq_nonneg _) (by positivity))
  linarith

/-- The [absolute cube of a difference of two real numbers](hyp:x,y) is
[bounded by a polynomial whose mixed linear terms cancel under centering](goal). -/
theorem abs_sub_cube_le_moment_polynomial (x y : ℝ) :
    |x - y| ^ 3 ≤ |x| ^ 3 + |y| ^ 3 - 2 * x * y * (|x| + |y|) +
      x ^ 2 * y ^ 2 + (x ^ 2 + y ^ 2) / 2 := by
  have hsame (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      |a - b| ^ 3 ≤ a ^ 3 + b ^ 3 - 2 * a * b * (a + b) +
        a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) / 2 := by
    by_cases hab : b ≤ a
    · exact nonneg_cube_bound a b ha hb hab
    · have h := nonneg_cube_bound b a hb ha (le_of_not_ge hab)
      rw [abs_sub_comm] at h
      nlinarith [h]
  have hopposite (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a + b) ^ 3 ≤ a ^ 3 + b ^ 3 + 2 * a * b * (a + b) +
        a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (a * b - (a + b) / 2), sq_nonneg (a - b)]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simpa only [abs_of_nonneg hx, abs_of_nonneg hy] using hsame x y hx hy
  · have h := hopposite x (-y) hx (neg_nonneg.mpr hy)
    rw [abs_of_nonneg hx, abs_of_nonpos hy,
      abs_of_nonneg (show 0 ≤ x - y by linarith)]
    nlinarith [h]
  · have h := hopposite (-x) y (neg_nonneg.mpr hx) hy
    rw [abs_of_nonpos hx, abs_of_nonneg hy,
      abs_of_nonpos (show x - y ≤ 0 by linarith)]
    nlinarith [h]
  · have h := hsame (-x) (-y) (neg_nonneg.mpr hx) (neg_nonneg.mpr hy)
    have he : |(-x) - (-y)| = |x - y| := by
      rw [neg_sub_neg, abs_sub_comm]
    rw [he] at h
    rw [abs_of_nonpos hx, abs_of_nonpos hy]
    nlinarith [h]

/-- For [a centered probability law](hyp:μ,hmean_int,hmean) with
[unit second moment](hyp:hvar_int,hvar) and
[integrable third absolute moment](hyp:hthird_int), [the difference of two
independent draws has an integrable absolute cube whose expectation is at
most twice the marginal third absolute moment plus two](goal). -/
theorem symmetrized_unit_third_moment_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (μ.prod μ) ∧
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂μ.prod μ) ≤
        2 * ((∫ x : ℝ, |x| ^ 3 ∂μ) + 1) := by
  -- The signed absolute-square factor needs only the second moment.
  have hsigned : Integrable (fun x : ℝ => x * |x|) μ := by
    refine hvar_int.mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
    intro x
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, ← pow_two, sq_abs]
    exact le_refl _
  have h₃₁ := hthird_int.comp_fst μ
  have h₃₂ := hthird_int.comp_snd μ
  have h₂₁ := hvar_int.comp_fst μ
  have h₂₂ := hvar_int.comp_snd μ
  have hm₁ := hsigned.mul_prod hmean_int
  have hm₂ := hmean_int.mul_prod hsigned
  have h₂₂prod := hvar_int.mul_prod hvar_int
  let P : ℝ × ℝ → ℝ := fun p =>
    (|p.1| ^ 3 + |p.2| ^ 3) -
      2 * ((p.1 * |p.1|) * p.2 + p.1 * (p.2 * |p.2|)) +
      p.1 ^ 2 * p.2 ^ 2 + (p.1 ^ 2 + p.2 ^ 2) / 2
  have hP : Integrable P (μ.prod μ) :=
    (((h₃₁.add h₃₂).sub ((hm₁.add hm₂).const_mul 2)).add h₂₂prod).add
      ((h₂₁.add h₂₂).div_const 2)
  have hbound (p : ℝ × ℝ) : |p.1 - p.2| ^ 3 ≤ P p := by
    calc
      _ ≤ |p.1| ^ 3 + |p.2| ^ 3 - 2 * p.1 * p.2 * (|p.1| + |p.2|) +
          p.1 ^ 2 * p.2 ^ 2 + (p.1 ^ 2 + p.2 ^ 2) / 2 :=
        abs_sub_cube_le_moment_polynomial p.1 p.2
      _ = P p := by dsimp [P]; ring
  have hdiff : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (μ.prod μ) := by
    refine hP.mono_nonneg (by fun_prop) (Filter.Eventually.of_forall ?_)
      (Filter.Eventually.of_forall hbound)
    intro p
    positivity
  refine ⟨hdiff, (integral_mono hdiff hP (fun p => hbound p)).trans ?_⟩
  change (∫ p : ℝ × ℝ,
    (|p.1| ^ 3 + |p.2| ^ 3) -
      2 * ((p.1 * |p.1|) * p.2 + p.1 * (p.2 * |p.2|)) +
      p.1 ^ 2 * p.2 ^ 2 + (p.1 ^ 2 + p.2 ^ 2) / 2 ∂μ.prod μ) ≤ _
  have hsum : Integrable (fun p : ℝ × ℝ => |p.1| ^ 3 + |p.2| ^ 3) (μ.prod μ) :=
    h₃₁.add h₃₂
  have hmix : Integrable (fun p : ℝ × ℝ =>
      2 * ((p.1 * |p.1|) * p.2 + p.1 * (p.2 * |p.2|))) (μ.prod μ) :=
    (hm₁.add hm₂).const_mul 2
  have hsub : Integrable (fun p : ℝ × ℝ =>
      (|p.1| ^ 3 + |p.2| ^ 3) -
        2 * ((p.1 * |p.1|) * p.2 + p.1 * (p.2 * |p.2|))) (μ.prod μ) :=
    hsum.sub hmix
  have hmain : Integrable (fun p : ℝ × ℝ =>
      (|p.1| ^ 3 + |p.2| ^ 3) -
        2 * ((p.1 * |p.1|) * p.2 + p.1 * (p.2 * |p.2|)) +
        p.1 ^ 2 * p.2 ^ 2) (μ.prod μ) := hsub.add h₂₂prod
  have hhalf : Integrable (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2)
      (μ.prod μ) := (h₂₁.add h₂₂).div_const 2
  rw [integral_add hmain hhalf, integral_add hsub h₂₂prod,
    integral_sub hsum hmix, integral_add h₃₁ h₃₂,
    integral_const_mul, integral_add hm₁ hm₂, integral_div,
    integral_add h₂₁ h₂₂]
  rw [integral_prod_mul (fun x : ℝ => x * |x|) (fun y : ℝ => y),
    integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y * |y|),
    integral_prod_mul (fun x : ℝ => x ^ 2) (fun y : ℝ => y ^ 2),
    integral_fun_fst (fun x : ℝ => |x| ^ 3),
    integral_fun_snd (fun x : ℝ => |x| ^ 3),
    integral_fun_fst (fun x : ℝ => x ^ 2),
    integral_fun_snd (fun x : ℝ => x ^ 2)]
  simp only [probReal_univ, one_smul, hmean, hvar, mul_zero, zero_mul,
    zero_add, sub_zero, mul_one]
  linarith

end Causalean.Stat.CLT.BerryEsseen
