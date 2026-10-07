module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Markov
public import Mathlib

/-!
# Rational approximation with an inverse basis function

The scalar construction needs a uniform lower bound for approximation of
`x/(x+qa)` by `α/x + P(x)` on `[a,1]`, with `a=c₀/K²` and
`P` of degree at most `3K`.  This is stronger than ordinary polynomial
approximation and is the analytic input to inverse moment matching.
-/

public section

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

private theorem poly_diff_bound (P : Polynomial ℝ) (n : ℕ)
    (hn : P.natDegree ≤ n) {a b x : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc a b, |P.eval t| ≤ M) :
    |P.eval x - P.eval a| ≤
      (2 * (n : ℝ)^2 / (b-a) * M) * (x-a) := by
  have hsup : intervalSupNorm (fun t => P.eval t) a b ≤ M :=
    (intervalSupNorm_le_iff P.continuous.continuousOn hab.le).2 hM
  have hmark := markov_derivative_Icc P hab n hn
  have hderiv : ∀ t ∈ Set.Ico a b,
      ‖P.derivative.eval t‖ ≤ 2 * (n : ℝ)^2 / (b-a) * M := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := ⟨ht.1, ht.2.le⟩
    have h := (intervalSupNorm_le_iff P.derivative.continuous.continuousOn hab.le).1 hmark t ht'
    simp only [Real.norm_eq_abs] at h ⊢
    exact h.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
  have hhas : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun z => P.eval z) (P.derivative.eval t) (Set.Icc a b) t := by
    intro t _
    exact (P.hasDerivAt t).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hhas hderiv x ⟨hax, hxb⟩
  simpa only [Real.norm_eq_abs] using h

/- At the points `a`, `2a`, and `4a`, the weights `1,-3,2`
  annihilate both a constant and the inverse basis function. Markov's
  inequality bounds the polynomial's variation across these points. -/

/-- For [a positive coefficient q no larger than one](hyp:q,hq₀,hq₁), [there are a scale constant c₀ strictly between zero and one and an error constant δ > 0 such that, for every positive integer K, every real number α, and every real polynomial P of degree at most 3K, the function x / (x + q·c₀/K²) differs in absolute value from α / x + P(x) by at least δ at some point x of the interval from c₀/K² to 1](goal). -/
theorem exists_inverseRationalApproxGap (q : ℝ) (hq₀ : 0 < q) (hq₁ : q ≤ 1) :
    ∃ c₀ δ : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 0 < δ ∧
      ∀ K : ℕ, 1 ≤ K → ∀ α : ℝ, ∀ P : Polynomial ℝ,
        P.natDegree ≤ 3 * K →
          ∃ x ∈ Set.Icc (c₀ / (K : ℝ) ^ 2) 1,
            δ ≤ |x / (x + q * (c₀ / (K : ℝ) ^ 2)) -
              (α / x + P.eval x)| := by
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (le_of_lt hq₀) (sub_nonneg.mpr hq₁)]
  refine ⟨q ^ 2 / 100000, q ^ 2 / 1000, by positivity, ?_, by positivity, ?_⟩
  · nlinarith
  intro K hK α P hP
  let c : ℝ := q ^ 2 / 100000
  let δ : ℝ := q ^ 2 / 1000
  let a : ℝ := c / (K : ℝ) ^ 2
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcsmall : c ≤ (1 : ℝ) / 100000 := by
    dsimp [c]
    nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have haK : a * (K : ℝ) ^ 2 = c := by
    dsimp [a]
    field_simp
  have ha4 : 4 * a ≤ 1 := by
    have hKsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hca : a ≤ c := by
      apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hKsq) (le_of_lt hcpos)]
    linarith
  have ha1 : a < 1 := by linarith
  have hhalf : (1 : ℝ) / 2 ≤ 1 - a := by linarith
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ (1 : ℝ) / 1000 := by
    dsimp [δ]
    nlinarith
  by_contra hnone
  push Not at hnone
  have herr (x : ℝ) (hx : x ∈ Set.Icc a 1) :
      |x / (x + q * a) - (α / x + P.eval x)| < δ := by
    simpa only [a, c, δ] using hnone x hx
  have htarget (x : ℝ) (hx : x ∈ Set.Icc a 1) :
      0 ≤ x / (x + q * a) ∧ x / (x + q * a) ≤ 1 := by
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hden : 0 < x + q * a := by positivity
    constructor
    · exact div_nonneg hxpos.le hden.le
    · exact (div_le_one hden).2 (by nlinarith [mul_nonneg (le_of_lt hq₀) (le_of_lt ha)])
  let A : ℝ := |α / a|
  let M : ℝ := 1 + δ + A
  have hMpos : 0 ≤ M := by dsimp [M, A]; positivity
  have hM (x : ℝ) (hx : x ∈ Set.Icc a 1) : |P.eval x| ≤ M := by
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hdiv : |α / x| ≤ A := by
      dsimp [A]
      rw [abs_div, abs_div, abs_of_pos hxpos, abs_of_pos ha]
      exact div_le_div_of_nonneg_left (abs_nonneg α) ha hx.1
    have he := (abs_le.mp (le_of_lt (herr x hx)))
    have hd := abs_le.mp hdiv
    have hf := htarget x hx
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith
  have hvar2 := poly_diff_bound P (3 * K) hP ha1
    (show a ≤ 2 * a by linarith) (show 2 * a ≤ 1 by linarith) hM
  have hvar4 := poly_diff_bound P (3 * K) hP ha1
    (show a ≤ 4 * a by linarith) ha4 hM
  have hcoef : 2 / (1-a) ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-a)).2
    linarith
  have hprod : ((3 * (K : ℝ)) ^ 2) * a = 9 * c := by
    nlinarith [haK]
  have hB : (2 * ((3 * (K : ℝ)) ^ 2) / (1-a) * M) * a ≤
      36 * c * M := by
    calc
      _ = (2 / (1-a)) * (((3 * (K : ℝ)) ^ 2) * a) * M := by ring
      _ = (2 / (1-a)) * (9*c) * M := by rw [hprod]
      _ ≤ 4 * (9*c) * M := by gcongr
      _ = 36 * c * M := by ring
  have hv2 : |P.eval (2*a) - P.eval a| ≤ 36 * c * M := by
    calc
      _ ≤ 2 * ((3 * (K : ℝ)) ^ 2) / (1-a) * M * (2*a-a) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hvar2
      _ = (2 * ((3 * (K : ℝ)) ^ 2) / (1-a) * M) * a := by ring
      _ ≤ 36 * c * M := hB
  have hv4 : |P.eval (4*a) - P.eval a| ≤ 108 * c * M := by
    calc
      _ ≤ 2 * ((3 * (K : ℝ)) ^ 2) / (1-a) * M * (4*a-a) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hvar4
      _ = 3 * ((2 * ((3 * (K : ℝ)) ^ 2) / (1-a) * M) * a) := by ring
      _ ≤ 3 * (36 * c * M) := by gcongr
      _ = 108 * c * M := by ring
  have hnode1 : a ∈ Set.Icc a 1 := ⟨le_rfl, ha1.le⟩
  have hnode2 : 2*a ∈ Set.Icc a 1 := ⟨by linarith, by linarith⟩
  have hnode4 : 4*a ∈ Set.Icc a 1 := ⟨by linarith, ha4⟩
  have he1 := abs_le.mp (le_of_lt (herr a hnode1))
  have he2 := abs_le.mp (le_of_lt (herr (2*a) hnode2))
  have he4 := abs_le.mp (le_of_lt (herr (4*a) hnode4))
  have hf1 := htarget a hnode1
  have hf2 := htarget (2*a) hnode2
  have hf4 := htarget (4*a) hnode4
  have hα2 : α / (2*a) = (α/a)/2 := by field_simp
  have hα4 : α / (4*a) = (α/a)/4 := by field_simp
  have hA : A ≤ 2 + 4*δ + 72*c*M := by
    have hv := abs_le.mp hv2
    have habs : |α/a| ≤ 2 + 4*δ + 72*c*M := by
      apply abs_le.mpr
      rw [hα2] at he2
      constructor <;> linarith
    exact habs
  have hcs : c ≤ (1 : ℝ) / 144 := by linarith
  have hMbound : M ≤ 6 + 10*δ := by
    have hcm : 72*c*M ≤ M/2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcs) hMpos]
    change 1 + δ + A ≤ 6 + 10*δ
    change |α/a| ≤ 2 + 4*δ + 72*c*M at hA
    linarith
  have hMseven : M ≤ 7 := by linarith
  have hrat1 : a / (a + q*a) = 1/(1+q) := by
    have hd : 0 < 1+q := by positivity
    field_simp
  have hrat2 : (2*a) / (2*a + q*a) = 2/(2+q) := by
    have hd : 0 < 2+q := by positivity
    field_simp
  have hrat4 : (4*a) / (4*a + q*a) = 4/(4+q) := by
    have hd : 0 < 4+q := by positivity
    field_simp
  let D : ℝ := 1/(1+q) - 3*(2/(2+q)) + 2*(4/(4+q))
  have hDup : D ≤ 6*δ + 324*c*M := by
    have hv2' := abs_le.mp hv2
    have hv4' := abs_le.mp hv4
    dsimp [D]
    rw [← hrat1, ← hrat2, ← hrat4]
    rw [hα2] at he2
    rw [hα4] at he4
    linarith
  have hDformula :
      D = 3*q^2 / ((q+1)*(q+2)*(q+4)) := by
    dsimp [D]
    have h1 : q+1 ≠ 0 := ne_of_gt (by positivity)
    have h2 : q+2 ≠ 0 := ne_of_gt (by positivity)
    have h4 : q+4 ≠ 0 := ne_of_gt (by positivity)
    field_simp [h1,h2,h4]
    ring
  have hdenpos : 0 < (q+1)*(q+2)*(q+4) := by positivity
  have hdenle : (q+1)*(q+2)*(q+4) ≤ 30 := by
    have h1 : q+1 ≤ (2:ℝ) := by linarith only [hq₁]
    have h2 : q+2 ≤ (3:ℝ) := by linarith only [hq₁]
    have h4 : q+4 ≤ (5:ℝ) := by linarith only [hq₁]
    have hp2 : 0 ≤ q+2 := by linarith only [hq₀]
    have hp4 : 0 ≤ q+4 := by linarith only [hq₀]
    calc
      _ ≤ 2*(q+2)*(q+4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hp2) hp4
      _ ≤ 2*3*(q+4) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2 (by norm_num)) hp4
      _ ≤ 2*3*5 := by linarith only [h4]
      _ = 30 := by norm_num
  have hDlo : q^2/10 ≤ D := by
    rw [hDformula]
    apply (le_div_iff₀ hdenpos).2
    nlinarith only [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hdenle)]
  have hsmallgap : 6*δ + 324*c*M < q^2/10 := by
    have hcm : c*M ≤ 7*q^2/100000 := by
      dsimp [c]
      nlinarith only [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hMseven)]
    dsimp [δ]
    nlinarith only [hcm, sq_pos_of_pos hq₀]
  linarith only [hDup, hDlo, hsmallgap]

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
