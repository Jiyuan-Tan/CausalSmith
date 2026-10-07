module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Norms
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Cosine orthogonality and explicit best approximation

The orthogonal projection is the actual finite integral formula from Definitions.
The Pythagorean identity supplies best approximation against every rank-k cosine
polynomial, without assuming that a separately chosen Hilbert projection agrees
with the formula. No completeness of the infinite cosine system is needed.
-/

public section

open MeasureTheory
open scoped BigOperators
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- Each [normalized cosine mode](hyp:j) is [continuous on the real line](goal). -/
@[fun_prop]
theorem continuous_cosineBasis (j : ℕ) : Continuous (cosineBasis j) := by
  unfold cosineBasis
  split_ifs <;> fun_prop

/-- Every [finite cosine polynomial](hyp:k,a) is [continuous on the real line](goal). -/
@[fun_prop]
theorem continuous_cosinePolynomial (k : ℕ) (a : ℕ → ℝ) :
    Continuous (cosinePolynomial k a) := by
  unfold cosinePolynomial
  fun_prop

/-- The uniform integral of [two normalized cosine modes](hyp:i,j)
is [one for equal indices and zero for distinct indices](goal).

Handle zero indices separately; otherwise use the cosine product-to-sum identity,
`integral_cos`, and `integral_Icc_eq_integral_Ioc`. Frequencies are integer multiples
of π and the interval is exactly `[0,1]`, so normalization is √2, not √(2π).
Library search also found the proved neutral result
`Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.cosine_mode_orthogonality`
in Jackson/Coefficients. Its period-integral signature may be reused after evenness
and scaling bridges; the direct interval calculation may require fewer imports.
-/
theorem cosineBasis_orthonormal (i j : ℕ) :
    (∫ x, cosineBasis i x * cosineBasis j x ∂uniformMeasure) =
      if i = j then 1 else 0 := by
  have hcos (m : ℤ) :
      (∫ x, Real.cos (Real.pi * (m : ℝ) * x) ∂uniformMeasure) =
        if m = 0 then 1 else 0 := by
    rw [uniformIntegral_eq_intervalIntegral]
    by_cases hm : m = 0
    · simp [hm]
    · have hm0 : Real.pi * (m : ℝ) ≠ 0 :=
        mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hm)
      rw [if_neg hm, intervalIntegral.integral_comp_mul_left _ hm0, integral_cos]
      simp only [mul_one, mul_zero, Real.sin_zero, sub_zero]
      rw [mul_comm Real.pi, Real.sin_int_mul_pi]
      simp
  have hraw :
      (∫ x, Real.cos (Real.pi * (i : ℝ) * x) *
        Real.cos (Real.pi * (j : ℝ) * x) ∂uniformMeasure) =
        ((if i = j then 1 else 0) + (if i = 0 ∧ j = 0 then 1 else 0)) / 2 := by
    have hpoint (x : ℝ) :
        Real.cos (Real.pi * (i : ℝ) * x) * Real.cos (Real.pi * (j : ℝ) * x) =
        (Real.cos (Real.pi * ((i : ℤ) - j : ℤ) * x) +
          Real.cos (Real.pi * ((i : ℤ) + j : ℤ) * x)) / 2 := by
      push_cast
      rw [show Real.pi * ((i : ℝ) - j) * x =
        Real.pi * i * x - Real.pi * j * x by ring,
        show Real.pi * ((i : ℝ) + j) * x =
        Real.pi * i * x + Real.pi * j * x by ring,
        Real.cos_sub, Real.cos_add]
      ring
    simp_rw [hpoint]
    rw [integral_div]
    have h₁ : Integrable (fun x : ℝ => Real.cos (Real.pi * ((i : ℤ) - j : ℤ) * x)) uniformMeasure :=
      (show Continuous (fun x : ℝ => Real.cos (Real.pi * ((i : ℤ) - j : ℤ) * x)) by
        fun_prop).continuousOn.integrableOn_Icc
    have h₂ : Integrable (fun x : ℝ => Real.cos (Real.pi * ((i : ℤ) + j : ℤ) * x)) uniformMeasure :=
      (show Continuous (fun x : ℝ => Real.cos (Real.pi * ((i : ℤ) + j : ℤ) * x)) by
        fun_prop).continuousOn.integrableOn_Icc
    rw [integral_add h₁ h₂, hcos, hcos]
    have hsub : (i : ℤ) - j = 0 ↔ i = j := by omega
    have hadd : (i : ℤ) + j = 0 ↔ i = 0 ∧ j = 0 := by omega
    simp only [hsub, hadd]
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · simp [cosineBasis, hi, hj]
  · subst i
    simp only [cosineBasis, if_true, if_neg hj, one_mul]
    rw [integral_const_mul]
    simpa [hj, eq_comm] using congrArg (Real.sqrt 2 * ·) (hcos (j : ℤ))
  · subst j
    simp only [cosineBasis, if_true, if_neg hi, mul_one]
    rw [integral_const_mul]
    simpa [hi] using congrArg (Real.sqrt 2 * ·) (hcos (i : ℤ))
  · simp only [cosineBasis, if_neg hi, if_neg hj]
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp_rw [show ∀ x : ℝ,
      (Real.sqrt 2 * Real.cos (Real.pi * i * x)) *
        (Real.sqrt 2 * Real.cos (Real.pi * j * x)) =
      2 * (Real.cos (Real.pi * i * x) * Real.cos (Real.pi * j * x)) by
        intro x
        calc
          _ = (Real.sqrt 2 * Real.sqrt 2) *
            (Real.cos (Real.pi * i * x) * Real.cos (Real.pi * j * x)) := by ring
          _ = _ := by rw [hs]]
    rw [integral_const_mul, hraw]
    simp [hi]
    split_ifs <;> norm_num

/-- The residual of a [continuous target](hyp:hf) after rank-k projection has
[zero coefficient in every retained mode](goal), for an [index below rank](hyp:hj). -/
theorem cosineProjection_residual_orthogonal {f : ℝ → ℝ} {k j : ℕ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hj : j < k) :
    (∫ x, (f x - cosineProjection k f x) * cosineBasis j x ∂uniformMeasure) = 0 := by
  have hfb : Integrable (fun x => f x * cosineBasis j x) uniformMeasure :=
    (hf.mul (continuous_cosineBasis j).continuousOn).integrableOn_Icc
  have hpb : Integrable (fun x => cosineProjection k f x * cosineBasis j x) uniformMeasure :=
    ((continuous_cosinePolynomial k (cosineCoefficient f)).continuousOn.mul
      (continuous_cosineBasis j).continuousOn).integrableOn_Icc
  simp_rw [sub_mul]
  rw [integral_sub hfb hpb]
  have hproj : (∫ x, cosineProjection k f x * cosineBasis j x ∂uniformMeasure) =
      cosineCoefficient f j := by
    unfold cosineProjection cosinePolynomial
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun i hi =>
      (show Integrable (fun x => cosineCoefficient f i * (cosineBasis i x * cosineBasis j x))
        uniformMeasure from
        (((continuous_cosineBasis i).mul (continuous_cosineBasis j)).continuousOn.integrableOn_Icc).const_mul _))]
    simp_rw [integral_const_mul, cosineBasis_orthonormal]
    simp [Finset.mem_range.mpr hj]
  rw [hproj]
  simp [cosineCoefficient]

/-- For a [continuous target](hyp:hf) and [arbitrary cosine coefficients](hyp:a),
[the squared error decomposes into projection error plus squared distance
from the projection to that polynomial](goal). -/
theorem cosineProjection_pythagoras {f : ℝ → ℝ} (k : ℕ) (a : ℕ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    (∫ x, |f x - cosinePolynomial k a x| ^ 2 ∂uniformMeasure) =
      (∫ x, |f x - cosineProjection k f x| ^ 2 ∂uniformMeasure) +
      (∫ x, |cosineProjection k f x - cosinePolynomial k a x| ^ 2 ∂uniformMeasure) := by
  let r := fun x => f x - cosineProjection k f x
  let d := fun x => cosineProjection k f x - cosinePolynomial k a x
  have hr : ContinuousOn r (Set.Icc (0 : ℝ) 1) :=
    hf.sub (continuous_cosinePolynomial k (cosineCoefficient f)).continuousOn
  have hd : ContinuousOn d (Set.Icc (0 : ℝ) 1) :=
    (continuous_cosinePolynomial k (cosineCoefficient f)).continuousOn.sub
      (continuous_cosinePolynomial k a).continuousOn
  have hcross : (∫ x, r x * d x ∂uniformMeasure) = 0 := by
    have hpoint (x : ℝ) : r x * d x =
        ∑ j ∈ Finset.range k, (cosineCoefficient f j - a j) * (r x * cosineBasis j x) := by
      dsimp [d, cosineProjection, cosinePolynomial]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp_rw [hpoint]
    rw [integral_finsetSum _ (fun j hj =>
      (show Integrable (fun x => (cosineCoefficient f j - a j) * (r x * cosineBasis j x))
        uniformMeasure from
        (hr.mul (continuous_cosineBasis j).continuousOn).integrableOn_Icc.const_mul _))]
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_const_mul,
      cosineProjection_residual_orthogonal hf (Finset.mem_range.mp hj), mul_zero]
  have hpoint (x : ℝ) : |f x - cosinePolynomial k a x| ^ 2 =
      |r x| ^ 2 + |d x| ^ 2 + 2 * (r x * d x) := by
    dsimp [r, d]
    simp only [sq_abs]
    ring
  simp_rw [hpoint]
  have hrd : Integrable (fun x => 2 * (r x * d x)) uniformMeasure :=
    (hr.mul hd).integrableOn_Icc.const_mul 2
  have hsum : Integrable (fun x => |r x| ^ 2 + |d x| ^ 2) uniformMeasure :=
    (integrable_sq_of_continuousOn hr).add (integrable_sq_of_continuousOn hd)
  rw [integral_add hsum hrd,
    integral_add (integrable_sq_of_continuousOn hr) (integrable_sq_of_continuousOn hd),
    integral_const_mul, hcross]
  simp [r, d]


/-- The projection of a [continuous target](hyp:hf) has [L² error no greater
than any competitor](goal) that
[belongs to the same cosine span](hyp:hspan). -/
theorem cosineProjection_bestApproximation {f p : ℝ → ℝ} {k : ℕ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hspan : InCosineSpan k p) :
    l2Norm (fun x => f x - cosineProjection k f x) ≤ l2Norm (fun x => f x - p x) := by
  obtain ⟨a, ha⟩ := hspan
  have heq : (∫ x, |f x - p x| ^ 2 ∂uniformMeasure) =
      ∫ x, |f x - cosinePolynomial k a x| ^ 2 ∂uniformMeasure := by
    apply integral_congr_ae
    apply (ae_restrict_iff' measurableSet_Icc).2
    exact ae_of_all _ (fun x hx => by dsimp only; rw [ha x hx])
  unfold l2Norm
  apply Real.sqrt_le_sqrt
  rw [heq, cosineProjection_pythagoras k a hf]
  exact le_add_of_nonneg_right (integral_nonneg fun x => sq_nonneg _)

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

