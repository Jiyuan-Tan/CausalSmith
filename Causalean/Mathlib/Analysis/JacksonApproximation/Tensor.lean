import Causalean.Mathlib.Analysis.JacksonApproximation.TrigExtraction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite tensor Jackson convolution and polynomial extraction

This module tensorizes the normalized Jackson kernel, proves product-integration and convolution
identities on finite period boxes, extracts multivariate polynomials, and gives a quantitative
Lipschitz approximation bound.
-/

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open MeasureTheory Real
open scoped BigOperators

/-- [A finite dimension](hyp:d) determines [the standard period box](goal), whose coordinates all
lie between minus π and π.
-/
def periodBox (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-Real.pi) Real.pi}

/-- [A finite dimension](hyp:d) determines [the normalized cube](goal), whose coordinates all lie
between minus one and one.
-/
def normalizedCube (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- [An integer kernel order](hyp:K), [a finite dimension](hyp:d), and [a point in period
coordinates](hyp:u) determine [the tensor Jackson kernel](goal), the product of the
one-dimensional kernels across coordinates.
-/
noncomputable def tensorJackson (K d : ℕ) (u : Fin d → ℝ) : ℝ :=
  ∏ i, jackson K (u i)

/-- [A finite dimension](hyp:d) and [a point in period coordinates](hyp:t) determine [the
coordinatewise cosine point](goal).
-/
noncomputable def cosPoint {d : ℕ} (t : Fin d → ℝ) : Fin d → ℝ := fun i => Real.cos (t i)

/-- For [a finite dimension](hyp:d) and [a point in period coordinates](hyp:t), [the
coordinatewise cosine point lies in the normalized cube](goal).
-/
theorem cosPoint_mem_normalizedCube {d : ℕ} (t : Fin d → ℝ) :
    cosPoint t ∈ normalizedCube d := by
  intro i
  exact ⟨Real.neg_one_le_cos (t i), Real.cos_le_one (t i)⟩

/-- [A finite dimension](hyp:d), [a real function on normalized coordinates](hyp:f), and [a point
in period coordinates](hyp:t) determine [the cosine lift of the function](goal) by
coordinatewise cosine precomposition.
-/
noncomputable def cosLift {d : ℕ} (f : (Fin d → ℝ) → ℝ) (t : Fin d → ℝ) : ℝ :=
  f (cosPoint t)

/-- [A finite dimension](hyp:d), [an integer kernel order](hyp:K), [a real function on normalized
coordinates](hyp:f), and [a point in period coordinates](hyp:x) determine [the tensor Jackson
convolution](goal), the kernel-weighted average of the translated cosine lift over the period
box.
-/
noncomputable def tensorConvolution {d : ℕ} (K : ℕ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ u in periodBox d, f (cosPoint (x - u)) * tensorJackson K d u

/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
and [a point in period coordinates](hyp:u), [the tensor Jackson kernel is nonnegative](goal).
-/
theorem tensorJackson_nonneg {d K : ℕ} (hK : 0 < K) (u : Fin d → ℝ) :
    0 ≤ tensorJackson K d u := by
  exact Finset.prod_nonneg fun i _ ↦ jackson_nonneg K hK (u i)

/-- For [integer order K](hyp:K) and [a finite dimension](hyp:d), [the tensor Jackson kernel is
measurable](goal).
-/
@[measurability, fun_prop]
theorem measurable_tensorJackson (K d : ℕ) : Measurable (tensorJackson K d) := by
  unfold tensorJackson
  fun_prop

/-- For [integer order K](hyp:K) and [a finite dimension](hyp:d), [the tensor Jackson kernel is
integrable over the standard period box](goal).
-/
theorem integrableOn_tensorJackson (K d : ℕ) :
    IntegrableOn (tensorJackson K d) (periodBox d) := by
  change Integrable (fun u : Fin d → ℝ ↦ ∏ i, jackson K (u i))
    (volume.restrict (periodBox d))
  rw [show periodBox d = Set.univ.pi (fun _ ↦ Set.Icc (-Real.pi) Real.pi) by
    ext u
    simp only [periodBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc], volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod fun _ ↦ integrableOn_jackson K

/-- Given [a finite dimension](hyp:d), [one integrand for each coordinate](hyp:g), and
[integrability of every coordinate integrand over the standard period](hyp:hg), [the integral
of their product over the period box equals the product of their one-dimensional
integrals](goal).
-/
theorem integral_periodBox_prod {d : ℕ} (g : Fin d → ℝ → ℝ)
    (hg : ∀ i, IntegrableOn (g i) (Set.Icc (-Real.pi) Real.pi)) :
    (∫ u in periodBox d, ∏ i, g i (u i)) =
      ∏ i, ∫ t in Set.Icc (-Real.pi) Real.pi, g i t := by
  rw [show periodBox d = Set.univ.pi (fun _ ↦ Set.Icc (-Real.pi) Real.pi) by
    ext u
    simp only [periodBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc], volume_pi, Measure.restrict_pi_pi]
  exact MeasureTheory.integral_fintype_prod_eq_prod g

/-- For [a finite dimension](hyp:d) and [integer order K](hyp:K) that is [strictly
positive](hyp:hK), [the tensor Jackson kernel has unit mass over the period box](goal).
-/
theorem tensorJackson_integral_eq_one {d K : ℕ} (hK : 0 < K) :
    (∫ u in periodBox d, tensorJackson K d u) = 1 := by
  rw [show tensorJackson K d = fun u ↦ ∏ i, jackson K (u i) by rfl,
    integral_periodBox_prod (fun _ ↦ jackson K) (fun _ ↦ integrableOn_jackson K)]
  simp [jackson_integral_eq_one K hK]

/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
and [a selected coordinate](hyp:i), [the tensor kernel's absolute first moment in that
coordinate equals the one-dimensional first moment](goal).
-/
theorem tensorJackson_first_moment_eq {d K : ℕ} (hK : 0 < K) (i : Fin d) :
    (∫ u in periodBox d, |u i| * tensorJackson K d u) =
      ∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t := by
  classical
  let g : Fin d → ℝ → ℝ := fun j t ↦ (if j = i then |t| else 1) * jackson K t
  have hi : IntegrableOn (fun t : ℝ ↦ |t| * jackson K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    ((continuous_abs.comp continuous_id).mul (continuous_jackson K)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hg : ∀ j, IntegrableOn (g j) (Set.Icc (-Real.pi) Real.pi) := by
    intro j
    by_cases hji : j = i
    · simpa [g, hji] using hi
    · simpa [g, hji] using integrableOn_jackson K
  rw [show (fun u : Fin d → ℝ ↦ |u i| * tensorJackson K d u) =
      fun u ↦ ∏ j, g j (u j) by
    funext u
    symm
    calc
      (∏ j, g j (u j)) =
          (∏ j, if j = i then |u j| else 1) * ∏ j, jackson K (u j) := by
        simp only [g, Finset.prod_mul_distrib]
      _ = |u i| * tensorJackson K d u := by simp [tensorJackson],
    integral_periodBox_prod g hg]
  have hmass : (∫ t in Set.Icc (-Real.pi) Real.pi, jackson K t) = 1 :=
    jackson_integral_eq_one K hK
  have hcoord : ∀ j, (∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
      if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t) else 1 := by
    intro j
    by_cases hji : j = i <;> simp [g, hji, hmass]
  calc
    (∏ j, ∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
        ∏ j, if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t)
          else 1 := Finset.prod_congr rfl fun j _ ↦ hcoord j
    _ = ∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t := by simp

/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
and [a selected coordinate](hyp:i), [the tensor kernel's second moment in that coordinate
equals the one-dimensional second moment](goal).
-/
theorem tensorJackson_second_moment_eq {d K : ℕ} (hK : 0 < K) (i : Fin d) :
    (∫ u in periodBox d, (u i) ^ 2 * tensorJackson K d u) =
      ∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t := by
  classical
  let g : Fin d → ℝ → ℝ := fun j t ↦ (if j = i then t ^ 2 else 1) * jackson K t
  have hi : IntegrableOn (fun t : ℝ ↦ t ^ 2 * jackson K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    ((continuous_id.pow 2).mul (continuous_jackson K)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hg : ∀ j, IntegrableOn (g j) (Set.Icc (-Real.pi) Real.pi) := by
    intro j
    by_cases hji : j = i
    · simpa [g, hji] using hi
    · simpa [g, hji] using integrableOn_jackson K
  rw [show (fun u : Fin d → ℝ ↦ (u i) ^ 2 * tensorJackson K d u) =
      fun u ↦ ∏ j, g j (u j) by
    funext u
    symm
    calc
      (∏ j, g j (u j)) =
          (∏ j, if j = i then (u j) ^ 2 else 1) * ∏ j, jackson K (u j) := by
        simp only [g, Finset.prod_mul_distrib]
      _ = (u i) ^ 2 * tensorJackson K d u := by simp [tensorJackson],
    integral_periodBox_prod g hg]
  have hmass : (∫ t in Set.Icc (-Real.pi) Real.pi, jackson K t) = 1 :=
    jackson_integral_eq_one K hK
  have hcoord : ∀ j, (∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
      if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t) else 1 := by
    intro j
    by_cases hji : j = i <;> simp [g, hji, hmass]
  calc
    (∏ j, ∫ t in Set.Icc (-Real.pi) Real.pi, g j t) =
        ∏ j, if j = i then (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t)
          else 1 := Finset.prod_congr rfl fun j _ ↦ hcoord j
    _ = ∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t := by simp

/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
[a function](hyp:f) that [is nonnegative throughout the normalized cube](hyp:hf), and [a
selected point in period coordinates](hyp:x), [the tensor convolution is nonnegative at that
point](goal).
-/
theorem tensorConvolution_nonneg {d K : ℕ} (hK : 0 < K)
    {f : (Fin d → ℝ) → ℝ} (hf : ∀ z ∈ normalizedCube d, 0 ≤ f z) (x : Fin d → ℝ) :
    0 ≤ tensorConvolution K f x := by
  rw [tensorConvolution]
  exact integral_nonneg fun u ↦
    mul_nonneg (hf _ (cosPoint_mem_normalizedCube _)) (tensorJackson_nonneg hK u)

/-- For [a finite dimension](hyp:d), [integer order K](hyp:K) that is [strictly positive](hyp:hK),
[a real constant](hyp:c), and [a point in period coordinates](hyp:x), [tensor convolution
preserves the constant function](goal).
-/
theorem tensorConvolution_const {d K : ℕ} (hK : 0 < K) (c : ℝ) (x : Fin d → ℝ) :
    tensorConvolution K (fun _ => c) x = c := by
  unfold tensorConvolution
  rw [integral_const_mul, tensorJackson_integral_eq_one hK, mul_one]

end Causalean.Mathlib.Analysis.JacksonApproximation
