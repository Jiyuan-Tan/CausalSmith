module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Grid

/-!
# Derivatives of bounded tensor-grid polynomials

A fixed tensor grid controls every coordinate derivative of a polynomial of bounded
coordinate degree throughout the normalized cube. This is the finite-dimensional
polynomial step in fixed-cube interpolation.
-/

public section

open scoped BigOperators
open Causalean.Mathlib.Analysis.Approximation.Chebyshev

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

private theorem tensor_monomial_smooth {d m : ℕ} (a : Fin d → Fin (m + 1)) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ =>
      MvPolynomial.eval x (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) := by
  simp only [MvPolynomial.eval_monomial, one_mul]
  apply contDiff_prod
  intro i hi
  exact ((contDiff_apply ℝ ℝ i).pow _)

private theorem cube_compact (d : ℕ) : IsCompact (cube d) := by
  have h := isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  convert h using 1
  ext x
  simp only [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
    Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc]

private theorem tensor_monomial_deriv_uniform (d m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ a : Fin d → Fin (m + 1), ∀ j ≤ m, ∀ x ∈ cube d,
        ‖iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
          MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x‖ ≤ M := by
  have h_each (a : Fin d → Fin (m + 1)) (j : Fin (m + 1)) :
      ∃ K : ℝ, ∀ x ∈ cube d,
        ‖iteratedFDeriv ℝ (j : ℕ) (fun z : Fin d → ℝ =>
          MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x‖ ≤ K := by
    exact (cube_compact d).exists_bound_of_continuousOn
      (((tensor_monomial_smooth a).continuous_iteratedFDeriv le_top).continuousOn)
  choose K hK using h_each
  have hfinite : (Set.range (fun q : (Fin d → Fin (m + 1)) × Fin (m + 1) =>
      K q.1 q.2)).Finite := Set.finite_range _
  obtain ⟨M, hM⟩ := hfinite.exists_le
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro a j hj x hx
  exact (hK a ⟨j, Nat.lt_succ_of_le hj⟩ x hx).trans
    ((hM (K a ⟨j, Nat.lt_succ_of_le hj⟩) ⟨(a, ⟨j, Nat.lt_succ_of_le hj⟩), rfl⟩).trans
      (le_max_left _ _))

private theorem tensor_eval_sum (d m : ℕ) (p : MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ i, p.degreeOf i ≤ m) :
    (fun z => MvPolynomial.eval z p) =
      (fun z => ∑ a : Fin d → Fin (m + 1),
        tensorCoeffs (D := m) p a *
        MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) := by
  funext z
  calc
    MvPolynomial.eval z p =
      MvPolynomial.eval z (tensorPolynomial (tensorCoeffs (D := m) p)) := by
        rw [tensorPolynomial_tensorCoeffs p hdeg]
    _ = _ := by simp [tensorPolynomial, MvPolynomial.eval_monomial]

private theorem tensor_eval_sum_deriv {d m j : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : Fin d → ℝ) :
    iteratedFDeriv ℝ j
      (fun z => ∑ a : Fin d → Fin (m + 1),
        tensorCoeffs (D := m) p a *
        MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x =
    ∑ a : Fin d → Fin (m + 1),
      tensorCoeffs (D := m) p a •
        iteratedFDeriv ℝ j
          (fun z => MvPolynomial.eval z
            (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x := by
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_congr rfl
    intro a ha
    have hs : ContDiff ℝ j (fun z : Fin d → ℝ =>
        MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) :=
      (tensor_monomial_smooth a).of_le le_top
    simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply'
        (a := tensorCoeffs (D := m) p a) hs.contDiffAt (x := x))
  · intro a ha
    have hs : ContDiff ℝ j (fun z : Fin d → ℝ =>
        MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) :=
      (tensor_monomial_smooth a).of_le le_top
    simpa only [smul_eq_mul] using
      (hs.const_smul (tensorCoeffs (D := m) p a)).contDiffAt (x := x)

/-- For [a dimension and a degree m](hyp:d,m), [there is a positive constant C such that every
multivariate polynomial of degree at most m in each variable that is bounded in absolute value by a
nonnegative B at every point of the fixed tensor grid has all its coordinate partial derivatives of
order at most m bounded in absolute value by C times B throughout the closed normalized
cube](goal). -/
theorem tensor_polynomial_deriv_bound (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : MvPolynomial (Fin d) ℝ) (B : ℝ),
        0 ≤ B → (∀ i, p.degreeOf i ≤ m) →
        (∀ b : Fin d → Fin (m + 1),
          |MvPolynomial.eval
            (Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorGridPoint b) p| ≤ B) →
        ∀ j ≤ m, ∀ f : Fin j → Fin d, ∀ x ∈ cube d,
          |coordPartial j (fun z => MvPolynomial.eval z p) f x| ≤ C * B := by
  classical
  obtain ⟨C₀, hC₀, hcoeff⟩ := tensor_coefficient_bound d m
  obtain ⟨M, hM₀, hM⟩ := tensor_monomial_deriv_uniform d m
  let A := Fin d → Fin (m + 1)
  have hcard : 0 < Fintype.card A := Fintype.card_pos_iff.mpr inferInstance
  refine ⟨(Fintype.card A : ℝ) * C₀ * (M + 1), by positivity, ?_⟩
  intro p B hB hdeg hgrid j hj f x hx
  let v : Fin j → (Fin d → ℝ) := fun k => Pi.single (f k) (1 : ℝ)
  have hv : ‖v‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro k
    change ‖(Pi.single (f k) (1 : ℝ) : Fin d → ℝ)‖ ≤ 1
    rw [Pi.norm_single]
    norm_num
  have hmono (a : A) :
      |(iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
        MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x) v| ≤
        M := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
          MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x‖ *
          (1 : ℝ) ^ j :=
        (iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
          MvPolynomial.eval z
            (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x).le_opNorm_mul_pow_of_le hv
      _ ≤ M := by simpa using hM a j hj x hx
  have hc : ∀ a : A, |tensorCoeffs (D := m) p a| ≤ C₀ * B :=
    hcoeff p B hB hdeg hgrid
  calc
    |coordPartial j (fun z => MvPolynomial.eval z p) f x| =
        |∑ a : A, tensorCoeffs (D := m) p a *
          (iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
            MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x) v| := by
      rw [coordPartial, tensor_eval_sum d m p hdeg, tensor_eval_sum_deriv p x]
      simp [v, smul_eq_mul]
      rfl
    _ ≤ ∑ a : A, |tensorCoeffs (D := m) p a| *
          |(iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
            MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x) v| := by
      calc
        _ ≤ ∑ a : A, |tensorCoeffs (D := m) p a *
              (iteratedFDeriv ℝ j (fun z : Fin d → ℝ =>
                MvPolynomial.eval z (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) x) v| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
    _ ≤ ∑ _a : A, (C₀ * B) * M := by
      apply Finset.sum_le_sum
      intro a ha
      exact (mul_le_mul_of_nonneg_right (hc a) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hmono a) (mul_nonneg (le_of_lt hC₀) hB))
    _ ≤ ((Fintype.card A : ℝ) * C₀ * (M + 1)) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        (Fintype.card A : ℝ) * ((C₀ * B) * M) =
            ((Fintype.card A : ℝ) * C₀ * B) * M := by ring
        _ ≤ ((Fintype.card A : ℝ) * C₀ * B) * (M + 1) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hC₀)) hB)
        _ = _ := by ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
