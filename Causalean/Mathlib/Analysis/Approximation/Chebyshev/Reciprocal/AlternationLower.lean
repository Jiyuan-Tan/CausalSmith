module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation

/-!
# Alternating residuals certify the best uniform error

This module extracts the sufficient direction of polynomial equioscillation
from Causalean's normalized Lagrange weights.  It is useful independently of
reciprocal approximation.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- A [nondegenerate interval](hyp:a,b,hab), [continuous target](hyp:f,hf),
[nonnegative error level](hyp:E,hE), [candidate polynomial](hyp:P), [degree
bound](hyp:m,hdegree), [uniform residual bound](hyp:hbound), and [ordered
alternating interval nodes](hyp:nodes,hmono,hmem,halt) imply [that the
candidate and optimal uniform errors equal that level](goal). -/
theorem alternatingResidual_certifiesBest
    {f : ℝ → ℝ} {a b E : ℝ} {m : ℕ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hE : 0 ≤ E) (P : Polynomial ℝ) (hdegree : P.natDegree ≤ m)
    (hbound : ∀ x ∈ Set.Icc a b, |f x - P.eval x| ≤ E)
    (nodes : Fin (m + 2) → ℝ) (hmono : StrictMono nodes)
    (hmem : ∀ i, nodes i ∈ Set.Icc a b)
    (halt : ∀ i, f (nodes i) - P.eval (nodes i) = (-1 : ℝ) ^ (i : ℕ) * E) :
    uniformApproxError f a b P = E ∧ bestUniformApproxError f a b m = E := by
  classical
  let w : Fin (m + 2) → ℝ := normalizedLagrangeWeight nodes
  have hinj : Function.Injective nodes := hmono.injective
  have hmass : ∑ i, |w i| = 1 :=
    sum_abs_normalizedLagrangeWeight_eq_one hinj
  have hpower (i : Fin (m + 2)) :
      (-1 : ℝ) ^ (m + 1 - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ) =
        (-1 : ℝ) ^ (m + 1) := by
    rw [← pow_add, Nat.sub_add_cancel]
    omega
  have hresidual :
      ∑ i, w i * (f (nodes i) - P.eval (nodes i)) =
        (-1 : ℝ) ^ (m + 1) * E := by
    calc
      ∑ i, w i * (f (nodes i) - P.eval (nodes i)) =
          ∑ i, ((-1 : ℝ) ^ (m + 1) * E) * |w i| := by
        apply Finset.sum_congr rfl
        intro i _
        have hwalt : w i = (-1 : ℝ) ^ (m + 1 - (i : ℕ)) * |w i| :=
          normalizedLagrangeWeight_alternates hmono i
        rw [halt i]
        calc
          w i * ((-1 : ℝ) ^ (i : ℕ) * E) =
              ((-1 : ℝ) ^ (m + 1 - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ)) * E * |w i| := by
                conv_lhs => rw [hwalt]
                ring
          _ = (-1 : ℝ) ^ (m + 1) * E * |w i| := by rw [hpower i]
      _ = (-1 : ℝ) ^ (m + 1) * E := by
        rw [← Finset.mul_sum, hmass, mul_one]
  have hcontinuous (Q : Polynomial ℝ) :
      ContinuousOn (fun x => f x - Q.eval x) (Set.Icc a b) :=
    hf.sub Q.continuous.continuousOn
  have hupper : uniformApproxError f a b P ≤ E :=
    (intervalSupNorm_le_iff (hcontinuous P) hab.le).mpr hbound
  have hlower (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ m) :
      E ≤ uniformApproxError f a b Q := by
    have hQzero : ∑ i, w i * Q.eval (nodes i) = 0 :=
      sum_normalizedLagrangeWeight_mul_eval_eq_zero hinj hQ
    have hPzero : ∑ i, w i * P.eval (nodes i) = 0 :=
      sum_normalizedLagrangeWeight_mul_eval_eq_zero hinj hdegree
    have hsum :
        ∑ i, w i * (f (nodes i) - Q.eval (nodes i)) =
          (-1 : ℝ) ^ (m + 1) * E := by
      calc
        ∑ i, w i * (f (nodes i) - Q.eval (nodes i)) =
            (∑ i, w i * f (nodes i)) - ∑ i, w i * Q.eval (nodes i) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = ∑ i, w i * f (nodes i) := by rw [hQzero, sub_zero]
        _ = (∑ i, w i * (f (nodes i) - P.eval (nodes i))) +
              ∑ i, w i * P.eval (nodes i) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = (-1 : ℝ) ^ (m + 1) * E := by rw [hPzero, add_zero, hresidual]
    have hpoint (i : Fin (m + 2)) :
        |f (nodes i) - Q.eval (nodes i)| ≤ uniformApproxError f a b Q :=
      ((intervalSupNorm_le_iff (hcontinuous Q) hab.le).mp le_rfl) _ (hmem i)
    have hsum_bound :
        |∑ i, w i * (f (nodes i) - Q.eval (nodes i))| ≤
          uniformApproxError f a b Q := by
      calc
        |∑ i, w i * (f (nodes i) - Q.eval (nodes i))| ≤
            ∑ i, |w i * (f (nodes i) - Q.eval (nodes i))| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |w i| * uniformApproxError f a b Q := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hpoint i) (abs_nonneg _)
        _ = uniformApproxError f a b Q := by
          rw [← Finset.sum_mul, hmass, one_mul]
    rw [hsum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hE] at hsum_bound
    exact hsum_bound
  have hP_lower : E ≤ uniformApproxError f a b P := hlower P hdegree
  have hP_eq : uniformApproxError f a b P = E := le_antisymm hupper hP_lower
  refine ⟨hP_eq, le_antisymm ?_ ?_⟩
  · exact (bestUniformApproxError_le hab hf hdegree).trans_eq hP_eq
  · unfold bestUniformApproxError
    apply le_csInf
    · exact ⟨uniformApproxError f a b P, P, hdegree, rfl⟩
    · rintro e ⟨Q, hQ, rfl⟩
      exact hlower Q hQ

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal
