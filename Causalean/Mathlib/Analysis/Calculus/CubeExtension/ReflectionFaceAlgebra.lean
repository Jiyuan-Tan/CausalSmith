module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetNorm
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionCoefficients

/-!
# Algebraic matching of reflected face jets

The reflection moment equations recover every coordinate evaluation of a
multilinear jet through the prescribed order. This is the algebraic input to
matching the exterior jet trace to the intrinsic cube jet at a face.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha) and [j ≤ m](hyp:hj), then for
[every continuous j-linear map T](hyp:T) and [coordinate directions f](hyp:f)
[the weighted sum over q of a_q times T evaluated on the standard basis vectors
e_{f(k)}, each scaled by −(q + 1) when f(k) = i and left unscaled otherwise,
equals T evaluated on the unscaled basis vectors](goal). -/
theorem reflection_weighted_coordinate_jet (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (j : ℕ) (hj : j ≤ m)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (f : Fin j → Fin d) :
    (∑ q : Fin (m + 1), a q *
      T (fun k =>
        (if f k = i then -((q.val : ℝ) + 1) else 1) •
          Pi.single (f k) (1 : ℝ))) =
      T (fun k => Pi.single (f k) (1 : ℝ)) := by
  classical
  let n := (Finset.univ.filter fun k : Fin j => f k = i).card
  have hn : n ≤ m := by
    exact (Finset.card_filter_le _ _).trans (by simpa using hj)
  have hprod (q : Fin (m + 1)) :
      (∏ k : Fin j, if f k = i then -((q.val : ℝ) + 1) else 1) =
        (-((q.val : ℝ) + 1)) ^ n := by
    rw [Finset.prod_ite]
    simp [n]
  have hmoment :
      (∑ q : Fin (m + 1), a q * (-((q.val : ℝ) + 1)) ^ n) = 1 := by
    simpa using ha ⟨n, Nat.lt_succ_of_le hn⟩
  calc
    (∑ q : Fin (m + 1), a q *
      T (fun k =>
        (if f k = i then -((q.val : ℝ) + 1) else 1) •
          Pi.single (f k) (1 : ℝ))) =
        (∑ q : Fin (m + 1), a q * (-((q.val : ℝ) + 1)) ^ n) *
          T (fun k => Pi.single (f k) (1 : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      rw [ContinuousMultilinearMap.map_smul_univ, hprod]
      simp [smul_eq_mul, mul_assoc]
    _ = _ := by rw [hmoment, one_mul]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
