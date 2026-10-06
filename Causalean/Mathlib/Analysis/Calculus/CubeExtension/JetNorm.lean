module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic

/-!
# From coordinate jets to full multilinear jets

Finite-dimensional coordinate bounds control the operator norm of a
multilinear derivative. This converts intrinsic cube balls into full-jet
estimates needed by quantitative extension constructions.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

set_option maxHeartbeats 1000000 in
-- Coordinate expansion over two finite index types needs extra elaboration time.
/-- In [dimension d](hyp:d) and through [order m](hyp:m), [there is a positive
constant C such that every continuous j-linear map T on coordinate space with
j ≤ m whose values on all tuples of standard basis vectors are bounded in
absolute value by B ≥ 0 has operator norm at most C·B](goal). -/
theorem exists_coord_multilinear_norm_constant (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ j ≤ m,
        ∀ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ,
        ∀ B : ℝ, 0 ≤ B →
          (∀ f : Fin j → Fin d,
            |T (fun k => Pi.single (f k) (1 : ℝ))| ≤ B) →
          ‖T‖ ≤ C * B := by
  classical
  refine ⟨((d + 1 : ℕ) : ℝ) ^ m, by positivity, ?_⟩
  intro j hj T B hB hcoord
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hsum (k : Fin j) :
      (∑ i : Fin d, (v k i) • Pi.single i (1 : ℝ)) = v k := by
    ext i
    simp [Pi.single_apply]
  have hterm (f : Fin j → Fin d) :
      ‖T (fun k => (v k (f k)) • Pi.single (f k) (1 : ℝ))‖ ≤
        B * ∏ k, ‖v k‖ := by
    rw [T.map_smul_univ, norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    have hc : ‖T (fun k => Pi.single (f k) (1 : ℝ))‖ ≤ B := by
      simpa [Real.norm_eq_abs] using hcoord f
    have hp : (∏ k, |v k (f k)|) ≤ ∏ k, ‖v k‖ := by
      apply Finset.prod_le_prod (fun k hk => abs_nonneg _)
      intro k hk
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (v k) (f k)
    calc
      (∏ k, |v k (f k)|) * ‖T (fun k => Pi.single (f k) (1 : ℝ))‖
          ≤ (∏ k, |v k (f k)|) * B := by gcongr
      _ = B * (∏ k, |v k (f k)|) := by ring
      _ ≤ B * (∏ k, ‖v k‖) := by gcongr
  have hcard : ((Fintype.card (Fin j → Fin d) : ℕ) : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ m := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact_mod_cast (calc
      d ^ j ≤ (d + 1) ^ j := Nat.pow_le_pow_left (by omega) j
      _ ≤ (d + 1) ^ m := Nat.pow_le_pow_right (by omega) hj)
  calc
    ‖T v‖ = ‖∑ f : Fin j → Fin d,
        T (fun k => (v k (f k)) • Pi.single (f k) (1 : ℝ))‖ := by
          congr 1
          conv_lhs => rw [← funext hsum]
          exact T.map_sum (fun k i => (v k i) • Pi.single i (1 : ℝ))
    _ ≤ ∑ f : Fin j → Fin d,
        ‖T (fun k => (v k (f k)) • Pi.single (f k) (1 : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _f : Fin j → Fin d, B * ∏ k, ‖v k‖ := Finset.sum_le_sum (fun f _ => hterm f)
    _ = ((Fintype.card (Fin j → Fin d) : ℕ) : ℝ) * (B * ∏ k, ‖v k‖) := by simp
    _ ≤ (((d + 1 : ℕ) : ℝ) ^ m) * (B * ∏ k, ‖v k‖) := by gcongr
    _ = (((d + 1 : ℕ) : ℝ) ^ m * B) * ∏ k, ‖v k‖ := by ring

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and [exponent
s](hyp:s), [there is a positive constant C such that every response u in the
intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the closed cube
has within-cube Fréchet derivatives of every order at most m with operator norm
at most C·L on the cube, and its order-m within-cube Fréchet derivative is
s-Hölder on the cube with coefficient C·L](goal). The constant does not depend on
the response or the radius. -/
theorem exists_full_intrinsic_jet_bounds (d m : ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d m s L u →
        (∀ j ≤ m, ∀ x ∈ cube d,
          ‖iteratedFDerivWithin ℝ j u (cube d) x‖ ≤ C * L) ∧
        (∀ x ∈ cube d, ∀ y ∈ cube d,
          ‖iteratedFDerivWithin ℝ m u (cube d) x -
            iteratedFDerivWithin ℝ m u (cube d) y‖
            ≤ C * L * ‖x - y‖ ^ s) := by
  obtain ⟨C, hC, hbound⟩ := exists_coord_multilinear_norm_constant d m
  refine ⟨C, hC, ?_⟩
  intro u L hL hu
  constructor
  · intro j hj x hx
    apply hbound j hj _ L hL
    intro f
    simpa only [coordJetOn, Real.norm_eq_abs] using hu.derivBound j hj f x hx
  · intro x hx y hy
    have hnonneg : 0 ≤ L * ‖x - y‖ ^ s := by positivity
    have h := hbound m le_rfl
      (iteratedFDerivWithin ℝ m u (cube d) x -
        iteratedFDerivWithin ℝ m u (cube d) y)
      (L * ‖x - y‖ ^ s) hnonneg
    have hcoord : ∀ f : Fin m → Fin d,
        |(iteratedFDerivWithin ℝ m u (cube d) x -
          iteratedFDerivWithin ℝ m u (cube d) y)
          (fun k => Pi.single (f k) (1 : ℝ))| ≤
          L * ‖x - y‖ ^ s := by
      intro f
      simpa only [sub_apply, coordJetOn] using
        hu.modulus f x hx y hy
    exact (h hcoord).trans_eq (by ring)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
