module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularAffineJets

/-!
# Quantitative affine transport between closed rectangular boxes

Coordinatewise affine changes of variables identify any two nondegenerate
finite boxes. This module records the uniform intrinsic Hölder norm estimate
needed to reuse a normalized one-face reflection on successive boxes.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [the source box](hyp:hsource) and [the target box both have positive side
lengths](hyp:htarget), then for [derivative order m](hyp:m) and [exponent
s](hyp:s) [there is a positive constant C such that whenever a response u lies
in the intrinsic Hölder ball of order m, exponent s and radius L ≥ 0 on the
target box, its pullback along the coordinatewise affine map lies in the
intrinsic Hölder ball of radius C·L on the source box](goal). The constant
depends only on the boxes, m and s; all jets are taken within their own box, so
the estimate does not depend on the ambient representative.

The proof uses the box and distance-power lemmas from
`RectangularAffineGeometry`, the within-jet affine chain rule in
`RectangularAffineJets`, and a finite maximum of the coordinate scaling
factors. -/
theorem exists_rectAffine_holder_constant {d : ℕ}
    (lo hi lo' hi' : Fin d → ℝ) (m : ℕ) (s : ℝ)
    (hsource : ∀ i, lo i < hi i)
    (htarget : ∀ i, lo' i < hi' i) :
  ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        HolderBallOn (rectBox lo' hi') m s L u →
        HolderBallOn (rectBox lo hi) m s (C * L)
          (fun x => u (rectAffine lo hi lo' hi' x)) := by
  let a : Fin d → ℝ := fun i => (hi' i - lo' i) / (hi i - lo i)
  let K : ℝ := 1 + ∑ i : Fin d, a i
  have ha (i : Fin d) : 0 ≤ a i :=
    (div_pos (sub_pos.mpr (htarget i)) (sub_pos.mpr (hsource i))).le
  have hK : 1 ≤ K := by
    dsimp [K]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ha i)
    linarith
  have haK (i : Fin d) : a i ≤ K := by
    have hsum : a i ≤ ∑ j : Fin d, a j :=
      Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
    dsimp [K]
    linarith
  have hprod (j : ℕ) (hj : j ≤ m) (f : Fin j → Fin d) :
      ∏ k : Fin j, a (f k) ≤ K ^ m := by
    calc
      ∏ k : Fin j, a (f k) ≤ ∏ _k : Fin j, K :=
        Finset.prod_le_prod (fun k _ => ha (f k)) (fun k _ => haK (f k))
      _ = K ^ j := by simp
      _ ≤ K ^ m := pow_le_pow_right₀ hK hj
  obtain ⟨D, hD, hdist⟩ :=
    exists_rectAffine_rpow_constant lo hi lo' hi' s hsource htarget
  refine ⟨K ^ m * (1 + D), mul_pos (pow_pos (by linarith : 0 < K) _) (by linarith), ?_⟩
  intro u L hL hu
  have hmap (x : Fin d → ℝ) (hx : x ∈ rectBox lo hi) :
      rectAffine lo hi lo' hi' x ∈ rectBox lo' hi' :=
    (Set.ext_iff.mp
      (rectAffine_preimage_rectBox lo hi lo' hi' hsource htarget) x).2 hx
  refine ⟨contDiffOn_rectAffine lo hi lo' hi' hsource htarget hu.regularity, ?_, ?_⟩
  · intro j hj f x hx
    rw [coordJetOn_rectAffine lo hi lo' hi' hsource htarget u f hx]
    have hp : 0 ≤ ∏ k : Fin j, a (f k) :=
      Finset.prod_nonneg (fun k _ => ha (f k))
    change |(∏ k : Fin j, a (f k)) * coordJetOn (rectBox lo' hi') j u f
      (rectAffine lo hi lo' hi' x)| ≤ _
    rw [abs_mul, abs_of_nonneg hp]
    calc
      (∏ k : Fin j, a (f k)) *
          |coordJetOn (rectBox lo' hi') j u f (rectAffine lo hi lo' hi' x)| ≤
          (∏ k : Fin j, a (f k)) * L :=
        mul_le_mul_of_nonneg_left (hu.derivBound j hj f _ (hmap x hx)) hp
      _ ≤ K ^ m * L := mul_le_mul_of_nonneg_right (hprod j hj f) hL
      _ ≤ (K ^ m * (1 + D)) * L := by
        have hKm : 0 ≤ K ^ m := pow_nonneg (by linarith : 0 ≤ K) _
        nlinarith [mul_nonneg (mul_nonneg hKm hD.le) hL]
  · intro f x hx y hy
    rw [coordJetOn_rectAffine lo hi lo' hi' hsource htarget u f hx,
      coordJetOn_rectAffine lo hi lo' hi' hsource htarget u f hy]
    have hp : 0 ≤ ∏ k : Fin m, a (f k) :=
      Finset.prod_nonneg (fun k _ => ha (f k))
    have hmod := hu.modulus f _ (hmap x hx) _ (hmap y hy)
    have hpow : 0 ≤ ‖x - y‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
    change |(∏ k : Fin m, a (f k)) * coordJetOn (rectBox lo' hi') m u f
      (rectAffine lo hi lo' hi' x) -
      (∏ k : Fin m, a (f k)) * coordJetOn (rectBox lo' hi') m u f
      (rectAffine lo hi lo' hi' y)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg hp]
    calc
      (∏ k : Fin m, a (f k)) *
          |coordJetOn (rectBox lo' hi') m u f (rectAffine lo hi lo' hi' x) -
            coordJetOn (rectBox lo' hi') m u f (rectAffine lo hi lo' hi' y)| ≤
          (∏ k : Fin m, a (f k)) *
            (L * ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ ^ s) :=
        mul_le_mul_of_nonneg_left hmod hp
      _ ≤ K ^ m * (L * (D * ‖x - y‖ ^ s)) := by
        gcongr
        · exact hprod m le_rfl f
        · exact hdist x y
      _ ≤ (K ^ m * (1 + D) * L) * ‖x - y‖ ^ s := by
        have hKm : 0 ≤ K ^ m := pow_nonneg (by linarith : 0 ≤ K) _
        nlinarith [mul_nonneg (mul_nonneg hKm hL) hpow]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
