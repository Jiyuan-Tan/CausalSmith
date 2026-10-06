module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetDiagonal
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetDifferenceAlgebra
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetDifferenceFirstOrder
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetPairingAlgebra
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetPolarization
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetSymmetry
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Product-jet pairing and difference estimates

This module constructs the fixed contractive pairings in the within-set product
rule and uses them to bound differences of product jets. It is the algebraic
part of Hölder control for smooth cutoff extensions.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- In [dimension d](hyp:d) and for [order m](hyp:m), [there are continuous
bilinear pairings B_i, one for each i ≤ m, taking an order-i and an
order-(m − i) multilinear map to an order-m multilinear map, each of operator
norm at most one, such that for every set S with unique within-set derivatives,
all functions v and w that are m times continuously differentiable within S,
and every point x of S lying in the closure of the interior of S, the order-m
within-S derivative of v·w at x equals the sum over i ≤ m of (m choose i) times
B_i applied to the order-i within-S derivative of v and the order-(m − i)
within-S derivative of w at x](goal). The pairings do not depend on the
functions, the set, or the point.

Use `exists_contracting_symmetric_productJet_pairing` for each `i ≤ m`.
The pairing agrees with the product of factor jets on diagonal tuples and is
invariant under permutations. Apply `iteratedFDerivWithin_mul_diagonal` to
identify the two sides on constant tuples, then use
`iteratedFDerivWithin_comp_perm_of_contDiffOn` and
`continuousMultilinearMap_eq_of_symmetric_diagonal` to recover equality of
the continuous multilinear maps. -/
theorem exists_contracting_productJet_pairings (d m : ℕ) :
    ∃ B : ∀ i : ℕ,
        (ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ) →L[ℝ]
          (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ) →L[ℝ]
          (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ),
      (∀ i ∈ Finset.range (m + 1), ‖B i‖ ≤ 1) ∧
      ∀ (S : Set (Fin d → ℝ)) (v w : (Fin d → ℝ) → ℝ)
        (x : Fin d → ℝ),
        UniqueDiffOn ℝ S → ContDiffOn ℝ m v S → ContDiffOn ℝ m w S →
        x ∈ S → x ∈ closure (interior S) →
        iteratedFDerivWithin ℝ m (fun z => v z * w z) S x =
          ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) •
            B i (iteratedFDerivWithin ℝ i v S x)
              (iteratedFDerivWithin ℝ (m - i) w S x) := by
  classical
  let B : ∀ i : ℕ,
      (ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ) :=
    fun i => if hi : i ≤ m then
      Classical.choose (exists_contracting_symmetric_productJet_pairing d m i hi)
    else 0
  have hBnorm (i : ℕ) (hi : i ≤ m) : ‖B i‖ ≤ 1 := by
    simpa only [B, dif_pos hi] using
      (Classical.choose_spec (exists_contracting_symmetric_productJet_pairing d m i hi)).1
  have hBdiag (i : ℕ) (hi : i ≤ m)
      (a : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ)
      (b : ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ)
      (z : Fin d → ℝ) :
      B i a b (fun _ => z) = a (fun _ => z) * b (fun _ => z) := by
    simpa only [B, dif_pos hi] using
      (Classical.choose_spec (exists_contracting_symmetric_productJet_pairing d m i hi)).2.1 a b z
  have hBperm (i : ℕ) (hi : i ≤ m)
      (a : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ)
      (b : ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ)
      (σ : Equiv.Perm (Fin m)) (z : Fin m → Fin d → ℝ) :
      B i a b (z ∘ σ) = B i a b z := by
    simpa only [B, dif_pos hi] using
      (Classical.choose_spec (exists_contracting_symmetric_productJet_pairing d m i hi)).2.2 a b σ z
  refine ⟨B, ?_, ?_⟩
  · intro i hi
    exact hBnorm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · intro S v w x huniq hv hw hx hxcl
    apply continuousMultilinearMap_eq_of_symmetric_diagonal
    · intro σ z
      exact iteratedFDerivWithin_comp_perm_of_contDiffOn huniq (hv.mul hw) hx hxcl σ z
    · intro σ z
      simp only [sum_apply, smul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hBperm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    · intro z
      rw [iteratedFDerivWithin_mul_diagonal huniq hv hw hx z]
      simp only [sum_apply, smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hBdiag i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- If [a set S has unique within-set derivatives](hyp:huniq), [two functions v
and w are m times continuously differentiable within S](hyp:hv,hw), and [two
points x and y lie in S](hyp:hx,hy) and [in the closure of the interior of
S](hyp:hxcl,hycl), then [the order-m within-S derivatives of v·w at x and at y
differ in norm by at most the sum over i ≤ m of (m choose i) times
‖Dⁱv(x) − Dⁱv(y)‖·‖D^(m−i)w(x)‖ + ‖Dⁱv(y)‖·‖D^(m−i)w(x) − D^(m−i)w(y)‖](goal),
where D^k denotes the order-k within-S derivative.

Apply `exists_contracting_productJet_pairings` at `x` and `y`, subtract the
two finite sums, and bound each summand by splitting its bilinear difference.
The pairing spaces depend on the summation index, so apply the pointwise
bilinear norm estimate inside `Finset.sum_le_sum`; the fixed-type lemma
`norm_bilinear_sum_sub_le` cannot be applied to the whole dependent sum.
The pairings are the same at both points and have norm at most one. The set
need only have unique within-set derivatives; convexity enters later for the
lower-jet Lipschitz estimates. -/
theorem norm_iteratedFDerivWithin_mul_sub_le
    {d m : ℕ} {S : Set (Fin d → ℝ)}
    (huniq : UniqueDiffOn ℝ S)
    {v w : (Fin d → ℝ) → ℝ}
    (hv : ContDiffOn ℝ m v S) (hw : ContDiffOn ℝ m w S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxcl : x ∈ closure (interior S))
    (hycl : y ∈ closure (interior S)) :
    ‖iteratedFDerivWithin ℝ m (fun z => v z * w z) S x -
      iteratedFDerivWithin ℝ m (fun z => v z * w z) S y‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (‖iteratedFDerivWithin ℝ i v S x - iteratedFDerivWithin ℝ i v S y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) w S x‖ +
          ‖iteratedFDerivWithin ℝ i v S y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) w S x -
              iteratedFDerivWithin ℝ (m - i) w S y‖) := by
  obtain ⟨B, hB, hform⟩ := exists_contracting_productJet_pairings d m
  rw [hform S v w x huniq hv hw hx hxcl,
    hform S v w y huniq hv hw hy hycl, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℝ) • B i (iteratedFDerivWithin ℝ i v S x)
          (iteratedFDerivWithin ℝ (m - i) w S x) -
         (m.choose i : ℝ) • B i (iteratedFDerivWithin ℝ i v S y)
          (iteratedFDerivWithin ℝ (m - i) w S y))‖ ≤
        ∑ i ∈ Finset.range (m + 1),
          ‖(m.choose i : ℝ) • B i (iteratedFDerivWithin ℝ i v S x)
            (iteratedFDerivWithin ℝ (m - i) w S x) -
           (m.choose i : ℝ) • B i (iteratedFDerivWithin ℝ i v S y)
            (iteratedFDerivWithin ℝ (m - i) w S y)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (‖iteratedFDerivWithin ℝ i v S x - iteratedFDerivWithin ℝ i v S y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) w S x‖ +
          ‖iteratedFDerivWithin ℝ i v S y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) w S x -
              iteratedFDerivWithin ℝ (m - i) w S y‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      apply mul_le_mul_of_nonneg_left _ hc
      have hbil (a : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ)
          (b : ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ) :
          ‖B i a b‖ ≤ ‖a‖ * ‖b‖ := by
        simpa using (B i).le_of_opNorm₂_le_of_le (hB i hi)
          (le_refl ‖a‖) (le_refl ‖b‖)
      have hsplit :
          B i (iteratedFDerivWithin ℝ i v S x)
              (iteratedFDerivWithin ℝ (m - i) w S x) -
            B i (iteratedFDerivWithin ℝ i v S y)
              (iteratedFDerivWithin ℝ (m - i) w S y) =
          B i (iteratedFDerivWithin ℝ i v S x - iteratedFDerivWithin ℝ i v S y)
              (iteratedFDerivWithin ℝ (m - i) w S x) +
            B i (iteratedFDerivWithin ℝ i v S y)
              (iteratedFDerivWithin ℝ (m - i) w S x -
                iteratedFDerivWithin ℝ (m - i) w S y) := by
        simp only [map_sub, sub_apply]
        abel
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add (hbil _ _) (hbil _ _))

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
