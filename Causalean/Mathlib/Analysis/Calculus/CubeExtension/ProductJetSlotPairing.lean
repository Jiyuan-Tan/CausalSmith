module
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# A fixed-slot pairing of multilinear jets

The first `i` argument slots of an order-`m` multilinear map can feed one
factor, and the remaining slots can feed a second factor. The resulting
bilinear operation is contractive and has the expected value on diagonal
tuples. Symmetrizing this operation is handled in the next module.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [i ≤ m](hyp:hi), then [there is a continuous bilinear pairing B taking an
order-i and an order-(m − i) scalar multilinear map on d-dimensional coordinate
space to an order-m multilinear map, with operator norm at most one, whose value
B(a, b) on m copies of a vector z is a(z, …, z)·b(z, …, z)](goal).

Construct the pairing by splitting `Fin m` into its first `i` slots and its
last `m-i` slots. `ContinuousMultilinearMap.curryFinFinset` supplies an
isometric slot regrouping; multiplication on `ℝ` supplies the bilinear map.
The diagonal identity then follows from
`ContinuousMultilinearMap.curryFinFinset_symm_apply_const`. -/
theorem exists_contracting_productJet_slot_pairing
    (d m i : ℕ) (hi : i ≤ m) :
    ∃ B :
        (ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ) →L[ℝ]
          (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ) →L[ℝ]
          (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ),
      ‖B‖ ≤ 1 ∧
      ∀ a b (z : Fin d → ℝ),
        B a b (fun _ => z) = a (fun _ => z) * b (fun _ => z) := by
  let s : Finset (Fin m) := Finset.image (Fin.castLE hi) Finset.univ
  have hs : s.card = i := by
    simp [s, Finset.card_image_of_injective, Fin.castLE_injective hi]
  have hsc : sᶜ.card = m - i := by
    simp [Finset.card_compl, hs]
  let C := ContinuousMultilinearMap.curryFinFinset ℝ (Fin d → ℝ) ℝ hs hsc
  let T : (ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ)) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ) := C.symm
  let S := ContinuousMultilinearMap.smulRightL ℝ
    (fun _ : Fin i => Fin d → ℝ)
    (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ)
  let B := ((ContinuousLinearMap.compL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ)
        (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ))
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)) T).comp S
  refine ⟨B, ?_, ?_⟩
  · apply B.opNorm_le_bound₂ zero_le_one
    intro a b
    change ‖T (a.smulRight b)‖ ≤ 1 * ‖a‖ * ‖b‖
    simp [T, ContinuousMultilinearMap.norm_smulRight]
  · intro a b z
    change C.symm (a.smulRight b) (fun _ => z) = _
    rw [ContinuousMultilinearMap.curryFinFinset_symm_apply_const]
    rfl

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
