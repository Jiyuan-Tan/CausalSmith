module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ProductJetSlotPairing
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Algebraic pairings for product jets

A pair of multilinear maps can be combined into a multilinear map by
averaging over the ways to assign argument slots to the two factors. This
module isolates the algebraic construction from the derivative product rule.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- If [i ≤ m](hyp:hi), then [there is a continuous bilinear pairing B taking an
order-i and an order-(m − i) scalar multilinear map on d-dimensional coordinate
space to an order-m multilinear map, with operator norm at most one, whose value
B(a, b) on m copies of a vector z is a(z, …, z)·b(z, …, z), and whose output is
invariant under every permutation of its m arguments](goal).

Apply `exists_contracting_productJet_slot_pairing`, then average its output
over the finite group `Equiv.Perm (Fin m)`. Each permutation of input slots
acts isometrically on continuous multilinear maps. The average has norm at
most one because every summand does, including when `m = 0`. Constant tuples
are fixed by permutations, so the diagonal identity survives the average.
For invariance, reindex the finite sum by right composition with the given
permutation. This lemma is purely algebraic and makes no differentiability
assumption. -/
theorem exists_contracting_symmetric_productJet_pairing
    (d m i : ℕ) (hi : i ≤ m) :
    ∃ B :
        (ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin d → ℝ) ℝ) →L[ℝ]
          (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ) →L[ℝ]
          (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ),
      ‖B‖ ≤ 1 ∧
      (∀ a b (z : Fin d → ℝ),
        B a b (fun _ => z) = a (fun _ => z) * b (fun _ => z)) ∧
      (∀ a b (σ : Equiv.Perm (Fin m)) (z : Fin m → Fin d → ℝ),
        B a b (z ∘ σ) = B a b z) := by
  obtain ⟨B₀, hB₀, hdiag⟩ := exists_contracting_productJet_slot_pairing d m i hi
  let N : ℝ := Fintype.card (Equiv.Perm (Fin m))
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := Equiv.Perm (Fin m))
  let P (σ : Equiv.Perm (Fin m)) :
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ) :=
    let e := ContinuousMultilinearMap.domDomCongrₗᵢ ℝ (Fin d → ℝ) ℝ σ
    e.toLinearIsometry.toContinuousLinearMap
  let A :
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ) :=
    N⁻¹ • ∑ σ : Equiv.Perm (Fin m), P σ
  have hA : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound zero_le_one
    intro f
    have hsum : ‖∑ σ : Equiv.Perm (Fin m), P σ f‖ ≤ N * ‖f‖ := by
      calc
        ‖∑ σ : Equiv.Perm (Fin m), P σ f‖ ≤
            ∑ σ : Equiv.Perm (Fin m), ‖P σ f‖ := norm_sum_le _ _
        _ = N * ‖f‖ := by
          simp [P, N]
    change ‖N⁻¹ • (∑ σ : Equiv.Perm (Fin m), P σ) f‖ ≤ 1 * ‖f‖
    simp only [sum_apply, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hN, one_mul]
    calc
      N⁻¹ * ‖∑ σ : Equiv.Perm (Fin m), P σ f‖ ≤ N⁻¹ * (N * ‖f‖) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)
      _ = ‖f‖ := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  have hA_apply (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)
      (z : Fin m → Fin d → ℝ) :
      A f z = N⁻¹ * ∑ σ : Equiv.Perm (Fin m), f (z ∘ σ) := by
    simp [A, P, ContinuousMultilinearMap.domDomCongrₗᵢ,
      ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def, smul_eq_mul]
  have hA_diag (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)
      (z : Fin d → ℝ) : A f (fun _ => z) = f (fun _ => z) := by
    rw [hA_apply]
    have hconst : (∑ σ : Equiv.Perm (Fin m), f ((fun _ => z) ∘ σ)) =
        N * f (fun _ => z) := by simp [N, Function.comp_def]
    rw [hconst, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  have hA_perm (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)
      (σ : Equiv.Perm (Fin m)) (z : Fin m → Fin d → ℝ) :
      A f (z ∘ σ) = A f z := by
    rw [hA_apply, hA_apply]
    congr 1
    let e : Equiv.Perm (Equiv.Perm (Fin m)) := Equiv.mulLeft σ
    convert (Equiv.sum_comp e (fun τ : Equiv.Perm (Fin m) => f (z ∘ τ))) using 1;
      simp [e, Function.comp_assoc, Equiv.Perm.mul_def]
  let B := ((ContinuousLinearMap.compL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin (m - i) => Fin d → ℝ) ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin d → ℝ) ℝ)) A).comp B₀
  refine ⟨B, ?_, ?_, ?_⟩
  · apply B.opNorm_le_bound₂ zero_le_one
    intro a b
    change ‖A (B₀ a b)‖ ≤ 1 * ‖a‖ * ‖b‖
    have hB₀ab : ‖B₀ a b‖ ≤ ‖a‖ * ‖b‖ := by
      calc
        ‖B₀ a b‖ ≤ ‖B₀ a‖ * ‖b‖ := (B₀ a).le_opNorm b
        _ ≤ (‖B₀‖ * ‖a‖) * ‖b‖ :=
          mul_le_mul_of_nonneg_right (B₀.le_opNorm a) (norm_nonneg _)
        _ ≤ ‖a‖ * ‖b‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          calc
            ‖B₀‖ * ‖a‖ ≤ 1 * ‖a‖ :=
              mul_le_mul_of_nonneg_right hB₀ (norm_nonneg _)
            _ = ‖a‖ := one_mul _
    calc
      ‖A (B₀ a b)‖ ≤ ‖A‖ * ‖B₀ a b‖ := A.le_opNorm _
      _ ≤ 1 * ‖B₀ a b‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ 1 * (‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left hB₀ab zero_le_one
      _ = 1 * ‖a‖ * ‖b‖ := by ring
  · intro a b z
    change A (B₀ a b) (fun _ => z) = _
    rw [hA_diag, hdiag]
  · intro a b σ z
    change A (B₀ a b) (z ∘ σ) = A (B₀ a b) z
    exact hA_perm _ _ _

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
