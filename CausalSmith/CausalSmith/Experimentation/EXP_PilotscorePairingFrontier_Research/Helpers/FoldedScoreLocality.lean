module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedGeometryBounds

/-! # Coordinate locality of the folded score -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma foldedHypercube_flip_eq_of_bump_eq_zero (hd : 0 < d) (β h κ ε : ℝ)
    (K : ℕ) (ψ : Fin K → XSpace d → ℝ) (θ : Fin K → Bool)
    (j : Fin K) (x : XSpace d) (hψ : ψ j x = 0) :
    foldedHypercube hd β h κ ε K ψ θ x =
      foldedHypercube hd β h κ ε K ψ (flipCoordinate θ j) x := by
  have hsum : (∑ i : Fin K, localSign (θ i) * ψ i x) =
      ∑ i : Fin K, localSign ((flipCoordinate θ j) i) * ψ i x := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : i = j
    · subst i
      simp [hψ]
    · simp [flipCoordinate, hij]
  simp only [foldedHypercube, foldedRawScore]
  rw [hsum]

lemma FoldedGeometry.foldedHypercube_flip_eq_off_cell
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {ψ : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (β κ ε : ℝ)
    (θ : Fin K → Bool) (j : Fin K) (x : XSpace d) (hx : x ∉ Q j) :
    foldedHypercube hd β (q : ℝ)⁻¹ κ ε K ψ θ x =
      foldedHypercube hd β (q : ℝ)⁻¹ κ ε K ψ (flipCoordinate θ j) x := by
  apply foldedHypercube_flip_eq_of_bump_eq_zero
  exact hgeo.bump_eq_zero_off_cell j hx

end CausalSmith.Experimentation.PilotscorePairingFrontier
