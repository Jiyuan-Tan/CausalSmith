module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic

/-! # Finite active-cell enumeration for the folded hypercube -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

/-- An active mesh index determines a side cube of reciprocal-integer width. -/
lemma activeMeshCell_isSideCube (hd : 0 < d) (q : ℕ) (hq : 0 < q)
    (v : Fin d → ℕ) (hv : activeMeshCell hd q v) :
    IsSideCube ((q : ℝ)⁻¹) (meshCube ((q : ℝ)⁻¹) v) := by
  let a : XSpace d := fun i => (v i : ℝ) * (q : ℝ)⁻¹
  refine ⟨a, ?_, ?_⟩
  · intro i
    constructor
    · dsimp [a]
      positivity
    · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hvi : (v i : ℝ) + 1 ≤ q := by
        exact_mod_cast (Nat.succ_le_of_lt (hv.1 i))
      dsimp [a]
      calc
        (v i : ℝ) * (q : ℝ)⁻¹ + (q : ℝ)⁻¹ =
            ((v i : ℝ) + 1) * (q : ℝ)⁻¹ := by ring
        _ ≤ (q : ℝ) * (q : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hvi (inv_nonneg.mpr hqR.le)
        _ = 1 := mul_inv_cancel₀ hqR.ne'
  · ext x
    simp [meshCube, a, add_mul]

/-- Every positive reciprocal mesh has a finite, duplicate-free enumeration
of exactly its active cells, with the canonical cubes, bumps, and cores. -/
lemma exists_foldedGeometry (hd : 0 < d) (q : ℕ) (hq : 0 < q) :
    ∃ K : ℕ, ∃ Q : Fin K → Set (XSpace d),
      ∃ ψ : Fin K → XSpace d → ℝ, ∃ B : Fin K → Set (XSpace d),
        FoldedGeometry hd q K Q ψ B := by
  classical
  let Active := {v : Fin d → Fin q |
    activeMeshCell hd q (fun i => (v i).val)}
  let e : Active ≃ Fin (Fintype.card Active) := Fintype.equivFin Active
  let k : Fin (Fintype.card Active) → Fin d → ℕ :=
    fun j i => ((e.symm j).val i).val
  let Q : Fin (Fintype.card Active) → Set (XSpace d) :=
    fun j => meshCube ((q : ℝ)⁻¹) (k j)
  let ψ : Fin (Fintype.card Active) → XSpace d → ℝ :=
    fun j => meshBump hd ((q : ℝ)⁻¹) (k j)
  let B : Fin (Fintype.card Active) → Set (XSpace d) :=
    fun j => meshCore hd ((q : ℝ)⁻¹) (k j)
  refine ⟨Fintype.card Active, Q, ψ, B, hq, k, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    funext r
    apply Fin.ext
    exact congrFun hij r
  · intro v
    constructor
    · intro hv
      let w : Active :=
        ⟨fun i => ⟨v i, hv.1 i⟩, by
          simpa [Active] using hv⟩
      refine ⟨e w, ?_⟩
      funext i
      simp [k, w]
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
  · intro j
    exact ⟨rfl, rfl, rfl⟩

/-- Every cube in a folded-geometry enumeration is a reciprocal-width side
cube. -/
lemma FoldedGeometry.isSideCube {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (j : Fin K) :
    IsSideCube ((q : ℝ)⁻¹) (Q j) := by
  rcases hgeo with ⟨hq, k, hk, hcomplete, hdefs⟩
  have hactive : activeMeshCell hd q (k j) :=
    (hcomplete (k j)).2 ⟨j, rfl⟩
  rw [(hdefs j).1]
  exact activeMeshCell_isSideCube hd q hq (k j) hactive

end CausalSmith.Experimentation.PilotscorePairingFrontier
