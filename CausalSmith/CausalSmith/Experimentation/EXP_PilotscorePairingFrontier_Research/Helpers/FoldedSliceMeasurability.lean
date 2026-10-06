module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceAgreement

/-! # Measurability of folded score slices -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

@[fun_prop]
lemma measurable_foldedFirstBump : Measurable foldedFirstBump := by
  unfold foldedFirstBump
  fun_prop

@[fun_prop]
lemma measurable_foldedTransverseBump : Measurable foldedTransverseBump := by
  unfold foldedTransverseBump
  fun_prop

@[fun_prop]
lemma measurable_meshTransverseBump (h : ℝ) (k : Fin d -> ℕ) :
    Measurable (meshTransverseBump h k) := by
  unfold meshTransverseBump
  apply Finset.measurable_fun_prod
  intro i hi
  by_cases hi0 : i.val = 0
  · simp [hi0]
  · simp only [hi0, if_false]
    fun_prop

@[fun_prop]
lemma measurable_meshBump (hd : 0 < d) (h : ℝ) (k : Fin d -> ℕ) :
    Measurable (meshBump hd h k) := by
  unfold meshBump
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_fun_prod
    intro i hi
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · simp only [hi0, if_false]
      fun_prop

@[fun_prop]
lemma measurable_meshCellTransverseCoefficient (hd : 0 < d) (h : ℝ)
    (idx : Fin K -> Fin d -> ℕ) (theta : Fin K -> Bool) (k : ℕ) :
    Measurable (fun x => meshCellTransverseCoefficient hd h idx theta x k) := by
  unfold meshCellTransverseCoefficient
  apply Finset.measurable_fun_sum
  intro j hj
  by_cases hjk : idx j ⟨0, hd⟩ = k
  · simp only [hjk, if_true]
    fun_prop
  · simp [hjk]

/-- The transverse coefficient does not depend on the first coordinate. -/
lemma meshCellTransverseCoefficient_eq_of_tail_eq (hd : 0 < d) (h : ℝ)
    (idx : Fin K -> Fin d -> ℕ) (theta : Fin K -> Bool)
    {x y : XSpace d} (hxy : forall i : Fin d, i.val ≠ 0 -> x i = y i)
    (k : ℕ) :
    meshCellTransverseCoefficient hd h idx theta x k =
      meshCellTransverseCoefficient hd h idx theta y k := by
  classical
  unfold meshCellTransverseCoefficient meshTransverseBump
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hi0 : i.val = 0
  · simp [hi0]
  · simp [hi0, hxy i hi0]

end CausalSmith.Experimentation.PilotscorePairingFrontier
