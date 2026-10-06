module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceAgreement
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedKLAssembly

/-! # Beta-one score slices -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

noncomputable def linearFoldedSlice (n K : ℕ) (h eps : ℝ)
    (idx : Fin K → Fin (n + 1) → ℕ) (theta : Fin K → Bool)
    (z : Fin n → ℝ) (x : ℝ) : ℝ :=
  foldedRawScore (Nat.zero_lt_succ n) 1 h 1 eps K
    (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x, z))

@[fun_prop]
lemma measurable_linearFoldedSlice (n K : ℕ) (h eps : ℝ)
    (idx : Fin K → Fin (n + 1) → ℕ) (theta : Fin K → Bool)
    (z : Fin n → ℝ) :
    Measurable (linearFoldedSlice n K h eps idx theta z) := by
  unfold linearFoldedSlice
  apply (measurable_foldedRawScore_of_measurable_bumps
    (Nat.zero_lt_succ n) 1 h 1 eps K _ (fun j => measurable_meshBump _ _ _) theta).comp
  fun_prop

lemma linearFoldedSlice_eq_cell (n K k : ℕ) {h eps x : ℝ}
    (hh : 0 < h) (idx : Fin K → Fin (n + 1) → ℕ) (theta : Fin K → Bool)
    (z : Fin n → ℝ)
    (hx : x / h ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    linearFoldedSlice n K h eps idx theta z x =
      linearFoldedCell k h eps (foldedTailCoefficient n K h idx theta z k)
        (x / h - k) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let X := e.symm (x, z)
  have hX0 : X ⟨0, Nat.zero_lt_succ n⟩ = x := by
    simp [X, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have htail (i : Fin (n + 1)) (hi : i.val ≠ 0) :
      X i = (e.symm (0, z)) i := by
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero (by simpa using hi)
    simp [X, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hcoef : meshCellTransverseCoefficient (Nat.zero_lt_succ n) h idx theta X k =
      foldedTailCoefficient n K h idx theta z k := by
    rw [foldedTailCoefficient]
    exact meshCellTransverseCoefficient_eq_of_tail_eq
      (Nat.zero_lt_succ n) h idx theta htail k
  have hfactor := signed_meshBump_sum_factor_cell
    (Nat.zero_lt_succ n) idx theta X k (by rw [hX0]; exact hx)
  rw [hX0] at hfactor
  rw [hcoef] at hfactor
  unfold linearFoldedSlice foldedRawScore
  rw [linearFoldedCell_def]
  simp only [lt_self_iff_false, if_false, Real.rpow_one]
  change 1 / 4 + X ⟨0, Nat.zero_lt_succ n⟩ / 2 +
      eps * h * (∑ j, localSign (theta j) * meshBump _ h (idx j) X) = _
  rw [hX0, hfactor]
  field_simp [hh.ne']
  ring

/-- Every transverse beta-one slice has the explicit affine-mesh density. -/
lemma map_linearFoldedSlice_eq_withDensity
    (n q K : ℕ) (hq : 0 < q) {h eps : ℝ} (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K → Fin (n + 1) → ℕ) (hinj : Function.Injective idx)
    (theta : Fin K → Bool) (z : Fin n → ℝ)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 128) :
    Measure.map (linearFoldedSlice n K h eps idx theta z)
        ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      (volume : Measure ℝ).withDensity
        (linearMeshDensity q h eps (foldedTailCoefficient n K h idx theta z)) := by
  apply map_linear_mesh_eq_withDensity q hq hhq _
    (fun k => foldedTailCoefficient_mem_Icc n K h hinj theta z k)
    heps0 heps (measurable_linearFoldedSlice n K h eps idx theta z)
  intro k hk x hx
  apply linearFoldedSlice_eq_cell n K k (by rw [hhq]; positivity) idx theta z
  rw [hhq] at hx ⊢
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · calc
      (k : ℝ) = (k : ℝ) * (q : ℝ)⁻¹ / (q : ℝ)⁻¹ := by field_simp
      _ ≤ x / (q : ℝ)⁻¹ :=
        (div_le_div_iff_of_pos_right (inv_pos.mpr hqR)).2 hx.1
  · calc
      x / (q : ℝ)⁻¹ ≤ ((k : ℝ) + 1) * (q : ℝ)⁻¹ / (q : ℝ)⁻¹ :=
        (div_le_div_iff_of_pos_right (inv_pos.mpr hqR)).2 hx.2
      _ = (k : ℝ) + 1 := by field_simp

end CausalSmith.Experimentation.PilotscorePairingFrontier
