module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedBranchAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFubiniDensity
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceMeasurability

/-! # One-dimensional laws of canonical folded-score slices -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

noncomputable def foldedTailCoefficient (n K : ℕ) (h : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ) (k : ℕ) : ℝ :=
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  meshCellTransverseCoefficient (Nat.zero_lt_succ n) h idx theta (e.symm (0, z)) k

noncomputable def foldedSliceInner (n K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ) (x : ℝ) : ℝ :=
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let X := e.symm (x, z)
  x + kappa * h ^ beta * triangularWave (x / h) +
    eps * (kappa * h ^ beta) *
      (∑ j : Fin K, localSign (theta j) * meshBump (Nat.zero_lt_succ n) h (idx j) X)

noncomputable def foldedSliceScoreDensity (n q K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal 2 * perturbedMeshFoldedDensity q h (kappa * h ^ beta) eps
    (foldedTailCoefficient n K h idx theta z) (2 * t - 1 / 2)

@[fun_prop]
lemma measurable_foldedTailCoefficient (n K : ℕ) (h : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool) (k : ℕ) :
    Measurable (fun z => foldedTailCoefficient n K h idx theta z k) := by
  unfold foldedTailCoefficient
  apply (measurable_meshCellTransverseCoefficient
    (Nat.zero_lt_succ n) h idx theta k).comp
  fun_prop

@[fun_prop]
lemma measurable_foldedSliceInner (n K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ) :
    Measurable (foldedSliceInner n K beta h kappa eps idx theta z) := by
  unfold foldedSliceInner
  apply Measurable.add
  · fun_prop
  · apply Measurable.mul measurable_const
    apply Finset.measurable_fun_sum
    intro j hj
    apply Measurable.mul measurable_const
    exact (measurable_meshBump (Nat.zero_lt_succ n) h (idx j)).comp (by fun_prop)

lemma foldedTailCoefficient_mem_Icc (n K : ℕ) (h : ℝ)
    {idx : Fin K -> Fin (n + 1) -> ℕ} (hinj : Function.Injective idx)
    (theta : Fin K -> Bool) (z : Fin n -> ℝ) (k : ℕ) :
    foldedTailCoefficient n K h idx theta z k ∈ Set.Icc (-1 : ℝ) 1 := by
  apply (abs_le).mp
  exact meshCellTransverseCoefficient_abs_le_one
    (Nat.zero_lt_succ n) hinj theta _ k

lemma foldedSliceInner_eq_perturbed_cell (n q K k : ℕ)
    {beta h kappa eps x : ℝ}
    (hh : 0 < h)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ)
    (hx : x / h ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) :
    foldedSliceInner n K beta h kappa eps idx theta z x =
      perturbedTriangularCell k h (kappa * h ^ beta) eps
        (foldedTailCoefficient n K h idx theta z k) (x / h - k) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let X := e.symm (x, z)
  have hX0 : X (0 : Fin (n + 1)) = x := by
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
  have hpert := signed_meshBump_sum_factor_cell
    (Nat.zero_lt_succ n) idx theta X k (by simpa [hX0] using hx)
  have hX0' : X ⟨0, Nat.zero_lt_succ n⟩ = x := by simpa using hX0
  rw [hX0'] at hpert
  rw [hcoef] at hpert
  unfold foldedSliceInner
  dsimp only [e, X]
  rw [hpert, perturbedTriangularCell_def]
  field_simp [hh.ne']
  <;> ring

/-- Each transverse slice of the canonical pre-fold map has the exact
finite interval-mixture law. -/
lemma map_foldedSliceInner_eq_perturbedMeshMixture
    (n q K : ℕ) (hq : 0 < q) {beta h kappa eps : ℝ}
    (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (hinj : Function.Injective idx)
    (theta : Fin K -> Bool) (z : Fin n -> ℝ)
    (ha : 0 ≤ kappa * h ^ beta) (hscale : 4 ≤ kappa * h ^ beta / h)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64) :
    Measure.map (foldedSliceInner n K beta h kappa eps idx theta z)
        ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      perturbedMeshMixture q h (kappa * h ^ beta) eps
        (foldedTailCoefficient n K h idx theta z) := by
  apply map_eq_perturbedMeshMixture q hq hhq
    (foldedTailCoefficient n K h idx theta z)
    (fun k hk => foldedTailCoefficient_mem_Icc n K h hinj theta z k)
    ha hscale heps0 heps
    (measurable_foldedSliceInner n K beta h kappa eps idx theta z)
  intro k hk x hx
  apply foldedSliceInner_eq_perturbed_cell n q K k
    (by rw [hhq]; positivity) idx theta z
  rw [hhq] at hx ⊢
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · calc
      (k : ℝ) = (k : ℝ) * (q : ℝ)⁻¹ / (q : ℝ)⁻¹ := by field_simp
      _ ≤ x / (q : ℝ)⁻¹ := (div_le_div_iff_of_pos_right (inv_pos.mpr hqR)).2 hx.1
  · calc
      x / (q : ℝ)⁻¹ ≤ ((k : ℝ) + 1) * (q : ℝ)⁻¹ / (q : ℝ)⁻¹ :=
        (div_le_div_iff_of_pos_right (inv_pos.mpr hqR)).2 hx.2
      _ = (k : ℝ) + 1 := by field_simp

lemma foldedRawScore_slice_eq (n K : ℕ) {beta h kappa eps : ℝ}
    (hbeta : beta < 1)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool)
    (z : Fin n -> ℝ) (x : ℝ) :
    foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
        (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
        ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0).symm (x, z)) =
      1 / 4 + 1 / 2 * triangularFold
        (foldedSliceInner n K beta h kappa eps idx theta z x) := by
  unfold foldedRawScore foldedSliceInner
  simp only [hbeta, if_true]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- The score law of every transverse slice has the explicit rescaled folded
density. -/
lemma map_foldedRawScore_slice_eq_withDensity
    (n q K : ℕ) (hq : 0 < q) {beta h kappa eps : ℝ}
    (hbeta : beta < 1) (hhq : h = (q : ℝ)⁻¹)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (hinj : Function.Injective idx)
    (theta : Fin K -> Bool) (z : Fin n -> ℝ)
    (ha : 0 ≤ kappa * h ^ beta) (hscale : 4 ≤ kappa * h ^ beta / h)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (hsmall : kappa * h ^ beta * (1 + eps) ≤ 1 / 12) :
    Measure.map
        (fun x => foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
          (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
          ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => ℝ) 0).symm (x, z)))
        ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      (volume : Measure ℝ).withDensity
        (foldedSliceScoreDensity n q K beta h kappa eps idx theta z) := by
  let inner := foldedSliceInner n K beta h kappa eps idx theta z
  let foldScore : ℝ -> ℝ := fun y => 1 / 4 + 1 / 2 * triangularFold y
  have hinner : Measurable inner :=
    measurable_foldedSliceInner n K beta h kappa eps idx theta z
  have hfold : Measurable foldScore := by dsimp [foldScore]; fun_prop
  have hraw : (fun x => foldedRawScore (Nat.zero_lt_succ n) beta h kappa eps K
          (fun j => meshBump (Nat.zero_lt_succ n) h (idx j)) theta
          ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => ℝ) 0).symm (x, z))) = foldScore ∘ inner := by
    funext x
    exact foldedRawScore_slice_eq n K hbeta idx theta z x
  rw [hraw, ← Measure.map_map hfold hinner]
  rw [map_foldedSliceInner_eq_perturbedMeshMixture n q K hq hhq idx hinj
    theta z ha hscale heps0 heps]
  change Measure.map (fun y : ℝ => 1 / 4 + 1 / 2 * triangularFold y) _ = _
  rw [show (fun y : ℝ => 1 / 4 + 1 / 2 * triangularFold y) =
      (fun y : ℝ => 1 / 4 + 1 / 2 * y) ∘ triangularFold by rfl,
    ← Measure.map_map
      (by fun_prop : Measurable (fun y : ℝ => 1 / 4 + 1 / 2 * y))
      measurable_triangularFold,
    map_triangularFold_perturbedMeshMixture_of_small q hq hhq
      (foldedTailCoefficient n K h idx theta z)
      (fun k hk => foldedTailCoefficient_mem_Icc n K h hinj theta z k)
      ha heps0 heps hsmall,
    map_scoreAffine_withDensity]
  · rfl
  · exact measurable_perturbedMeshFoldedDensity q h
      (kappa * h ^ beta) eps (foldedTailCoefficient n K h idx theta z)

end CausalSmith.Experimentation.PilotscorePairingFrontier
