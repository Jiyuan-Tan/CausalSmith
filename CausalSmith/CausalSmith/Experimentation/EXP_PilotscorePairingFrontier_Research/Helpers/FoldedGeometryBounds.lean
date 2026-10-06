module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedConstruction
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedBump

/-! # Set-theoretic bounds for folded mesh cells -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma meshCore_subset_meshCube (hd : 0 < d) (q : ℕ) (hq : 0 < q)
    (k : Fin d → ℕ) :
    meshCore hd ((q : ℝ)⁻¹) k ⊆ meshCube ((q : ℝ)⁻¹) k := by
  intro x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  refine ⟨hx.1, fun i => ?_⟩
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, hd⟩ := Fin.ext hi
    subst i
    constructor
    · have hlo := hx.2.1
      have hfrac : (0 : ℝ) ≤ 7 / 16 * (q : ℝ)⁻¹ := by positivity
      rw [add_mul] at hlo
      linarith
    · left
      have hhi := hx.2.2.1
      rw [add_mul] at hhi
      have hfrac : 9 / 16 * (q : ℝ)⁻¹ < 1 * (q : ℝ)⁻¹ := by
        exact mul_lt_mul_of_pos_right (by norm_num) hh
      linarith
  · constructor
    · have hlo := (hx.2.2.2 i hi).1
      have hfrac : (0 : ℝ) ≤ 1 / 4 * (q : ℝ)⁻¹ := by positivity
      rw [add_mul] at hlo
      linarith
    · left
      have hhi := (hx.2.2.2 i hi).2
      rw [add_mul] at hhi
      have hfrac : 3 / 4 * (q : ℝ)⁻¹ < 1 * (q : ℝ)⁻¹ := by
        exact mul_lt_mul_of_pos_right (by norm_num) hh
      linarith

lemma FoldedGeometry.core_subset {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (j : Fin K) : B j ⊆ Q j := by
  rcases hgeo with ⟨hq, k, hk, hcomplete, hdefs⟩
  rw [(hdefs j).1, (hdefs j).2.2]
  exact meshCore_subset_meshCube hd q hq (k j)

lemma FoldedGeometry.bump_bounds {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (j : Fin K) (x : XSpace d) :
    0 ≤ ψ j x ∧ ψ j x ≤ 1 := by
  rcases hgeo with ⟨hq, k, hk, hcomplete, hdefs⟩
  rw [(hdefs j).2.1]
  exact ⟨meshBump_nonneg hd _ _ _, meshBump_le_one hd _ _ _⟩

lemma FoldedGeometry.bump_eq_zero_off_cell {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (j : Fin K) {x : XSpace d}
    (hx : x ∉ Q j) : ψ j x = 0 := by
  rcases hgeo with ⟨hq, k, hk, hcomplete, hdefs⟩
  have hactive : activeMeshCell hd q (k j) :=
    (hcomplete (k j)).2 ⟨j, rfl⟩
  rw [(hdefs j).1] at hx
  rw [(hdefs j).2.1]
  exact meshBump_eq_zero_off_cube hd q hq (k j) hactive.1 hx

lemma FoldedGeometry.bump_eq_one_on_core {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (j : Fin K) {x : XSpace d}
    (hx : x ∈ B j) : ψ j x = 1 := by
  rcases hgeo with ⟨hq, k, hk, hcomplete, hdefs⟩
  rw [(hdefs j).2.2] at hx
  rw [(hdefs j).2.1]
  exact meshBump_eq_one_on_core hd (inv_pos.mpr (by exact_mod_cast hq)) (k j) hx

lemma meshCore_measure_lower (hd : 0 < d) (q : ℕ) (hq : 0 < q)
    (k : Fin d → ℕ) (hk : ∀ i, k i < q) :
    (((q : ℝ)⁻¹ / 8) ^ d) ≤
      (cubeMeasure d).real (meshCore hd ((q : ℝ)⁻¹) k) := by
  let h : ℝ := (q : ℝ)⁻¹
  let lo : XSpace d := fun i => (k i + 7 / 16 : ℝ) * h
  let hi : XSpace d := fun i => (k i + 9 / 16 : ℝ) * h
  let R : Set (XSpace d) := Set.Icc lo hi
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < h := by dsimp [h]; positivity
  have hle : lo ≤ hi := by
    intro i
    dsimp [lo, hi]
    exact mul_le_mul_of_nonneg_right (by norm_num) hh.le
  have hRcube : R ⊆ cube d := by
    intro x hx i
    have hki : (k i : ℝ) + 1 ≤ q := by
      exact_mod_cast Nat.succ_le_of_lt (hk i)
    have hupper : ((k i : ℝ) + 1) * h ≤ 1 := by
      calc
        ((k i : ℝ) + 1) * h ≤ (q : ℝ) * h :=
          mul_le_mul_of_nonneg_right hki hh.le
        _ = 1 := by dsimp [h]; exact mul_inv_cancel₀ hqR.ne'
    constructor
    · have hlo0 : 0 ≤ lo i := by dsimp [lo]; positivity
      exact hlo0.trans (hx.1 i)
    · have hfrac : (k i + 9 / 16 : ℝ) < (k i : ℝ) + 1 := by norm_num
      exact (hx.2 i).trans (mul_le_mul_of_nonneg_right hfrac.le hh.le |>.trans hupper)
  have hRcore : R ⊆ meshCore hd h k := by
    intro x hx
    refine ⟨hRcube hx, ?_, ?_, ?_⟩
    · exact hx.1 ⟨0, hd⟩
    · exact hx.2 ⟨0, hd⟩
    · intro i hi0
      constructor
      · have hfrac : (k i + 1 / 4 : ℝ) ≤ k i + 7 / 16 := by norm_num
        exact (mul_le_mul_of_nonneg_right hfrac hh.le).trans (hx.1 i)
      · have hfrac : (k i + 9 / 16 : ℝ) ≤ k i + 3 / 4 := by norm_num
        exact (hx.2 i).trans (mul_le_mul_of_nonneg_right hfrac hh.le)
  have hRmeas : MeasurableSet R := measurableSet_Icc
  have hcubeMeas : MeasurableSet (cube d) := by
    exact MeasurableSet.univ_pi' (fun _ : Fin d => measurableSet_Icc)
  have hRmass : (cubeMeasure d).real R = (h / 8) ^ d := by
    have hrestrict : (cubeMeasure d).real R = volume.real R := by
      unfold cubeMeasure
      rw [measureReal_restrict_apply' hcubeMeas]
      simp [Set.inter_eq_self_of_subset_left hRcube, ← MeasureTheory.volume_pi]
    rw [hrestrict]
    dsimp [R]
    rw [measureReal_def, Real.volume_Icc_pi_toReal hle]
    have hdiff : ∀ i : Fin d, hi i - lo i = h / 8 := by
      intro i
      dsimp [hi, lo]
      ring
    simp_rw [hdiff]
    simp [div_pow]
  rw [show (q : ℝ)⁻¹ = h by rfl, ← hRmass]
  have hfinite : cubeMeasure d Set.univ ≠ ⊤ := by
    unfold cubeMeasure
    rw [Measure.restrict_apply_univ]
    rw [show cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) by
        ext x
        simp only [cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
          true_implies, Set.mem_Icc]]
    rw [Measure.pi_pi]
    simp [Real.volume_Icc]
  exact measureReal_mono hRcore (ne_top_of_le_ne_top hfinite
    (measure_mono (Set.subset_univ (meshCore hd h k))))

lemma FoldedGeometry.core_measure_lower {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) (j : Fin K) :
    (((q : ℝ)⁻¹ / 8) ^ d) ≤ (cubeMeasure d).real (B j) := by
  rcases hgeo with ⟨hq, k, hk, hcomplete, hdefs⟩
  have hactive : activeMeshCell hd q (k j) :=
    (hcomplete (k j)).2 ⟨j, rfl⟩
  rw [(hdefs j).2.2]
  exact meshCore_measure_lower hd q hq (k j) hactive.1

lemma meshCube_disjoint_of_ne (q : ℕ) (hq : 0 < q)
    {k l : Fin d → ℕ} (hk : ∀ i, k i < q) (hl : ∀ i, l i < q)
    (hkl : k ≠ l) :
    Disjoint (meshCube ((q : ℝ)⁻¹) k) (meshCube ((q : ℝ)⁻¹) l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hkl
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hsucc : k i + 1 ≤ l i := Nat.succ_le_of_lt hlt
    have hreal : ((k i : ℝ) + 1) * (q : ℝ)⁻¹ ≤
        (l i : ℝ) * (q : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) hh.le
    rcases (hxk.2 i).2 with hstrict | hend
    · exact (not_lt_of_ge ((hreal.trans (hxl.2 i).1))) hstrict
    · have hkq : k i + 1 < q := lt_of_le_of_lt hsucc (hl i)
      have hboundary : ((k i : ℝ) + 1) * (q : ℝ)⁻¹ < 1 := by
        calc
          ((k i : ℝ) + 1) * (q : ℝ)⁻¹ < (q : ℝ) * (q : ℝ)⁻¹ :=
            mul_lt_mul_of_pos_right (by exact_mod_cast hkq) hh
          _ = 1 := mul_inv_cancel₀ hqR.ne'
      linarith [hend.1, hend.2]
  · have hsucc : l i + 1 ≤ k i := Nat.succ_le_of_lt hgt
    have hreal : ((l i : ℝ) + 1) * (q : ℝ)⁻¹ ≤
        (k i : ℝ) * (q : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) hh.le
    rcases (hxl.2 i).2 with hstrict | hend
    · exact (not_lt_of_ge ((hreal.trans (hxk.2 i).1))) hstrict
    · have hlq : l i + 1 < q := lt_of_le_of_lt hsucc (hk i)
      have hboundary : ((l i : ℝ) + 1) * (q : ℝ)⁻¹ < 1 := by
        calc
          ((l i : ℝ) + 1) * (q : ℝ)⁻¹ < (q : ℝ) * (q : ℝ)⁻¹ :=
            mul_lt_mul_of_pos_right (by exact_mod_cast hlq) hh
          _ = 1 := mul_inv_cancel₀ hqR.ne'
      linarith [hend.1, hend.2]

lemma FoldedGeometry.pairwise_disjoint {hd : 0 < d} {q K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q ψ B) {i j : Fin K} (hij : i ≠ j) :
    Disjoint (Q i) (Q j) := by
  rcases hgeo with ⟨hq, k, hkinj, hcomplete, hdefs⟩
  have hi : activeMeshCell hd q (k i) := (hcomplete (k i)).2 ⟨i, rfl⟩
  have hj : activeMeshCell hd q (k j) := (hcomplete (k j)).2 ⟨j, rfl⟩
  rw [(hdefs i).1, (hdefs j).1]
  exact meshCube_disjoint_of_ne q hq hi.1 hj.1 (fun h => hij (hkinj h))

end CausalSmith.Experimentation.PilotscorePairingFrontier
