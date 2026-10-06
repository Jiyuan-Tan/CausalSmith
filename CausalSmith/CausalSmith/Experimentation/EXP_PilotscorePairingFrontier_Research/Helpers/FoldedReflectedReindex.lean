module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSignedEnvelope

/-! # Reindexing the three reflected boundary blocks -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

noncomputable def perturbedShiftedIndices (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (i : Fin 7) (y : ℝ) : Finset ℤ :=
  shiftedGridIndices h
    (perturbedBranches h a ε 0 i).lower
    (perturbedBranches h a ε 0 i).upper (ε * a)
    (perturbedBranchLowerShift h a ε (reflectedCoefficient q c) i)
    (perturbedBranchUpperShift h a ε (reflectedCoefficient q c) i) y

noncomputable def negativeGridBlock (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (i : Fin 7) (y : ℝ) : Finset ℤ :=
  (perturbedShiftedIndices q h a ε c i y).filter
    (fun z : ℤ => -(q : ℤ) ≤ z ∧ z < 0)

noncomputable def middleGridBlock (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (i : Fin 7) (y : ℝ) : Finset ℤ :=
  (perturbedShiftedIndices q h a ε c i y).filter
    (fun z : ℤ => 0 ≤ z ∧ z < q)

noncomputable def upperGridBlock (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (i : Fin 7) (y : ℝ) : Finset ℤ :=
  (perturbedShiftedIndices q h a ε c i y).filter
    (fun z : ℤ => (q : ℤ) ≤ z ∧ z < 2 * q)

lemma sum_shiftedIndices_eq_three_blocks {q : ℕ} {h a ε y : ℝ}
    (c : ℕ → ℝ) (hq : 0 < q) (hhq : h = (q : ℝ)⁻¹)
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (ha12 : a ≤ 1 / 12)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (i : Fin 7) :
    (∑ z ∈ perturbedShiftedIndices q h a ε c i y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) =
      (∑ z ∈ negativeGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) +
      (∑ z ∈ middleGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) +
      (∑ z ∈ upperGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) := by
  classical
  let s := perturbedShiftedIndices q h a ε c i y
  let f := perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i
  have hbounds (z : ℤ) (hz : z ∈ s) : -(q : ℤ) ≤ z ∧ z < 2 * (q : ℤ) := by
    exact shiftedPerturbed_index_bounds hq hhq ha hε0 hε
      (reflectedCoefficient_mem_Icc hc) ha12 hy i hz
  change (∑ z ∈ s, f z) =
    (∑ z ∈ s.filter (fun z : ℤ => -(q : ℤ) ≤ z ∧ z < 0), f z) +
    (∑ z ∈ s.filter (fun z : ℤ => 0 ≤ z ∧ z < q), f z) +
    (∑ z ∈ s.filter (fun z : ℤ => (q : ℤ) ≤ z ∧ z < 2 * q), f z)
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hb := hbounds z hz
  by_cases hz0 : z < 0
  · have hnmid : ¬(0 ≤ z ∧ z < (q : ℤ)) := by omega
    have hnupper : ¬((q : ℤ) ≤ z ∧ z < 2 * (q : ℤ)) := by
      have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
      omega
    simp [hz0, hb.1, hnmid, hnupper]
  · have hz0' : 0 ≤ z := le_of_not_gt hz0
    by_cases hzq : z < q
    · have hnneg : ¬(-(q : ℤ) ≤ z ∧ z < 0) := by omega
      have hnupper : ¬((q : ℤ) ≤ z ∧ z < 2 * (q : ℤ)) := by omega
      simp [hz0, hz0', hzq, hnneg, hnupper]
    · have hzq' : (q : ℤ) ≤ z := le_of_not_gt hzq
      have hnneg : ¬(-(q : ℤ) ≤ z ∧ z < 0) := by omega
      have hnmid : ¬(0 ≤ z ∧ z < (q : ℤ)) := by omega
      simp [hz0, hz0', hzq, hzq', hb.2, hnneg, hnmid]

noncomputable def perturbedMeshFoldedDensityReal (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range q, ∑ i : Fin 7, (
    (Set.Icc (perturbedCellLower k h a ε (c k) i)
      (perturbedCellUpper k h a ε (c k) i)).indicator
        (fun _ => h / (perturbedBranches h a ε (c k) i).slope) (-y) +
    (Set.Icc (perturbedCellLower k h a ε (c k) i)
      (perturbedCellUpper k h a ε (c k) i)).indicator
        (fun _ => h / (perturbedBranches h a ε (c k) i).slope) y +
    (Set.Icc (perturbedCellLower k h a ε (c k) i)
      (perturbedCellUpper k h a ε (c k) i)).indicator
        (fun _ => h / (perturbedBranches h a ε (c k) i).slope) (2 - y))

lemma perturbedMeshFoldedDensityReal_eq_signedGrid {q : ℕ} {h a ε y : ℝ}
    (c : ℕ → ℝ) (hq : 0 < q) (hhq : h = (q : ℝ)⁻¹)
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (ha12 : a ≤ 1 / 12)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    perturbedMeshFoldedDensityReal q h a ε c y =
      signedPerturbedGridDensity h a ε (reflectedCoefficient q c) y := by
  have hh : 0 < h := by rw [hhq]; positivity
  have hneg :
      (∑ i : Fin 7, ∑ z ∈ negativeGridBlock q h a ε c i.rev y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i.rev z) =
      ∑ i : Fin 7, ∑ z ∈ negativeGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z := by
    simpa using (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin 7))
      (fun i : Fin 7 => (∑ z ∈ negativeGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z : ℝ)))
  have hupp :
      (∑ i : Fin 7, ∑ z ∈ upperGridBlock q h a ε c i.rev y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i.rev z) =
      ∑ i : Fin 7, ∑ z ∈ upperGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z := by
    simpa using (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin 7))
      (fun i : Fin 7 => (∑ z ∈ upperGridBlock q h a ε c i y,
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z : ℝ)))
  unfold perturbedMeshFoldedDensityReal
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib]
  simp only [perturbedCellLower, perturbedCellUpper]
  simp_rw [negative_block_reindex c hq hh ha hε0 hc]
  simp_rw [upper_block_reindex c hq hhq ha hε0 hc]
  simp_rw [middle_block_reindex c hh ha hε0 hc]
  change
    (∑ i : Fin 7, ∑ z ∈ negativeGridBlock q h a ε c i.rev y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i.rev z) +
    (∑ i : Fin 7, ∑ z ∈ middleGridBlock q h a ε c i y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) +
    (∑ i : Fin 7, ∑ z ∈ upperGridBlock q h a ε c i.rev y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i.rev z) = _
  rw [hneg, hupp]
  change
    (∑ i : Fin 7, ∑ z ∈ negativeGridBlock q h a ε c i y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) +
    (∑ i : Fin 7, ∑ z ∈ middleGridBlock q h a ε c i y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) +
    (∑ i : Fin 7, ∑ z ∈ upperGridBlock q h a ε c i y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z) =
    ∑ i : Fin 7, ∑ z ∈ perturbedShiftedIndices q h a ε c i y,
      perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z
  simp_rw [sum_shiftedIndices_eq_three_blocks c hq hhq ha hε0 hε hc ha12 hy]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

lemma perturbedCellWeight_toReal (i : Fin 7) {h a ε c : ℝ}
    (hh : 0 < h) (hs : 0 < (perturbedBranches h a ε c i).slope) :
    (perturbedCellWeight h a ε c i).toReal =
      h / (perturbedBranches h a ε c i).slope := by
  rw [perturbedCellWeight_eq_ofReal_div i hh.le hs.le,
    ENNReal.toReal_ofReal (div_nonneg hh.le hs.le)]

lemma perturbedMeshFoldedDensity_toReal_eq_real {q : ℕ} {h a ε y : ℝ}
    (c : ℕ → ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (hh : 0 < h) (hs : ∀ k < q, ∀ i,
      0 < (perturbedBranches h a ε (c k) i).slope) :
    (perturbedMeshFoldedDensity q h a ε c y).toReal =
      perturbedMeshFoldedDensityReal q h a ε c y := by
  have hwtop (k : ℕ) (i : Fin 7) : perturbedCellWeight h a ε (c k) i ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpretop (t : ℝ) : perturbedMeshPreFoldDensity q h a ε c t ≠ ⊤ := by
    unfold perturbedMeshPreFoldDensity
    apply ENNReal.sum_ne_top.mpr
    intro k hk
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    by_cases hm : t ∈ Set.Icc
        (perturbedCellLower k h a ε (c k) i)
        (perturbedCellUpper k h a ε (c k) i) <;> simp [hm, hwtop k i]
  have hpre (t : ℝ) :
      (perturbedMeshPreFoldDensity q h a ε c t).toReal =
        ∑ k ∈ Finset.range q, ∑ i : Fin 7,
          (Set.Icc (perturbedCellLower k h a ε (c k) i)
            (perturbedCellUpper k h a ε (c k) i)).indicator
              (fun _ => h / (perturbedBranches h a ε (c k) i).slope) t := by
    unfold perturbedMeshPreFoldDensity
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        by_cases hm : t ∈ Set.Icc
            (perturbedCellLower k h a ε (c k) i)
            (perturbedCellUpper k h a ε (c k) i) <;>
          simp [hm, perturbedCellWeight_toReal i hh
            (hs k (Finset.mem_range.mp hk) i)]
      · intro i hi
        by_cases hm : t ∈ Set.Icc
            (perturbedCellLower k h a ε (c k) i)
            (perturbedCellUpper k h a ε (c k) i) <;> simp [hm, hwtop k i]
    · intro k hk
      apply ENNReal.sum_ne_top.mpr
      intro i hi
      by_cases hm : t ∈ Set.Icc
          (perturbedCellLower k h a ε (c k) i)
          (perturbedCellUpper k h a ε (c k) i) <;> simp [hm, hwtop k i]
  rw [perturbedMeshFoldedDensity_apply_Ioo q h a ε c hy]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hpretop (-y), hpretop y⟩)
      (hpretop (2 - y)),
    ENNReal.toReal_add (hpretop (-y)) (hpretop y), hpre, hpre, hpre]
  unfold perturbedMeshFoldedDensityReal
  simp_rw [Finset.sum_add_distrib]

lemma perturbedMeshFoldedDensity_error {q : ℕ} {h a ε y : ℝ}
    (c : ℕ → ℝ) (hq : 0 < q) (hhq : h = (q : ℝ)⁻¹)
    (ha : 0 ≤ a) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1)
    (hsmall : a * (1 + ε) ≤ 1 / 12) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    |(perturbedMeshFoldedDensity q h a ε c y).toReal - 1| ≤
      4 * h / a + 24 * ε := by
  have hh : 0 < h := by rw [hhq]; positivity
  have hs (k : ℕ) (_hk : k < q) (i : Fin 7) :
      0 < (perturbedBranches h a ε (c k) i).slope := by
    have hlo := perturbedBranches_slope_lower hh hscale hε0 hε (hc k) i
    have ha_pos : 0 < a := by
      have := (le_div_iff₀ hh).mp hscale
      linarith
    linarith
  have ha12 : a ≤ 1 / 12 := by
    have : a ≤ a * (1 + ε) := by nlinarith
    exact this.trans hsmall
  rw [perturbedMeshFoldedDensity_toReal_eq_real c hy hh hs,
    perturbedMeshFoldedDensityReal_eq_signedGrid c hq hhq ha hε0
      (hε.trans (by norm_num)) hc ha12 hy]
  exact (signedPerturbedGridDensity_error (reflectedCoefficient q c)
    hh ha hscale hε0 hε (reflectedCoefficient_mem_Icc hc) y).trans
      (signedPerturbedGridError_le hh ha hscale hε0 hε)

end CausalSmith.Experimentation.PilotscorePairingFrontier
