module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedDensityAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCellPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPerturbedCoverage
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedReflectedDensity

/-! # Interval-mixture form of a perturbed mesh cell -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

noncomputable def perturbedCellWeight (h a ε c : ℝ) (i : Fin 7) : ℝ≥0∞ :=
  ENNReal.ofReal h * ENNReal.ofReal ((perturbedBranches h a ε c i).slope)⁻¹

noncomputable def perturbedCellLower (k : ℕ) (h a ε c : ℝ) (i : Fin 7) : ℝ :=
  (k : ℝ) * h + (perturbedBranches h a ε c i).lower

noncomputable def perturbedCellUpper (k : ℕ) (h a ε c : ℝ) (i : Fin 7) : ℝ :=
  (k : ℝ) * h + (perturbedBranches h a ε c i).upper

/-- The exact seven-piece pushforward of one physical mesh cell, written as
the interval mixture consumed by the reflection lemma. -/
lemma map_perturbed_mesh_cell_eq_intervalMixture (k : ℕ) {h a ε c : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.map
        (fun x : ℝ => perturbedTriangularCell k h a ε c (x / h - k))
        (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) =
      intervalMixture (perturbedCellWeight h a ε c)
        (perturbedCellLower k h a ε c) (perturbedCellUpper k h a ε c) := by
  rw [map_perturbed_mesh_cell_rescaled k hh,
    map_perturbed_unit_cell_signed k hh ha hscale hε0 hε hc,
    intervalMixture_def]
  simp [Fin.sum_univ_succ, perturbedCellWeight, perturbedCellLower,
    perturbedCellUpper, perturbedBranches, smul_smul]
  ring_nf
  abel

lemma perturbedCellWeight_eq_ofReal_div (i : Fin 7) {h a ε c : ℝ}
    (hh : 0 ≤ h) (_hs : 0 ≤ (perturbedBranches h a ε c i).slope) :
    perturbedCellWeight h a ε c i =
      ENNReal.ofReal (h / (perturbedBranches h a ε c i).slope) := by
  rw [perturbedCellWeight, div_eq_mul_inv, ENNReal.ofReal_mul hh]

lemma perturbedCell_bounds {q k : ℕ} {h a ε c : ℝ}
    (hq : 0 < q) (hkq : k < q) (hhq : h = (q : ℝ)⁻¹)
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (hsmall : a * (1 + ε) ≤ 1 / 12) :
    (∀ i, -1 ≤ perturbedCellLower k h a ε c i) ∧
    (∀ i, perturbedCellUpper k h a ε c i ≤ 2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < h := by rw [hhq]; positivity
  have hk0 : 0 ≤ (k : ℝ) * h := mul_nonneg (by positivity) hh.le
  have hkle : (k : ℝ) * h ≤ 1 := by
    have hkqR : (k : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt hkq)
    rw [hhq]
    calc
      (k : ℝ) * (q : ℝ)⁻¹ ≤ (q : ℝ) * (q : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hkqR (inv_nonneg.mpr hqR.le)
      _ = 1 := mul_inv_cancel₀ hqR.ne'
  have hkhle : (k : ℝ) * h + h ≤ 1 := by
    have hkqR : ((k : ℝ) + 1) ≤ q := by
      exact_mod_cast (Nat.succ_le_of_lt hkq)
    rw [hhq]
    calc
      (k : ℝ) * (q : ℝ)⁻¹ + (q : ℝ)⁻¹ =
          ((k : ℝ) + 1) * (q : ℝ)⁻¹ := by ring
      _ ≤ (q : ℝ) * (q : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hkqR (inv_nonneg.mpr hqR.le)
      _ = 1 := mul_inv_cancel₀ hqR.ne'
  have ha12 : a ≤ 1 / 12 := by
    have : a ≤ a * (1 + ε) := by nlinarith
    exact this.trans hsmall
  have heac_lo : -(a / 64) ≤ ε * a * c := by
    have heale : ε * a ≤ a / 64 := by nlinarith
    have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heanon]
  have heac_hi : ε * a * c ≤ a / 64 := by
    have heale : ε * a ≤ a / 64 := by nlinarith
    have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heanon]
  constructor
  · intro i
    fin_cases i <;>
      simp [perturbedCellLower, perturbedBranches] <;> nlinarith
  · intro i
    fin_cases i <;>
      simp [perturbedCellUpper, perturbedBranches] <;> nlinarith

/-- Reflection reverses the seven affine branches and flips the transverse
coefficient. -/
lemma perturbedBranches_reflect_lower (h a ε c : ℝ) (i : Fin 7) :
    (perturbedBranches h a ε (-c) i.rev).lower =
      h - (perturbedBranches h a ε c i).upper := by
  fin_cases i <;> simp [perturbedBranches] <;> ring

lemma perturbedBranches_reflect_upper (h a ε c : ℝ) (i : Fin 7) :
    (perturbedBranches h a ε (-c) i.rev).upper =
      h - (perturbedBranches h a ε c i).lower := by
  fin_cases i <;> simp [perturbedBranches] <;> ring

lemma perturbedBranches_reflect_slope (h a ε c : ℝ) (i : Fin 7) :
    (perturbedBranches h a ε (-c) i.rev).slope =
      (perturbedBranches h a ε c i).slope := by
  fin_cases i <;> simp [perturbedBranches] <;> ring

-- keep: reusable reflection identity for the folded branch construction
lemma perturbedCellWeight_reflect (h a ε c : ℝ) (i : Fin 7) :
    perturbedCellWeight h a ε (-c) i.rev = perturbedCellWeight h a ε c i := by
  simp only [perturbedCellWeight, perturbedBranches_reflect_slope]

lemma perturbedBranches_lower_displacement {h a ε c : ℝ}
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (i : Fin 7) :
    |(perturbedBranches h a ε c i).lower -
      (perturbedBranches h a ε 0 i).lower| ≤ ε * a := by
  have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
  have heac : |ε * a * c| ≤ ε * a := by
    rw [abs_mul, abs_of_nonneg heanon]
    exact mul_le_of_le_one_right heanon ((abs_le).2 hc)
  have heac' : |ε| * |a| * |c| ≤ ε * a := by
    simpa [abs_mul] using heac
  fin_cases i <;> simp [perturbedBranches] <;> linarith

lemma perturbedBranches_upper_displacement {h a ε c : ℝ}
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (i : Fin 7) :
    |(perturbedBranches h a ε c i).upper -
      (perturbedBranches h a ε 0 i).upper| ≤ ε * a := by
  have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
  have heac : |ε * a * c| ≤ ε * a := by
    rw [abs_mul, abs_of_nonneg heanon]
    exact mul_le_of_le_one_right heanon ((abs_le).2 hc)
  have heac' : |ε| * |a| * |c| ≤ ε * a := by
    simpa [abs_mul] using heac
  fin_cases i <;> simp [perturbedBranches] <;> linarith

lemma perturbedBranches_slope_displacement {h a ε c : ℝ}
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (i : Fin 7) :
    |(perturbedBranches h a ε c i).slope -
      (perturbedBranches h a ε 0 i).slope| ≤ 32 * ε * a := by
  have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
  have heac : |ε * a * c| ≤ ε * a := by
    rw [abs_mul, abs_of_nonneg heanon]
    exact mul_le_of_le_one_right heanon ((abs_le).2 hc)
  have heac' : |ε| * |a| * |c| ≤ ε * a := by
    simpa [abs_mul] using heac
  have heac32 : 32 * |ε| * |a| * |c| ≤ 32 * ε * a := by
    nlinarith
  fin_cases i <;> simp [perturbedBranches] <;> nlinarith

lemma perturbedBranches_slope_lower {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (i : Fin 7) :
    3 * a ≤ (perturbedBranches h a ε c i).slope := by
  have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  have ha : 0 ≤ a := le_trans (by positivity : 0 ≤ 4 * h) ha4
  have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
  have heac_lo : -(ε * a) ≤ ε * a * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heanon]
  have heac_hi : ε * a * c ≤ ε * a := by
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heanon]
  fin_cases i <;> simp [perturbedBranches] <;> nlinarith

lemma perturbedBranches_weight_displacement {h a ε c : ℝ}
    (hh : 0 < h) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (i : Fin 7) :
    |h / (perturbedBranches h a ε c i).slope -
      h / (perturbedBranches h a ε 0 i).slope| ≤ 4 * ε * h / a := by
  let s := (perturbedBranches h a ε c i).slope
  let s0 := (perturbedBranches h a ε 0 i).slope
  have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
  have ha_pos : 0 < a := lt_of_lt_of_le (by positivity : 0 < 4 * h) ha4
  have hs3 : 3 * a ≤ s := perturbedBranches_slope_lower hh hscale hε0 hε hc i
  have hs03 : 3 * a ≤ s0 := perturbedBranches_slope_lower hh hscale hε0 hε
    (by exact ⟨by norm_num, by norm_num⟩) i
  have hs : 0 < s := lt_of_lt_of_le (by positivity : 0 < 3 * a) hs3
  have hs0 : 0 < s0 := lt_of_lt_of_le (by positivity : 0 < 3 * a) hs03
  have hds : |s - s0| ≤ 32 * ε * a :=
    perturbedBranches_slope_displacement ha_pos.le hε0 hc i
  have hprod : 9 * a ^ 2 ≤ s * s0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs3) (sub_nonneg.mpr hs03)]
  have hmain : h * |s0 - s| * a ≤ 4 * ε * h * (s * s0) := by
    have hds' : |s0 - s| ≤ 32 * ε * a := by simpa [abs_sub_comm] using hds
    have hεh : 0 ≤ 4 * ε * h := by positivity
    calc
      h * |s0 - s| * a ≤ h * (32 * ε * a) * a := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hds' hh.le) ha_pos.le
      _ ≤ 4 * ε * h * (9 * a ^ 2) := by
        nlinarith [mul_nonneg (mul_nonneg hε0 hh.le) (sq_nonneg a)]
      _ ≤ 4 * ε * h * (s * s0) := mul_le_mul_of_nonneg_left hprod hεh
  have hid : h / s - h / s0 = h * (s0 - s) / (s * s0) := by
    field_simp [hs.ne', hs0.ne']
  rw [show (perturbedBranches h a ε c i).slope = s from rfl,
    show (perturbedBranches h a ε 0 i).slope = s0 from rfl, hid,
    abs_div, abs_mul, abs_of_pos hh, abs_mul, abs_of_pos hs, abs_of_pos hs0]
  apply (le_div_iff₀ ha_pos).2
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hs hs0)]
  simpa [mul_assoc] using hmain

noncomputable def perturbedMeshMixture (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) : Measure ℝ :=
  ∑ k ∈ Finset.range q,
    intervalMixture (perturbedCellWeight h a ε (c k))
      (perturbedCellLower k h a ε (c k)) (perturbedCellUpper k h a ε (c k))

noncomputable def perturbedMeshFoldedDensity (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range q,
    foldedIntervalMixtureDensity (perturbedCellWeight h a ε (c k))
      (perturbedCellLower k h a ε (c k)) (perturbedCellUpper k h a ε (c k)) y

@[fun_prop]
lemma measurable_perturbedMeshFoldedDensity (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) : Measurable (perturbedMeshFoldedDensity q h a ε c) := by
  unfold perturbedMeshFoldedDensity
  apply Finset.measurable_fun_sum
  intro k hk
  exact measurable_foldedIntervalMixtureDensity _ _ _

lemma perturbedMeshFoldedDensity_ne_top (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (y : ℝ) :
    perturbedMeshFoldedDensity q h a ε c y ≠ ⊤ := by
  unfold perturbedMeshFoldedDensity
  apply ENNReal.sum_ne_top.mpr
  intro k hk
  exact foldedIntervalMixtureDensity_ne_top _ _ _
    (fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) y

noncomputable def perturbedMeshPreFoldDensity (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range q, ∑ i : Fin 7,
    (Set.Icc (perturbedCellLower k h a ε (c k) i)
      (perturbedCellUpper k h a ε (c k) i)).indicator
        (fun _ => perturbedCellWeight h a ε (c k) i) y

lemma perturbedMeshFoldedDensity_apply_Ioo (q : ℕ) (h a ε : ℝ)
    (c : ℕ → ℝ) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    perturbedMeshFoldedDensity q h a ε c y =
      perturbedMeshPreFoldDensity q h a ε c (-y) +
      perturbedMeshPreFoldDensity q h a ε c y +
      perturbedMeshPreFoldDensity q h a ε c (2 - y) := by
  unfold perturbedMeshFoldedDensity perturbedMeshPreFoldDensity
  simp_rw [foldedIntervalMixtureDensity_apply_Ioo _ _ _ hy,
    Finset.sum_add_distrib]

lemma map_eq_perturbedMeshMixture (q : ℕ) (hq : 0 < q) {h a ε : ℝ}
    (hhq : h = (q : ℝ)⁻¹) (c : ℕ → ℝ) (hc : ∀ k < q, c k ∈ Set.Icc (-1 : ℝ) 1)
    (ha : 0 ≤ a) (hscale : 4 ≤ a / h) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64)
    {F : ℝ → ℝ} (hF : Measurable F)
    (hcell : ∀ k < q, ∀ x ∈ Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h),
      F x = perturbedTriangularCell k h a ε (c k) (x / h - k)) :
    Measure.map F ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      perturbedMeshMixture q h a ε c := by
  rw [map_eq_sum_perturbed_cells q hq hhq c hF hcell]
  unfold perturbedMeshMixture
  apply Finset.sum_congr rfl
  intro k hk
  have hkq := Finset.mem_range.mp hk
  calc
    ENNReal.ofReal h •
        Measure.map (perturbedTriangularCell k h a ε (c k))
          (volume.restrict (Set.Icc (0 : ℝ) 1)) =
      Measure.map
          (fun x : ℝ => perturbedTriangularCell k h a ε (c k) (x / h - k))
          (volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h))) :=
        (map_perturbed_mesh_cell_rescaled k (by rw [hhq]; positivity)).symm
    _ = _ := map_perturbed_mesh_cell_eq_intervalMixture k
      (by rw [hhq]; positivity) ha hscale hε0 hε (hc k hkq)

lemma map_triangularFold_perturbedMeshMixture (q : ℕ) {h a ε : ℝ}
    (c : ℕ → ℝ)
    (hL : ∀ k < q, ∀ i, -1 ≤ perturbedCellLower k h a ε (c k) i)
    (hU : ∀ k < q, ∀ i, perturbedCellUpper k h a ε (c k) i ≤ 2) :
    Measure.map triangularFold (perturbedMeshMixture q h a ε c) =
      (volume : Measure ℝ).withDensity (perturbedMeshFoldedDensity q h a ε c) := by
  unfold perturbedMeshMixture
  rw [Measure.map_finset_sum measurable_triangularFold.aemeasurable]
  have hsum :
      (∑ k ∈ Finset.range q,
        Measure.map triangularFold
          (intervalMixture (perturbedCellWeight h a ε (c k))
            (perturbedCellLower k h a ε (c k))
            (perturbedCellUpper k h a ε (c k)))) =
      ∑ k ∈ Finset.range q,
        (volume : Measure ℝ).withDensity
          (foldedIntervalMixtureDensity (perturbedCellWeight h a ε (c k))
            (perturbedCellLower k h a ε (c k))
            (perturbedCellUpper k h a ε (c k))) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact map_triangularFold_intervalMixture_eq_withDensity _ _ _
      (hL k (Finset.mem_range.mp hk)) (hU k (Finset.mem_range.mp hk))
  rw [hsum]
  unfold perturbedMeshFoldedDensity
  induction Finset.range q using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
      simp only [Finset.sum_insert hks]
      rw [ih]
      rw [← withDensity_add_left]
      · rfl
      · exact measurable_foldedIntervalMixtureDensity _ _ _

lemma map_triangularFold_perturbedMeshMixture_of_small
    (q : ℕ) (hq : 0 < q) {h a ε : ℝ} (hhq : h = (q : ℝ)⁻¹)
    (c : ℕ → ℝ) (hc : ∀ k < q, c k ∈ Set.Icc (-1 : ℝ) 1)
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64)
    (hsmall : a * (1 + ε) ≤ 1 / 12) :
    Measure.map triangularFold (perturbedMeshMixture q h a ε c) =
      (volume : Measure ℝ).withDensity (perturbedMeshFoldedDensity q h a ε c) := by
  apply map_triangularFold_perturbedMeshMixture q c
  · intro k hk
    exact (perturbedCell_bounds hq hk hhq ha hε0 hε (hc k hk) hsmall).1
  · intro k hk
    exact (perturbedCell_bounds hq hk hhq ha hε0 hε (hc k hk) hsmall).2

end CausalSmith.Experimentation.PilotscorePairingFrontier
