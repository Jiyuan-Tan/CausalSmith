module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedDensityAssembly

/-! # Density of a folded finite interval mixture

This file packages the endpoint-safe reflection calculation for a finite
mixture of weighted intervals.  It separates the measure-theoretic fold from
the later finite coverage count.
-/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

noncomputable def foldedLeftSet {n : ℕ} (L U : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  (fun t : ℝ => -t) '' (Set.Icc (L i) (U i) ∩ Set.Icc (-1 : ℝ) 0)

noncomputable def foldedMiddleSet {n : ℕ} (L U : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  Set.Icc (L i) (U i) ∩ Set.Ioc (0 : ℝ) 1

noncomputable def foldedRightSet {n : ℕ} (L U : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  (fun t : ℝ => 2 - t) '' (Set.Icc (L i) (U i) ∩ Set.Ioc (1 : ℝ) 2)

noncomputable def foldedIntervalMixtureDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) (y : ℝ) : ℝ≥0∞ :=
  finiteSetMixtureDensity w (foldedLeftSet L U) y +
    finiteSetMixtureDensity w (foldedMiddleSet L U) y +
    finiteSetMixtureDensity w (foldedRightSet L U) y

lemma measurableSet_foldedLeftSet {n : ℕ} (L U : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (foldedLeftSet L U i) := by
  have hemb : MeasurableEmbedding (fun t : ℝ => -t) :=
    continuous_neg.measurableEmbedding (by intro x y h; linarith)
  have h := hemb.measurableSet_image.mpr
    (measurableSet_Icc.inter measurableSet_Icc :
      MeasurableSet (Set.Icc (L i) (U i) ∩ Set.Icc (-1 : ℝ) 0))
  simpa [foldedLeftSet] using h

lemma measurableSet_foldedMiddleSet {n : ℕ} (L U : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (foldedMiddleSet L U i) :=
  measurableSet_Icc.inter measurableSet_Ioc

lemma measurableSet_foldedRightSet {n : ℕ} (L U : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (foldedRightSet L U i) := by
  have hemb : MeasurableEmbedding (fun t : ℝ => 2 - t) :=
    (continuous_const.sub continuous_id).measurableEmbedding
      (fun _ _ h => sub_right_inj.mp h)
  exact hemb.measurableSet_image.mpr (measurableSet_Icc.inter measurableSet_Ioc)

lemma measurable_foldedIntervalMixtureDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) :
    Measurable (foldedIntervalMixtureDensity w L U) := by
  unfold foldedIntervalMixtureDensity
  exact (Measurable.add
    (measurable_finiteSetMixtureDensity w (foldedLeftSet L U)
      (measurableSet_foldedLeftSet L U))
    (measurable_finiteSetMixtureDensity w (foldedMiddleSet L U)
      (measurableSet_foldedMiddleSet L U))).add
    (measurable_finiteSetMixtureDensity w (foldedRightSet L U)
      (measurableSet_foldedRightSet L U))

lemma foldedIntervalMixtureDensity_ne_top {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ)
    (hw : ∀ i, w i ≠ ⊤) (y : ℝ) :
    foldedIntervalMixtureDensity w L U y ≠ ⊤ := by
  unfold foldedIntervalMixtureDensity
  simp_rw [finiteSetMixtureDensity_apply]
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.add_ne_top.mpr
    constructor <;> apply ENNReal.sum_ne_top.mpr
    · intro i hi
      by_cases hm : y ∈ foldedLeftSet L U i <;> simp [hm, hw i]
    · intro i hi
      by_cases hm : y ∈ foldedMiddleSet L U i <;> simp [hm, hw i]
  · apply ENNReal.sum_ne_top.mpr
    intro i hi
    by_cases hm : y ∈ foldedRightSet L U i <;> simp [hm, hw i]

/-- Folding a finite interval mixture gives the sum of its reflected left,
unchanged middle, and reflected right pieces. -/
lemma map_triangularFold_intervalMixture {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ)
    (hL : ∀ i, -1 ≤ L i) (hU : ∀ i, U i ≤ 2) :
    Measure.map triangularFold (intervalMixture w L U) =
      finiteSetMixture w (foldedLeftSet L U) +
      finiteSetMixture w (foldedMiddleSet L U) +
      finiteSetMixture w (foldedRightSet L U) := by
  rw [intervalMixture_def, Measure.map_finset_sum' measurable_triangularFold.aemeasurable]
  rw [finiteSetMixture_def, finiteSetMixture_def, finiteSetMixture_def,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact map_triangularFold_smul_restrict_partition (w i) (hL i) (hU i)

/-- Density form of the folded finite interval mixture. -/
lemma map_triangularFold_intervalMixture_eq_withDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ)
    (hL : ∀ i, -1 ≤ L i) (hU : ∀ i, U i ≤ 2) :
    Measure.map triangularFold (intervalMixture w L U) =
      (volume : Measure ℝ).withDensity (foldedIntervalMixtureDensity w L U) := by
  rw [map_triangularFold_intervalMixture w L U hL hU,
    finiteSetMixture_eq_withDensity w (foldedLeftSet L U)
      (measurableSet_foldedLeftSet L U),
    finiteSetMixture_eq_withDensity w (foldedMiddleSet L U)
      (measurableSet_foldedMiddleSet L U),
    finiteSetMixture_eq_withDensity w (foldedRightSet L U)
      (measurableSet_foldedRightSet L U)]
  unfold foldedIntervalMixtureDensity
  rw [← withDensity_add_left, ← withDensity_add_left]
  · rfl
  · exact Measurable.add
      (measurable_finiteSetMixtureDensity w (foldedLeftSet L U)
        (measurableSet_foldedLeftSet L U))
      (measurable_finiteSetMixtureDensity w (foldedMiddleSet L U)
        (measurableSet_foldedMiddleSet L U))
  · exact measurable_finiteSetMixtureDensity w (foldedLeftSet L U)
      (measurableSet_foldedLeftSet L U)

lemma foldedIntervalMixtureDensity_apply_Ioo {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    foldedIntervalMixtureDensity w L U y =
      ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) (-y) +
      ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) y +
      ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) (2 - y) := by
  unfold foldedIntervalMixtureDensity
  simp_rw [finiteSetMixtureDensity_apply]
  have hleft :
      (∑ i, (foldedLeftSet L U i).indicator (fun _ => w i) y) =
        ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) (-y) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hm := mem_folded_left_image_iff (L := L i) (U := U i) hy
    by_cases hmem : y ∈ foldedLeftSet L U i
    · have hraw : y ∈
          (fun t : ℝ => -t) '' (Set.Icc (L i) (U i) ∩ Set.Icc (-1 : ℝ) 0) := by
        simpa only [foldedLeftSet] using hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hm.mp hraw)]
    · have hraw : y ∉
          (fun t : ℝ => -t) '' (Set.Icc (L i) (U i) ∩ Set.Icc (-1 : ℝ) 0) := by
        simpa only [foldedLeftSet] using hmem
      have hmem' : -y ∉ Set.Icc (L i) (U i) := fun h => hraw (hm.mpr h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  have hmiddle :
      (∑ i, (foldedMiddleSet L U i).indicator (fun _ => w i) y) =
        ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) y := by
    apply Finset.sum_congr rfl
    intro i hi
    have hm := mem_folded_middle_piece_iff (L := L i) (U := U i) hy
    by_cases hmem : y ∈ foldedMiddleSet L U i
    · have hraw : y ∈ Set.Icc (L i) (U i) ∩ Set.Ioc (0 : ℝ) 1 := by
        simpa only [foldedMiddleSet] using hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hm.mp hraw)]
    · have hraw : y ∉ Set.Icc (L i) (U i) ∩ Set.Ioc (0 : ℝ) 1 := by
        simpa only [foldedMiddleSet] using hmem
      have hmem' : y ∉ Set.Icc (L i) (U i) := fun h => hraw (hm.mpr h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  have hright :
      (∑ i, (foldedRightSet L U i).indicator (fun _ => w i) y) =
        ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) (2 - y) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hm := mem_folded_right_image_iff (L := L i) (U := U i) hy
    by_cases hmem : y ∈ foldedRightSet L U i
    · have hraw : y ∈
          (fun t : ℝ => 2 - t) '' (Set.Icc (L i) (U i) ∩ Set.Ioc (1 : ℝ) 2) := by
        simpa only [foldedRightSet] using hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hm.mp hraw)]
    · have hraw : y ∉
          (fun t : ℝ => 2 - t) '' (Set.Icc (L i) (U i) ∩ Set.Ioc (1 : ℝ) 2) := by
        simpa only [foldedRightSet] using hmem
      have hmem' : 2 - y ∉ Set.Icc (L i) (U i) := fun h => hraw (hm.mpr h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  rw [hleft, hmiddle, hright]

end CausalSmith.Experimentation.PilotscorePairingFrontier
