module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCellPushforward
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFoldPushforward

/-! # Density form of finite affine-branch measures -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open scoped ENNReal

@[no_expose]
noncomputable def intervalMixture {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) : Measure ℝ :=
  ∑ i, w i • (volume : Measure ℝ).restrict (Set.Icc (L i) (U i))

@[no_expose]
noncomputable def intervalMixtureDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ i, (Set.Icc (L i) (U i)).indicator (fun _ => w i) y

@[no_expose]
noncomputable def finiteSetMixture {n : ℕ}
    (w : Fin n → ℝ≥0∞) (S : Fin n → Set ℝ) : Measure ℝ :=
  ∑ i, w i • (volume : Measure ℝ).restrict (S i)

@[no_expose]
noncomputable def finiteSetMixtureDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (S : Fin n → Set ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑ i, (S i).indicator (fun _ => w i) y

lemma intervalMixture_def {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) :
    intervalMixture w L U =
      ∑ i, w i • (volume : Measure ℝ).restrict (Set.Icc (L i) (U i)) := by
  simp only [intervalMixture]

lemma finiteSetMixtureDensity_apply {n : ℕ}
    (w : Fin n → ℝ≥0∞) (S : Fin n → Set ℝ) (y : ℝ) :
    finiteSetMixtureDensity w S y =
      ∑ i, (S i).indicator (fun _ => w i) y := by
  simp only [finiteSetMixtureDensity]

lemma finiteSetMixture_def {n : ℕ}
    (w : Fin n → ℝ≥0∞) (S : Fin n → Set ℝ) :
    finiteSetMixture w S =
      ∑ i, w i • (volume : Measure ℝ).restrict (S i) := by
  simp only [finiteSetMixture]

lemma measurable_finiteSetMixtureDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (S : Fin n → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) :
    Measurable (finiteSetMixtureDensity w S) := by
  rw [show finiteSetMixtureDensity w S =
      fun y => ∑ i, (S i).indicator (fun _ => w i) y from
    funext (finiteSetMixtureDensity_apply w S)]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hS i)

lemma finiteSetMixture_eq_withDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (S : Fin n → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) :
    finiteSetMixture w S =
      (volume : Measure ℝ).withDensity (finiteSetMixtureDensity w S) := by
  ext s hs
  simp only [finiteSetMixture, finiteSetMixtureDensity, withDensity_apply _ hs]
  rw [Measure.finsetSum_apply, MeasureTheory.lintegral_finsetSum]
  apply Finset.sum_congr rfl
  · intro i hi
    rw [← withDensity_apply _ hs, MeasureTheory.withDensity_indicator (hS i),
      MeasureTheory.withDensity_const, Measure.smul_apply]
  · exact fun i _ => measurable_const.indicator (hS i)

-- keep: reusable finite-mixture density assembly interface
lemma intervalMixture_eq_withDensity {n : ℕ}
    (w : Fin n → ℝ≥0∞) (L U : Fin n → ℝ) :
    intervalMixture w L U =
      (volume : Measure ℝ).withDensity (intervalMixtureDensity w L U) := by
  ext s hs
  simp only [intervalMixture, intervalMixtureDensity, withDensity_apply _ hs]
  rw [Measure.finsetSum_apply, MeasureTheory.lintegral_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← withDensity_apply _ hs, MeasureTheory.withDensity_indicator measurableSet_Icc,
    MeasureTheory.withDensity_const, Measure.smul_apply]
  · exact fun i _ =>
      measurable_const.indicator measurableSet_Icc

-- keep: reusable left-branch pushforward identity for folded mixtures
lemma map_triangularFold_smul_restrict_left (w : ℝ≥0∞) {L U : ℝ}
    (hL : -1 ≤ L) (hU : U ≤ 0) :
    Measure.map triangularFold
        (w • (volume : Measure ℝ).restrict (Set.Icc L U)) =
      w • volume.restrict (Set.Icc (-U) (-L)) := by
  rw [Measure.map_smul]
  have hmap := map_triangularFold_restrict_left (Set.Icc L U) measurableSet_Icc
    (fun t ht => ⟨hL.trans ht.1, ht.2.trans hU⟩)
  rw [hmap]
  congr 2
  ext t
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor <;> linarith [hx.1, hx.2]
  · intro ht
    refine ⟨-t, ?_, by ring⟩
    constructor <;> linarith [ht.1, ht.2]

-- keep: reusable middle-branch pushforward identity for folded mixtures
lemma map_triangularFold_smul_restrict_middle (w : ℝ≥0∞) {L U : ℝ}
    (hL : 0 ≤ L) (hU : U ≤ 1) :
    Measure.map triangularFold
        (w • (volume : Measure ℝ).restrict (Set.Icc L U)) =
      w • volume.restrict (Set.Icc L U) := by
  rw [Measure.map_smul]
  exact congrArg (w • ·) <|
    map_triangularFold_restrict_middle (Set.Icc L U) measurableSet_Icc
      (fun t ht => ⟨hL.trans ht.1, ht.2.trans hU⟩)

-- keep: reusable right-branch pushforward identity for folded mixtures
lemma map_triangularFold_smul_restrict_right (w : ℝ≥0∞) {L U : ℝ}
    (hL : 1 ≤ L) (hU : U ≤ 2) :
    Measure.map triangularFold
        (w • (volume : Measure ℝ).restrict (Set.Icc L U)) =
      w • volume.restrict (Set.Icc (2 - U) (2 - L)) := by
  rw [Measure.map_smul]
  have hmap := map_triangularFold_restrict_right (Set.Icc L U) measurableSet_Icc
    (fun t ht => ⟨hL.trans ht.1, ht.2.trans hU⟩)
  rw [hmap]
  congr 2
  ext t
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor <;> linarith [hx.1, hx.2]
  · intro ht
    refine ⟨2 - t, ?_, by ring⟩
    constructor <;> linarith [ht.1, ht.2]

-- keep: reusable affine-score pushforward identity for folded mixtures
lemma map_scoreAffine_smul_restrict (w : ℝ≥0∞) (L U : ℝ) :
    Measure.map (fun y : ℝ => 1 / 4 + 1 / 2 * y)
        (w • (volume : Measure ℝ).restrict (Set.Icc L U)) =
      (ENNReal.ofReal 2 * w) •
        volume.restrict
          (Set.Icc (1 / 4 + L / 2) (1 / 4 + U / 2)) := by
  rw [Measure.map_smul]
  have hm := map_affine_restrict_Icc_of_pos (1 / 4) (1 / 2) L U
    (by norm_num : (0 : ℝ) < 1 / 2)
  rw [hm, smul_smul]
  congr 1
  · norm_num
    exact mul_comm _ _
  · congr 2 <;> ring

lemma map_add_measure {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ ν : Measure α} {f : α → γ} (hf : Measurable f) :
    Measure.map f (μ + ν) = Measure.map f μ + Measure.map f ν := by
  ext s hs
  simp [Measure.map_apply hf hs]

lemma volume_restrict_Icc_fold_regions {L U : ℝ}
    (hL : -1 ≤ L) (hU : U ≤ 2) :
    (volume : Measure ℝ).restrict (Set.Icc L U) =
      volume.restrict (Set.Icc L U ∩ Set.Icc (-1 : ℝ) 0) +
      volume.restrict (Set.Icc L U ∩ Set.Ioc (0 : ℝ) 1) +
      volume.restrict (Set.Icc L U ∩ Set.Ioc (1 : ℝ) 2) := by
  let A := Set.Icc L U ∩ Set.Icc (-1 : ℝ) 0
  let B := Set.Icc L U ∩ Set.Ioc (0 : ℝ) 1
  let C := Set.Icc L U ∩ Set.Ioc (1 : ℝ) 2
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact (not_lt_of_ge hxA.2.2) hxB.2.1
  have hABC : Disjoint (A ∪ B) C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    rcases hx with hxA | hxB
    · exact (not_lt_of_ge (hxA.2.2.trans (by norm_num))) hxC.2.1
    · exact (not_lt_of_ge hxB.2.2) hxC.2.1
  have hcover : A ∪ B ∪ C = Set.Icc L U := by
    ext x
    constructor
    · rintro ((hx | hx) | hx) <;> exact hx.1
    · intro hx
      by_cases hx0 : x ≤ 0
      · exact Or.inl (Or.inl ⟨hx, by constructor <;> linarith [hL, hx.1]⟩)
      · by_cases hx1 : x ≤ 1
        · exact Or.inl (Or.inr ⟨hx, by constructor <;> linarith⟩)
        · exact Or.inr ⟨hx, by constructor <;> linarith [hU, hx.2]⟩
  calc
    (volume : Measure ℝ).restrict (Set.Icc L U) =
        volume.restrict (A ∪ B ∪ C) := congrArg volume.restrict hcover.symm
    _ = volume.restrict (A ∪ B) + volume.restrict C := by
      rw [Measure.restrict_union hABC]
      exact measurableSet_Icc.inter measurableSet_Ioc
    _ = volume.restrict A + volume.restrict B + volume.restrict C := by
      rw [Measure.restrict_union hAB]
      exact measurableSet_Icc.inter measurableSet_Ioc

/-- Exact reflection of one weighted branch interval, expressed with an
endpoint-safe three-region partition. -/
lemma map_triangularFold_smul_restrict_partition (w : ℝ≥0∞) {L U : ℝ}
    (hL : -1 ≤ L) (hU : U ≤ 2) :
    Measure.map triangularFold
        (w • (volume : Measure ℝ).restrict (Set.Icc L U)) =
      w • volume.restrict
          ((fun t : ℝ => -t) '' (Set.Icc L U ∩ Set.Icc (-1 : ℝ) 0)) +
      w • volume.restrict (Set.Icc L U ∩ Set.Ioc (0 : ℝ) 1) +
      w • volume.restrict
          ((fun t : ℝ => 2 - t) '' (Set.Icc L U ∩ Set.Ioc (1 : ℝ) 2)) := by
  rw [volume_restrict_Icc_fold_regions hL hU, smul_add, smul_add,
    map_add_measure measurable_triangularFold, map_add_measure measurable_triangularFold]
  rw [Measure.map_smul,
    map_triangularFold_restrict_left _
      (measurableSet_Icc.inter measurableSet_Icc)
      (fun t ht => ht.2),
    Measure.map_smul,
    map_triangularFold_restrict_middle _
      (measurableSet_Icc.inter measurableSet_Ioc)
      (fun t ht => ⟨ht.2.1.le, ht.2.2⟩),
    Measure.map_smul,
    map_triangularFold_restrict_right _
      (measurableSet_Icc.inter measurableSet_Ioc)
      (fun t ht => ⟨ht.2.1.le, ht.2.2⟩)]

lemma mem_folded_left_image_iff {L U y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    y ∈ (fun t : ℝ => -t) '' (Set.Icc L U ∩ Set.Icc (-1 : ℝ) 0) ↔
      -y ∈ Set.Icc L U := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht.1
  · intro ht
    refine ⟨-y, ⟨ht, ?_⟩, by ring⟩
    constructor <;> linarith [hy.1, hy.2]

lemma mem_folded_middle_piece_iff {L U y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    y ∈ Set.Icc L U ∩ Set.Ioc (0 : ℝ) 1 ↔ y ∈ Set.Icc L U := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hy.1, hy.2.le⟩

lemma mem_folded_right_image_iff {L U y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    y ∈ (fun t : ℝ => 2 - t) '' (Set.Icc L U ∩ Set.Ioc (1 : ℝ) 2) ↔
      2 - y ∈ Set.Icc L U := by
  constructor
  · rintro ⟨t, ht, hty⟩
    have : t = 2 - y := by linarith
    simpa [this] using ht.1
  · intro ht
    refine ⟨2 - y, ⟨ht, ?_⟩, by ring⟩
    constructor <;> linarith [hy.1, hy.2]

end CausalSmith.Experimentation.PilotscorePairingFrontier
