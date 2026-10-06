module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSliceLaw

/-! # Joint measurability of transverse folded densities -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma measurable_foldedIntervalMixtureDensity_family
    {zeta : Type*} [MeasurableSpace zeta] {n : ℕ}
    (w : zeta -> Fin n -> ENNReal) (L U : zeta -> Fin n -> ℝ)
    (hw : forall i, Measurable (fun z => w z i))
    (hL : forall i, Measurable (fun z => L z i))
    (hU : forall i, Measurable (fun z => U z i)) :
    Measurable (fun zy : zeta × ℝ =>
      foldedIntervalMixtureDensity (w zy.1) (L zy.1) (U zy.1) zy.2) := by
  let leftSet (i : Fin n) : Set (zeta × ℝ) :=
    {zy | L zy.1 i ≤ -zy.2 ∧ -zy.2 ≤ U zy.1 i ∧
      (-1 : ℝ) ≤ -zy.2 ∧ -zy.2 ≤ 0}
  let middleSet (i : Fin n) : Set (zeta × ℝ) :=
    {zy | L zy.1 i ≤ zy.2 ∧ zy.2 ≤ U zy.1 i ∧
      0 < zy.2 ∧ zy.2 ≤ 1}
  let rightSet (i : Fin n) : Set (zeta × ℝ) :=
    {zy | L zy.1 i ≤ 2 - zy.2 ∧ 2 - zy.2 ≤ U zy.1 i ∧
      1 < 2 - zy.2 ∧ 2 - zy.2 ≤ 2}
  have hleft (i : Fin n) : MeasurableSet (leftSet i) := by
    change MeasurableSet {zy : zeta × ℝ | L zy.1 i ≤ -zy.2 ∧
      -zy.2 ≤ U zy.1 i ∧ (-1 : ℝ) ≤ -zy.2 ∧ -zy.2 ≤ 0}
    exact (measurableSet_le (hL i |>.comp measurable_fst)
      measurable_snd.neg).inter
      ((measurableSet_le measurable_snd.neg (hU i |>.comp measurable_fst)).inter
      ((measurableSet_le
        (measurable_const : Measurable (fun _ : zeta × ℝ => (-1 : ℝ)))
        measurable_snd.neg).inter
      (measurableSet_le measurable_snd.neg
        (measurable_const : Measurable (fun _ : zeta × ℝ => (0 : ℝ))))))
  have hmiddle (i : Fin n) : MeasurableSet (middleSet i) := by
    change MeasurableSet {zy : zeta × ℝ | L zy.1 i ≤ zy.2 ∧
      zy.2 ≤ U zy.1 i ∧ 0 < zy.2 ∧ zy.2 ≤ 1}
    exact (measurableSet_le (hL i |>.comp measurable_fst) measurable_snd).inter
      ((measurableSet_le measurable_snd (hU i |>.comp measurable_fst)).inter
      ((measurableSet_lt
        (measurable_const : Measurable (fun _ : zeta × ℝ => (0 : ℝ)))
        measurable_snd).inter
      (measurableSet_le measurable_snd
        (measurable_const : Measurable (fun _ : zeta × ℝ => (1 : ℝ))))))
  have hright (i : Fin n) : MeasurableSet (rightSet i) := by
    have href : Measurable (fun zy : zeta × ℝ => 2 - zy.2) := by fun_prop
    change MeasurableSet {zy : zeta × ℝ | L zy.1 i ≤ 2 - zy.2 ∧
      2 - zy.2 ≤ U zy.1 i ∧ 1 < 2 - zy.2 ∧ 2 - zy.2 ≤ 2}
    exact (measurableSet_le (hL i |>.comp measurable_fst) href).inter
      ((measurableSet_le href (hU i |>.comp measurable_fst)).inter
      ((measurableSet_lt
        (measurable_const : Measurable (fun _ : zeta × ℝ => (1 : ℝ))) href).inter
      (measurableSet_le href
        (measurable_const : Measurable (fun _ : zeta × ℝ => (2 : ℝ))))))
  unfold foldedIntervalMixtureDensity
  simp_rw [finiteSetMixtureDensity_apply]
  apply Measurable.add
  · apply Measurable.add
    · apply Finset.measurable_fun_sum
      intro i hi
      rw [show (fun zy : zeta × ℝ =>
          (foldedLeftSet (L zy.1) (U zy.1) i).indicator
            (fun _ => w zy.1 i) zy.2) =
          (leftSet i).indicator (fun zy => w zy.1 i) by
        funext zy
        have hm : zy.2 ∈ foldedLeftSet (L zy.1) (U zy.1) i ↔
            zy ∈ leftSet i := by
          simp only [foldedLeftSet, Set.mem_image, Set.mem_inter_iff,
            Set.mem_Icc, leftSet, Set.mem_setOf_eq]
          constructor
          · rintro ⟨x, ⟨hxLU, hx10⟩, hxy⟩
            exact ⟨by linarith [hxLU.1], by linarith [hxLU.2],
              by linarith [hx10.1], by linarith [hx10.2]⟩
          · intro hz
            refine ⟨-zy.2, ?_, by ring⟩
            exact ⟨⟨by linarith [hz.1], by linarith [hz.2.1]⟩,
              ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩⟩
        by_cases hz : zy ∈ leftSet i
        · rw [Set.indicator_of_mem ((hm).2 hz), Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)),
            Set.indicator_of_notMem hz]]
      exact (hw i).comp measurable_fst |>.indicator (hleft i)
    · apply Finset.measurable_fun_sum
      intro i hi
      rw [show (fun zy : zeta × ℝ =>
          (foldedMiddleSet (L zy.1) (U zy.1) i).indicator
            (fun _ => w zy.1 i) zy.2) =
          (middleSet i).indicator (fun zy => w zy.1 i) by
        funext zy
        have hm : zy.2 ∈ foldedMiddleSet (L zy.1) (U zy.1) i ↔
            zy ∈ middleSet i := by
          simp [middleSet, foldedMiddleSet, and_assoc]
        by_cases hz : zy ∈ middleSet i
        · rw [Set.indicator_of_mem (hm.2 hz), Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)),
            Set.indicator_of_notMem hz]]
      exact (hw i).comp measurable_fst |>.indicator (hmiddle i)
  · apply Finset.measurable_fun_sum
    intro i hi
    rw [show (fun zy : zeta × ℝ =>
        (foldedRightSet (L zy.1) (U zy.1) i).indicator
          (fun _ => w zy.1 i) zy.2) =
        (rightSet i).indicator (fun zy => w zy.1 i) by
      funext zy
      have hm : zy.2 ∈ foldedRightSet (L zy.1) (U zy.1) i ↔
          zy ∈ rightSet i := by
        simp only [foldedRightSet, Set.mem_image, Set.mem_inter_iff,
          Set.mem_Icc, Set.mem_Ioc, rightSet, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x, ⟨hxLU, hx12⟩, hxy⟩
          exact ⟨by linarith [hxLU.1], by linarith [hxLU.2],
            by linarith [hx12.1], by linarith [hx12.2]⟩
        · intro hz
          refine ⟨2 - zy.2, ?_, by ring⟩
          exact ⟨⟨by linarith [hz.1], by linarith [hz.2.1]⟩,
            ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩⟩
      by_cases hz : zy ∈ rightSet i
      · rw [Set.indicator_of_mem (hm.2 hz), Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)),
          Set.indicator_of_notMem hz]]
    exact (hw i).comp measurable_fst |>.indicator (hright i)

@[fun_prop]
lemma measurable_perturbedMeshFoldedDensity_family
    {zeta : Type*} [MeasurableSpace zeta]
    (q : ℕ) (h a eps : ℝ) (c : zeta -> ℕ -> ℝ)
    (hc : forall k, Measurable (fun z => c z k)) :
    Measurable (fun zy : zeta × ℝ =>
      perturbedMeshFoldedDensity q h a eps (c zy.1) zy.2) := by
  unfold perturbedMeshFoldedDensity
  apply Finset.measurable_fun_sum
  intro k hk
  let w : zeta -> Fin 7 -> ENNReal :=
    fun z i => perturbedCellWeight h a eps (c z k) i
  let L : zeta -> Fin 7 -> ℝ :=
    fun z i => perturbedCellLower k h a eps (c z k) i
  let U : zeta -> Fin 7 -> ℝ :=
    fun z i => perturbedCellUpper k h a eps (c z k) i
  have hw : forall i, Measurable (fun z => w z i) := by
    intro i
    unfold w perturbedCellWeight
    fin_cases i <;> simp [perturbedBranches] <;> fun_prop
  have hL : forall i, Measurable (fun z => L z i) := by
    intro i
    unfold L perturbedCellLower
    fin_cases i <;> simp [perturbedBranches] <;> fun_prop
  have hU : forall i, Measurable (fun z => U z i) := by
    intro i
    unfold U perturbedCellUpper
    fin_cases i <;> simp [perturbedBranches] <;> fun_prop
  exact measurable_foldedIntervalMixtureDensity_family w L U hw hL hU

@[fun_prop]
lemma measurable_foldedSliceScoreDensity_joint
    (n q K : ℕ) (beta h kappa eps : ℝ)
    (idx : Fin K -> Fin (n + 1) -> ℕ) (theta : Fin K -> Bool) :
    Measurable (fun zt : (Fin n -> ℝ) × ℝ =>
      foldedSliceScoreDensity n q K beta h kappa eps idx theta zt.1 zt.2) := by
  unfold foldedSliceScoreDensity
  apply Measurable.mul measurable_const
  change Measurable (fun zt : (Fin n -> ℝ) × ℝ =>
    perturbedMeshFoldedDensity q h (kappa * h ^ beta) eps
      (fun k => foldedTailCoefficient n K h idx theta zt.1 k)
      (2 * zt.2 - 1 / 2))
  have hm := measurable_perturbedMeshFoldedDensity_family q h
    (kappa * h ^ beta) eps
    (fun z k => foldedTailCoefficient n K h idx theta z k)
    (fun k => measurable_foldedTailCoefficient n K h idx theta k)
  have hc : Measurable (fun zt : (Fin n -> ℝ) × ℝ =>
      (zt.1, 2 * zt.2 - 1 / 2)) := by fun_prop
  exact hm.comp hc

end CausalSmith.Experimentation.PilotscorePairingFrontier
