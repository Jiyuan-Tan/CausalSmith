module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawAttainment

/-! Measure-level reconstruction leaves for the compatibility converse. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,a), [this definition](goal) introduces the corresponding object. -/
def scoreAssignedKeyLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (a : ArmSpace) : Measure (LabelSpace J × ArmSpace) :=
  (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).map
    (fun e => (g e, a))

/-- For [the specified mathematical inputs](hyp:ε,J,H,g), [this definition](goal) introduces the corresponding object. -/
def randomizedKeyLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J) :
    Measure (LabelSpace J × ArmSpace) :=
  scoreAssignedKeyLaw H g false + scoreAssignedKeyLaw H g true

/-- For [the specified mathematical inputs](hyp:J,Prel), [this definition](goal) introduces the corresponding object. -/
def releasedKeyLaw {J : ℕ} (Prel : Measure (Observation J)) :
    Measure (LabelSpace J × ArmSpace) :=
  Prel.map (fun z => (z.1, z.2.1))

/-- For [the specified mathematical inputs](hyp:J,Prel), [this definition](goal) introduces the corresponding object. -/
def releasedPairLaw {J : ℕ} (Prel : Measure (Observation J)) :
    Measure ((LabelSpace J × ArmSpace) × OutcomeSpace) :=
  Prel.map (fun z => ((z.1, z.2.1), z.2.2))

private lemma releasedPairing_measurable {J : ℕ} :
    Measurable (fun z : Observation J => ((z.1, z.2.1), z.2.2)) := by
  fun_prop
/-- For [the specified mathematical inputs](hyp:J,Prel), [this definition](goal) introduces the corresponding object. -/
instance releasedPairLaw_isProbabilityMeasure {J : ℕ}
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel] :
    IsProbabilityMeasure (releasedPairLaw Prel) := by
  unfold releasedPairLaw
  exact Measure.isProbabilityMeasure_map releasedPairing_measurable.aemeasurable

/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel), this result [establishes the stated mathematical conclusion](goal). -/
lemma releasedPairLaw_fst {J : ℕ}
    (Prel : Measure (Observation J)) :
    (releasedPairLaw Prel).fst = releasedKeyLaw Prel := by
  unfold Measure.fst releasedPairLaw releasedKeyLaw
  rw [Measure.map_map measurable_fst releasedPairing_measurable]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel), this result [establishes the stated mathematical conclusion](goal). -/
lemma releasedPairLaw_map_unpair {J : ℕ}
    (Prel : Measure (Observation J)) :
    (releasedPairLaw Prel).map (fun p => (p.1.1, p.1.2, p.2)) = Prel := by
  unfold releasedPairLaw
  rw [Measure.map_map (by fun_prop) releasedPairing_measurable]
  have hfun : ((fun p : (LabelSpace J × ArmSpace) × OutcomeSpace =>
      (p.1.1, p.1.2, p.2)) ∘
      (fun z : Observation J => ((z.1, z.2.1), z.2.2))) = id := by
    funext z
    rfl
  rw [hfun, Measure.map_id]

/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel), this result [establishes the stated mathematical conclusion](goal). -/
lemma releasedPairLaw_disintegrate {J : ℕ}
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel] :
    (releasedKeyLaw Prel) ⊗ₘ (releasedPairLaw Prel).condKernel =
      releasedPairLaw Prel := by
  rw [← releasedPairLaw_fst Prel]
  exact (releasedPairLaw Prel).disintegrate (releasedPairLaw Prel).condKernel

private lemma armProb_measurable {ε : ℝ} (a : ArmSpace) :
    Measurable (armProb a : ScoreSpace ε → ℝ) := by
  cases a
  · change Measurable (fun e : ScoreSpace ε => 1 - (e : ℝ))
    fun_prop
  · change Measurable (fun e : ScoreSpace ε => (e : ℝ))
    fun_prop

private lemma armProb_mem_Icc {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (e : ScoreSpace ε) : armProb a e ∈ Icc (0 : ℝ) 1 := by
  rcases e.property with ⟨he0, he1⟩
  cases a <;> simp [armProb] <;> constructor <;> linarith [hOverlap.1]

private lemma armProb_integrable {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsFiniteMeasure H]
    (hOverlap : Overlap ε) (a : ArmSpace) :
    Integrable (armProb a : ScoreSpace ε → ℝ) H := by
  apply Integrable.of_bound (armProb_measurable a).aestronglyMeasurable 1
  filter_upwards [] with e
  have h := armProb_mem_Icc hOverlap a e
  simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hg,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma propensityTilt_real_cell {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J) :
    (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).real (cell g r) =
      armCellMass H g a r := by
  let F : ScoreSpace ε → ℝ := (cell g r).indicator (armProb a)
  have hcell : MeasurableSet (cell g r) :=
    measurableSet_eq_fun hg measurable_const
  have hF : Measurable F := (armProb_measurable a).indicator hcell
  have hbound : ∀ e, F e ∈ Icc (0 : ℝ) 1 := by
    intro e
    by_cases he : e ∈ cell g r
    · simpa [F, Set.indicator, he] using armProb_mem_Icc hOverlap a e
    · simp [F, Set.indicator, he]
  have hInt : Integrable F H := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    filter_upwards [] with e
    simpa [Real.norm_eq_abs, abs_of_nonneg (hbound e).1] using (hbound e).2
  unfold Measure.real armCellMass
  rw [withDensity_apply _ hcell]
  have hlin :
      (∫⁻ e in cell g r, ENNReal.ofReal (armProb a e) ∂H) =
        ∫⁻ e, ENNReal.ofReal (F e) ∂H := by
    rw [← lintegral_indicator hcell]
    apply lintegral_congr
    intro e
    by_cases he : e ∈ cell g r <;> simp [F, Set.indicator, he]
  rw [hlin, ← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall (fun e => (hbound e).1))]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun e => (hbound e).1))]
  rw [← integral_indicator hcell]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hg,hOverlap,r,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma randomizedKeyLaw_real_singleton {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (hOverlap : Overlap ε) (r : LabelSpace J) (a : ArmSpace) :
    (randomizedKeyLaw H g).real {(r, a)} = armCellMass H g a r := by
  letI : IsFiniteMeasure
      (H.withDensity (fun e => ENNReal.ofReal (armProb false e))) :=
    isFiniteMeasure_withDensity_ofReal (armProb_integrable H hOverlap false).hasFiniteIntegral
  letI : IsFiniteMeasure
      (H.withDensity (fun e => ENNReal.ofReal (armProb true e))) :=
    isFiniteMeasure_withDensity_ofReal (armProb_integrable H hOverlap true).hasFiniteIntegral
  have hkey (b : ArmSpace) : Measurable (fun e : ScoreSpace ε => (g e, b)) := by
    fun_prop
  have hsingle : MeasurableSet ({(r, a)} : Set (LabelSpace J × ArmSpace)) :=
    measurableSet_singleton _
  letI : IsFiniteMeasure (scoreAssignedKeyLaw H g false) := ⟨by
    have hs : (H.withDensity (fun e => ENNReal.ofReal (armProb false e))) Set.univ < ∞ :=
      measure_lt_top _ _
    unfold scoreAssignedKeyLaw
    rw [Measure.map_apply (hkey false) MeasurableSet.univ]
    exact hs
  ⟩
  letI : IsFiniteMeasure (scoreAssignedKeyLaw H g true) := ⟨by
    have hs : (H.withDensity (fun e => ENNReal.ofReal (armProb true e))) Set.univ < ∞ :=
      measure_lt_top _ _
    unfold scoreAssignedKeyLaw
    rw [Measure.map_apply (hkey true) MeasurableSet.univ]
    exact hs
  ⟩
  unfold randomizedKeyLaw
  rw [Measure.real_def, Measure.add_apply]
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  unfold scoreAssignedKeyLaw
  rw [Measure.map_apply (hkey false) hsingle, Measure.map_apply (hkey true) hsingle]
  cases a
  · have hpreFalse : (fun e : ScoreSpace ε => (g e, false)) ⁻¹' {(r, false)} =
        cell g r := by ext e; simp [cell]
    have hpreTrue : (fun e : ScoreSpace ε => (g e, true)) ⁻¹' {(r, false)} = ∅ := by
      ext e
      simp
    rw [hpreFalse, hpreTrue, measure_empty, ENNReal.toReal_zero, add_zero]
    exact propensityTilt_real_cell H g hg hOverlap false r
  · have hpreFalse : (fun e : ScoreSpace ε => (g e, false)) ⁻¹' {(r, true)} = ∅ := by
      ext e
      simp
    have hpreTrue : (fun e : ScoreSpace ε => (g e, true)) ⁻¹' {(r, true)} =
        cell g r := by ext e; simp [cell]
    rw [hpreFalse, hpreTrue, measure_empty, ENNReal.toReal_zero, zero_add]
    exact propensityTilt_real_cell H g hg hOverlap true r

/-- Given [the stated mathematical inputs and assumptions](hyp:J,Prel,r,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma releasedKeyLaw_real_singleton {J : ℕ}
    (Prel : Measure (Observation J)) [IsProbabilityMeasure Prel]
    (r : LabelSpace J) (a : ArmSpace) :
    (releasedKeyLaw Prel).real {(r, a)} =
      Prel.real {z | z.1 = r ∧ z.2.1 = a} := by
  have hkey : Measurable (fun z : Observation J => (z.1, z.2.1)) := by fun_prop
  have hsingle : MeasurableSet ({(r, a)} : Set (LabelSpace J × ArmSpace)) :=
    measurableSet_singleton _
  unfold releasedKeyLaw
  rw [MeasureTheory.map_measureReal_apply hkey hsingle]
  congr 1
  ext z
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma randomizedKeyLaw_eq_releasedKeyLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) :
    randomizedKeyLaw H g = releasedKeyLaw Prel := by
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  letI : IsFiniteMeasure
      (H.withDensity (fun e => ENNReal.ofReal (armProb false e))) :=
    isFiniteMeasure_withDensity_ofReal
      (armProb_integrable H hOverlap false).hasFiniteIntegral
  letI : IsFiniteMeasure
      (H.withDensity (fun e => ENNReal.ofReal (armProb true e))) :=
    isFiniteMeasure_withDensity_ofReal
      (armProb_integrable H hOverlap true).hasFiniteIntegral
  letI : IsFiniteMeasure (scoreAssignedKeyLaw H g false) := ⟨by
    have hs : (H.withDensity (fun e => ENNReal.ofReal (armProb false e))) Set.univ < ∞ :=
      measure_lt_top _ _
    unfold scoreAssignedKeyLaw
    rw [Measure.map_apply (by
      exact hMass.2.2.1.prodMk measurable_const) MeasurableSet.univ]
    exact hs
  ⟩
  letI : IsFiniteMeasure (scoreAssignedKeyLaw H g true) := ⟨by
    have hs : (H.withDensity (fun e => ENNReal.ofReal (armProb true e))) Set.univ < ∞ :=
      measure_lt_top _ _
    unfold scoreAssignedKeyLaw
    rw [Measure.map_apply (by
      exact hMass.2.2.1.prodMk measurable_const) MeasurableSet.univ]
    exact hs
  ⟩
  letI : IsFiniteMeasure (randomizedKeyLaw H g) := by
    unfold randomizedKeyLaw scoreAssignedKeyLaw
    infer_instance
  letI : IsProbabilityMeasure (releasedKeyLaw Prel) := by
    unfold releasedKeyLaw
    have hkey : Measurable (fun z : Observation J => (z.1, z.2.1)) := by fun_prop
    exact Measure.isProbabilityMeasure_map hkey.aemeasurable
  apply Measure.ext_of_measureReal_singleton
  rintro ⟨r, a⟩
  rw [randomizedKeyLaw_real_singleton H g hMass.2.2.1 hOverlap r a,
    releasedKeyLaw_real_singleton Prel r a, hMass.2.2.2 a r]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
