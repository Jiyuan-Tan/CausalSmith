module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionSieveDensity
public import Causalean.Stat.Quantile.AtomicApproximation.Main
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionDistanceTriangle

/-! Bridge from synchronized real-line atomic approximation to the paper's
compact-carrier projection sieve. -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeCDFDistance_eq_realCdfDistance (μ ν : Measure OutcomeSpace) :
    outcomeCDFDistance μ ν =
      Causalean.Stat.Quantile.AtomicApproximation.cdfDistance 0 1
        (μ.map (fun y : OutcomeSpace => (y : ℝ)))
        (ν.map (fun y : OutcomeSpace => (y : ℝ))) := by
  unfold outcomeCDFDistance Causalean.Stat.Quantile.AtomicApproximation.cdfDistance
  rw [Measure.real_def, Measure.real_def, Measure.real_def, Measure.real_def]
  rw [Measure.map_apply (by fun_prop : Measurable fun y : OutcomeSpace => (y : ℝ))
    MeasurableSet.univ, Measure.map_apply
      (by fun_prop : Measurable fun y : OutcomeSpace => (y : ℝ)) MeasurableSet.univ]
  simp only [preimage_univ]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  simp only [Measure.real_def]
  rw [Measure.map_apply (by fun_prop : Measurable fun y : OutcomeSpace => (y : ℝ))
      measurableSet_Iic,
    Measure.map_apply (by fun_prop : Measurable fun y : OutcomeSpace => (y : ℝ))
      measurableSet_Iic]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreCDFDistance_eq_realCdfDistance {ε : ℝ}
    (μ ν : Measure (ScoreSpace ε)) :
    scoreCDFDistance μ ν =
      Causalean.Stat.Quantile.AtomicApproximation.cdfDistance ε (1 - ε)
        (μ.map (fun e : ScoreSpace ε => (e : ℝ)))
        (ν.map (fun e : ScoreSpace ε => (e : ℝ))) := by
  unfold scoreCDFDistance Causalean.Stat.Quantile.AtomicApproximation.cdfDistance
  rw [Measure.real_def, Measure.real_def, Measure.real_def, Measure.real_def]
  rw [Measure.map_apply (by fun_prop : Measurable fun e : ScoreSpace ε => (e : ℝ))
    MeasurableSet.univ, Measure.map_apply
      (by fun_prop : Measurable fun e : ScoreSpace ε => (e : ℝ)) MeasurableSet.univ]
  simp only [preimage_univ]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  simp only [Measure.real_def]
  rw [Measure.map_apply (by fun_prop : Measurable fun e : ScoreSpace ε => (e : ℝ))
      measurableSet_Iic,
    Measure.map_apply (by fun_prop : Measurable fun e : ScoreSpace ε => (e : ℝ))
      measurableSet_Iic]
  rfl

/-- For [the specified mathematical inputs](hyp:x), [this definition](goal) introduces the corresponding object. -/
def realOutcomePoint (x : ℝ) : OutcomeSpace :=
  ⟨max 0 (min 1 x), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)⟩
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma realOutcomePoint_continuous : Continuous realOutcomePoint := by
  unfold realOutcomePoint
  exact Continuous.subtype_mk
    (continuous_const.max (continuous_const.min continuous_id)) _
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma realOutcomePoint_surjective : Function.Surjective realOutcomePoint := by
  intro y
  refine ⟨(y : ℝ), ?_⟩
  apply Subtype.ext
  simp [realOutcomePoint, y.property.1, y.property.2]
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma rationalOutcomePoint_denseRange :
    DenseRange (rationalOutcomePoint : ℚ → OutcomeSpace) := by
  have h := DenseRange.comp realOutcomePoint_surjective.denseRange
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)) realOutcomePoint_continuous
  convert h using 1
  funext q
  rfl

/-- For [the specified mathematical inputs](hyp:ε,hOverlap,y), [this definition](goal) introduces the corresponding object. -/
def outcomeToScore {ε : ℝ} (hOverlap : Overlap ε)
    (y : OutcomeSpace) : ScoreSpace ε :=
  ⟨ε + (1 - 2 * ε) * (y : ℝ), by
    have hw : 0 ≤ 1 - 2 * ε := by linarith [hOverlap.2]
    constructor
    · nlinarith [y.property.1]
    · nlinarith [y.property.2]⟩
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeToScore_continuous {ε : ℝ} (hOverlap : Overlap ε) :
    Continuous (outcomeToScore hOverlap) := by
  unfold outcomeToScore
  exact Continuous.subtype_mk (by fun_prop) _
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeToScore_surjective {ε : ℝ} (hOverlap : Overlap ε) :
    Function.Surjective (outcomeToScore hOverlap) := by
  intro e
  have hw : 0 < 1 - 2 * ε := by linarith [hOverlap.2]
  let y : OutcomeSpace := ⟨((e : ℝ) - ε) / (1 - 2 * ε), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr e.property.1) hw.le
    · apply (div_le_one hw).2
      linarith [e.property.2]⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change ε + (1 - 2 * ε) * (((e : ℝ) - ε) / (1 - 2 * ε)) = (e : ℝ)
  have hcancel : (1 - 2 * ε) * (((e : ℝ) - ε) / (1 - 2 * ε)) =
      (e : ℝ) - ε := by
    exact mul_div_cancel₀ _ (ne_of_gt hw)
  linarith
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma rationalScorePoint_denseRange {ε : ℝ} (hOverlap : Overlap ε) :
    DenseRange (rationalScorePoint ε hOverlap : ℚ → ScoreSpace ε) := by
  have h := DenseRange.comp (outcomeToScore_surjective hOverlap).denseRange
    rationalOutcomePoint_denseRange (outcomeToScore_continuous hOverlap)
  convert h using 1
  funext q
  rfl

/-- [This definition](goal) introduces the corresponding mathematical object. -/
def outcomeSieveLocations : Set ℝ :=
  Set.range (fun q : ℚ => (rationalOutcomePoint q : ℝ))

/-- For [the specified mathematical inputs](hyp:ε,hOverlap), [this definition](goal) introduces the corresponding object. -/
def scoreSieveLocations {ε : ℝ} (hOverlap : Overlap ε) : Set ℝ :=
  Set.range (fun q : ℚ => (rationalScorePoint ε hOverlap q : ℝ))
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeSieveLocations_countable : outcomeSieveLocations.Countable := by
  unfold outcomeSieveLocations
  exact Set.countable_range _
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreSieveLocations_countable {ε : ℝ} (hOverlap : Overlap ε) :
    (scoreSieveLocations hOverlap).Countable := by
  unfold scoreSieveLocations
  exact Set.countable_range _
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeSieveLocations_subset : outcomeSieveLocations ⊆ Icc (0 : ℝ) 1 := by
  rintro x ⟨q, rfl⟩
  exact (rationalOutcomePoint q).property
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreSieveLocations_subset {ε : ℝ} (hOverlap : Overlap ε) :
    scoreSieveLocations hOverlap ⊆ Icc ε (1 - ε) := by
  rintro x ⟨q, rfl⟩
  exact (rationalScorePoint ε hOverlap q).property
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeSieveLocations_dense :
    Dense ((Subtype.val : OutcomeSpace → ℝ) ⁻¹' outcomeSieveLocations) := by
  have heq : ((Subtype.val : OutcomeSpace → ℝ) ⁻¹' outcomeSieveLocations) =
      Set.range (rationalOutcomePoint : ℚ → OutcomeSpace) := by
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, rfl⟩
  rw [heq]
  exact rationalOutcomePoint_denseRange
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreSieveLocations_dense {ε : ℝ} (hOverlap : Overlap ε) :
    Dense ((Subtype.val : ScoreSpace ε → ℝ) ⁻¹' scoreSieveLocations hOverlap) := by
  have heq : ((Subtype.val : ScoreSpace ε → ℝ) ⁻¹' scoreSieveLocations hOverlap) =
      Set.range (rationalScorePoint ε hOverlap : ℚ → ScoreSpace ε) := by
    ext e
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, rfl⟩
  rw [heq]
  exact rationalScorePoint_denseRange hOverlap

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,μ,ν,hmass,η,hη), this result [establishes the stated mathematical conclusion](goal). -/
lemma exists_synchronized_sieveLocations_cell_approx {ε : ℝ}
    (hOverlap : Overlap ε)
    (μ : Measure OutcomeSpace) (ν : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (hN : 0 < N) (q : ℚ), 0 ≤ q ∧
      ∃ (x : Fin N → outcomeSieveLocations)
        (y : Fin N → scoreSieveLocations hOverlap),
        (Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
          (fun i => (x i : ℝ))).real Set.univ = (q : ℝ) ∧
        (Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
          (fun i => (y i : ℝ))).real Set.univ = (q : ℝ) ∧
        Causalean.Stat.Quantile.AtomicApproximation.cdfDistance 0 1
          (μ.map (fun z : OutcomeSpace => (z : ℝ)))
          (Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
            (fun i => (x i : ℝ))) +
        Causalean.Stat.Quantile.AtomicApproximation.cdfDistance ε (1 - ε)
          (ν.map (fun z : ScoreSpace ε => (z : ℝ)))
          (Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
            (fun i => (y i : ℝ))) < η := by
  let μr : Measure ℝ := μ.map (fun z : OutcomeSpace => (z : ℝ))
  let νr : Measure ℝ := ν.map (fun z : ScoreSpace ε => (z : ℝ))
  letI : IsFiniteMeasure μr := Measure.isFiniteMeasure_map μ _
  letI : IsFiniteMeasure νr := Measure.isFiniteMeasure_map ν _
  have hμ : μr (Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [Measure.map_apply (by fun_prop : Measurable fun z : OutcomeSpace => (z : ℝ))
      measurableSet_Icc.compl]
    have he : (fun z : OutcomeSpace => (z : ℝ)) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
      ext z
      simp [z.property]
    simp [he]
  have hν : νr (Icc ε (1 - ε))ᶜ = 0 := by
    rw [Measure.map_apply (by fun_prop : Measurable fun z : ScoreSpace ε => (z : ℝ))
      measurableSet_Icc.compl]
    have he : (fun z : ScoreSpace ε => (z : ℝ)) ⁻¹' (Icc ε (1 - ε))ᶜ = ∅ := by
      ext z
      simp [z.property]
    simp [he]
  have hm : μr.real Set.univ = νr.real Set.univ := by
    simp only [μr, νr, Measure.real_def]
    rw [Measure.map_apply (by fun_prop : Measurable fun z : OutcomeSpace => (z : ℝ))
      MeasurableSet.univ,
      Measure.map_apply (by fun_prop : Measurable fun z : ScoreSpace ε => (z : ℝ))
        MeasurableSet.univ]
    simpa only [preimage_univ, ← Measure.real_def] using hmass
  exact Causalean.Stat.Quantile.AtomicApproximation.exists_synchronized_rational_equalAtom_approx
    μr νr 0 1 ε (1 - ε) (by norm_num) (by linarith [hOverlap.2])
    hμ hν hm outcomeSieveLocations (scoreSieveLocations hOverlap)
    outcomeSieveLocations_subset (scoreSieveLocations_subset hOverlap)
    outcomeSieveLocations_countable (scoreSieveLocations_countable hOverlap)
    outcomeSieveLocations_dense (scoreSieveLocations_dense hOverlap) η hη

/-- Given [the stated mathematical inputs and assumptions](hyp:N,q,x,y), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedOutcome_map_eq_equalAtom {N : ℕ} (q : ℚ)
    (x y : Fin N → ℚ) :
    (synchronizedRationalOutcomeMeasure
      (List.ofFn fun i : Fin N => (x i, y i, q / N))).map
        (fun z : OutcomeSpace => (z : ℝ)) =
      Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
        (fun i => (rationalOutcomePoint (x i) : ℝ)) := by
  unfold synchronizedRationalOutcomeMeasure rationalOutcomeMeasure
    Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure
  simp only [List.map_ofFn, List.sum_ofFn]
  let f : OutcomeSpace → ℝ := fun z => (z : ℝ)
  let M : Fin N → Measure OutcomeSpace := fun i =>
    ENNReal.ofReal ((q / N : ℚ) : ℝ) • Measure.dirac (rationalOutcomePoint (x i))
  change (∑ i, M i).map f = _
  have hmap (s : Finset (Fin N)) :
      (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [Measure.map_add _ _ (by fun_prop : Measurable f), ih]
  rw [show (∑ i : Fin N, M i).map f = ∑ i : Fin N, (M i).map f by
    simpa using hmap Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.map_smul, Measure.map_dirac']
  · simp [f, Rat.cast_div, Rat.cast_natCast]
  · fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,N,q,x,y), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedScore_map_eq_equalAtom {ε : ℝ} (hOverlap : Overlap ε)
    {N : ℕ} (q : ℚ) (x y : Fin N → ℚ) :
    (synchronizedRationalScoreMeasure ε hOverlap
      (List.ofFn fun i : Fin N => (x i, y i, q / N))).map
        (fun z : ScoreSpace ε => (z : ℝ)) =
      Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
        (fun i => (rationalScorePoint ε hOverlap (y i) : ℝ)) := by
  unfold synchronizedRationalScoreMeasure rationalScoreMeasure
    Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure
  simp only [List.map_ofFn, List.sum_ofFn]
  let f : ScoreSpace ε → ℝ := fun z => (z : ℝ)
  let M : Fin N → Measure (ScoreSpace ε) := fun i =>
    ENNReal.ofReal ((q / N : ℚ) : ℝ) • Measure.dirac (rationalScorePoint ε hOverlap (y i))
  change (∑ i, M i).map f = _
  have hmap (s : Finset (Fin N)) :
      (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [Measure.map_add _ _ (by fun_prop : Measurable f), ih]
  rw [show (∑ i : Fin N, M i).map f = ∑ i : Fin N, (M i).map f by
    simpa using hmap Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.map_smul, Measure.map_dirac']
  · simp [f, Rat.cast_div, Rat.cast_natCast]
  · fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,μ,ν,hmass,η,hη), this result [establishes the stated mathematical conclusion](goal). -/
lemma exists_synchronizedRationalCode_cell_approx {ε : ℝ}
    (hOverlap : Overlap ε)
    (μ : Measure OutcomeSpace) (ν : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real Set.univ = ν.real Set.univ)
    (η : ℝ) (hη : 0 < η) :
    ∃ code : List ProjectionRationalAtom,
      outcomeCDFDistance μ (synchronizedRationalOutcomeMeasure code) +
        scoreCDFDistance ν (synchronizedRationalScoreMeasure ε hOverlap code) < η := by
  classical
  obtain ⟨N, hN, q, hq, x, y, hmx, hmy, hdist⟩ :=
    exists_synchronized_sieveLocations_cell_approx hOverlap μ ν hmass η hη
  let xq : Fin N → ℚ := fun i => Classical.choose (x i).property
  let yq : Fin N → ℚ := fun i => Classical.choose (y i).property
  have hx (i : Fin N) : (rationalOutcomePoint (xq i) : ℝ) = (x i : ℝ) :=
    Classical.choose_spec (x i).property
  have hy (i : Fin N) : (rationalScorePoint ε hOverlap (yq i) : ℝ) = (y i : ℝ) :=
    Classical.choose_spec (y i).property
  let code : List ProjectionRationalAtom :=
    List.ofFn fun i : Fin N => (xq i, yq i, q / N)
  refine ⟨code, ?_⟩
  have hout : (synchronizedRationalOutcomeMeasure code).map
      (fun z : OutcomeSpace => (z : ℝ)) =
      Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
        (fun i => (x i : ℝ)) := by
    rw [show code = List.ofFn (fun i : Fin N => (xq i, yq i, q / N)) from rfl,
      synchronizedOutcome_map_eq_equalAtom]
    congr 1
    funext i
    exact hx i
  have hscore : (synchronizedRationalScoreMeasure ε hOverlap code).map
      (fun z : ScoreSpace ε => (z : ℝ)) =
      Causalean.Stat.Quantile.AtomicApproximation.equalAtomMeasure N (q : ℝ)
        (fun i => (y i : ℝ)) := by
    rw [show code = List.ofFn (fun i : Fin N => (xq i, yq i, q / N)) from rfl,
      synchronizedScore_map_eq_equalAtom]
    congr 1
    funext i
    exact hy i
  rw [outcomeCDFDistance_eq_realCdfDistance,
    scoreCDFDistance_eq_realCdfDistance, hout, hscore]
  exact hdist

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,lam,σ,hfinite,hcompat,η,hη), this result [establishes the stated mathematical conclusion](goal). -/
lemma exists_rationalSieveArray_close {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤)
    (hcompat : ProjectionCompatible lam σ)
    (η : ℝ) (hη : 0 < η) :
    ∃ code : ArmSpace → LabelSpace J → List ProjectionRationalAtom,
      let b := ((fun a r => synchronizedRationalOutcomeMeasure (code a r)),
        (fun a r => synchronizedRationalScoreMeasure ε hOverlap (code a r)))
      b ∈ rationalArraySieve ε J ∧ ProjectionCompatible b.1 b.2 ∧
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          (outcomeCDFDistance (lam a r) (b.1 a r) +
            scoreCDFDistance (σ a r) (b.2 a r))) < η := by
  classical
  let δ : ℝ := η / (2 * (J + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcell (a : ArmSpace) (r : LabelSpace J) :
      ∃ code : List ProjectionRationalAtom,
        outcomeCDFDistance (lam a r) (synchronizedRationalOutcomeMeasure code) +
          scoreCDFDistance (σ a r)
            (synchronizedRationalScoreMeasure ε hOverlap code) < δ := by
    letI : IsFiniteMeasure (lam a r) := ⟨(hfinite a r).1⟩
    letI : IsFiniteMeasure (σ a r) := ⟨(hfinite a r).2⟩
    exact exists_synchronizedRationalCode_cell_approx hOverlap
      (lam a r) (σ a r) (hcompat a r) δ hδ
  let code : ArmSpace → LabelSpace J → List ProjectionRationalAtom :=
    fun a r => Classical.choose (hcell a r)
  have hbound (a : ArmSpace) (r : LabelSpace J) :=
    Classical.choose_spec (hcell a r)
  refine ⟨code, synchronizedRationalArray_mem_sieve hOverlap code,
    synchronizedRationalArray_compatible hOverlap code, ?_⟩
  have hsum : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      (outcomeCDFDistance (lam a r) (synchronizedRationalOutcomeMeasure (code a r)) +
        scoreCDFDistance (σ a r)
          (synchronizedRationalScoreMeasure ε hOverlap (code a r)))) ≤
      ∑ a : ArmSpace, ∑ _r : LabelSpace J, δ := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro r hr
    exact (hbound a r).le
  have hcard : (∑ a : ArmSpace, ∑ _r : LabelSpace J, δ) =
      (2 * (J : ℝ)) * δ := by
    simp
    ring
  rw [hcard] at hsum
  calc
    _ ≤ (2 * (J : ℝ)) * δ := hsum
    _ < η := by
      dsimp [δ]
      have hden : (0 : ℝ) < 2 * ((J : ℝ) + 1) := by positivity
      calc
        2 * (J : ℝ) * (η / (2 * ((J : ℝ) + 1))) =
            (2 * (J : ℝ) * η) / (2 * ((J : ℝ) + 1)) := by ring
        _ < η := (div_lt_iff₀ hden).2 (by nlinarith [hη])
/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeCDFDistance_symm (μ ν : Measure OutcomeSpace) :
    outcomeCDFDistance μ ν = outcomeCDFDistance ν μ := by
  unfold outcomeCDFDistance
  rw [abs_sub_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  rw [abs_sub_comm]
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreCDFDistance_symm {ε : ℝ} (μ ν : Measure (ScoreSpace ε)) :
    scoreCDFDistance μ ν = scoreCDFDistance ν μ := by
  unfold scoreCDFDistance
  rw [abs_sub_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  rw [abs_sub_comm]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,α,x,lam,σ,b,hbfinite,hcompat,hlamfinite,hcloseOut,hcloseScore), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_of_strict_population_slack
    {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε)
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hbfinite : ∀ a r, (b.1 a r) Set.univ < ⊤ ∧ (b.2 a r) Set.univ < ⊤)
    (hcompat : ProjectionCompatible b.1 b.2)
    (hlamfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤)
    (hcloseOut :
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (b.1 a r) (lam a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (lam a r) (empiricalTrialCells x.1 a r)) ≤
        4 * J / (α * Real.sqrt n))
    (hcloseScore :
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (b.2 a r) (σ a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (σ a r) (empiricalScoreCells g x.2 a r)) ≤
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m)) :
    b ∈ projectionCandidates g α x := by
  refine ⟨hbfinite, hcompat, ?_, ?_⟩
  · have htri (a : ArmSpace) (r : LabelSpace J) :=
      outcomeCDFDistance_triangle (b.1 a r) (lam a r)
        (empiricalTrialCells x.1 a r) (hbfinite a r).1
        (hlamfinite a r).1 (empiricalTrialCells_finite x.1 a r)
    have hsum : (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (b.1 a r) (empiricalTrialCells x.1 a r)) ≤
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (b.1 a r) (lam a r)) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (lam a r) (empiricalTrialCells x.1 a r)) := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro r hr
      exact htri a r
    exact hsum.trans hcloseOut
  · have htri (a : ArmSpace) (r : LabelSpace J) :=
      scoreCDFDistance_triangle hOverlap (b.2 a r) (σ a r)
        (empiricalScoreCells g x.2 a r) (hbfinite a r).2
        (hlamfinite a r).2 (empiricalScoreCells_finite g x.2 a r)
    have hsum : (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (b.2 a r) (empiricalScoreCells g x.2 a r)) ≤
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (b.2 a r) (σ a r)) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (σ a r) (empiricalScoreCells g x.2 a r)) := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro r hr
      exact htri a r
    exact hsum.trans hcloseScore

-- keep: source-named reusable density theorem for the canonical rational sieve
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,lam,σ,hfinite,hcompat,η,hη), this result [establishes the stated mathematical conclusion](goal). -/
lemma rationalSieve_dense {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤)
    (hcompat : ProjectionCompatible lam σ) (η : ℝ) (hη : 0 < η) :
    ∃ b ∈ rationalArraySieve ε J,
      ProjectionCompatible b.1 b.2 ∧
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        (outcomeCDFDistance (lam a r) (b.1 a r) +
          scoreCDFDistance (σ a r) (b.2 a r))) < η := by
  obtain ⟨code, hb, hc, hd⟩ :=
    exists_rationalSieveArray_close hOverlap lam σ hfinite hcompat η hη
  exact ⟨_, hb, hc, hd⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte
