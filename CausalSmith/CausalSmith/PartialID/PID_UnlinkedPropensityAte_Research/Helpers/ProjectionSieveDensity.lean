module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionGeometry

/-!
Exact-mass rational encodings for the external projection sieve.

The outcome and score locations may differ, but every atom uses one shared
rational weight.  This supplies the synchronized finite arrays needed by an
eventual density argument for the equal-mass projection candidates.
-/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- [This definition](goal) introduces the corresponding mathematical object. -/
abbrev ProjectionRationalAtom := ℚ × ℚ × ℚ

/-- For [the specified mathematical inputs](hyp:l), [this definition](goal) introduces the corresponding object. -/
def synchronizedRationalOutcomeMeasure (l : List ProjectionRationalAtom) :
    Measure OutcomeSpace :=
  rationalOutcomeMeasure (l.map fun p => (p.1, p.2.2))

/-- For [the specified mathematical inputs](hyp:ε,hOverlap,l), [this definition](goal) introduces the corresponding object. -/
def synchronizedRationalScoreMeasure (ε : ℝ) (hOverlap : Overlap ε)
    (l : List ProjectionRationalAtom) : Measure (ScoreSpace ε) :=
  rationalScoreMeasure ε hOverlap (l.map fun p => (p.2.1, p.2.2))

/-- Given [the stated mathematical inputs and assumptions](hyp:l), this result [establishes the stated mathematical conclusion](goal). -/
lemma rationalOutcomeMeasure_apply_univ (l : List (ℚ × ℚ)) :
    rationalOutcomeMeasure l Set.univ =
      (l.map fun p => ENNReal.ofReal (p.2 : ℝ)).sum := by
  induction l with
  | nil => simp [rationalOutcomeMeasure]
  | cons p l ih =>
      change (ENNReal.ofReal (p.2 : ℝ) •
          Measure.dirac (rationalOutcomePoint p.1)) Set.univ +
        rationalOutcomeMeasure l Set.univ =
          ENNReal.ofReal (p.2 : ℝ) +
            (l.map fun p => ENNReal.ofReal (p.2 : ℝ)).sum
      rw [ih]
      simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,l), this result [establishes the stated mathematical conclusion](goal). -/
lemma rationalScoreMeasure_apply_univ {ε : ℝ} (hOverlap : Overlap ε)
    (l : List (ℚ × ℚ)) :
    rationalScoreMeasure ε hOverlap l Set.univ =
      (l.map fun p => ENNReal.ofReal (p.2 : ℝ)).sum := by
  induction l with
  | nil => simp [rationalScoreMeasure]
  | cons p l ih =>
      change (ENNReal.ofReal (p.2 : ℝ) •
          Measure.dirac (rationalScorePoint ε hOverlap p.1)) Set.univ +
        rationalScoreMeasure ε hOverlap l Set.univ =
          ENNReal.ofReal (p.2 : ℝ) +
            (l.map fun p => ENNReal.ofReal (p.2 : ℝ)).sum
      rw [ih]
      simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,l), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedRationalMeasure_mass_eq {ε : ℝ} (hOverlap : Overlap ε)
    (l : List ProjectionRationalAtom) :
    synchronizedRationalOutcomeMeasure l Set.univ =
      synchronizedRationalScoreMeasure ε hOverlap l Set.univ := by
  rw [synchronizedRationalOutcomeMeasure, synchronizedRationalScoreMeasure,
    rationalOutcomeMeasure_apply_univ, rationalScoreMeasure_apply_univ]
  apply congrArg List.sum
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro p hp
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,code), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedRationalArray_compatible {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε)
    (code : ArmSpace → LabelSpace J → List ProjectionRationalAtom) :
    ProjectionCompatible
      (fun a r => synchronizedRationalOutcomeMeasure (code a r))
      (fun a r => synchronizedRationalScoreMeasure ε hOverlap (code a r)) := by
  intro a r
  exact congrArg ENNReal.toReal
    (synchronizedRationalMeasure_mass_eq hOverlap (code a r))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,code), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedRationalArray_mem_sieve {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε)
    (code : ArmSpace → LabelSpace J → List ProjectionRationalAtom) :
    ((fun a r => synchronizedRationalOutcomeMeasure (code a r)),
      (fun a r => synchronizedRationalScoreMeasure ε hOverlap (code a r))) ∈
        rationalArraySieve ε J := by
  classical
  unfold rationalArraySieve
  simp only [dif_pos hOverlap, Set.mem_inter_iff, Set.mem_range, Set.mem_setOf_eq]
  constructor
  · refine ⟨((fun a r => (code a r).map fun p => (p.1, p.2.2)),
      (fun a r => (code a r).map fun p => (p.2.1, p.2.2))), ?_⟩
    rfl
  · exact synchronizedRationalArray_compatible hOverlap code

/-- Given [the stated mathematical inputs and assumptions](hyp:l), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedRationalOutcomeMeasure_finite
    (l : List ProjectionRationalAtom) :
    synchronizedRationalOutcomeMeasure l Set.univ < ⊤ := by
  rw [synchronizedRationalOutcomeMeasure, rationalOutcomeMeasure_apply_univ]
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, ENNReal.add_lt_top]
      exact ⟨ENNReal.ofReal_lt_top, ih⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,l), this result [establishes the stated mathematical conclusion](goal). -/
lemma synchronizedRationalScoreMeasure_finite {ε : ℝ}
    (hOverlap : Overlap ε) (l : List ProjectionRationalAtom) :
    synchronizedRationalScoreMeasure ε hOverlap l Set.univ < ⊤ := by
  rw [synchronizedRationalScoreMeasure,
    rationalScoreMeasure_apply_univ hOverlap]
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, ENNReal.add_lt_top]
      exact ⟨ENNReal.ofReal_lt_top, ih⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte
