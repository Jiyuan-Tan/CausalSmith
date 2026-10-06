module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogQuantileIntegrals
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogFullLaw

/-! Arm-cell normalization leaves for the score-log construction. -/

@[expose] public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- For [the specified mathematical inputs](hyp:J,r,q,t,c), [this definition](goal) introduces the corresponding object. -/
def scoreLogReleasedCellLaw {J : ℕ} (r : LabelSpace J) (q t c : ℝ) :
    Measure (Observation J) :=
  ENNReal.ofReal q •
      (trialOutcomeLaw (t / q)).map (fun y => (r, true, y)) +
    ENNReal.ofReal c • Measure.dirac (r, false, trialZeroOutcome)
/-- Given [the stated mathematical inputs and assumptions](hyp:J,r,q,t,c,hq0,hc0,hs0,hs1,hsum), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogReleasedCellLaw_isProbabilityMeasure {J : ℕ}
    (r : LabelSpace J) (q t c : ℝ)
    (hq0 : 0 ≤ q) (hc0 : 0 ≤ c) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1)
    (hsum : q + c = 1) :
    IsProbabilityMeasure (scoreLogReleasedCellLaw r q t c) := by
  letI := trialOutcomeLaw_isProbabilityMeasure (t / q) hs0 hs1
  rw [isProbabilityMeasure_iff]
  unfold scoreLogReleasedCellLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, Measure.dirac_apply, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hq0 hc0, hsum]
  norm_num
/-- Given [the stated mathematical inputs and assumptions](hyp:J,r,q,t,c,hq0,hs0,hs1), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogReleasedCellLaw_treated_mass {J : ℕ}
    (r : LabelSpace J) (q t c : ℝ)
    (hq0 : 0 ≤ q) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1) :
    (scoreLogReleasedCellLaw r q t c).real
        {z | z.1 = r ∧ z.2.1 = true} = q := by
  letI := trialOutcomeLaw_isProbabilityMeasure (t / q) hs0 hs1
  unfold scoreLogReleasedCellLaw
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop)]
  · simp [hq0, trialZeroOutcome]
  · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
/-- Given [the stated mathematical inputs and assumptions](hyp:J,r,q,t,c,hs0,hs1), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogReleasedCellLaw_treated_mass_ennreal {J : ℕ}
    (r : LabelSpace J) (q t c : ℝ)
    (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1) :
    scoreLogReleasedCellLaw r q t c {z | z.1 = r ∧ z.2.1 = true} =
      ENNReal.ofReal q := by
  letI := trialOutcomeLaw_isProbabilityMeasure (t / q) hs0 hs1
  unfold scoreLogReleasedCellLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop)]
  · simp [trialZeroOutcome]
  · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)

/-- Given [the stated mathematical inputs and assumptions](hyp:J,r,q,t,c,hq,hc0,hs0,hs1,hsum), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogReleasedCellLaw_armCellOutcomeLaw {J : ℕ}
    (r : LabelSpace J) (q t c : ℝ)
    (hq : 0 < q) (hc0 : 0 ≤ c) (hs0 : 0 ≤ t / q) (hs1 : t / q ≤ 1)
    (hsum : q + c = 1) :
    let Prel := scoreLogReleasedCellLaw r q t c
    let hPrel : IsProbabilityMeasure Prel :=
      scoreLogReleasedCellLaw_isProbabilityMeasure r q t c hq.le hc0 hs0 hs1 hsum
    armCellOutcomeLaw Prel hPrel true r
        (by simpa [Prel, scoreLogReleasedCellLaw_treated_mass r q t c hq.le hs0 hs1]
          using hq) =
      threeScoreOutcomeLaw q t := by
  dsimp only
  letI : IsProbabilityMeasure (scoreLogReleasedCellLaw r q t c) :=
    scoreLogReleasedCellLaw_isProbabilityMeasure r q t c hq.le hc0 hs0 hs1 hsum
  apply Measure.ext fun B hB => ?_
  rw [armCellOutcomeLaw_apply]
  rw [scoreLogReleasedCellLaw_treated_mass_ennreal r q t c hs0 hs1]
  unfold scoreLogReleasedCellLaw threeScoreOutcomeLaw trialOutcomeLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.map_apply (by fun_prop)]
  · rw [Measure.add_apply, Measure.add_apply,
      Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.smul_apply]
    simp only [Measure.dirac_apply,
      Set.indicator_of_mem, smul_eq_mul]
    simp [trialOneOutcome, trialZeroOutcome]
    have hqE : ENNReal.ofReal q ≠ 0 := by positivity
    have hqT : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [← mul_assoc, ENNReal.inv_mul_cancel hqE hqT, one_mul]
    by_cases h1 : (1 : ℝ) ∈ B <;> by_cases h0 : (0 : ℝ) ∈ B <;>
      simp [Set.indicator, h1, h0, trialOneOutcome, trialZeroOutcome]
  · exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
        ((by fun_prop : Measurable fun z : Observation J => (z.2.2 : ℝ)) hB))
  · exact hB

end
end CausalSmith.PartialID.UnlinkedPropensityAte
