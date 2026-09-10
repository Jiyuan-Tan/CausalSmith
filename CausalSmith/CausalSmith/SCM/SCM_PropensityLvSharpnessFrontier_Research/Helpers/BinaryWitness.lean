import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements

/-! # Full-support binary witnesses for generator separation -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- The concrete binary law is a probability measure for a probability
coordinate.  For the specified model objects, [the stated conditions](hyp:hp), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_isProbabilityMeasure
lemma binaryLaw_isProbabilityMeasure (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (binaryLaw p) := by
  rw [isProbabilityMeasure_iff]
  simpa [binaryLaw, ENNReal.ofReal_sub 1 hp.1] using
    tsub_add_cancel_of_le (ENNReal.ofReal_le_one.mpr hp.2)

/-- The success event of the concrete binary law has its defining mass.  For the specified model objects, [the stated conditions](hyp:hp), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_true
lemma binaryLaw_true (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    binaryLaw p {true} = ENNReal.ofReal p := by
  rw [binaryLaw]
  simp

/-- Full-support binary laws are mutually absolutely continuous.  For the specified model objects, [the stated conditions](hyp:hp,hq), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_mutuallyAC
lemma binaryLaw_mutuallyAC (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : q ∈ Set.Ioo 0 1) :
    MutuallyAC (binaryLaw p) (binaryLaw q) := by
  constructor <;> intro s hzero
  · have hs : MeasurableSet s := MeasurableSet.of_discrete
    have hq0 : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq.1)
    have hq1 : ENNReal.ofReal (1 - q) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hq.2))
    have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp.1)
    have hp1 : ENNReal.ofReal (1 - p) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp.2))
    simpa [binaryLaw, hq0, hq1, hp0, hp1] using hzero
  · have hs : MeasurableSet s := MeasurableSet.of_discrete
    have hq0 : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq.1)
    have hq1 : ENNReal.ofReal (1 - q) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hq.2))
    have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp.1)
    have hp1 : ENNReal.ofReal (1 - p) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp.2))
    simpa [binaryLaw, hq0, hq1, hp0, hp1] using hzero

/-- The lower-cap Bernoulli law is the mixture of the observed Bernoulli law
and the point mass at failure.  For the specified model objects, [the stated conditions](hyp:he,hp), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_lowerCap_mixture
lemma binaryLaw_lowerCap_mixture (e p : ℝ)
    (he : e ∈ Set.Icc 0 1) (hp : p ∈ Set.Icc 0 1) :
    binaryLaw (e * p) = ENNReal.ofReal e • binaryLaw p +
      ENNReal.ofReal (1 - e) • binaryLaw 0 := by
  ext s hs
  simp only [binaryLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul he.1]
  rw [ENNReal.ofReal_sub 1 (mul_nonneg he.1 hp.1)]
  rw [ENNReal.ofReal_sub 1 he.1, ENNReal.ofReal_sub 1 hp.1]
  have hep : ENNReal.ofReal e * ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_mul he.1]
    exact ENNReal.ofReal_le_one.mpr (calc
      e * p ≤ 1 * p := mul_le_mul_of_nonneg_right he.2 hp.1
      _ ≤ 1 := by simpa using hp.2)
  have he' : ENNReal.ofReal e ≤ 1 := ENNReal.ofReal_le_one.mpr he.2
  have hp' : ENNReal.ofReal p ≤ 1 := ENNReal.ofReal_le_one.mpr hp.2
  have hepE : ENNReal.ofReal e * ENNReal.ofReal p ≤ ENNReal.ofReal e :=
    mul_le_of_le_one_right (by simp) hp'
  have hid : ENNReal.ofReal e * (1 - ENNReal.ofReal p) +
      (1 - ENNReal.ofReal e) = 1 - ENNReal.ofReal (e * p) := by
    rw [ENNReal.ofReal_mul he.1]
    apply ENNReal.eq_sub_of_add_eq
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    calc
      ENNReal.ofReal e * (1 - ENNReal.ofReal p) +
          (1 - ENNReal.ofReal e) + ENNReal.ofReal e * ENNReal.ofReal p =
          (ENNReal.ofReal e * (1 - ENNReal.ofReal p) +
            ENNReal.ofReal e * ENNReal.ofReal p) +
            (1 - ENNReal.ofReal e) := by ac_rfl
      _ = ENNReal.ofReal e * ((1 - ENNReal.ofReal p) + ENNReal.ofReal p) +
          (1 - ENNReal.ofReal e) := by rw [mul_add]
      _ = ENNReal.ofReal e + (1 - ENNReal.ofReal e) := by
        rw [tsub_add_cancel_of_le hp', mul_one]
      _ = 1 := by rw [add_comm, tsub_add_cancel_of_le he']
  by_cases hf : false ∈ s <;> by_cases ht : true ∈ s <;>
    simp [hs, hf, ht, hid, tsub_add_cancel_of_le hep,
      tsub_add_cancel_of_le hp', tsub_add_cancel_of_le he'] <;>
    rw [ENNReal.ofReal_mul he.1, tsub_add_cancel_of_le hep,
      add_comm, tsub_add_cancel_of_le he']

/-- The lower-cap Bernoulli law belongs to the one-sided propensity mixture
class.  For the specified model objects, [the stated conditions](hyp:hPos,hp), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryLaw_lowerCap_mem_mixtureOneSided
lemma binaryLaw_lowerCap_mem_mixtureOneSided (e p : ℝ)
    (hPos : StrictPositivity e) (hp : p ∈ Set.Icc 0 1) :
    binaryLaw (e * p) ∈ mixtureClassOneSidedSet e (binaryLaw p) := by
  have hep : e * p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hPos.1.le hp.1,
      calc
        e * p ≤ 1 * p := mul_le_mul_of_nonneg_right hPos.2.le hp.1
        _ ≤ 1 := by simpa using hp.2⟩
  let _ : IsProbabilityMeasure (binaryLaw p) := binaryLaw_isProbabilityMeasure p hp
  let hQ : IsProbabilityMeasure (binaryLaw (e * p)) :=
    binaryLaw_isProbabilityMeasure (e * p) hep
  let hR : IsProbabilityMeasure (binaryLaw 0) :=
    binaryLaw_isProbabilityMeasure 0 (by simp)
  exact
    { positivity := Or.inr hPos
      observed_probability := inferInstance
      candidate_probability := hQ
      representation := fun _ => ⟨binaryLaw 0, hR,
        binaryLaw_lowerCap_mixture e p ⟨hPos.1.le, hPos.2.le⟩ hp⟩
      boundary := fun he => (ne_of_lt hPos.2 he).elim }

end CausalSmith.SCM.PropensityLvSharpnessFrontier
