import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge

/-! # Canonical fixed-stratum bow witnesses -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set
open scoped ENNReal

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: measurable_potentialOutcome
lemma measurable_potentialOutcome {Y : Type*} [MeasurableSpace Y] (a : Bool) :
    Measurable (potentialOutcome (Y := Y) a) := by
  cases a
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: measurable_selectedPotentialOutcome
lemma measurable_selectedPotentialOutcome {Y : Type*} [MeasurableSpace Y] :
    Measurable (fun z : Bool × Y × Y => potentialOutcome (treatment z) z) := by
  simp only [potentialOutcome, treatment]
  exact Measurable.ite ((measurableSet_singleton true).preimage measurable_fst)
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)

/-- The canonical bow law puts the observed arm on the diagonal with law `P`
and the opposite arm on the diagonal with residual law `R`. -/
-- @node: canonicalBowLaw
noncomputable def canonicalBowLaw {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y) : Measure (Bool × Y × Y) :=
  ENNReal.ofReal e • P.map (fun y => (a, y, y)) +
    ENNReal.ofReal (1 - e) • R.map (fun y => (!a, y, y))

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: canonicalBowLaw_isProbabilityMeasure
lemma canonicalBowLaw_isProbabilityMeasure {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IsProbabilityMeasure (canonicalBowLaw a e P R) := by
  rw [isProbabilityMeasure_iff]
  simp only [canonicalBowLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, mul_one, ENNReal.ofReal_sub 1 he0]
  simpa using add_tsub_cancel_of_le (ENNReal.ofReal_le_one.mpr he1)

/-- Canonical latent realization of a propensity mixture. -/
-- @node: canonicalBowWitness
noncomputable def canonicalBowWitness {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : BowWitness Y where
  law := canonicalBowLaw a e P R
  probability := canonicalBowLaw_isProbabilityMeasure a e P R he0 he1
  realizedOutcome := fun z => potentialOutcome (treatment z) z

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: canonicalBowWitness_consistency
lemma canonicalBowWitness_consistency {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    POConsistency (canonicalBowWitness a e P R he0 he1) := by
  filter_upwards [] with z
  rfl

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: canonicalBowWitness_propensity
lemma canonicalBowWitness_propensity {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    armPropensity (canonicalBowWitness a e P R he0 he1) a = e := by
  simp only [armPropensity, canonicalBowWitness, canonicalBowLaw, treatment,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hset : MeasurableSet {z : Bool × Y × Y | z.1 = a} :=
    (measurableSet_singleton a).preimage measurable_fst
  rw [Measure.map_apply (by fun_prop) hset,
    Measure.map_apply (by fun_prop) hset]
  simp [ENNReal.toReal_ofReal he0]

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: canonicalBowWitness_interventionalLaw
lemma canonicalBowWitness_interventionalLaw {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    interventionalLaw (canonicalBowWitness a e P R he0 he1) a =
      ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R := by
  simp only [interventionalLaw, canonicalBowWitness, canonicalBowLaw]
  rw [Measure.map_add _ _ (measurable_potentialOutcome a),
    Measure.map_smul, Measure.map_smul,
    Measure.map_map (measurable_potentialOutcome a) (by fun_prop),
    Measure.map_map (measurable_potentialOutcome a) (by fun_prop)]
  cases a
  · change ENNReal.ofReal e • Measure.map (fun y : Y => y) P +
      ENNReal.ofReal (1 - e) • Measure.map (fun y : Y => y) R = _
    simp
  · change ENNReal.ofReal e • Measure.map (fun y : Y => y) P +
      ENNReal.ofReal (1 - e) • Measure.map (fun y : Y => y) R = _
    simp

/-- For the specified model objects, [the stated conditions](hyp:he,he1), [the stated mathematical relationship holds](goal). -/
-- @node: canonicalBowWitness_armLaw
lemma canonicalBowWitness_armLaw {Y : Type*} [MeasurableSpace Y]
    (a : Bool) (e : ℝ) (P R : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he : 0 < e) (he1 : e ≤ 1) :
    armLaw (canonicalBowWitness a e P R he.le he1) a = P := by
  ext s hs
  have harm : MeasurableSet {z : Bool × Y × Y | treatment z = a} :=
    (measurableSet_singleton a).preimage measurable_fst
  simp only [armLaw]
  rw [show observedOutcome (canonicalBowWitness a e P R he.le he1) =
      (fun z => potentialOutcome (treatment z) z) from rfl]
  rw [Measure.smul_apply,
    Measure.map_apply measurable_selectedPotentialOutcome hs]
  rw [Measure.restrict_apply (hs.preimage measurable_selectedPotentialOutcome)]
  simp only [canonicalBowWitness, canonicalBowLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) harm,
    Measure.map_apply (by fun_prop) harm,
    Measure.map_apply (by fun_prop)
      ((hs.preimage measurable_selectedPotentialOutcome).inter harm),
    Measure.map_apply (by fun_prop)
      ((hs.preimage measurable_selectedPotentialOutcome).inter harm)]
  have hArmSame : (fun y : Y => (a, y, y)) ⁻¹'
      {z : Bool × Y × Y | treatment z = a} = Set.univ := by
    ext y
    simp [treatment]
  have hArmOther : (fun y : Y => (!a, y, y)) ⁻¹'
      {z : Bool × Y × Y | treatment z = a} = ∅ := by
    ext y
    cases a <;> simp [treatment]
  have hObsSame : (fun y : Y => (a, y, y)) ⁻¹'
      (((fun z => potentialOutcome (treatment z) z) ⁻¹' s) ∩
        {z : Bool × Y × Y | treatment z = a}) = s := by
    ext y
    cases a <;> simp [potentialOutcome, treatment]
  have hObsOther : (fun y : Y => (!a, y, y)) ⁻¹'
      (((fun z => potentialOutcome (treatment z) z) ⁻¹' s) ∩
        {z : Bool × Y × Y | treatment z = a}) = ∅ := by
    ext y
    cases a <;> simp [treatment]
  rw [hArmSame, hArmOther, hObsSame, hObsOther]
  simp only [measure_univ, measure_empty, mul_one, mul_zero, add_zero]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr he).ne'
    ENNReal.ofReal_ne_top, one_mul]

/-- The propensity-scaled observed arm law is a submeasure of the
interventional law of every consistent bow witness.  For the specified model objects, [the stated conditions](hyp:hCons,hpos), [the stated mathematical relationship holds](goal).
-/
-- @node: scaled_armLaw_le_interventionalLaw
lemma scaled_armLaw_le_interventionalLaw {Y : Type*} [MeasurableSpace Y]
    (w : BowWitness Y) (a : Bool) (hCons : POConsistency w)
    (hpos : 0 < armPropensity w a) :
    ENNReal.ofReal (armPropensity w a) • armLaw w a ≤ interventionalLaw w a := by
  let E : Set (Bool × Y × Y) := {z | treatment z = a}
  have hE : MeasurableSet E := (measurableSet_singleton a).preimage measurable_fst
  have hmass_top : w.law E ≠ ⊤ := measure_ne_top w.law E
  have hmass_pos : w.law E ≠ 0 := by
    intro hz
    have : armPropensity w a = 0 := by simp [armPropensity, E, hz]
    exact (ne_of_gt hpos) this
  have hcoef : ENNReal.ofReal (armPropensity w a) = w.law E :=
    ENNReal.ofReal_toReal hmass_top
  have hscaled : ENNReal.ofReal (armPropensity w a) • armLaw w a =
      (w.law.restrict E).map (observedOutcome w) := by
    rw [armLaw]
    change ENNReal.ofReal (armPropensity w a) •
      ((w.law E)⁻¹ • (w.law.restrict E).map (observedOutcome w)) = _
    rw [hcoef, smul_smul, ENNReal.mul_inv_cancel hmass_pos hmass_top, one_smul]
  have hae : observedOutcome w =ᵐ[w.law.restrict E] potentialOutcome a := by
    change ∀ᵐ z ∂w.law.restrict E, observedOutcome w z = potentialOutcome a z
    rw [ae_restrict_iff' hE]
    filter_upwards [hCons] with z hz hza
    rw [hz]
    simpa [E, treatment] using congrArg (fun b => potentialOutcome b z) hza
  rw [hscaled, Measure.map_congr hae]
  exact Measure.map_mono Measure.restrict_le_self (measurable_potentialOutcome a)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
