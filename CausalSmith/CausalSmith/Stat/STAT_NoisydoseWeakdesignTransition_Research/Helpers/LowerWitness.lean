module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.Packet
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ScheduleMeasurability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Order.Interval.Set.ProjIcc

/-! Helpers — LowerWitness -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Common fixed-envelope weak design, including the constant-density kappa=0 case. -/
def witnessDesignDensity (kappa t : ℝ) : ℝ :=
  if t ∈ Icc (-1/2 : ℝ) (1/2) then (kappa+1)*(2 : ℝ)^kappa*|t|^kappa else 0
/-- The symmetric power integral used to normalize the common latent design. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witness_abs_power_integral
lemma witness_abs_power_integral (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    (∫ t in (-1/2 : ℝ)..(1/2), |t| ^ kappa) =
      2 * (1/2 : ℝ) ^ (kappa+1) / (kappa+1) := by
  have hc : Continuous (fun t : ℝ => |t| ^ kappa) := by
    first | fun_prop | exact continuous_abs.rpow_const (fun _ => Or.inr hkappa)
  have hhalf : (∫ t in (0 : ℝ)..(1/2), |t| ^ kappa) =
      (1/2 : ℝ) ^ (kappa+1) / (kappa+1) := by
    calc
      _ = ∫ t in (0 : ℝ)..(1/2), t ^ kappa := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at ht
        simp only [abs_of_nonneg ht.1]
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < kappa))]
        rw [Real.zero_rpow (by linarith : kappa+1 ≠ 0), sub_zero]
  have hleft : (∫ t in (-1/2 : ℝ)..0, |t| ^ kappa) =
      ∫ t in (0 : ℝ)..(1/2), |t| ^ kappa := by
    have h := intervalIntegral.integral_comp_neg (fun t : ℝ => |t| ^ kappa)
      (a := (-1/2 : ℝ)) (b := 0)
    norm_num only [abs_neg, neg_zero, neg_div, neg_neg] at h
    simpa only [neg_div] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1/2) 0) (hc.intervalIntegrable 0 (1/2)), hleft, hhalf]
  ring

/-- Lebesgue measure on the compact dose subtype. -/
def doseVolume : Measure Dose := volume.comap Subtype.val
/-- The common design integrates to one on the public dose subtype. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witnessDesignDensity_integral
lemma witnessDesignDensity_integral (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    (∫ a : Dose, witnessDesignDensity kappa ((a : ℝ)-a0) ∂doseVolume) = 1 := by
  rw [doseVolume, integral_subtype_comap (s := Icc (0 : ℝ) 1)
    measurableSet_Icc (fun a : ℝ => witnessDesignDensity kappa (a-a0))]
  have heq : (∫ a in Icc (0 : ℝ) 1, witnessDesignDensity kappa (a-a0)) =
      ∫ a in Icc (0 : ℝ) 1, (kappa+1)*2^kappa*|a-a0|^kappa := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro a ha
    simp only [witnessDesignDensity, if_pos (show a-a0 ∈ Icc (-1/2 : ℝ) (1/2) by
      dsimp [a0]; constructor <;> linarith [ha.1, ha.2])]
  rw [heq, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => |t|^kappa) a0]
  norm_num only [a0, zero_sub, ← neg_div, show (1 : ℝ)-1/2 = 1/2 by norm_num]
  have hsym := witness_abs_power_integral kappa hkappa
  simp only [neg_div] at hsym
  rw [hsym, Real.rpow_add (by norm_num : (0 : ℝ) < 1/2), Real.rpow_one]
  have hpow : (2 : ℝ)^kappa * (1/2 : ℝ)^kappa = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1/2)]
    norm_num
  have hden : kappa+1 ≠ 0 := by linarith
  field_simp
  nlinarith [hpow]

/-- The compact-dose density is integrable, including the constant-power case. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witnessDesignDensity_integrable
lemma witnessDesignDensity_integrable (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    Integrable (fun a : Dose => witnessDesignDensity kappa ((a : ℝ)-a0)) doseVolume := by
  apply (integrableOn_iff_comap_subtypeVal (s := Icc (0 : ℝ) 1)
    (f := fun a : ℝ => witnessDesignDensity kappa (a-a0)) (μ := volume) measurableSet_Icc).mp
  have hc : Continuous (fun a : ℝ => (kappa+1)*2^kappa*|a-a0|^kappa) := by
    fun_prop
  apply hc.integrableOn_Icc.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
  simp only [witnessDesignDensity, if_pos (show a-a0 ∈ Icc (-1/2 : ℝ) (1/2) by
    dsimp [a0]; constructor <;> linarith [ha.1, ha.2])]

/-- Uniform Lebesgue mass on the unit dose and rank subtype is one. [This is the stated conclusion](goal). -/
-- @node: doseVolume_probability
lemma doseVolume_probability : IsProbabilityMeasure doseVolume := by
  constructor
  rw [doseVolume, comap_subtype_coe_apply measurableSet_Icc,
    Subtype.coe_image_univ, Real.volume_Icc]
  norm_num

/-- The power-weighted compact dose law is a probability measure. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witnessDose_probability
lemma witnessDose_probability (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    IsProbabilityMeasure (doseVolume.withDensity
      (fun a : Dose => ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (witnessDesignDensity_integrable kappa hkappa)]
  · rw [witnessDesignDensity_integral kappa hkappa, ENNReal.ofReal_one]
  · apply Filter.Eventually.of_forall
    intro a
    dsimp only [witnessDesignDensity, Pi.zero_apply]
    split_ifs
    · exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (abs_nonneg _) _)
    · exact le_rfl

/-- Independent stratum, latent dose, error and rank seed. -/
def lowerSeedLaw (kappa : ℝ) : Measure (Bool × Dose × ℝ × Dose) :=
  (((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) : Measure Bool).prod
    ((doseVolume.withDensity (fun a => ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))).prod
      ((gaussianReal 0 1).prod doseVolume))
/-- Structural threshold outcomes are built in the fixed public schedule space from a continuous profile. -/
def lowerWitnessLaw (E : PathSpace S) (kappa : ℝ) (mu : ThresholdProfile) : Measure (StructSpace S) :=
  (lowerSeedLaw kappa).map (fun p =>
    (p.1, (p.2.1 : ℝ), p.2.2.1, E.embed (mu,p.2.2.2),
      E.eval (E.embed (mu,p.2.2.2)) p.2.1, (p.2.2.2 : ℝ)))
/-- The threshold construction is measurable in the independent product seeds. [This is the stated conclusion](goal). -/
-- @node: lowerWitness_seedMap_measurable
@[fun_prop] lemma lowerWitness_seedMap_measurable (E : PathSpace S) (mu : ThresholdProfile) :
    Measurable (fun p : Bool × Dose × ℝ × Dose =>
      (p.1, (p.2.1 : ℝ), p.2.2.1, E.embed (mu,p.2.2.2),
        E.eval (E.embed (mu,p.2.2.2)) p.2.1, (p.2.2.2 : ℝ))) := by
  have he : Measurable (fun p : Bool × Dose × ℝ × Dose => E.embed (mu, p.2.2.2)) := by
    first | fun_prop | exact E.measurable_embed.comp (by fun_prop)
  have hy : Measurable (fun p : Bool × Dose × ℝ × Dose =>
      E.eval (E.embed (mu,p.2.2.2)) p.2.1) := by
    first | fun_prop | exact E.measurable_eval.comp (he.prodMk (by fun_prop))
  fun_prop

/-- The reference threshold profile has constant success probability one half. -/
def referenceProfile : ThresholdProfile :=
  ContinuousMap.const Dose (Set.projIcc (0 : ℝ) 1 zero_le_one (1/2))
/-- The independent stratum, dose, Gaussian and rank seed has total mass one. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerSeedLaw_probability
lemma lowerSeedLaw_probability (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    IsProbabilityMeasure (lowerSeedLaw kappa) := by
  letI : IsProbabilityMeasure doseVolume := doseVolume_probability
  letI : IsProbabilityMeasure (doseVolume.withDensity
      (fun a : Dose => ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))) :=
    witnessDose_probability kappa hkappa
  letI : IsProbabilityMeasure
      (((1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true) : Measure Bool) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    simpa only [one_div] using ENNReal.inv_two_add_inv_two
  unfold lowerSeedLaw
  infer_instance

/-- [For a path-space design](hyp:E), [an admissible overlap parameter](hyp:hkappa), and [a threshold profile](hyp:mu), [the lower-witness law is a probability measure](goal). -/
-- @node: lowerWitnessLaw_probability
lemma lowerWitnessLaw_probability (E : PathSpace S) (kappa : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (mu : ThresholdProfile) : IsProbabilityMeasure (lowerWitnessLaw E kappa mu) := by
  letI := lowerSeedLaw_probability kappa hkappa.1
  exact Measure.isProbabilityMeasure_map (lowerWitness_seedMap_measurable E mu).aemeasurable
/-- A threshold witness packaged as a probability law, with normalization proved locally. -/
def lowerWitness (E : PathSpace S) (kappa : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (mu : ThresholdProfile) : ProbabilityMeasure (StructSpace S) :=
  ⟨lowerWitnessLaw E kappa mu, lowerWitnessLaw_probability E kappa hkappa mu⟩
/-- Every threshold witness keeps its latent dose in the public compact interval. [This is the stated conclusion](goal). -/
-- @node: lowerWitness_latentSupport
lemma lowerWitness_latentSupport (E : PathSpace S) (kappa : ℝ) (mu : ThresholdProfile) :
    LatentSupport (lowerWitnessLaw E kappa mu) := by
  unfold LatentSupport lowerWitnessLaw
  rw [ae_map_iff (lowerWitness_seedMap_measurable E mu).aemeasurable
    (measurableSet_Icc.preimage (by fun_prop))]
  exact Filter.Eventually.of_forall fun p => p.2.1.property

/-- Threshold embedding gives binary potential outcomes at every fixed public dose. [This is the stated conclusion](goal). -/
-- @node: lowerWitness_binaryPotentialOutcomes
lemma lowerWitness_binaryPotentialOutcomes (E : PathSpace S) (kappa : ℝ)
    (mu : ThresholdProfile) : BinaryPotentialOutcomes E (lowerWitnessLaw E kappa mu) := by
  intro a ha
  have hm : Measurable (fun w : StructSpace S => potentialOutcome E w a) := by
    first
    | fun_prop
    | exact E.measurable_eval.comp
        ((show Measurable (sSched (S := S)) by fun_prop).prodMk
          (measurable_const (a := (⟨a, ha⟩ : Dose))))
  unfold lowerWitnessLaw
  apply (ae_map_iff (lowerWitness_seedMap_measurable E mu).aemeasurable
    ((measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ)))).union
      (measurableSet_eq_fun hm (measurable_const (a := (1 : ℝ)))))).mpr
  apply Filter.Eventually.of_forall
  intro p
  change E.eval (E.embed (mu, p.2.2.2)) a = 0 ∨
    E.eval (E.embed (mu, p.2.2.2)) a = 1
  rw [show a = ((⟨a, ha⟩ : Dose) : ℝ) from rfl, E.eval_embed]
  split_ifs <;> simp

/-- Binary threshold outcomes are bounded in the full model's outcome interval. [This is the stated conclusion](goal). -/
-- @node: lowerWitness_boundedPotentialOutcomes
lemma lowerWitness_boundedPotentialOutcomes (E : PathSpace S) (kappa : ℝ)
    (mu : ThresholdProfile) : BoundedPotentialOutcomes E (lowerWitnessLaw E kappa mu) := by
  intro a ha
  filter_upwards [lowerWitness_binaryPotentialOutcomes E kappa mu a ha] with w hw
  rcases hw with hw | hw <;> rw [hw] <;> norm_num

/-- The observed outcome is the embedded schedule evaluated at the realized dose. [This is the stated conclusion](goal). -/
-- @node: lowerWitness_doseConsistency
lemma lowerWitness_doseConsistency (E : PathSpace S) (kappa : ℝ)
    (mu : ThresholdProfile) : DoseConsistency E (lowerWitnessLaw E kappa mu) := by
  have hm : Measurable (fun w : StructSpace S =>
      E.eval (sSched w) (Set.projIcc 0 1 zero_le_one (sA w))) := by
    first
    | fun_prop
    | exact E.measurable_eval.comp
        ((show Measurable (sSched (S := S)) by fun_prop).prodMk
          ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp (by fun_prop)))
  have heq : ∀ᵐ w ∂lowerWitnessLaw E kappa mu,
      sY w = E.eval (sSched w) (Set.projIcc 0 1 zero_le_one (sA w)) := by
    unfold lowerWitnessLaw
    rw [ae_map_iff (lowerWitness_seedMap_measurable E mu).aemeasurable
      (measurableSet_eq_fun (by fun_prop) hm)]
    apply Filter.Eventually.of_forall
    intro p
    simp only [sY, sSched, sA, Set.projIcc_of_mem zero_le_one p.2.1.property]
  filter_upwards [heq, lowerWitness_latentSupport E kappa mu] with w hw ha
  simpa only [Set.projIcc_of_mem zero_le_one ha, potentialOutcome] using hw

/-- The witness factors every stratum/dose rectangle from the schedule and rank seed. [Under the stated conditions](hyp:hkappa,hB,hD). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_rectangle
lemma lowerWitness_rectangle (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) (x : Bool) (B : Set (S × ℝ)) (D : Set ℝ)
    (hB : MeasurableSet B) (hD : MeasurableSet D) :
    (lowerWitnessLaw E kappa mu) {w | (sSched w, sU w) ∈ B ∧ sA w ∈ D ∧ sX w = x} =
      (1/2 : ℝ≥0∞) *
        (doseVolume.withDensity (fun a : Dose =>
          ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0))))
          (Subtype.val ⁻¹' D) *
        doseVolume ((fun u : Dose => (E.embed (mu, u), (u : ℝ))) ⁻¹' B) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  have hset : MeasurableSet {w : StructSpace S |
      (sSched w, sU w) ∈ B ∧ sA w ∈ D ∧ sX w = x} := by
    exact (hB.preimage (by fun_prop)).inter
      ((hD.preimage (by fun_prop)).inter
        (measurableSet_eq_fun (by fun_prop) measurable_const))
  unfold lowerWitnessLaw
  rw [Measure.map_apply (lowerWitness_seedMap_measurable E mu) hset]
  have heq : (fun p : Bool × Dose × ℝ × Dose =>
      (p.1, (p.2.1 : ℝ), p.2.2.1, E.embed (mu,p.2.2.2),
        E.eval (E.embed (mu,p.2.2.2)) p.2.1, (p.2.2.2 : ℝ))) ⁻¹'
      {w | (sSched w, sU w) ∈ B ∧ sA w ∈ D ∧ sX w = x} =
        {x} ×ˢ ((Subtype.val ⁻¹' D) ×ˢ
          ((univ : Set ℝ) ×ˢ ((fun u : Dose => (E.embed (mu, u), (u : ℝ))) ⁻¹' B))) := by
    ext p
    simp only [mem_preimage, mem_setOf_eq, sSched, sU, sA, sX, mem_prod,
      mem_singleton_iff, mem_univ, true_and]
    tauto
  rw [heq, lowerSeedLaw, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp only [measure_univ, one_mul]
  have hx : (((1/2 : ℝ≥0∞) • Measure.dirac false +
      (1/2 : ℝ≥0∞) • Measure.dirac true) : Measure Bool) {x} = 1/2 := by
    cases x <;> simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply', smul_eq_mul]
  rw [hx]
  ring

/-- Both strata of every witness have probability one half. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_stratum_mass
lemma lowerWitness_stratum_mass (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) (x : Bool) :
    (lowerWitnessLaw E kappa mu) {w | sX w = x} = 1/2 := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  simpa using lowerWitness_rectangle E kappa hkappa mu x univ univ
    MeasurableSet.univ MeasurableSet.univ

/-- [For a nonnegative design exponent](hyp:hkappa), [the witness's two strata each have mass one half](goal). -/
lemma lowerWitness_strataProb (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) (x : Bool) : strataProb (lowerWitnessLaw E kappa mu) x = 1/2 := by
  rw [strataProb, measureReal_def, lowerWitness_stratum_mass E kappa hkappa mu x]
  norm_num

/-- [For a nonnegative design exponent](hyp:hkappa), [the common half-mass strata satisfy the public overlap interval](goal) for [any minimum stratum mass](hyp:pmin) [at most one half](hyp:hpmin). -/
-- @node: lowerWitness_stratumOverlap
lemma lowerWitness_stratumOverlap (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) (pmin : ℝ) (hpmin : pmin ≤ 1/2) :
    StratumOverlap pmin (lowerWitnessLaw E kappa mu) := by
  intro x
  rw [lowerWitness_strataProb E kappa hkappa mu x]
  constructor <;> linarith

/-- [For a nonnegative design exponent](hyp:hkappa), [both witness strata have positive mass](goal). -/
lemma lowerWitness_stratumPositive (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) : StratumPositive (lowerWitnessLaw E kappa mu) := by
  intro x
  rw [lowerWitness_strataProb E kappa hkappa mu x]
  norm_num

/-- Whole-schedule exchangeability follows from the independent rank and dose seeds. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_scheduleUnconfoundedness
lemma lowerWitness_scheduleUnconfoundedness (E : PathSpace S) (kappa : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) :
    ScheduleUnconfoundedness (lowerWitnessLaw E kappa mu) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  intro x B D hB hD
  have hjoint := lowerWitness_rectangle E kappa hkappa mu x (B ×ˢ univ) D
    (hB.prod MeasurableSet.univ) hD
  have hsched := lowerWitness_rectangle E kappa hkappa mu x (B ×ˢ univ) univ
    (hB.prod MeasurableSet.univ) MeasurableSet.univ
  have hdose := lowerWitness_rectangle E kappa hkappa mu x univ D MeasurableSet.univ hD
  simp only [mem_prod, mem_univ, and_true, preimage_univ, measure_univ, mul_one] at hjoint hsched hdose
  simp only [true_and] at hsched hdose
  unfold strataProb
  simp only [measureReal_def, hjoint, hsched, hdose,
    lowerWitness_stratum_mass E kappa hkappa mu x, ENNReal.toReal_mul]
  ring

/-- The auxiliary rank and latent dose factor within every public stratum. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_rankTreatmentIndependence
lemma lowerWitness_rankTreatmentIndependence (E : PathSpace S) (kappa : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) :
    RankTreatmentIndependence (lowerWitnessLaw E kappa mu) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  intro x B D hB hD
  have hjoint := lowerWitness_rectangle E kappa hkappa mu x (univ ×ˢ B) D
    (MeasurableSet.univ.prod hB) hD
  have hrank := lowerWitness_rectangle E kappa hkappa mu x (univ ×ˢ B) univ
    (MeasurableSet.univ.prod hB) MeasurableSet.univ
  have hdose := lowerWitness_rectangle E kappa hkappa mu x univ D MeasurableSet.univ hD
  simp only [mem_prod, mem_univ, true_and, preimage_univ, measure_univ, mul_one] at hjoint hrank hdose
  unfold strataProb
  simp only [measureReal_def, hjoint, hrank, hdose,
    lowerWitness_stratum_mass E kappa hkappa mu x, ENNReal.toReal_mul]
  ring

/-- The real-valued rank marginal is exactly uniform on the public unit interval. [This is the stated conclusion](goal). -/
-- @node: doseVolume_map_coe
lemma doseVolume_map_coe : doseVolume.map (Subtype.val : Dose → ℝ) =
    volume.restrict (Icc (0 : ℝ) 1) := by
  rw [doseVolume, map_comap_subtype_coe measurableSet_Icc]

/-- Normalizing a half-mass stratum leaves the independent uniform rank law. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_rankUniform
lemma lowerWitness_rankUniform (E : PathSpace S) (kappa : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) :
    RankUniform (lowerWitnessLaw E kappa mu) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  intro x
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB, stratumLaw, Measure.smul_apply,
    Measure.restrict_apply (hB.preimage (by fun_prop)),
    lowerWitness_stratum_mass E kappa hkappa mu x]
  have heq : (sU (S := S) ⁻¹' B) ∩ {w | sX w = x} =
      {w | sU w ∈ B ∧ sX w = x} := rfl
  rw [heq]
  have hrank := lowerWitness_rectangle E kappa hkappa mu x (univ ×ˢ B) univ
    (MeasurableSet.univ.prod hB) MeasurableSet.univ
  simp only [mem_prod, mem_univ, true_and, and_true, preimage_univ, measure_univ, mul_one] at hrank
  have hpre : ((fun u : Dose => (E.embed (mu, u), (u : ℝ))) ⁻¹' (univ ×ˢ B)) =
      (Subtype.val : Dose → ℝ) ⁻¹' B := by
    ext u
    simp
  rw [hrank, hpre]
  rw [smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [← doseVolume_map_coe, Measure.map_apply (by fun_prop) hB]

/-- The probability of a lower-rank threshold is its level on the unit interval. [This is the stated conclusion](goal). -/
-- @node: doseVolume_Iic
lemma doseVolume_Iic (p : Dose) :
    doseVolume {u : Dose | (u : ℝ) ≤ (p : ℝ)} = ENNReal.ofReal (p : ℝ) := by
  change doseVolume ((Subtype.val : Dose → ℝ) ⁻¹' Iic (p : ℝ)) = _
  rw [← Measure.map_apply (by fun_prop) measurableSet_Iic, doseVolume_map_coe,
    Measure.restrict_apply measurableSet_Iic]
  have heq : Iic (p : ℝ) ∩ Icc (0 : ℝ) 1 = Icc 0 (p : ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hp, h0, h1⟩; exact ⟨h0, hp⟩
    · rintro ⟨h0, hp⟩; exact ⟨hp, h0, hp.trans p.property.2⟩
  rw [heq, Real.volume_Icc, sub_zero]

/-- At each fixed dose, the witness evaluates the chosen profile against its auxiliary rank. [This is the stated conclusion](goal). -/
-- @node: lowerWitness_fixed_threshold
lemma lowerWitness_fixed_threshold (E : PathSpace S) (kappa : ℝ) (mu : ThresholdProfile)
    (a : Dose) : ∀ᵐ w ∂lowerWitnessLaw E kappa mu,
      potentialOutcome E w a = if sU w ≤ (mu a : ℝ) then 1 else 0 := by
  have hm : Measurable (fun w : StructSpace S => potentialOutcome E w a) := by
    first
    | fun_prop
    | exact E.measurable_eval.comp
        ((show Measurable (sSched (S := S)) by fun_prop).prodMk measurable_const)
  have ht : Measurable (fun w : StructSpace S =>
      if sU w ≤ (mu a : ℝ) then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      measurable_const measurable_const
  unfold lowerWitnessLaw
  apply (ae_map_iff (lowerWitness_seedMap_measurable E mu).aemeasurable
    (measurableSet_eq_fun hm ht)).mpr
  exact Filter.Eventually.of_forall fun p => E.eval_embed mu p.2.2.2 a

/-- Integrating the independent uniform rank recovers exactly the prescribed conditional mean. [Under the stated conditions](hyp:hkappa,ha). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_condPotMean
lemma lowerWitness_condPotMean (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) (x : Bool) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    condPotMean E (lowerWitnessLaw E kappa mu) x a =
      (mu (Set.projIcc 0 1 zero_le_one a) : ℝ) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  let p : Dose := mu ⟨a, ha⟩
  have hset : MeasurableSet {w : StructSpace S | sU w ≤ (p : ℝ) ∧ sX w = x} := by
    exact (measurableSet_le (show Measurable (sU (S := S)) by fun_prop)
      (measurable_const (a := (p : ℝ)))).inter
      (measurableSet_eq_fun (show Measurable (sX (S := S)) by fun_prop)
        (measurable_const (a := x)))
  have hnum : (∫ w, (if sX w = x then potentialOutcome E w a else 0)
      ∂lowerWitnessLaw E kappa mu) =
      (lowerWitnessLaw E kappa mu).real {w | sU w ≤ (p : ℝ) ∧ sX w = x} := by
    calc
      _ = ∫ w, ({w : StructSpace S | sU w ≤ (p : ℝ) ∧ sX w = x}.indicator
          (fun _ => (1 : ℝ))) w ∂lowerWitnessLaw E kappa mu := by
        apply integral_congr_ae
        filter_upwards [lowerWitness_fixed_threshold E kappa mu ⟨a, ha⟩] with w hw
        rw [hw]
        simp only [indicator_apply, mem_setOf_eq, p]
        split_ifs <;> simp_all
      _ = _ := integral_indicator_one hset
  have hrank := lowerWitness_rectangle E kappa hkappa mu x (univ ×ˢ Iic (p : ℝ)) univ
    (MeasurableSet.univ.prod measurableSet_Iic) MeasurableSet.univ
  have hpre : ((fun u : Dose => (E.embed (mu, u), (u : ℝ))) ⁻¹' (univ ×ˢ Iic (p : ℝ))) =
      {u : Dose | (u : ℝ) ≤ (p : ℝ)} := by
    ext u
    simp
  simp only [mem_prod, mem_univ, mem_Iic, true_and, and_true,
    preimage_univ, measure_univ, mul_one] at hrank
  rw [hpre, doseVolume_Iic] at hrank
  rw [condPotMean, hnum, strataProb, measureReal_def, measureReal_def, hrank,
    lowerWitness_stratum_mass E kappa hkappa mu x, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal p.property.1]
  norm_num [p, Set.projIcc_of_mem zero_le_one ha]

/-- The measurement-error marginal is the independent standard Gaussian seed. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_gaussianChannel
lemma lowerWitness_gaussianChannel (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) : GaussianChannel (lowerWitnessLaw E kappa mu) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  unfold GaussianChannel lowerWitnessLaw
  rw [Measure.map_map (by fun_prop) (lowerWitness_seedMap_measurable E mu)]
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB]
  have heq : (sZ ∘ (fun p : Bool × Dose × ℝ × Dose =>
      (p.1, (p.2.1 : ℝ), p.2.2.1, E.embed (mu,p.2.2.2),
        E.eval (E.embed (mu,p.2.2.2)) p.2.1, (p.2.2.2 : ℝ)))) ⁻¹' B =
      (univ : Set Bool) ×ˢ ((univ : Set Dose) ×ˢ (B ×ˢ (univ : Set Dose))) := by
    ext p
    simp [Function.comp_def, sZ]
  rw [heq, lowerSeedLaw, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp [measure_univ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_two_add_inv_two, one_div]

/-- The Gaussian seed factors from every measurable joint stratum/dose/schedule event. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_errorIndependence
lemma lowerWitness_errorIndependence (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) : ErrorIndependence (lowerWitnessLaw E kappa mu) := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  let seed := fun p : Bool × Dose × ℝ × Dose =>
    (p.1, (p.2.1 : ℝ), p.2.2.1, E.embed (mu,p.2.2.2),
      E.eval (E.embed (mu,p.2.2.2)) p.2.1, (p.2.2.2 : ℝ))
  have hs : Measurable seed := lowerWitness_seedMap_measurable E mu
  have he : Measurable (fun p : Bool × Dose × ℝ × Dose =>
      (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2))) := by
    have hm : Measurable (fun p : Bool × Dose × ℝ × Dose => E.embed (mu,p.2.2.2)) := by
      exact E.measurable_embed.comp (by fun_prop)
    fun_prop
  have hfactor (B : Set ℝ) (D : Set (Bool × ℝ × S))
      (hB : MeasurableSet B) (hD : MeasurableSet D) :
      lowerSeedLaw kappa {p | p.2.2.1 ∈ B ∧ (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D} =
        gaussianReal 0 1 B * lowerSeedLaw kappa
          {p | (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D} := by
    have hj : MeasurableSet {p : Bool × Dose × ℝ × Dose |
        p.2.2.1 ∈ B ∧ (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D} :=
      (hB.preimage (by fun_prop)).inter (hD.preimage he)
    have hd : MeasurableSet {p : Bool × Dose × ℝ × Dose |
        (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D} := hD.preimage he
    unfold lowerSeedLaw
    rw [Measure.prod_apply hj, Measure.prod_apply hd]
    rw [← lintegral_const_mul' _ _ (measure_ne_top _ _)]
    apply lintegral_congr
    intro x
    rw [Measure.prod_apply (hj.preimage (measurable_prodMk_left)),
      Measure.prod_apply (hd.preimage (measurable_prodMk_left))]
    rw [← lintegral_const_mul' _ _ (measure_ne_top _ _)]
    apply lintegral_congr
    intro a
    have hpre : Prod.mk a ⁻¹' Prod.mk x ⁻¹'
        {p : Bool × Dose × ℝ × Dose | (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D} =
        (univ : Set ℝ) ×ˢ {u : Dose | (x, (a : ℝ), E.embed (mu,u)) ∈ D} := by
      ext p
      simp
    rw [hpre]
    change ((gaussianReal 0 1).prod doseVolume)
        (B ×ˢ {u : Dose | (x, (a : ℝ), E.embed (mu,u)) ∈ D}) =
      gaussianReal 0 1 B * ((gaussianReal 0 1).prod doseVolume)
        ((univ : Set ℝ) ×ˢ {u : Dose | (x, (a : ℝ), E.embed (mu,u)) ∈ D})
    rw [Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]
  unfold ErrorIndependence
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro B D hB hD
  have hvec : Measurable (fun w : StructSpace S => (sX w, sA w, sSched w)) := by fun_prop
  rw [lowerWitnessLaw, Measure.map_apply hs ((hB.preimage (by fun_prop)).inter (hD.preimage hvec)),
    Measure.map_apply hs (hB.preimage (by fun_prop)), Measure.map_apply hs (hD.preimage hvec)]
  change lowerSeedLaw kappa {p | p.2.2.1 ∈ B ∧ (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D} =
    lowerSeedLaw kappa {p | p.2.2.1 ∈ B} * lowerSeedLaw kappa
      {p | (p.1, (p.2.1 : ℝ), E.embed (mu,p.2.2.2)) ∈ D}
  have hz : lowerSeedLaw kappa {p | p.2.2.1 ∈ B} = gaussianReal 0 1 B := by
    have hg := lowerWitness_gaussianChannel E kappa hkappa mu
    rw [GaussianChannel, lowerWitnessLaw, Measure.map_map (by fun_prop) hs] at hg
    have hv := congrArg (fun M : Measure ℝ => M B) hg
    rw [Measure.map_apply (by fun_prop) hB] at hv
    exact hv
  rw [hz]
  exact hfactor B D hB hD

/-- [For a nonnegative design exponent](hyp:hkappa), [the witness's conditional means lie in the unit interval](goal), because they are the values of a threshold profile with values in the unit interval. -/
-- @node: lowerWitness_meanRange
lemma lowerWitness_meanRange (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) :
    MeanRange E (lowerWitnessLaw E kappa mu) := by
  intro x a ha
  rw [lowerWitness_condPotMean E kappa hkappa mu x a ha]
  exact (mu _).2

/-- The radius-one Holder bound transfers from the profile to the actual conditional means. [Under the stated conditions](hyp:hkappa,hholder). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_holderMean
lemma lowerWitness_holderMean (E : PathSpace S) (beta kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile)
    (hholder : ∀ a b, |(mu a : ℝ)-(mu b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) :
    HolderMean E beta (lowerWitnessLaw E kappa mu) := by
  intro x a ha b hb
  rw [lowerWitness_condPotMean E kappa hkappa mu x a ha,
    lowerWitness_condPotMean E kappa hkappa mu x b hb]
  simpa only [Set.projIcc_of_mem zero_le_one ha, Set.projIcc_of_mem zero_le_one hb]
    using hholder ⟨a, ha⟩ ⟨b, hb⟩

/-- The power design is a measurable density on the real centered-dose line. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witnessDesignDensity_measurable
@[fun_prop] lemma witnessDesignDensity_measurable (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    Measurable (witnessDesignDensity kappa) := by
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa) := by fun_prop
  exact hc.measurable.ite measurableSet_Icc measurable_const

/-- The normalizing coefficient lies between one and twelve throughout the public exponent range. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa). -/
-- @node: witnessDesignDensity_coefficient
lemma witnessDesignDensity_coefficient (kappa : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    1 ≤ (kappa+1)*2^kappa ∧ (kappa+1)*2^kappa ≤ 12 := by
  have hlo : (1 : ℝ) ≤ 2^kappa := Real.one_le_rpow (by norm_num) hkappa.1
  have hhi : (2 : ℝ)^kappa ≤ 4 := by
    calc
      _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hkappa.2
      _ = 4 := by norm_num
  constructor <;> nlinarith [hkappa.1, hkappa.2]

/-- [The normalized power density meets the envelopes](goal) given by [a lower constant](hyp:clo) [at most its normalizing coefficient](hyp:hlo) and [an upper constant](hyp:chi) [at least that coefficient](hyp:hhi) on its support. -/
-- @node: witnessDesignDensity_envelopes
lemma witnessDesignDensity_envelopes (kappa clo chi : ℝ)
    (hlo : clo ≤ (kappa+1)*(2 : ℝ)^kappa) (hhi : (kappa+1)*(2 : ℝ)^kappa ≤ chi) :
    ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      clo*|t|^kappa ≤ witnessDesignDensity kappa t ∧
      witnessDesignDensity kappa t ≤ chi*|t|^kappa := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [witnessDesignDensity, if_pos ht]
  have hp := Real.rpow_nonneg (abs_nonneg t) kappa
  exact ⟨mul_le_mul_of_nonneg_right hlo hp, mul_le_mul_of_nonneg_right hhi hp⟩

/-- Conditioning on either stratum leaves the common weighted dose seed unchanged. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_conditionalDose
lemma lowerWitness_conditionalDose (E : PathSpace S) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (mu : ThresholdProfile) (x : Bool) :
    (stratumLaw (lowerWitnessLaw E kappa mu) x).map sA =
      (doseVolume.withDensity (fun a : Dose =>
        ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))).map Subtype.val := by
  letI := doseVolume_probability
  letI := witnessDose_probability kappa hkappa
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB, stratumLaw, Measure.smul_apply,
    Measure.restrict_apply (hB.preimage (by fun_prop)),
    lowerWitness_stratum_mass E kappa hkappa mu x]
  have hdose := lowerWitness_rectangle E kappa hkappa mu x univ B MeasurableSet.univ hB
  simp only [mem_univ, true_and, preimage_univ, measure_univ, mul_one] at hdose
  change (1/2 : ℝ≥0∞)⁻¹ • (lowerWitnessLaw E kappa mu)
    {w | sA w ∈ B ∧ sX w = x} = _
  rw [hdose, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul,
    Measure.map_apply (by fun_prop) hB]

/-- Subtracting the public center transports compact-dose volume to centered compact volume. [This is the stated conclusion](goal). -/
-- @node: doseVolume_map_centered
lemma doseVolume_map_centered :
    doseVolume.map (fun a : Dose => (a : ℝ)-a0) =
      volume.restrict (Icc (-1/2 : ℝ) (1/2)) := by
  have hpre : (fun a : ℝ => a-a0) ⁻¹' Icc (-1/2 : ℝ) (1/2) = Icc (0 : ℝ) 1 := by
    ext a
    simp only [mem_preimage, mem_Icc, a0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hm := (measurePreserving_sub_right volume a0).restrict_preimage
    (s := Icc (-1/2 : ℝ) (1/2)) measurableSet_Icc
  rw [hpre] at hm
  have heq := hm.map_eq
  rw [← doseVolume_map_coe, Measure.map_map (by fun_prop) (by fun_prop)] at heq
  exact heq

/-- Weighting and centering the compact dose gives exactly the stipulated power density. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: witnessDose_map_centered
lemma witnessDose_map_centered (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    (doseVolume.withDensity (fun a : Dose =>
      ENNReal.ofReal (witnessDesignDensity kappa ((a : ℝ)-a0)))).map
        (fun a : Dose => (a : ℝ)-a0) =
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))).withDensity
        (fun t => ENNReal.ofReal (witnessDesignDensity kappa t)) := by
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB, withDensity_apply _ (hB.preimage (by fun_prop)),
    withDensity_apply _ hB, ← doseVolume_map_centered,
    setLIntegral_map hB (by fun_prop) (by fun_prop)]

/-- The conditional centered dose has the common density and [satisfies the weak-design envelopes](goal) for [a lower constant](hyp:clo) [at most the power-density coefficient](hyp:hlo) and [an upper constant](hyp:chi) [at least it](hyp:hhi). [Under the stated conditions](hyp:hkappa). -/
-- @node: lowerWitness_weakDesign
lemma lowerWitness_weakDesign (E : PathSpace S) (kappa : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (mu : ThresholdProfile) (clo chi : ℝ)
    (hlo : clo ≤ (kappa+1)*(2 : ℝ)^kappa) (hhi : (kappa+1)*(2 : ℝ)^kappa ≤ chi) :
    WeakDesign clo chi kappa (lowerWitnessLaw E kappa mu) := by
  refine ⟨fun _ => witnessDesignDensity kappa,
    fun _ => witnessDesignDensity_measurable kappa hkappa.1, ?_,
    fun _ => witnessDesignDensity_envelopes kappa clo chi hlo hhi⟩
  intro x
  have hc := congrArg (fun M : Measure ℝ => M.map (fun a => a-a0))
    (lowerWitness_conditionalDose E kappa hkappa.1 mu x)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hc
  exact hc.trans (witnessDose_map_centered kappa hkappa.1)

/-- One full-measure event carries the embedded threshold identity at every public dose. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: lowerWitness_structuralThreshold
lemma lowerWitness_structuralThreshold (E : PathSpace S) (kappa : ℝ)
    (hkappa : 0 ≤ kappa) (mu : ThresholdProfile) :
    StructuralThreshold E (lowerWitnessLaw E kappa mu) := by
  letI := pathSpace_countablySeparated E
  obtain ⟨c, hc, hinj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated S
  have hp : Measurable (fun w : StructSpace S =>
      Set.projIcc 0 1 zero_le_one (sU w)) := by
    fun_prop
  have he : Measurable (fun w : StructSpace S =>
      E.embed (mu, Set.projIcc 0 1 zero_le_one (sU w))) := by
    first | fun_prop | exact E.measurable_embed.comp (measurable_const.prodMk hp)
  have hgraph : ∀ᵐ w ∂lowerWitnessLaw E kappa mu,
      c (sSched w) = c (E.embed (mu, Set.projIcc 0 1 zero_le_one (sU w))) := by
    unfold lowerWitnessLaw
    apply (ae_map_iff (lowerWitness_seedMap_measurable E mu).aemeasurable
      (measurableSet_eq_fun (hc.comp (by fun_prop)) (hc.comp he))).mpr
    apply Filter.Eventually.of_forall
    intro p
    simp only [Function.comp_def, sSched, sU,
      Set.projIcc_of_mem zero_le_one p.2.2.2.property]
  have hrank : ∀ᵐ w ∂lowerWitnessLaw E kappa mu, sU w ∈ Icc (0 : ℝ) 1 := by
    unfold lowerWitnessLaw
    rw [ae_map_iff (lowerWitness_seedMap_measurable E mu).aemeasurable
      (measurableSet_Icc.preimage (by fun_prop))]
    exact Filter.Eventually.of_forall fun p => p.2.2.2.property
  filter_upwards [hgraph, hrank] with w hw hu
  intro a ha
  rw [lowerWitness_condPotMean E kappa hkappa mu (sX w) a ha]
  change E.eval (sSched w) a = _
  rw [hinj hw]
  have h := E.eval_embed mu (Set.projIcc 0 1 zero_le_one (sU w)) ⟨a, ha⟩
  simpa only [Set.projIcc_of_mem zero_le_one hu,
    Set.projIcc_of_mem zero_le_one ha] using h

/-- The assembled witness belongs to the model [for any public class constants](hyp:K) [whose envelope constants bracket the power-density coefficient](hyp:hK) when the constructed profile has the required smoothness. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa,hsigma,hholder). -/
-- @node: lowerWitness_membership
lemma lowerWitness_membership (E : PathSpace S) (K : ClassConstants) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (hK : K.clo ≤ (kappa+1)*(2 : ℝ)^kappa ∧ (kappa+1)*(2 : ℝ)^kappa ≤ K.chi)
    (mu : ThresholdProfile)
    (hholder : ∀ a b, |(mu a : ℝ)-(mu b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) :
    NoisyDoseModelClass E K beta kappa sigma (lowerWitnessLaw E kappa mu) ∧
    BinaryPotentialOutcomes E (lowerWitnessLaw E kappa mu) ∧
    RankUniform (lowerWitnessLaw E kappa mu) ∧
    RankTreatmentIndependence (lowerWitnessLaw E kappa mu) ∧
    StructuralThreshold E (lowerWitnessLaw E kappa mu) ∧
    (∀ x a, a ∈ Icc (0 : ℝ) 1 → condPotMean E (lowerWitnessLaw E kappa mu) x a = (mu (Set.projIcc 0 1 zero_le_one a) : ℝ)) := by
  refine ⟨?_, lowerWitness_binaryPotentialOutcomes E kappa mu,
    lowerWitness_rankUniform E kappa hkappa.1 mu,
    lowerWitness_rankTreatmentIndependence E kappa hkappa.1 mu, ?_,
    lowerWitness_condPotMean E kappa hkappa.1 mu⟩
  · refine
      { stratumOverlap := lowerWitness_stratumOverlap E kappa hkappa.1 mu K.pmin K.pmin_le_half
        latentSupport := lowerWitness_latentSupport E kappa mu
        weakDesign := ?_
        holderMean := lowerWitness_holderMean E beta kappa hkappa.1 mu hholder
        meanRange := lowerWitness_meanRange E kappa hkappa.1 mu
        gaussianChannel := lowerWitness_gaussianChannel E kappa hkappa.1 mu
        errorIndependence := ?_
        scheduleUnconfoundedness := lowerWitness_scheduleUnconfoundedness E kappa hkappa.1 mu
        boundedPO := lowerWitness_boundedPotentialOutcomes E kappa mu
        consistency := lowerWitness_doseConsistency E kappa mu }
    · exact lowerWitness_weakDesign E kappa hkappa mu K.clo K.chi hK.1 hK.2
    · exact lowerWitness_errorIndependence E kappa hkappa.1 mu
  · exact lowerWitness_structuralThreshold E kappa hkappa.1 mu

/-- All threshold profiles use the same stratum and latent-dose design. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa). -/
-- @node: lowerWitness_common_design
lemma lowerWitness_common_design (E : PathSpace S) (kappa : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (mu nu : ThresholdProfile) :
    (lowerWitnessLaw E kappa mu).map (fun w => (sX w, sA w)) =
      (lowerWitnessLaw E kappa nu).map (fun w => (sX w, sA w)) := by
  unfold lowerWitnessLaw
  rw [Measure.map_map (by fun_prop) (lowerWitness_seedMap_measurable E mu),
    Measure.map_map (by fun_prop) (lowerWitness_seedMap_measurable E nu)]
  rfl

end CausalSmith.Stat.NoisydoseWeakdesignTransition
