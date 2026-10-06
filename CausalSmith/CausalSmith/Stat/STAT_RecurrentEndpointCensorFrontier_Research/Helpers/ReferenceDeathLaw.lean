module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathHazardExtension

/-!
# Exponential continuation of the paper's death law

This module splices a shifted rate-one exponential continuation onto the
paper's death-time law after the study horizon.  The splice retains the
original law through time one and preserves total probability mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The rate-one exponential law translated to start at the study horizon. -/
noncomputable def shiftedUnitExpLaw : Measure ℝ :=
  Measure.map (fun x : ℝ => 1 + x) (expMeasure 1)

/-- The original death law through time one, followed by a rate-one exponential tail. -/
noncomputable def referenceDeathLaw (P : SubjectLaw) (a : Arm) : Measure ℝ :=
  (armDeathEventLaw P a).restrict (Set.Iic 1) +
    (armDeathEventLaw P a) (Set.Ioi 1) • shiftedUnitExpLaw

/-- The exponential continuation has total mass one. -/
lemma shiftedUnitExpLaw_apply_univ : shiftedUnitExpLaw Set.univ = 1 := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  rw [shiftedUnitExpLaw, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

/-- The closed upper tail of the shifted continuation is the translated exponential tail. -/
lemma shiftedUnitExpLaw_real_Ici (s : ℝ) (hs : 1 ≤ s) :
    shiftedUnitExpLaw.real (Set.Ici s) = Real.exp (-(s - 1)) := by
  rw [measureReal_def, shiftedUnitExpLaw,
    Measure.map_apply (by fun_prop) measurableSet_Ici]
  change (expMeasure 1).real ((fun x : ℝ => 1 + x) ⁻¹' Set.Ici s) = _
  have hpre : (fun x : ℝ => 1 + x) ⁻¹' Set.Ici s = Set.Ici (s - 1) := by
    ext x
    change (s ≤ 1 + x) ↔ (s - 1 ≤ x)
    constructor <;> intro h <;> linarith
  rw [hpre, expMeasure_real_Ici 1 (by norm_num) (s - 1) (sub_nonneg.mpr hs)]
  ring_nf

/-- The continuation mass is exactly the paper survival probability at time one. -/
lemma armDeathEventLaw_real_Ioi_one {P : SubjectLaw} (hDeath : DeathHazard P)
    (a : Arm) :
    (armDeathEventLaw P a).real (Set.Ioi 1) = survival P a 1 := by
  rw [measureReal_def, armDeathEventLaw, Measure.map_apply
    (measurable_latentSubject_death a) measurableSet_Ioi]
  change P.latent.real {z | 1 < z.death a} = survival P a 1
  exact hDeath.2.2.2.2 a

/-- Splicing the original death law at time one preserves total probability mass. -/
lemma referenceDeathLaw_apply_univ (P : SubjectLaw) (a : Arm) :
    referenceDeathLaw P a Set.univ = 1 := by
  let μ := armDeathEventLaw P a
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, armDeathEventLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  rw [referenceDeathLaw, Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, shiftedUnitExpLaw_apply_univ,
    smul_eq_mul, mul_one]
  change μ (Set.Iic 1) + μ (Set.Ioi 1) = 1
  rw [← measure_union]
  · simp
  · exact Set.Iic_disjoint_Ioi le_rfl
  · exact measurableSet_Ioi

/-- The exponential continuation is a probability measure. -/
instance referenceDeathLaw.isProbabilityMeasure (P : SubjectLaw) (a : Arm) :
    IsProbabilityMeasure (referenceDeathLaw P a) :=
  ⟨referenceDeathLaw_apply_univ P a⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
