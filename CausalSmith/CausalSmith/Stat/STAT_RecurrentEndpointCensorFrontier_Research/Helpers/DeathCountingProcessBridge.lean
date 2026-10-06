module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic
public import Causalean.Stat.RecurrentEvent.CountingProcess

/-!
# Death counting-process marginal adapters

The canonical counting-process model treats its second coordinate as the
counted event.  These definitions put the paper's death time in that
coordinate and use arm-specific follow-up as the first coordinate.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

noncomputable def armDeathFailureTime (a : Arm) (z : LatentSubject) : ℝ :=
  if z.treatment = a then censorHorizon z a else 0

@[fun_prop] lemma measurable_armDeathFailureTime (a : Arm) :
    Measurable (armDeathFailureTime a) := by
  unfold armDeathFailureTime
  apply Measurable.ite
  · exact measurableSet_eq_fun
      measurable_latentSubject_treatment measurable_const
  · exact measurable_censorHorizon.comp (measurable_id.prodMk measurable_const)
  · exact measurable_const

lemma armDeathFailureTime_nonneg (a : Arm) (z : LatentSubject) :
    0 ≤ armDeathFailureTime a z := by
  unfold armDeathFailureTime
  split_ifs
  · unfold censorHorizon
    split_ifs
    · norm_num
    · exact le_min ENNReal.toReal_nonneg (by norm_num)
  · norm_num

noncomputable def armDeathFailureLaw (P : SubjectLaw) (a : Arm) : Measure ℝ :=
  P.latent.map (armDeathFailureTime a)

noncomputable def armDeathEventLaw (P : SubjectLaw) (a : Arm) : Measure ℝ :=
  P.latent.map (fun z : LatentSubject => z.death a)

lemma armDeathFailureLaw_nonnegativeTimeLaw (P : SubjectLaw) (a : Arm) :
    Causalean.Stat.RecurrentEvent.CountingProcess.NonnegativeTimeLaw
      (armDeathFailureLaw P a) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  constructor
  · rw [armDeathFailureLaw, Measure.map_apply
      (measurable_armDeathFailureTime a) MeasurableSet.univ]
    exact P.prob
  · rw [armDeathFailureLaw, Measure.map_apply
      (measurable_armDeathFailureTime a) measurableSet_Ici]
    exact (mem_ae_iff_prob_eq_one
      (measurableSet_Ici.preimage (measurable_armDeathFailureTime a))).mp
      (Filter.Eventually.of_forall fun z => armDeathFailureTime_nonneg a z)

lemma armDeathEventLaw_nonnegativeTimeLaw (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) :
    Causalean.Stat.RecurrentEvent.CountingProcess.NonnegativeTimeLaw
      (armDeathEventLaw P a) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  constructor
  · rw [armDeathEventLaw, Measure.map_apply
      (measurable_latentSubject_death a) MeasurableSet.univ]
    exact P.prob
  · rw [armDeathEventLaw, Measure.map_apply
      (measurable_latentSubject_death a) measurableSet_Ici]
    have htail : P.latent.real {z : LatentSubject | (0 : ℝ) ≤ z.death a} = 1 := by
      simpa [survival] using hDeath.2.2.2.1 a 0 (by norm_num)
    change (P.latent ((fun z : LatentSubject => z.death a) ⁻¹' Set.Ici 0)).toReal = 1
      at htail
    exact (ENNReal.toReal_eq_one_iff _).mp
      (by simpa [measureReal_def] using htail)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
