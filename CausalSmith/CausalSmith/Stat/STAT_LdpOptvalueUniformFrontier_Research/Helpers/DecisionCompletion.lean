module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.DecisionSampling

/-!
# A measurable completion of the iid decision experiment

Finite atomic sampling weights extend the canonical experiment to all population
measures. On probability laws this extension is exactly the iid experiment.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Fix [the local protocol Q](hyp:Q) and [the probability law P](hyp:P). [Atomic iid weights followed by the fixed protocol and its independent coins](goal). -/
-- @node: completedDecisionLaw
def completedDecisionLaw (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) : Measure (DecisionSpace Q) :=
  Measure.sum fun o : Fin n → ObsRecord d =>
    (∏ i, observedLaw P {o i}) •
      (((Measure.dirac o).prod (Q.seedLaw.prod uniform01)).bind (fun w =>
        (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2))))

/-- For every protocol, the completed finite atomic decision law is [measurable even off the
probability model](goal). -/
-- @node: measurable_completedDecisionLaw
@[fun_prop] lemma measurable_completedDecisionLaw (Q : LocalProtocol n (ObsRecord d)) :
    Measurable (completedDecisionLaw Q) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [completedDecisionLaw, Measure.sum_apply _ hE, Measure.smul_apply,
    smul_eq_mul]
  apply Measurable.tsum
  intro o
  apply Measurable.mul _ measurable_const
  apply Finset.measurable_prod
  intro i hi
  exact (Measure.measurable_coe (measurableSet_singleton (o i))).comp
    (Measure.measurable_map observe (by fun_prop))

/-- [On probability populations, atomic sampling is the canonical iid experiment](goal). -/
-- @node: completedDecisionLaw_eq_canonical
lemma completedDecisionLaw_eq_canonical (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    completedDecisionLaw Q P = decisionLaw (canonicalScheme n d) Q P := by
  haveI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hAtomic : Measure.pi (fun _ : Fin n => observedLaw P) =
      Measure.sum (fun o : Fin n → ObsRecord d =>
        (∏ i, observedLaw P {o i}) • Measure.dirac o) := by
    conv_lhs => rw [← Measure.sum_smul_dirac
      (Measure.pi (fun _ : Fin n => observedLaw P))]
    simp only [Measure.pi_singleton]
  unfold decisionLaw canonicalScheme
  rw [hAtomic, Measure.prod_sum_left,
    Measure.bind_sum _ _ (measurable_protocol_decisionRows Q).aemeasurable]
  simp only [Measure.prod_smul_left, Measure.bind_smul, completedDecisionLaw]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
