module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic
public import Mathlib.Probability.Independence.Basic

/-!
Distinct subjects have almost surely different censor times under an iid
sample law with an absolutely continuous censor hazard. This removes the
common-jump term in pairwise counting-process calculations.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given (absolutely continuous)
censor hazard](hyp:hazard,hHazard), [two different subjects](hyp:hij) [almost surely have different
censor times](goal). -/
theorem distinct_censor_times_ae {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ x ∂sampleLaw n failureLaw censorLaw, (x i).2 ≠ (x j).2 := by
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  haveI : NullSingletonClass censorLaw := by
    rw [hHazard.2.2.2.2]
    infer_instance
  haveI : IsProbabilityMeasure (failureLaw.prod censorLaw) := inferInstance
  haveI : IsProbabilityMeasure (sampleLaw n failureLaw censorLaw) := by
    unfold sampleLaw
    infer_instance
  have hmap (k : Fin n) :
      (sampleLaw n failureLaw censorLaw).map (fun x => (x k).2) = censorLaw := by
    change (Measure.pi (fun _ : Fin n => failureLaw.prod censorLaw)).map
      (fun x => (x k).2) = censorLaw
    calc
      _ = Measure.map Prod.snd
          (Measure.map (Function.eval k)
            (Measure.pi (fun _ : Fin n => failureLaw.prod censorLaw))) := by
            rw [Measure.map_map measurable_snd (measurable_pi_apply k)]
            rfl
      _ = censorLaw := by
        rw [(measurePreserving_eval
          (fun _ : Fin n => failureLaw.prod censorLaw) k).map_eq,
          Measure.map_snd_prod, measure_univ, one_smul]
  have hind : ProbabilityTheory.IndepFun
      (fun x : Sample n => (x i).2) (fun x : Sample n => (x j).2)
      (sampleLaw n failureLaw censorLaw) := by
    have h := ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => failureLaw.prod censorLaw)
      (X := fun _ => Prod.snd) (fun _ => measurable_snd.aemeasurable)
    exact h.indepFun hij
  have hprod : (∀ᵐ z ∂censorLaw.prod censorLaw, z.1 ≠ z.2) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
    filter_upwards [] with a
    exact (censorLaw.ae_ne a).mono (fun b hb => Ne.symm hb)
  have hpair := hind.map_prod_eq_prod_map_map
    ((measurable_pi_apply i).snd.aemeasurable : AEMeasurable (fun x : Sample n => (x i).2)
      (sampleLaw n failureLaw censorLaw))
    ((measurable_pi_apply j).snd.aemeasurable : AEMeasurable (fun x : Sample n => (x j).2)
      (sampleLaw n failureLaw censorLaw))
  rw [hmap i, hmap j] at hpair
  have hp : MeasurableSet {z : ℝ × ℝ | z.1 ≠ z.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  exact (ae_map_iff (by fun_prop : AEMeasurable
    (fun x : Sample n => ((x i).2, (x j).2)) (sampleLaw n failureLaw censorLaw)) hp).1
    (hpair.symm ▸ hprod)

end Causalean.Stat.RecurrentEvent.CountingProcess
