module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
Tonelli's identity for integrating a nonnegative time kernel to an independent
random horizon. The horizon contributes its inclusive tail probability.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- For a random horizon drawn from [a nonnegative time law](hyp:hEvaluation) and [a nonnegative
extended-valued measurable function of time](hyp:hf), [the expected integral of the function from
0 to the random horizon equals the integral over nonnegative times s of the function times the
probability that the horizon is at least s](goal). -/
theorem lintegral_random_horizon (evaluationLaw : Measure ℝ)
    (hEvaluation : NonnegativeTimeLaw evaluationLaw)
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ u : ℝ, ∫⁻ s in Set.Icc 0 u, f s ∂volume ∂evaluationLaw) =
    ∫⁻ s : ℝ, f s * evaluationLaw (Set.Ici s)
      ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
  /- Use Tonelli on `(u,s) ↦ 1_{0≤s≤u} f(s)`; the `u` section is
     `evaluationLaw (Ici s)` and the `s` section is the restricted time integral. -/
  classical
  haveI : IsProbabilityMeasure evaluationLaw := ⟨hEvaluation.1⟩
  have hkernel : Measurable (fun p : ℝ × ℝ =>
      (Set.Icc 0 p.1).indicator f p.2) := by
    have hset : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} :=
      (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    simpa only [Set.indicator, Set.mem_Icc, Function.comp_def] using
      (@Measurable.ite (ℝ × ℝ) ENNReal (f ∘ Prod.snd) (fun _ => 0)
        _ _ (fun p => 0 ≤ p.2 ∧ p.2 ≤ p.1) (Classical.decPred _) hset
        (hf.comp measurable_snd) measurable_const)
  calc
    (∫⁻ u : ℝ, ∫⁻ s in Set.Icc 0 u, f s ∂volume ∂evaluationLaw) =
        ∫⁻ u : ℝ, ∫⁻ s : ℝ,
          (Set.Icc 0 u).indicator f s ∂volume ∂evaluationLaw := by
        apply lintegral_congr
        intro u
        exact (lintegral_indicator measurableSet_Icc f).symm
    _ = ∫⁻ s : ℝ, ∫⁻ u : ℝ,
          (Set.Icc 0 u).indicator f s ∂evaluationLaw ∂volume :=
        lintegral_lintegral_swap hkernel.aemeasurable
    _ = ∫⁻ s : ℝ, (Set.Ici (0 : ℝ)).indicator
          (fun s => f s * evaluationLaw (Set.Ici s)) s ∂volume := by
        apply lintegral_congr
        intro s
        by_cases hs : 0 ≤ s
        · have hsection : (fun u : ℝ => (Set.Icc 0 u).indicator f s) =
              (Set.Ici s).indicator (fun _ => f s) := by
            funext u
            simp [Set.indicator, hs, Set.mem_Icc, Set.mem_Ici]
          rw [hsection, lintegral_indicator_const measurableSet_Ici]
          simp [Set.indicator, hs]
        · have hsection : (fun u : ℝ => (Set.Icc 0 u).indicator f s) =
              fun _ => 0 := by
            funext u
            simp [Set.indicator, hs, Set.mem_Icc]
          rw [hsection]
          simp [Set.indicator, hs]
    _ = ∫⁻ s : ℝ, f s * evaluationLaw (Set.Ici s)
          ∂(volume.restrict (Set.Ici (0 : ℝ))) :=
        lintegral_indicator measurableSet_Ici _

end Causalean.Stat.RecurrentEvent.CountingProcess
