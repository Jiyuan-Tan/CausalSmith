module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
Coordinate resampling under the finite iid law. Integrating out an original
censor time and drawing a fresh censor time leaves the law of the sample
unchanged. This product-measure fact is the disintegration step for the
predictable censor-compensator identity.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and [censor times following a nonnegative time law](hyp:hCensor), [the
expectation of a nonnegative measurable function of the sample](hyp:hF) [is unchanged when one
subject's censor time is redrawn independently from the censor law](goal), as an extended
nonnegative integral. -/
theorem lintegral_resample_censor {n : ℕ}
    (failureLaw censorLaw : Measure ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hCensor : NonnegativeTimeLaw censorLaw)
    (F : Sample n → ENNReal) (hF : Measurable F) (i : Fin n) :
    (∫⁻ x : Sample n, F x ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n, ∫⁻ c : ℝ,
      F (Function.update x i ((x i).1, c)) ∂censorLaw
      ∂sampleLaw n failureLaw censorLaw := by
  classical
  have : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  have : IsProbabilityMeasure censorLaw := ⟨hCensor.1⟩
  let μ : Fin n → Measure (ℝ × ℝ) := fun _ => failureLaw.prod censorLaw
  let G : Sample n → ENNReal := fun x =>
    ∫⁻ c : ℝ, F (Function.update x i ((x i).1, c)) ∂censorLaw
  have hG : Measurable G := by
    dsimp [G]
    apply Measurable.lintegral_prod_right
    fun_prop
  change (∫⁻ x, F x ∂Measure.pi μ) = ∫⁻ x, G x ∂Measure.pi μ
  apply lintegral_eq_of_lmarginal_eq {i} hF hG
  rw [lmarginal_singleton, lmarginal_singleton]
  funext x
  dsimp [μ, G]
  simp only [Function.update_idem]
  rw [lintegral_prod _ (by fun_prop)]
  rw [lintegral_prod _ (by fun_prop)]
  simp

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and [censor times following a nonnegative time law](hyp:hCensor), for [a
payoff process jointly measurable in time and sample](hyp:hMeasurable), [the expected payoff at
subject i's observed censor event by time u equals the expectation obtained by drawing that
subject's censor time afresh from the censor law, holding the rest of the sample fixed, and
evaluating the payoff at the fresh time in the updated sample](goal), as extended nonnegative
integrals.

The payoff may depend on every subject's observed history. -/
theorem lintegral_censor_event_resample {n : ℕ}
    (failureLaw censorLaw : Measure ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hCensor : NonnegativeTimeLaw censorLaw)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) :
    (∫⁻ x : Sample n,
      ENNReal.ofReal (if (x i).2 ≤ u ∧ (x i).2 < (x i).1
        then H (x i).2 x else 0)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n, ∫⁻ c : ℝ,
      ENNReal.ofReal (if c ≤ u ∧ c < (x i).1
        then H c (Function.update x i ((x i).1, c)) else 0)
        ∂censorLaw ∂sampleLaw n failureLaw censorLaw := by
  classical
  let F : Sample n → ENNReal := fun x =>
    ENNReal.ofReal (if (x i).2 ≤ u ∧ (x i).2 < (x i).1
      then H (x i).2 x else 0)
  have hF : Measurable F := by
    dsimp [F]
    have hCensorCoord : Measurable (fun x : Sample n => (x i).2) := by
      fun_prop
    have hFailureCoord : Measurable (fun x : Sample n => (x i).1) := by
      fun_prop
    have hEvent : MeasurableSet
        {x : Sample n | (x i).2 ≤ u ∧ (x i).2 < (x i).1} := by
      exact (measurableSet_le hCensorCoord measurable_const).inter
        (measurableSet_lt hCensorCoord hFailureCoord)
    have hPair : Measurable (fun x : Sample n => ((x i).2, x)) := by
      fun_prop
    have hPayoff : Measurable (fun x : Sample n => H (x i).2 x) :=
      hMeasurable.comp hPair
    exact ENNReal.measurable_ofReal.comp (hPayoff.ite hEvent measurable_const)
  simpa only [F, Function.update_self, Prod.fst, Prod.snd] using
    lintegral_resample_censor failureLaw censorLaw hFailure hCensor F hF i

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given (absolutely continuous)
censor hazard](hyp:hazard,hHazard), [the event that two different subjects](hyp:hij) [share the same
censor time has probability zero](goal). -/
theorem distinct_censor_times_null {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (i j : Fin n) (hij : i ≠ j) :
    sampleLaw n failureLaw censorLaw
      {x : Sample n | (x i).2 = (x j).2} = 0 := by
  classical
  have hsingle (a : ℝ) : censorLaw {a} = 0 := by
    rw [hHazard.2.2.2.2, withDensity_apply _ (measurableSet_singleton a)]
    simp
  let F : Sample n → ENNReal := fun x =>
    if (x i).2 = (x j).2 then 1 else 0
  have hset : MeasurableSet {x : Sample n | (x i).2 = (x j).2} := by
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hF : Measurable F := by
    exact measurable_const.ite hset measurable_const
  have hmeasure : sampleLaw n failureLaw censorLaw
      {x : Sample n | (x i).2 = (x j).2} =
      ∫⁻ x : Sample n, F x ∂sampleLaw n failureLaw censorLaw := by
    simpa only [F, Set.indicator, Set.mem_ofPred_eq, one_mul] using
      (lintegral_indicator_const hset (1 : ENNReal)).symm
  rw [hmeasure, lintegral_resample_censor failureLaw censorLaw hFailure
    hHazard.1 F hF i]
  simp only [F, Function.update_self, Function.update_of_ne (Ne.symm hij)]
  have hinner (x : Sample n) :
      (∫⁻ c : ℝ, (if c = (x j).2 then (1 : ENNReal) else 0) ∂censorLaw) = 0 := by
    have hs : MeasurableSet ({(x j).2} : Set ℝ) := measurableSet_singleton _
    have h := (lintegral_indicator_const (μ := censorLaw) hs (1 : ENNReal))
    simpa [Set.indicator, hsingle] using h
  simp [hinner]

end Causalean.Stat.RecurrentEvent.CountingProcess
