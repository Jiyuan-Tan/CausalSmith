module
public import Causalean.Stat.RecurrentEvent.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Measurability of finite stopped histories

The stopped observation of a finite recurrence sample is a measurable
function into an arm, exit, death flag, and countable time sequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]

/-- [A recurrent-event model](hyp:M) has [a measurable finite-horizon
stopped-observation map](goal). -/
theorem Model.measurable_observe (M : Model A X) : Measurable M.observe := by
  have hstop : Measurable M.stopTime := by
    unfold Model.stopTime
    fun_prop
  have hdeath : Measurable (fun ω : Outcome A X =>
      decide (ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon)) := by
    change Measurable (fun ω : Outcome A X =>
      if ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon then true else false)
    apply Measurable.ite
      ((measurableSet_le (show Measurable (fun ω : Outcome A X => ω.2.2.1) by fun_prop)
        (show Measurable (fun ω : Outcome A X => ω.2.2.2) by fun_prop)).inter
        (measurableSet_lt (show Measurable (fun ω : Outcome A X => ω.2.2.1) by fun_prop)
          measurable_const))
    all_goals exact measurable_const
  have hsample (n : ℕ) : Measurable (fun s :
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X =>
      if h : n < s.1 then M.time (s.2 ⟨n, h⟩) else M.horizon + 1) := by
    intro t ht
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet ((fun x : Fin m → X =>
      if h : n < m then M.time (x ⟨n, h⟩) else M.horizon + 1) ⁻¹' t)
    by_cases h : n < m
    · simp only [dif_pos h]
      exact ht.preimage (M.measurable_time.comp (measurable_pi_apply (⟨n, h⟩ : Fin m)))
    · simp only [dif_neg h]
      exact measurable_const ht
  have hcoord (n : ℕ) : Measurable (fun ω : Outcome A X =>
      if h : n < ω.2.1.1 then
        if M.time (ω.2.1.2 ⟨n, h⟩) < M.stopTime ω then
          M.time (ω.2.1.2 ⟨n, h⟩) else M.horizon + 1
      else M.horizon + 1) := by
    let f : Outcome A X → ℝ := fun ω =>
      if h : n < ω.2.1.1 then M.time (ω.2.1.2 ⟨n, h⟩) else M.horizon + 1
    have hf : Measurable f := (hsample n).comp (measurable_fst.comp measurable_snd)
    have hc : Measurable (fun ω : Outcome A X => ω.2.1.1) :=
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_finiteSample_count.comp
        (measurable_fst.comp measurable_snd)
    have heq : (fun ω : Outcome A X =>
      if h : n < ω.2.1.1 then
        if M.time (ω.2.1.2 ⟨n, h⟩) < M.stopTime ω then
          M.time (ω.2.1.2 ⟨n, h⟩) else M.horizon + 1
      else M.horizon + 1) =
        (fun ω => if n < ω.2.1.1 ∧ f ω < M.stopTime ω then f ω else M.horizon + 1) := by
      funext ω
      by_cases h : n < ω.2.1.1 <;> simp [f, h]
    rw [heq]
    exact Measurable.ite ((measurableSet_lt measurable_const hc).inter
      (measurableSet_lt hf hstop)) hf measurable_const
  unfold Model.observe
  exact measurable_fst.prodMk
    (hstop.prodMk (hdeath.prodMk (measurable_pi_lambda _ hcoord)))

/-- [An arm space](hyp:A) determines [the stopped-history counting kernel](goal),
which places one unit of mass at every retained recurrence time and preserves
ties with their multiplicities. -/
noncomputable def historyCountingKernel (A : Type*) [MeasurableSpace A] :
    Kernel (A × (ℝ × (Bool × (ℕ → ℝ)))) ℝ where
  toFun y := Measure.sum (fun n : ℕ =>
    if y.2.2.2 n < y.2.1 then Measure.dirac (y.2.2.2 n) else 0)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) =>
      (Measure.sum (fun n : ℕ =>
        if y.2.2.2 n < y.2.1 then Measure.dirac (y.2.2.2 n) else 0)) s)
    simp_rw [Measure.sum_apply _ hs]
    apply Measurable.tsum
    intro n
    have ht : Measurable (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) => y.2.2.2 n) := by
      fun_prop
    have he : Measurable (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) => y.2.1) := by
      fun_prop
    have hd : Measurable (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) =>
        (Measure.dirac (y.2.2.2 n)) s) := by
      simpa [Measure.dirac_apply, Set.indicator] using
        (Measurable.ite (hs.preimage ht)
          (measurable_const : Measurable (fun _ : A × (ℝ × (Bool × (ℕ → ℝ))) =>
            (1 : ℝ≥0∞))) measurable_const)
    have heq : (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) =>
        (if y.2.2.2 n < y.2.1 then Measure.dirac (y.2.2.2 n) else 0) s) =
        (fun y => if y.2.2.2 n < y.2.1 then (Measure.dirac (y.2.2.2 n)) s
          else (0 : ℝ≥0∞)) := by
      funext y
      split <;> simp_all
    rw [heq]
    exact Measurable.ite (measurableSet_lt ht he) hd measurable_const

end Causalean.Stat.RecurrentEvent
