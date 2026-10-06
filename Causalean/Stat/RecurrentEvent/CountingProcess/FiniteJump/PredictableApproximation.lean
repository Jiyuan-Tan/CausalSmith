module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Basic

/-!
# Finite-valued approximation of bounded predictable payoffs

This isolates the simple-function approximation needed to pass from finite-range
predictable compensation to bounded predictable compensation. The approximants
remain predictable, obey the original uniform bound, and converge at every
time-sample point.
-/

public section

open MeasureTheory Filter

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A uniformly bounded predictable real payoff admits finite-valued
predictable approximants with the same bound and pointwise convergence. [The
model and payoff](hyp:M,H), [predictability](hyp:hH), and [the nonnegative
common bound](hyp:C,hC,hbound) give [the finite-valued approximation
sequence](goal). -/
theorem Model.bounded_predictable_approximation (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ω, |H t ω| ≤ C) :
    ∃ G : ℕ → ℝ → Ω → ℝ,
      (∀ n, M.Predictable (G n)) ∧
      (∀ n, Set.Finite (Set.range (fun p : ℝ × Ω => G n p.1 p.2))) ∧
      (∀ n t ω, |G n t ω| ≤ C) ∧
      (∀ t ω, Tendsto (fun n => G n t ω) atTop (nhds (H t ω))) := by
  letI : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
  have hsm : StronglyMeasurable[predictableSpace M.filtration]
      (fun p : ℝ × Ω => H p.1 p.2) := hH.stronglyMeasurable
  refine ⟨fun n t ω => hsm.approxBounded C n (t, ω), ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hsm.approxBounded C n).measurable
  · intro n
    exact (hsm.approxBounded C n).finite_range
  · intro n t ω
    simpa only [Real.norm_eq_abs] using hsm.norm_approxBounded_le hC n (t, ω)
  · intro t ω
    apply hsm.tendsto_approxBounded_of_norm_le
    simpa only [Real.norm_eq_abs] using hbound t ω

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
