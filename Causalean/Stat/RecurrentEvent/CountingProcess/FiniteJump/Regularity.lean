module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.PrefixPredictability
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.PrefixRegularity

/-!
# Measurability and integrability of bounded predictable integrals

Uniform bounds on the integrand and intensity, together with a second moment
for the finite event count, supply the integrability needed in the compensator
and square-expansion arguments.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The square of a predictable integrand remains predictable. [The model and
payoff](hyp:M,H) and [predictability](hyp:hH) give [predictability of the
squared payoff](goal). -/
theorem Model.predictable_quadratic (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H) : M.Predictable (M.quadraticPayoff H) := by
  exact hH.pow_const 2

/-- The strict-past compensated integral is predictable when its integrand
and the at-risk intensity are predictable. -/
theorem Model.predictable_prefix (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H) :
    M.Predictable (M.prefixIntegral H) := by
  exact (M.predictable_strictJumpIntegral H hH).sub
    (M.predictable_energyIntegral H hH)

/-- Twice the current predictable value times its strictly past compensated
integral is predictable. -/
theorem Model.predictable_prefix_payoff (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H) :
    M.Predictable (M.prefixPayoff H) := by
  exact (measurable_const.mul hH).mul (M.predictable_prefix H hH)

/-- The quadratic jump payoff is integrable for a bounded predictable
integrand under the event-count second-moment bound. -/
theorem Model.integrable_quadratic_jump (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.jumpIntegral (M.quadraticPayoff H) M.horizon) μ := by
  obtain ⟨C, hC⟩ := hbound
  apply M.integrable_jump (M.quadraticPayoff H) (M.predictable_quadratic H hH)
  refine ⟨C ^ 2, ?_⟩
  intro t ω
  simpa [Model.quadraticPayoff, abs_pow] using
    (pow_le_pow_left₀ (abs_nonneg (H t ω)) (hC t ω) 2)

/-- The quadratic compensator payoff is integrable for a bounded
predictable integrand under the uniform intensity bound. -/
theorem Model.integrable_quadratic_energy (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.energyIntegral (M.quadraticPayoff H) M.horizon) μ := by
  obtain ⟨C, hC⟩ := hbound
  apply M.integrable_energy (M.quadraticPayoff H) (M.predictable_quadratic H hH)
  refine ⟨C ^ 2, ?_⟩
  intro t ω
  simpa [Model.quadraticPayoff, abs_pow] using
    (pow_le_pow_left₀ (abs_nonneg (H t ω)) (hC t ω) 2)


end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
