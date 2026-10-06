module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarMomentPriors
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Real-valued measures from finite scalar moment priors

This module converts the finite weights and nodes of `ScalarMomentPriors` into
probability measures on the real line. Their support and moment identities are
the input required by the analytic moment-matched mixture theorem.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory
open scoped BigOperators ENNReal

/-- The real-valued atomic prior selected from one side of a finite scalar
moment-prior pair. -/
noncomputable def scalarMomentPrior {L : ℕ} (P : ScalarMomentPriors L)
    (side : Bool) : Measure ℝ :=
  ∑ i : Fin P.m,
    ENNReal.ofReal (if side then P.w₁ i else P.w₀ i) • Measure.dirac (P.node i)

/-- Each side of a finite scalar moment-prior pair is a probability measure
on the real line. -/
theorem scalarMomentPrior_isProbability {L : ℕ}
    (P : ScalarMomentPriors L) (side : Bool) :
    IsProbabilityMeasure (scalarMomentPrior P side) := by
  classical
  cases side with
  | false =>
      constructor
      simpa [scalarMomentPrior, ENNReal.ofReal_sum_of_nonneg
        (fun i _ => P.w₀_nonneg i)] using congrArg ENNReal.ofReal P.w₀_sum
  | true =>
      constructor
      simpa [scalarMomentPrior, ENNReal.ofReal_sum_of_nonneg
        (fun i _ => P.w₁_nonneg i)] using congrArg ENNReal.ofReal P.w₁_sum

/-- Each real-valued scalar moment prior is supported on the unit interval. -/
theorem scalarMomentPrior_supported {L : ℕ}
    (P : ScalarMomentPriors L) (side : Bool) :
    scalarMomentPrior P side {u : ℝ | |u| ≤ 1} = 1 := by
  classical
  have hnode (i : Fin P.m) : P.node i ∈ {u : ℝ | |u| ≤ 1} := by
    exact abs_le.mpr (P.node_mem i)
  have hmass : scalarMomentPrior P side {u : ℝ | |u| ≤ 1} =
      scalarMomentPrior P side Set.univ := by
    simp [scalarMomentPrior, Measure.coe_finsetSum,
      Measure.dirac_apply_of_mem, hnode]
  exact hmass.trans (IsProbabilityMeasure.measure_univ
    (self := scalarMomentPrior_isProbability P side))

/-- Given [a scalar moment prior](hyp:P), [a moment order](hyp:j), and [a proof that the order is within the matched degree](hyp:hj), [the two prior measures have equal moments of that order](goal). -/
theorem scalarMomentPrior_moments_eq {L : ℕ}
    (P : ScalarMomentPriors L) (j : ℕ) (hj : j ≤ L) :
    (∫ u : ℝ, u ^ j ∂scalarMomentPrior P false) =
      ∫ u : ℝ, u ^ j ∂scalarMomentPrior P true := by
  classical
  have hIntegral (side : Bool) :
      (∫ u : ℝ, u ^ j ∂scalarMomentPrior P side) =
        ∑ i : Fin P.m, (if side then P.w₁ i else P.w₀ i) * P.node i ^ j := by
    cases side with
    | false =>
        rw [scalarMomentPrior, integral_finsetSum_measure]
        · simp [integral_smul_measure, integral_dirac, P.w₀_nonneg]
        · intro i hi
          exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    | true =>
        rw [scalarMomentPrior, integral_finsetSum_measure]
        · simp [integral_smul_measure, integral_dirac, P.w₁_nonneg]
        · intro i hi
          exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [hIntegral false, hIntegral true]
  exact P.moments_eq j hj

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
