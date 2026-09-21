/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract sign-aligned multiple-IV finite algebra

Public facade for a finite-support ordered-score response-type algebra. This
module exports the ordered finite index,
the numeric matrix score adapter, tail coefficients, the
finite-support population bridge, the observed `E[h(Z)Y] / E[h(Z)D]` bridge,
response-type weights, and normalization facts conditional on abstract sign
alignment. It does not formalize MTW partial monotonicity or derive sign
alignment from behavioral restrictions.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/mogstad_torgovitsky_walters_multiple_iv.md`.
-/

module
public import Causalean.PO.ID.Exact.MultipleInstrumentIV.Population

/-! # Multiple-Instrument IV Main Facade

This file provides the public finite-support facade for an abstract
multiple-instrument response-type algebra. It exposes the signed adjacent
ratio, the response-type weighted-sum form, positivity under an assumed sign-
alignment condition, and the corresponding population bridge statements. It
does not provide the behavioral or empirical conditions in the full MTW
multiple-instrument characterization. -/

@[expose] public section

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset

namespace ResponseTypeStats

variable {K : ℕ} (I : FiniteIndex K) (R : ResponseTypeStats K)

/-- [The signed adjacent outcome numerator](goal) aggregates within-type causal effects from
[finite response-type statistics](hyp:R) using the unnormalized weights induced by [an ordered
score](hyp:I). -/
noncomputable def signedAdjacentNumerator : ℝ :=
  ∑ g : ResponseType K, R.unnormTypeWeight I g * R.effect g

/-- [The signed adjacent treatment denominator](goal) aggregates all unnormalized type weights
induced by [an ordered score](hyp:I) and [finite response-type statistics](hyp:R). -/
noncomputable def signedAdjacentDenominator : ℝ :=
  R.typeWeightDenom I

/-- [The finite-algebra centered-score IV ratio is the signed adjacent outcome numerator divided
by the treatment denominator](goal) for [an ordered score](hyp:I) and [finite response-type
statistics](hyp:R), provided [that denominator is nonzero](hyp:_hden).

The `PopulationBridge` facade below upgrades this finite ratio to the
corresponding finite-support centered-score IV ratio. A population-2SLS interpretation requires
separate hypotheses tying the score to an observed first-stage projection. -/
theorem centeredScoreIVFiniteAlgebra_eq_signedAdjacentRatio
    (_hden : R.signedAdjacentDenominator I ≠ 0) :
    R.centeredScoreIVFiniteAlgebra I =
      R.signedAdjacentNumerator I / R.signedAdjacentDenominator I := by
  rfl

/-- [The centered-score IV ratio equals the response-type-weighted causal-effect sum](goal) for
[an ordered score](hyp:I) and [finite response-type statistics](hyp:R) when [the score-weight
denominator is nonzero](hyp:hden). -/
theorem centeredScoreIVFiniteAlgebra_eq_responseTypeWeightedSum'
    (hden : R.typeWeightDenom I ≠ 0) :
    R.centeredScoreIVFiniteAlgebra I = R.responseTypeEstimand I := by
  exact R.centeredScoreIVFiniteAlgebra_eq_responseTypeWeightedSum I hden

/-- [The centered-score IV ratio is a convex response-type average](goal) for [an ordered
score](hyp:I) and [finite response-type statistics](hyp:R) when [response types are
sign-aligned](hyp:hAlign) and [the score-weight denominator is positive](hyp:hden).

This does not derive sign alignment from a behavioral monotonicity restriction. -/
theorem centeredScoreIVFiniteAlgebra_eq_positiveResponseTypeAverage_of_signAligned'
    (hAlign : R.SignAligned I)
    (hden : 0 < R.typeWeightDenom I) :
    R.centeredScoreIVFiniteAlgebra I = R.responseTypeEstimand I ∧
      (∀ g : ResponseType K, 0 ≤ R.normalizedTypeWeight I g) ∧
      (∑ g : ResponseType K, R.normalizedTypeWeight I g = 1) := by
  exact R.centeredScoreIVFiniteAlgebra_eq_positiveResponseTypeAverage_of_signAligned I hAlign hden

end ResponseTypeStats

namespace ResponseTypeStats.PopulationBridge

variable {K : ℕ} (I : FiniteIndex K) (P : ResponseTypeStats.PopulationBridge K)

/-- [The population-bridge centered-score IV ratio equals the signed adjacent outcome numerator
divided by its treatment denominator](goal) for [an ordered score](hyp:I) and [finite-support
population bridge](hyp:P), provided [the denominator is nonzero](hyp:hden). -/
theorem centeredScoreIVPopulationBridge_eq_signedAdjacentRatio
    (hden : P.stats.signedAdjacentDenominator I ≠ 0) :
    P.centeredScoreIVPopulationBridge I =
      P.stats.signedAdjacentNumerator I / P.stats.signedAdjacentDenominator I := by
  rw [P.centeredScoreIVPopulationBridge_eq_centeredScoreIVFiniteAlgebra I]
  exact P.stats.centeredScoreIVFiniteAlgebra_eq_signedAdjacentRatio I hden

/-- [The population-bridge centered-score IV ratio equals the response-type-weighted sum of
within-type causal effects](goal) for [an ordered score](hyp:I) and [finite-support population
bridge](hyp:P), provided [the score-weight denominator is nonzero](hyp:hden). -/
theorem centeredScoreIVPopulationBridge_eq_responseTypeWeightedSum
    (hden : P.stats.typeWeightDenom I ≠ 0) :
    P.centeredScoreIVPopulationBridge I = P.stats.responseTypeEstimand I := by
  rw [P.centeredScoreIVPopulationBridge_eq_centeredScoreIVFiniteAlgebra I]
  exact P.stats.centeredScoreIVFiniteAlgebra_eq_responseTypeWeightedSum I hden

/-- [The population-bridge centered-score IV ratio is a convex response-type average](goal) for
[an ordered score](hyp:I) and [finite-support population bridge](hyp:P) when [response types are
sign-aligned](hyp:hAlign) and [the score-weight denominator is positive](hyp:hden). -/
theorem centeredScoreIVPopulationBridge_eq_positiveResponseTypeAverage_of_signAligned
    (hAlign : P.stats.SignAligned I)
    (hden : 0 < P.stats.typeWeightDenom I) :
    P.centeredScoreIVPopulationBridge I = P.stats.responseTypeEstimand I ∧
      (∀ g : ResponseType K, 0 ≤ P.stats.normalizedTypeWeight I g) ∧
      (∑ g : ResponseType K, P.stats.normalizedTypeWeight I g = 1) := by
  rw [P.centeredScoreIVPopulationBridge_eq_centeredScoreIVFiniteAlgebra I]
  exact
    P.stats.centeredScoreIVFiniteAlgebra_eq_positiveResponseTypeAverage_of_signAligned
      I hAlign hden

end ResponseTypeStats.PopulationBridge

namespace ResponseTypeStats.PopulationBridge.ObservedBridge

open ResponseTypeStats.PopulationBridge

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
variable {μ : MeasureTheory.Measure Ω} {Z : Ω → Fin K}
variable {D : Ω → Bool} {Y : Ω → ℝ}
variable {I : FiniteIndex K} {P : ResponseTypeStats.PopulationBridge K}

/-- [The observed centered-score IV ratio equals the response-type-weighted sum of within-type
causal effects](goal) when [an observed-data bridge](hyp:B) links instrument, treatment, and
outcome to the response-type population, [the instrument is measurable](hyp:hZ), [the weighted
outcome](hyp:hYInt) and [weighted treatment](hyp:hDInt) are integrable, and [the observed first
stage is nonzero](hyp:hden).

This packages the full bridge chain:

    observedCenteredScoreIV = centeredScoreIVFiniteAlgebra = Σ_g ω_g Δ_g.

This has the algebraic form used by `prop:po-estimand-mtw-response-type-form`,
but the cited 2SLS result additionally requires `h` to be the fitted first-stage
score. Under `ObservedBridge`, `hden` equals `typeWeightDenom I` by
`observedFirstStageMoment_eq_firstStageMoment` and
`firstStageMoment_eq_typeWeightDenom`. -/
theorem observedCenteredScoreIV_eq_responseTypeWeightedSum
    (B : ObservedBridge μ Z D Y I P) [MeasureTheory.IsFiniteMeasure μ]
    (hZ : Measurable Z)
    (hYInt : MeasureTheory.Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ)
    (hDInt : MeasureTheory.Integrable
        (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ)
    (hden : observedFirstStageMoment μ Z D I ≠ 0) :
    observedCenteredScoreIV μ Z D Y I = P.stats.responseTypeEstimand I := by
  -- Step 1: observed → finite algebra
  have h1 : observedCenteredScoreIV μ Z D Y I = P.stats.centeredScoreIVFiniteAlgebra I :=
    B.observedCenteredScoreIV_eq_centeredScoreIVFiniteAlgebra hZ hYInt hDInt
  -- Step 2: the observed denominator equals typeWeightDenom
  have hden' : P.stats.typeWeightDenom I ≠ 0 := by
    rwa [← P.firstStageMoment_eq_typeWeightDenom I,
      ← B.observedFirstStageMoment_eq_firstStageMoment hZ hDInt]
  -- Step 3: finite algebra → response-type weighted sum
  rw [h1]
  exact P.stats.centeredScoreIVFiniteAlgebra_eq_responseTypeWeightedSum I hden'

end ResponseTypeStats.PopulationBridge.ObservedBridge

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
