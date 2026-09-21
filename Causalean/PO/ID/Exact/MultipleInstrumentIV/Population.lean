/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Centered-score IV observed population bridge

Measure-backed bridge from an observed centered-score IV moment ratio
`E[h(Z)Y] / E[h(Z)D]` to the finite response-type algebra. This file does not
require `h` to be the fitted treatment from a 2SLS first stage.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.ID.Exact.MultipleInstrumentIV.ResponseTypes

/-! # Multiple-Instrument IV Population Bridge

This file connects an observed centered-score IV moment ratio for a finite
instrument to the response-type finite algebra. It defines
the observed moments `observedReducedFormMoment`, `observedFirstStageMoment`,
and `observedCenteredScoreIV`; rewrites the first two as finite sums over instrument
cells; and packages the assumptions needed for the measure-backed bridge in
`ObservedBridge`.

The main results are `ObservedBridge.observedReducedFormMoment_eq_reducedFormMoment`,
`ObservedBridge.observedFirstStageMoment_eq_firstStageMoment`,
`ObservedBridge.observedCenteredScoreIV_eq_centeredScoreIVPopulationBridge`, and the
end-to-end theorem `ObservedBridge.observedCenteredScoreIV_eq_centeredScoreIVFiniteAlgebra`.
They show that the observable population ratio `E[h(Z)Y] / E[h(Z)D]` agrees
with the finite response-type algebra once the observed conditional means are
linked to the bridge. A separate projected-score premise is needed to call
this ratio population 2SLS. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset MeasureTheory

noncomputable section

namespace ResponseTypeStats.PopulationBridge

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

/-- [An instrument cell](goal) selects units in [a sample space](hyp:Ω) whose [finite-valued
instrument](hyp:Z) equals [one support point](hyp:k) in [the finite support](hyp:K). -/
def zEvent (Z : Ω → Fin K) (k : Fin K) : Set Ω :=
  Z ⁻¹' ({k} : Set (Fin K))

/-- [The observed centered-score outcome moment](goal) averages [outcome](hyp:Y) times the
centered score from [an ordered index](hyp:I), evaluated at [the instrument](hyp:Z) under [the
population measure](hyp:μ) on [the measurable sample space and finite support](hyp:Ω,K). -/
noncomputable def observedReducedFormMoment
    (μ : Measure Ω) (Z : Ω → Fin K) (Y : Ω → ℝ) (I : FiniteIndex K) : ℝ :=
  ∫ ω, I.centeredIndex (Z ω) * Y ω ∂μ

/-- [The observed centered-score treatment moment](goal) averages [binary treatment](hyp:D)
times the centered score from [an ordered index](hyp:I), evaluated at [the instrument](hyp:Z)
under [the population measure](hyp:μ) on [the measurable sample space and finite
support](hyp:Ω,K). -/
noncomputable def observedFirstStageMoment
    (μ : Measure Ω) (Z : Ω → Fin K) (D : Ω → Bool) (I : FiniteIndex K) : ℝ :=
  ∫ ω, I.centeredIndex (Z ω) * boolToReal (D ω) ∂μ

/-- [The observed centered-score IV ratio](goal) divides the centered-score moment of [the
outcome](hyp:Y) by that of [binary treatment](hyp:D), using [an instrument](hyp:Z), [ordered score
index](hyp:I), and [population measure](hyp:μ) on [the measurable sample space and finite
support](hyp:Ω,K). -/
noncomputable def observedCenteredScoreIV
    (μ : Measure Ω) (Z : Ω → Fin K) (D : Ω → Bool) (Y : Ω → ℝ)
    (I : FiniteIndex K) : ℝ :=
  observedReducedFormMoment μ Z Y I / observedFirstStageMoment μ Z D I

private lemma zEvent_measurable (Z : Ω → Fin K) (hZ : Measurable Z) (k : Fin K) :
    MeasurableSet (zEvent Z k) :=
  hZ (measurableSet_singleton k)

omit [MeasurableSpace Ω] in
private lemma zEvent_pairwise_disjoint (Z : Ω → Fin K) :
    Pairwise (Function.onFun Disjoint (zEvent Z)) := by
  intro k l hkl
  rw [Function.onFun]
  refine Set.disjoint_left.mpr ?_
  intro ω hk hl
  exact hkl ((Set.mem_singleton_iff.mp hk).symm.trans (Set.mem_singleton_iff.mp hl))

omit [MeasurableSpace Ω] in
private lemma zEvent_iUnion (Z : Ω → Fin K) :
    (⋃ k : Fin K, zEvent Z k) = Set.univ := by
  ext ω
  simp [zEvent]

private lemma eventCondExp_centered_mul_eq
    (μ : Measure Ω) (Z : Ω → Fin K) (hZ : Measurable Z)
    (Y : Ω → ℝ) (I : FiniteIndex K) (k : Fin K) :
    normalizedRestrictedIntegral μ (zEvent Z k) (fun ω => I.centeredIndex (Z ω) * Y ω) =
      I.centeredIndex k * normalizedRestrictedIntegral μ (zEvent Z k) Y := by
  calc
    normalizedRestrictedIntegral μ (zEvent Z k) (fun ω => I.centeredIndex (Z ω) * Y ω) =
        normalizedRestrictedIntegral μ (zEvent Z k) (fun ω => I.centeredIndex k * Y ω) := by
      apply eventCondExp_congr_on μ (zEvent_measurable Z hZ k)
      intro ω hω
      have hZω : Z ω = k := Set.mem_singleton_iff.mp hω
      simp [hZω]
    _ = I.centeredIndex k * normalizedRestrictedIntegral μ (zEvent Z k) Y := by
      exact eventCondExp_smul μ (zEvent Z k) (I.centeredIndex k) Y

/-- [The centered-score outcome moment equals the support-mass-weighted sum of instrument-cell
outcome means](goal) under [a finite population law](hyp:μ), for [a measurable
instrument](hyp:Z,hZ), [outcome](hyp:Y), [ordered score index](hyp:I), and [integrability of the
weighted outcome](hyp:hInt). This is the finite-support law of total expectation. -/
theorem observedReducedFormMoment_eq_sum_eventCondExp
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin K) (hZ : Measurable Z)
    (Y : Ω → ℝ) (I : FiniteIndex K)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ) :
    observedReducedFormMoment μ Z Y I =
      ∑ k : Fin K,
        (μ (zEvent Z k)).toReal * I.centeredIndex k *
          normalizedRestrictedIntegral μ (zEvent Z k) Y := by
  unfold observedReducedFormMoment
  rw [integral_eq_sum_measure_mul_eventCondExp
    (μ := μ) (A := zEvent Z)
    (hmeas := zEvent_measurable Z hZ)
    (hdisj := zEvent_pairwise_disjoint Z)
    (hcov := zEvent_iUnion Z)
    (f := fun ω => I.centeredIndex (Z ω) * Y ω) hInt]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  rw [eventCondExp_centered_mul_eq μ Z hZ Y I k]
  ring

/-- [The centered-score treatment moment equals the support-mass-weighted sum of instrument-cell
treatment means](goal) under [a finite population law](hyp:μ), for [a measurable
instrument](hyp:Z,hZ), [binary treatment](hyp:D), [ordered score index](hyp:I), and [integrability
of the weighted treatment](hyp:hInt). -/
theorem observedFirstStageMoment_eq_sum_eventCondExp
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin K) (hZ : Measurable Z)
    (D : Ω → Bool) (I : FiniteIndex K)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedFirstStageMoment μ Z D I =
      ∑ k : Fin K,
        (μ (zEvent Z k)).toReal * I.centeredIndex k *
          normalizedRestrictedIntegral μ (zEvent Z k) (fun ω => boolToReal (D ω)) := by
  exact observedReducedFormMoment_eq_sum_eventCondExp
    (μ := μ) (Z := Z) hZ (Y := fun ω => boolToReal (D ω)) I hInt

/-- An observed-data response-type bridge on [a measurable population space](hyp:Ω)
with [finite instrument support](hyp:K) connects [a population law](hyp:μ),
[a finite-valued instrument](hyp:Z), [a binary treatment](hyp:D), and
[a real-valued outcome](hyp:Y) to [an ordered score index](hyp:I) and
[a response-type population expansion](hyp:P). It requires
[the law to be a probability measure](hyp:isProbability),
[index masses to match observed instrument-cell probabilities](hyp:rho_eq_zMass),
[conditional outcome means to match the response-type expansion](hyp:outcome_cell), and
[conditional treatment means to follow the response-type expansion](hyp:treatment_cell)
around [a common baseline](hyp:baseTreatment).

The two conditional-expectation fields are the precise
place where consistency, exogeneity, and exclusion are used: for each
instrument cell, they replace the observed conditional mean by the
response-type expansion already consumed by the finite response-type algebra. -/
structure ObservedBridge (μ : Measure Ω) (Z : Ω → Fin K)
    (D : Ω → Bool) (Y : Ω → ℝ) (I : FiniteIndex K)
    (P : PopulationBridge K) where
  /-- The observed law is a probability measure, so the integrals below are
  population expectations. -/
  isProbability : IsProbabilityMeasure μ
  /-- The finite support masses in `I` are the probabilities of the observed
  instrument cells. -/
  rho_eq_zMass : ∀ k : Fin K, I.rho k = (μ (zEvent Z k)).toReal
  /-- Conditional outcome bridge after consistency, exogeneity, and exclusion:
  for each instrument cell Z = zᵏ, the observed conditional mean E[Y | Z = zᵏ]
  equals the response-type expansion `P.outcomeAtSupport k`.

  This is a field of the algebraic bridge. `MultipleInstrumentIV/POBridge.lean`
  derives it in `POMultipleIVSystem.toObservedBridge` from consistency and instrument
  independence, so callers may supply it directly or obtain the whole bridge from that system. -/
  outcome_cell :
    ∀ k : Fin K,
      normalizedRestrictedIntegral μ (zEvent Z k) Y = P.outcomeAtSupport k
  /-- Baseline treatment mean, common across support cells after exogeneity.
  The centered score cancels this term in the treatment moment. -/
  baseTreatment : ℝ
  /-- Conditional treatment bridge after consistency and exogeneity, stated in
  baseline-subtracted form: the adjacent telescoping term is the deviation from
  the baseline support point, not the raw treatment mean.

  Like `outcome_cell`, this field is derived from a `POMultipleIVSystem` under consistency and
  instrument independence by `POMultipleIVSystem.toObservedBridge`. -/
  treatment_cell :
    ∀ k : Fin K,
      normalizedRestrictedIntegral μ (zEvent Z k) (fun ω => boolToReal (D ω)) =
        baseTreatment + P.treatmentAtSupport k

namespace ObservedBridge

variable {μ : Measure Ω} {Z : Ω → Fin K} {D : Ω → Bool} {Y : Ω → ℝ}
variable {I : FiniteIndex K} {P : PopulationBridge K}

/-- [The observed centered-score outcome moment equals its finite response-type expansion](goal)
when [the observed-data bridge](hyp:B) holds, [the instrument is measurable](hyp:hZ), and [the
weighted outcome is integrable](hyp:hInt). -/
theorem observedReducedFormMoment_eq_reducedFormMoment
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ) :
    observedReducedFormMoment μ Z Y I = P.reducedFormMoment I := by
  rw [observedReducedFormMoment_eq_sum_eventCondExp μ Z hZ Y I hInt]
  unfold reducedFormMoment
  refine Finset.sum_congr rfl ?_
  intro k _hk
  rw [← B.rho_eq_zMass k, B.outcome_cell k]

/-- [The observed centered-score treatment moment equals its finite response-type
expansion](goal) when [the observed-data bridge](hyp:B) holds, [the instrument is
measurable](hyp:hZ), and [the weighted treatment is integrable](hyp:hInt). -/
theorem observedFirstStageMoment_eq_firstStageMoment
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedFirstStageMoment μ Z D I = P.firstStageMoment I := by
  rw [observedFirstStageMoment_eq_sum_eventCondExp μ Z hZ D I hInt]
  unfold firstStageMoment
  calc
    (∑ k : Fin K,
        (μ (zEvent Z k)).toReal * I.centeredIndex k *
          normalizedRestrictedIntegral μ (zEvent Z k) (fun ω => boolToReal (D ω))) =
        ∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (B.baseTreatment + P.treatmentAtSupport k) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [← B.rho_eq_zMass k, B.treatment_cell k]
    _ = (∑ k : Fin K, I.rho k * I.centeredIndex k) * B.baseTreatment +
          ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
      calc
        (∑ k : Fin K, I.rho k * I.centeredIndex k *
            (B.baseTreatment + P.treatmentAtSupport k)) =
            ∑ k : Fin K,
              (I.rho k * I.centeredIndex k * B.baseTreatment +
                I.rho k * I.centeredIndex k * P.treatmentAtSupport k) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring
        _ = (∑ k : Fin K, I.rho k * I.centeredIndex k * B.baseTreatment) +
              ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
          rw [Finset.sum_add_distrib]
        _ = (∑ k : Fin K, I.rho k * I.centeredIndex k) * B.baseTreatment +
              ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
          rw [Finset.sum_mul]
    _ = ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
      rw [I.centered_weight_sum_zero]
      simp

/-- [The observed centered-score IV ratio equals the finite-support population-bridge
ratio](goal) under [a measure, instrument, treatment, outcome, ordered score, and observed-data
bridge](hyp:μ,Z,D,Y,I,B), when [the instrument is measurable](hyp:hZ), [the weighted
outcome](hyp:hYInt) and [weighted treatment](hyp:hDInt) are integrable. -/
theorem observedCenteredScoreIV_eq_centeredScoreIVPopulationBridge
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hYInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ)
    (hDInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedCenteredScoreIV μ Z D Y I = P.centeredScoreIVPopulationBridge I := by
  unfold observedCenteredScoreIV centeredScoreIVPopulationBridge
  rw [B.observedReducedFormMoment_eq_reducedFormMoment hZ hYInt,
    B.observedFirstStageMoment_eq_firstStageMoment hZ hDInt]

/-- [The observed centered-score IV ratio equals the finite response-type algebra ratio](goal)
under [a measure, instrument, treatment, outcome, ordered score, and observed-data
bridge](hyp:μ,Z,D,Y,I,B), when [the instrument is measurable](hyp:hZ), [the weighted
outcome](hyp:hYInt) and [weighted treatment](hyp:hDInt) are integrable. -/
theorem observedCenteredScoreIV_eq_centeredScoreIVFiniteAlgebra
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hYInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ)
    (hDInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedCenteredScoreIV μ Z D Y I = P.stats.centeredScoreIVFiniteAlgebra I := by
  rw [B.observedCenteredScoreIV_eq_centeredScoreIVPopulationBridge hZ hYInt hDInt,
    P.centeredScoreIVPopulationBridge_eq_centeredScoreIVFiniteAlgebra I]

end ObservedBridge

end ResponseTypeStats.PopulationBridge

end

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
