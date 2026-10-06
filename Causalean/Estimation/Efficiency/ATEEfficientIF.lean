/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.ATEPathwiseDerivative

/-!
# AIPW as the efficient influence function for the observed-law ATE

This module proves that the AIPW function is an efficient influence function for
the observed-law ATE relative to bounded exponential tilts. The result assumes
bounded outcomes and strict overlap, and a backdoor estimation system inherits it
by transporting those observed-law conditions. The AIPW target is motivated by
Hahn (1998), but these bounded-tilt results are not a formalization of Hahn's
Theorem 1.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Filter MeasureTheory ProbabilityTheory
open _root_.Causalean.Estimation.ATE.BackdoorEstimationSystem

variable {γ : Type*} [MeasurableSpace γ]

/-- The [recomputed AIPW function is efficient for the observed-law ATE relative
to the bounded-tilt submodel class](goal) when [the observed law of covariates,
treatment, and outcome](hyp:P) has [outcomes bounded by a nonnegative
constant](hyp:B,hB,hY) and [strict overlap in both arms at a positive
level](hyp:ε,hε,hoverlap). This class generates the full nonparametric mean-zero
square-integrable tangent space.

The AIPW target is motivated by Hahn (1998); the formal result is a bounded-outcome,
bounded-tilt surrogate rather than a statement of Hahn's Theorem 1. -/
theorem observedAIPW_isEfficientInfluenceFunction_ATE
    (P : Measure (γ × Bool × ℝ)) [IsProbabilityMeasure P]
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hY : ∀ᵐ z ∂P, |projY z| ≤ B)
    (hoverlap : ∀ d, ∀ᵐ z ∂P, ε ≤ observedPropensity P d z) :
    IsEfficientInfluenceFunction P observedATE
      ((memLp_observedAIPW P B ε hB hε hY hoverlap).toLp
        (observedAIPW P)) (boundedTiltSubmodels P) := by
  let hφ := memLp_observedAIPW P B ε hB hε hY hoverlap
  apply isEfficientInfluenceFunction_of_hasDerivAt_tilt' P observedATE
    (observedAIPW P) hφ
    (integral_observedAIPW_eq_zero P B ε hB hε hY hoverlap)
  intro g M hg_meas hgM hg_mean
  exact hasDerivAt_observedATE_tilt P g |M| B ε hg_meas
    (fun z => (hgM z).trans (le_abs_self M)) hg_mean
    (abs_nonneg M) hB hε hY hoverlap

end Causalean.Estimation.Efficiency

namespace Causalean.Estimation.ATE.BackdoorEstimationSystem

open Causalean.PO
open Causalean.Estimation.Efficiency
open Filter MeasureTheory ProbabilityTheory

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Given [a backdoor estimation system `S`](hyp:S) and [a factual-outcome
bound `B`](hyp:B,hY_bound), [the induced observed outcome is bounded by `B`
almost everywhere](goal). -/
lemma observedOutcome_bounded
    (S : ATE.BackdoorEstimationSystem P γ) (B : ℝ)
    (hY_bound : ∀ ω, |S.toPOBackdoorSystem.factualY ω| ≤ B) :
    ∀ᵐ z ∂S.P_Z, |projY z| ≤ B := by
  rw [S.P_Z_eq]
  apply (ae_map_iff S.measurable_factualZ.aemeasurable ?_).2
  · filter_upwards with ω
    simpa [ATE.BackdoorEstimationSystem.factualZ, projY] using hY_bound ω
  · exact measurableSet_Iic.preimage
      ((measurable_snd.snd : Measurable (fun z : γ × Bool × ℝ => z.2.2)).abs)

/-- Given [a backdoor estimation system `S`](hyp:S), [strict overlap at level
`ε`](hyp:ε,h_overlap), and [the backdoor assumptions](hyp:hA), [the induced
observed law has overlap at level `ε` in both arms](goal). -/
lemma observedPropensity_overlap
    (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions) :
    ∀ d, ∀ᵐ z ∂S.P_Z, ε ≤ observedPropensity S.P_Z d z := by
  have heZ : ∀ᵐ z ∂S.P_Z,
      ε ≤ S.e_val (projX z) ∧ S.e_val (projX z) ≤ 1 - ε := by
    have heΩ : ∀ᵐ ω ∂P.μ,
        ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) ∧
          S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
      filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
      simpa [hcomp] using hover
    have hset : MeasurableSet
        {z : γ × Bool × ℝ |
          ε ≤ S.e_val (projX z) ∧ S.e_val (projX z) ≤ 1 - ε} := by
      exact measurableSet_Icc.preimage (S.e_meas.comp measurable_fst)
    rw [S.P_Z_eq]
    apply (ae_map_iff S.measurable_factualZ.aemeasurable hset).2
    filter_upwards [heΩ] with ω hω
    simpa [ATE.BackdoorEstimationSystem.factualZ, projX] using hω
  intro d
  have hp := Causalean.Estimation.Efficiency.ATE.BackdoorEstimationSystem.observedPropensity_P_Z_ae
    S hA d
  cases d
  · filter_upwards [hp, heZ] with z hpz hez
    rw [hpz]
    simp only [e_val_label, Bool.false_eq_true, ↓reduceIte]
    linarith [hez.2]
  · filter_upwards [hp, heZ] with z hpz hez
    rw [hpz]
    simpa [e_val_label] using hez.1

/-- Given [a backdoor estimation system `S`](hyp:S), [strict overlap at level
`ε`](hyp:ε,h_overlap), [the backdoor assumptions](hyp:hA), [a nonnegative
outcome bound `B`](hyp:B,hB), and [bounded factual outcomes](hyp:hY_bound), [the
observed-law AIPW function belongs to L²](goal). -/
theorem observedAIPW_memLp_of_bounded
    (S : ATE.BackdoorEstimationSystem P γ) {ε B : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (hB : 0 ≤ B)
    (hY_bound : ∀ ω, |S.toPOBackdoorSystem.factualY ω| ≤ B) :
    MemLp (observedAIPW S.P_Z) 2 S.P_Z :=
  memLp_observedAIPW S.P_Z B ε hB h_overlap.1
    (S.observedOutcome_bounded B hY_bound)
    (S.observedPropensity_overlap h_overlap hA)

/-- The [observed-law AIPW function is efficient for the observed-law ATE relative
to the bounded-tilt submodel class](goal) for [a backdoor ATE estimation
system](hyp:S) satisfying [the backdoor assumptions](hyp:hA), [strict overlap at
a positive level](hyp:ε,h_overlap), and [factual outcomes bounded by a
nonnegative constant](hyp:B,hB,hY_bound). No separate factual- or
potential-outcome second-moment premise is required.

The AIPW target is motivated by Hahn (1998); the formal result transports the
bounded-outcome, bounded-tilt surrogate above and is not Hahn's Theorem 1. -/
theorem aipw_is_efficientInfluenceFunction_ATE
    (S : ATE.BackdoorEstimationSystem P γ) {ε B : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (hB : 0 ≤ B)
    (hY_bound : ∀ ω, |S.toPOBackdoorSystem.factualY ω| ≤ B) :
    IsEfficientInfluenceFunction S.P_Z observedATE
      ((S.observedAIPW_memLp_of_bounded h_overlap hA hB hY_bound).toLp
        (observedAIPW S.P_Z)) (boundedTiltSubmodels S.P_Z) := by
  exact observedAIPW_isEfficientInfluenceFunction_ATE S.P_Z B ε hB h_overlap.1
    (S.observedOutcome_bounded B hY_bound)
    (S.observedPropensity_overlap h_overlap hA)

end Causalean.Estimation.ATE.BackdoorEstimationSystem
