/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.CausalApplication.Nuisance
public import Causalean.Estimation.ATE.Score.MeanZero

/-! # Exact-nuisance transport into the AIPW mean-zero equation

This file proves an equality-transport lemma: when supplied outcome-regression and
propensity functions already agree almost everywhere with both true nuisances, their
packaged `NuisanceVec` makes the AIPW estimating equation mean-zero at the average
treatment effect. No learner, empirical-risk minimizer, or convergence-rate hypothesis
appears here, and the result does not state the one-nuisance-correct double-robust
property. It reuses the existing exact-nuisance AIPW identification theorem.
-/

public section

namespace Causalean.ML.CausalApplication

open MeasureTheory Causalean.Estimation.ATE Causalean.PO
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **AIPW mean-zero transport under two exact nuisance equalities.** In [a backdoor
estimation system](hyp:P,γ,S), suppose [the propensity is bounded away from 0 and 1 by
`ε` (strict overlap)](hyp:ε,h_overlap), [the backdoor identification assumptions hold](hyp:hA),
[the squared factual outcome is integrable](hyp:h_y2), and [the squared potential outcome
under each treatment arm is integrable](hyp:h_yd2). If the supplied outcome-regression
functions and propensity function are [measurable](hyp:mhat,ehat,hmhat,hehat) and
[agree almost everywhere
under the covariate law with the true outcome regression and true propensity, respectively
(correct specification)](hyp:hμ_spec,he_spec), then [the AIPW moment functional built
from the supplied nuisance vector integrates to zero at the true average treatment
effect `S.θ₀`](goal). This lemma assumes both nuisance equalities; it does not expose
the one-nuisance-correct double-robust guarantee or establish that a learner supplies
either equality. -/
theorem aipw_mlNuisance_meanZero_transport_of_exact_nuisances
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε) (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    {mhat : Bool → γ → ℝ} {ehat : γ → ℝ}
    (hmhat : ∀ b, Measurable (mhat b)) (hehat : Measurable ehat)
    (hμ_spec : ∀ b, mhat b =ᵐ[S.P_X] S.μ_val b)
    (he_spec : ehat =ᵐ[S.P_X] S.e_val) :
    (∫ z, BackdoorEstimationSystem.aipwMomentFunctional
        (mlNuisanceVec mhat ehat hmhat hehat) z S.θ₀ ∂ S.P_Z) = 0 := by
  have hproj : Measurable (fun z : γ × Bool × ℝ => projX z) := by
    simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
  have hμZ (b : Bool) :
      (fun z => mhat b (projX z)) =ᵐ[S.P_Z] fun z => S.μ_val b (projX z) := by
    have hx := hμ_spec b
    rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] at hx
    exact (ae_map_iff hproj.aemeasurable
      (measurableSet_eq_fun (hmhat b) (S.μ_meas b))).mp hx
  have heZ : (fun z => ehat (projX z)) =ᵐ[S.P_Z] fun z => S.e_val (projX z) := by
    have hx := he_spec
    rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] at hx
    exact (ae_map_iff hproj.aemeasurable
      (measurableSet_eq_fun hehat S.e_meas)).mp hx
  have hfun :
      (fun z => BackdoorEstimationSystem.aipwMomentFunctional
        (mlNuisanceVec mhat ehat hmhat hehat) z S.θ₀) =ᵐ[S.P_Z] S.ψ_AIPW := by
    filter_upwards [hμZ true, hμZ false, heZ] with z hμ1 hμ0 he
    change aipwMoment z mhat ehat S.θ₀ = aipwMoment z S.μ_val S.e_val S.θ₀
    unfold aipwMoment
    rw [hμ1, hμ0, he]
  rw [integral_congr_ae hfun]
  exact BackdoorEstimationSystem.aipw_mean_zero_of_square_integrable S h_overlap hA h_y2 h_yd2

end Causalean.ML.CausalApplication
