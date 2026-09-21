/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core.ERM
public import Causalean.ML.Core.Losses

/-! # Population-risk targets

This file collects reusable statements about what a population-risk minimizer
recovers.  `populationRisk_eq_of_both_minimizers` shows that any two minimizers
attain the same risk, while `populationRisk_minimizer_eq_target` turns a unique
target minimizer into equality of functions. For squared loss, `IsResidualOrthogonal`
records a conditional-mean normal equation, and
`square_loss_population_target_of_isResidualOrthogonal` proves that a function
satisfying it minimizes squared population risk. The conditional-expectation bridge is
isolated in `ML/CausalApplication/RegressionBridge.lean`, so this layer stays self-contained
and causal-free.
-/

@[expose] public section

namespace Causalean.ML

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Any two population-risk minimizers over the same class attain the same risk. -/
theorem populationRisk_eq_of_both_minimizers
    {H : HypothesisClass X Y} {loss : Loss Y} {P : Measure (X × Y)} {h₁ h₂ : X → Y}
    (H1 : IsPopulationRiskMinimizer H loss P h₁)
    (H2 : IsPopulationRiskMinimizer H loss P h₂) :
    populationRisk loss P h₁ = populationRisk loss P h₂ :=
  le_antisymm ((isMinOn_iff.mp H1.isMin) h₂ H2.mem) ((isMinOn_iff.mp H2.isMin) h₁ H1.mem)

/-- If a target is known to be the unique population-risk minimizer, every
population-risk minimizer equals it. -/
theorem populationRisk_minimizer_eq_target
    {H : HypothesisClass X Y} {loss : Loss Y} {P : Measure (X × Y)} {target hstar : X → Y}
    (hStar : IsPopulationRiskMinimizer H loss P hstar)
    (hTarget : IsPopulationRiskMinimizer H loss P target)
    (hUnique : ∀ h₁ h₂, IsPopulationRiskMinimizer H loss P h₁ →
      IsPopulationRiskMinimizer H loss P h₂ → h₁ = h₂) :
    hstar = target :=
  hUnique hstar target hStar hTarget

/-- [A candidate regression function](hyp:m) is [residual-orthogonal](goal) under
[a joint covariate--response law](hyp:P,X) precisely when
[its residual is orthogonal to every admissible covariate function](step:1).

This is an integrability-qualified conditional-mean moment condition: the definition does
not require the response or candidate to lie in L². Measurability of the test function is
what links the condition to `condExp`; see `ML/CausalApplication/RegressionBridge.lean`. -/
def IsResidualOrthogonal (P : Measure (X × ℝ)) (m : X → ℝ) : Prop :=
  ∀ g : X → ℝ, Measurable g → Integrable (fun z => (z.2 - m z.1) * g z.1) P →
    ∫ z, (z.2 - m z.1) * g z.1 ∂P = 0

/-- [A residual-orthogonal candidate beats any admissible competitor in squared population
risk](goal) under [the joint covariate--response law](hyp:P,X). The guarantee compares it with
[the chosen competitor](hyp:h) and requires [residual orthogonality](hyp:hm),
[measurability of both functions](hyp:hm_meas,hh_meas),
[finite squared risks](hyp:hint_m,hint_h),
and [an integrable cross term](hyp:hcross).

Proof: complete the square
`(y − h x)² = (y − m x)² + 2 (y − m x)(m x − h x) + (m x − h x)²`; the cross term
integrates to zero by `IsResidualOrthogonal`, and the quadratic term is nonnegative. -/
theorem square_loss_population_target_of_isResidualOrthogonal
    {P : Measure (X × ℝ)} {m : X → ℝ} (hm : IsResidualOrthogonal P m)
    (h : X → ℝ) (hm_meas : Measurable m) (hh_meas : Measurable h)
    (hint_m : HasFinitePopulationRisk squaredLoss P m)
    (hint_h : HasFinitePopulationRisk squaredLoss P h)
    (hcross : Integrable (fun z => (z.2 - m z.1) * (m z.1 - h z.1)) P) :
    populationRisk squaredLoss P m ≤ populationRisk squaredLoss P h := by
  have hint_m' : Integrable (fun z : X × ℝ => (z.2 - m z.1) ^ 2) P := by
    simpa [HasFinitePopulationRisk, squaredLoss] using hint_m
  have hint_h' : Integrable (fun z : X × ℝ => (z.2 - h z.1) ^ 2) P := by
    simpa [HasFinitePopulationRisk, squaredLoss] using hint_h
  have hdiff :
      Integrable
        (fun z : X × ℝ => (z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) P :=
    hint_h'.sub hint_m'
  have hsq_int : Integrable (fun z : X × ℝ => (m z.1 - h z.1) ^ 2) P := by
    have htmp :
        Integrable
          (fun z : X × ℝ =>
            ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) -
              2 * ((z.2 - m z.1) * (m z.1 - h z.1))) P :=
      hdiff.sub (hcross.const_mul 2)
    convert htmp using 1
    funext z
    ring
  have horth : ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P = 0 :=
    hm (fun x => m x - h x) (hm_meas.sub hh_meas) hcross
  have hdiff_nonneg :
      0 ≤ ∫ z, ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) ∂P := by
    calc
      0 ≤ ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
        exact integral_nonneg (fun z => sq_nonneg _)
      _ = 2 * ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P +
            ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
        simp [horth]
      _ = ∫ z, 2 * ((z.2 - m z.1) * (m z.1 - h z.1)) +
            (m z.1 - h z.1) ^ 2 ∂P := by
        rw [integral_add]
        · rw [integral_const_mul]
        · exact hcross.const_mul 2
        · exact hsq_int
      _ = ∫ z, ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) ∂P := by
        apply integral_congr_ae
        filter_upwards with z
        ring
  have hle : ∫ z, (z.2 - m z.1) ^ 2 ∂P ≤ ∫ z, (z.2 - h z.1) ^ 2 ∂P := by
    have hnonneg_sub :
        0 ≤ ∫ z, (z.2 - h z.1) ^ 2 ∂P -
          ∫ z, (z.2 - m z.1) ^ 2 ∂P := by
      rw [← integral_sub hint_h' hint_m']
      exact hdiff_nonneg
    linarith
  simpa [populationRisk, squaredLoss] using hle

end Causalean.ML
