/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.Setup

/-! # Compatibility names for the control-arm marginal sensitivity model

The marginal sensitivity model is parameterized by a treatment arm in `Setup.lean`.
This file retains the former control-specific names as deprecated specializations at
`d = false`; it contains no separate control-arm derivation.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ), and
[a back-door system on them](hyp:S), the [control-arm complete-information σ-algebra](goal)
is the arm-uniform complete-information σ-algebra specialized to control. -/
@[deprecated "Use sigmaXY false." (since := "2026-09-17")]
noncomputable abbrev sigmaXY0 : MeasurableSpace P.Ω := S.sigmaXY false

/-- Deprecated control-arm specialization of the ambient measurability bound. -/
@[deprecated "Use sigmaXY_le false." (since := "2026-09-17")]
lemma sigmaXY0_le : S.sigmaXY0 ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.sigmaXY_le false

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ), and
[a back-door system on them](hyp:S), the [complete control propensity](goal) is the
arm-uniform complete propensity specialized to control. -/
@[deprecated "Use completeProp false." (since := "2026-09-17")]
noncomputable abbrev completeProp0 : P.Ω → ℝ := S.completeProp false

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a candidate complete control propensity](hyp:etilde),
the [candidate inverse-probability-weighted control mean](goal) is the arm-uniform candidate
mean specialized to control. -/
@[deprecated "Use candMean false." (since := "2026-09-17")]
noncomputable abbrev candMean0 (etilde : P.Ω → ℝ) : ℝ := S.candMean false etilde

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ), and
[a back-door system on them](hyp:S), the [control potential-outcome mean](goal) is the
arm-uniform potential-outcome mean specialized to control. -/
@[deprecated "Use Ymean false." (since := "2026-09-17")]
noncomputable abbrev Y0mean : ℝ := S.Ymean false

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), the [control-arm MSM
ambiguity set](goal) is the arm-uniform ambiguity set specialized to control. -/
@[deprecated "Use MSMSet false." (since := "2026-09-17")]
abbrev MSMSet0 (Λ : ℝ) : Set (P.Ω → ℝ) := S.MSMSet false Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), the [control-arm MSM
upper bound](goal) is the arm-uniform upper bound specialized to control. -/
@[deprecated "Use msmUpper false." (since := "2026-09-17")]
noncomputable abbrev msmUpper0 (Λ : ℝ) : ℝ := S.msmUpper false Λ

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate space](hyp:γ),
[a back-door system on them](hyp:S), and [a sensitivity level](hyp:Λ), the [control-arm MSM
lower bound](goal) is the arm-uniform lower bound specialized to control. -/
@[deprecated "Use msmLower false." (since := "2026-09-17")]
noncomputable abbrev msmLower0 (Λ : ℝ) : ℝ := S.msmLower false Λ

/-- Deprecated control-arm specialization of the arm-uniform IPW/tower bridge. -/
@[deprecated "Use candMean_completeProp_eq_Ymean false." (since := "2026-09-17")]
theorem candMean0_completeProp0_eq_Y0mean
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (hcons : P.Consistency)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < S.completeProp0 ω)
    (hint : Integrable (S.YofD false) P.μ)
    (hcand_int : Integrable
      (fun ω => S.dVar.indicator false ω * S.factualY ω / S.completeProp0 ω) P.μ) :
    S.candMean0 S.completeProp0 = S.Y0mean :=
  S.candMean_completeProp_eq_Ymean false hcons hpos hint hcand_int

/-- Deprecated control-arm specialization of truth membership in the MSM ambiguity set. -/
@[deprecated "Use completeProp_mem_MSMSet false." (since := "2026-09-17")]
theorem completeProp0_mem_MSMSet0 (Λ : ℝ)
    (hMSM :
      (∀ᵐ ω ∂P.μ, 0 < S.completeProp0 ω ∧ S.completeProp0 ω < 1) ∧
      (∀ᵐ ω ∂P.μ,
        1 / Λ ≤ OR (S.completeProp0 ω) (S.propScore false ω) ∧
          OR (S.completeProp0 ω) (S.propScore false ω) ≤ Λ)) :
    S.completeProp0 ∈ S.MSMSet0 Λ :=
  S.completeProp_mem_MSMSet false Λ hMSM

/-- Given [a sensitivity level](hyp:Λ), [the true complete propensity in the control MSM
set](hyp:hmem), [its control-mean bridge identity](hyp:hbridge), and [lower and upper
boundedness of the candidate means](hyp:hbdd,hbdd'), [the control potential-outcome mean lies
in the control MSM interval](goal).

Deprecated control-arm specialization of the arm-uniform MSM interval theorem. -/
@[deprecated "Use Ymean_mem_Icc false." (since := "2026-09-17")]
theorem Y0mean_mem_Icc (Λ : ℝ)
    (hmem : S.completeProp0 ∈ S.MSMSet0 Λ)
    (hbridge : S.candMean0 S.completeProp0 = S.Y0mean)
    (hbdd : BddBelow (S.candMean0 '' S.MSMSet0 Λ))
    (hbdd' : BddAbove (S.candMean0 '' S.MSMSet0 Λ)) :
    S.Y0mean ∈ Set.Icc (S.msmLower0 Λ) (S.msmUpper0 Λ) :=
  S.Ymean_mem_Icc false Λ hmem hbridge hbdd hbdd'

/-- Deprecated control-arm specialization of ambiguity-set monotonicity. -/
@[deprecated "Use MSMSet_mono false." (since := "2026-09-17")]
theorem MSMSet0_mono {Λ Λ' : ℝ} (hΛ : 1 ≤ Λ) (hΛΛ' : Λ ≤ Λ') :
    S.MSMSet0 Λ ⊆ S.MSMSet0 Λ' :=
  S.MSMSet_mono false hΛ hΛΛ'

/-- Deprecated control-arm specialization of upper-endpoint monotonicity. -/
@[deprecated "Use msmUpper_mono false." (since := "2026-09-17")]
theorem msmUpper0_mono {Λ Λ' : ℝ} (hΛ : 1 ≤ Λ) (hΛΛ' : Λ ≤ Λ')
    (hne : (S.candMean0 '' S.MSMSet0 Λ).Nonempty)
    (hbdd' : BddAbove (S.candMean0 '' S.MSMSet0 Λ')) :
    S.msmUpper0 Λ ≤ S.msmUpper0 Λ' :=
  S.msmUpper_mono false hΛ hΛΛ' hne hbdd'

/-- Deprecated control-arm specialization of lower-endpoint antitonicity. -/
@[deprecated "Use msmLower_anti false." (since := "2026-09-17")]
theorem msmLower0_anti {Λ Λ' : ℝ} (hΛ : 1 ≤ Λ) (hΛΛ' : Λ ≤ Λ')
    (hne : (S.candMean0 '' S.MSMSet0 Λ).Nonempty)
    (hbdd' : BddBelow (S.candMean0 '' S.MSMSet0 Λ')) :
    S.msmLower0 Λ' ≤ S.msmLower0 Λ :=
  S.msmLower_anti false hΛ hΛΛ' hne hbdd'

/-- Deprecated control-arm specialization of point identification at sensitivity one. -/
@[deprecated "Use MSMSet_one_eq false." (since := "2026-09-17")]
theorem MSMSet0_one_eq (etilde : P.Ω → ℝ)
    (hprop : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hmem : etilde ∈ S.MSMSet0 1) :
    ∀ᵐ ω ∂P.μ, etilde ω = S.propScore false ω :=
  S.MSMSet_one_eq false etilde hprop hmem

end POBackdoorSystem

end PO
end Causalean
