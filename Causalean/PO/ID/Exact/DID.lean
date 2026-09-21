/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-period Difference-in-Differences ATT identification

Implements def:po-did-system, def:po-did-assumptions, and prop:po-did-att from
Basic Concepts.tex.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Two-Period Difference-in-Differences

This file formalizes two-period difference-in-differences identification of the
average treatment effect on the treated. It packages the treatment and outcome
variables, the parallel-trends assumptions, and the resulting observable
contrast.

The proof works at the event-conditional-mean level: it needs consistency, no
anticipation, parallel trends, positivity of treated and control groups, and
integrability of the counterfactual outcomes that enter the DID contrast. The
main theorem `att_did` identifies the treated-group mean counterfactual contrast
with the observed treated-minus-control difference in outcome changes. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO

open MeasureTheory

/-- A two-period DID system packages [a treatment node](hyp:D) whose value space is
[identified with the booleans](hyp:hDbool), together with [a pre-period outcome
node](hyp:Y₀) and [a post-period outcome node](hyp:Y₁) each of whose value spaces is
[identified with the real line](hyp:hY0real,hY1real); the treatment node is required
to be [distinct from the pre-period outcome node](hyp:hDY0) and [distinct from the
post-period outcome node](hyp:hDY1). -/
structure PODIDSystem (P : POSystem) where
  D : P.V
  Y₀ : P.V
  Y₁ : P.V
  hDbool : P.X D ≃ᵐ Bool
  hY0real : P.X Y₀ ≃ᵐ ℝ
  hY1real : P.X Y₁ ≃ᵐ ℝ
  hDY0 : D ≠ Y₀
  hDY1 : D ≠ Y₁

namespace PODIDSystem

variable {P : POSystem} (S : PODIDSystem P)

/-- The [treatment variable used in two-period DID](goal) represents [the system's
treatment](hyp:S) [as the treated and control arms](step:1). -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- The [baseline outcome variable](goal) in [a two-period DID system](hyp:S) [records
the real-valued outcome before treatment](step:1). -/
def y0Var : POVar P ℝ := ⟨S.Y₀, S.hY0real⟩

/-- The [follow-up outcome variable](goal) in [a two-period DID system](hyp:S) [records
the real-valued outcome after treatment](step:1). -/
def y1Var : POVar P ℝ := ⟨S.Y₁, S.hY1real⟩

/-- The [baseline potential outcome](goal) in [a two-period DID system](hyp:S)
[records what each unit's pre-period outcome would be under the selected arm](step:1);
[the arm](hyp:d) is useful for stating and testing no anticipation. -/
noncomputable def Y0ofD (d : Bool) : P.Ω → ℝ := S.y0Var.cfUnder S.dVar d

/-- The [follow-up potential outcome](goal) in [a two-period DID system](hyp:S)
[records what each unit's post-period outcome would be under the selected arm](step:1),
with [that arm](hyp:d) defining the causal contrast of interest. -/
noncomputable def Y1ofD (d : Bool) : P.Ω → ℝ := S.y1Var.cfUnder S.dVar d

/-- The [observed treatment assignment](goal) in [a two-period DID system](hyp:S)
[records whether each unit belongs to the treated or control group](step:1). -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- The [observed baseline outcome](goal) in [a two-period DID system](hyp:S) [records
each unit's pre-treatment response](step:1). -/
noncomputable def factualY₀ : P.Ω → ℝ := S.y0Var.factual

/-- The [observed follow-up outcome](goal) in [a two-period DID system](hyp:S) [records
each unit's post-treatment response](step:1). -/
noncomputable def factualY₁ : P.Ω → ℝ := S.y1Var.factual

/-- The [observed treatment group](goal) in [a two-period DID system](hyp:S) [collects
the units assigned to the selected arm](step:1), with [the arm](hyp:d) distinguishing
treated from control units. -/
def dEvent (d : Bool) : Set P.Ω := S.dVar.event d

/-- In [a two-period DID system](hyp:S), [the baseline potential outcome under a fixed
arm](hyp:d) is [measurable, so group-conditional baseline means are well-defined](goal). -/
@[fun_prop]
lemma measurable_Y0ofD (d : Bool) : Measurable (S.Y0ofD d) :=
  S.y0Var.measurable_cfUnder S.dVar d

/-- In [a two-period DID system](hyp:S), [the follow-up potential outcome under a fixed
arm](hyp:d) is [measurable, so group-conditional follow-up means are well-defined](goal). -/
@[fun_prop]
lemma measurable_Y1ofD (d : Bool) : Measurable (S.Y1ofD d) :=
  S.y1Var.measurable_cfUnder S.dVar d

/-- [Treatment assignment in a two-period DID system](hyp:S) is [measurable, so treated
and control groups form valid conditioning events](goal). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- [The observed baseline outcome in a two-period DID system](hyp:S) is [measurable,
so its treated and control means can enter the DID contrast](goal). -/
@[fun_prop]
lemma measurable_factualY₀ : Measurable S.factualY₀ := S.y0Var.measurable_factual

/-- [The observed follow-up outcome in a two-period DID system](hyp:S) is [measurable,
so its treated and control means can enter the DID contrast](goal). -/
@[fun_prop]
lemma measurable_factualY₁ : Measurable S.factualY₁ := S.y1Var.measurable_factual

/-- In [a two-period DID system](hyp:S), [membership in either observed treatment
arm](hyp:d) defines [a measurable event suitable for group means](goal). -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.dVar.measurableSet_event _ (measurableSet_singleton _)

/-- The [average treatment effect on the treated](goal) in [a two-period DID
system](hyp:S) [is the treated-group mean difference between treated and untreated
follow-up potential outcomes](step:1). -/
noncomputable def ATT : ℝ :=
  normalizedRestrictedIntegral P.μ (S.dEvent true) (fun ω => S.Y1ofD true ω - S.Y1ofD false ω)

/-- Assumptions for two-period difference-in-differences identification of the
ATT (`def:po-did-assumptions`). In words: [the observed outcomes coincide with the
realized-arm potential outcomes](hyp:consistency); [in the pre-period the treated and
control groups have the same potential outcome regardless of treatment](hyp:noAnticipation);
and [absent treatment the two groups would have changed in parallel between the two
periods](hyp:parallelTrends). [The treated group](hyp:posTrue_ne_zero) and [the control
group](hyp:posFalse_ne_zero) each occur with positive probability, and [the control
pre-period outcome](hyp:intY0ofD_false), [the control post-period
outcome](hyp:intY1ofD_false), and [the treated post-period
outcome](hyp:intY1ofD_true) are integrable, so the group-conditional means are
well-defined and finite. -/
structure Assumptions (S : PODIDSystem P) : Prop where
  /-- Consistency (SUTVA): the observed outcome equals the potential outcome of
  the realized treatment arm. -/
  consistency : P.Consistency
  /-- No anticipation: in the pre-period the potential outcome does not depend on
  the (future) treatment, so `Y₀(1) = Y₀(0)` a.s. -/
  noAnticipation : ∀ᵐ ω ∂P.μ, S.Y0ofD true ω = S.Y0ofD false ω
  /-- Parallel trends: the average untreated change from the pre- to the
  post-period is the same in the treated group as in the control group. -/
  parallelTrends :
    normalizedRestrictedIntegral P.μ (S.dEvent true)
        (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
      = normalizedRestrictedIntegral P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
  /-- The treated group has positive probability, so its group-mean is defined.
  (Finiteness `μ ≠ ⊤` is automatic: `P.μ` is a probability measure.) -/
  posTrue_ne_zero : P.μ (S.dEvent true) ≠ 0
  /-- The control group has positive probability, so its group-mean is defined. -/
  posFalse_ne_zero : P.μ (S.dEvent false) ≠ 0
  /-- Integrability of the control pre-period potential outcome `Y₀(0)`. -/
  intY0ofD_false : Integrable (S.Y0ofD false) P.μ
  /-- Integrability of the control post-period potential outcome `Y₁(0)`. -/
  intY1ofD_false : Integrable (S.Y1ofD false) P.μ
  /-- Integrability of the treated post-period potential outcome `Y₁(1)`. -/
  intY1ofD_true : Integrable (S.Y1ofD true) P.μ

/-- Pointwise equality on the event `{D = d}`: `factualY₁ - factualY₀` equals
`Y₁(d) - Y₀(d)`. -/
private lemma factualDiff_eq_cfDiff_on_dEvent (hC : P.Consistency) (d : Bool) :
    ∀ ω ∈ S.dEvent d,
      S.factualY₁ ω - S.factualY₀ ω = S.Y1ofD d ω - S.Y0ofD d ω := by
  intro ω hω
  have h1 : S.Y1ofD d ω = S.factualY₁ ω :=
    POVar.cf_eq_factual_on_event hC S.y1Var S.dVar d S.hDY1.symm hω
  have h0 : S.Y0ofD d ω = S.factualY₀ ω :=
    POVar.cf_eq_factual_on_event hC S.y0Var S.dVar d S.hDY0.symm hω
  rw [h1, h0]

/-- In [a two-period DID system](hyp:S), under [the identifying assumptions —
consistency, no-anticipation,
parallel trends, and positive-probability, integrable treatment and control
groups](hyp:hA), [the average treatment effect on the treated equals the
difference between the treated group's mean pre-to-post outcome change and
the control group's mean pre-to-post outcome change](goal). -/
theorem att_did (hA : S.Assumptions) :
    S.ATT
      = normalizedRestrictedIntegral P.μ (S.dEvent true)
          (fun ω => S.factualY₁ ω - S.factualY₀ ω)
        - normalizedRestrictedIntegral P.μ (S.dEvent false)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) := by
  -- Step 1: by no anticipation, `Y₁(1) - Y₁(0)` rewrites a.e. as
  -- `(Y₁(1) - Y₀(1)) - (Y₁(0) - Y₀(0))`.
  have hAE : (fun ω => S.Y1ofD true ω - S.Y1ofD false ω)
      =ᵐ[P.μ] fun ω =>
        (S.Y1ofD true ω - S.Y0ofD true ω) -
          (S.Y1ofD false ω - S.Y0ofD false ω) := by
    refine hA.noAnticipation.mono (fun ω hω => ?_)
    change S.Y1ofD true ω - S.Y1ofD false ω
      = (S.Y1ofD true ω - S.Y0ofD true ω) - (S.Y1ofD false ω - S.Y0ofD false ω)
    rw [hω]; ring
  -- Step 2: split via additivity.  Use the `normalizedRestrictedIntegral` definition and
  -- `integral_congr_ae` + `integral_sub`.
  have hATT_split :
      S.ATT
        = normalizedRestrictedIntegral P.μ (S.dEvent true)
            (fun ω => S.Y1ofD true ω - S.Y0ofD true ω)
          - normalizedRestrictedIntegral P.μ (S.dEvent true)
              (fun ω => S.Y1ofD false ω - S.Y0ofD false ω) := by
    unfold ATT
    rw [eventCondExp_congr_ae P.μ (S.dEvent true) (ae_restrict_of_ae hAE)]
    -- `Y0ofD true` is integrable via a.e. equality with `Y0ofD false`.
    have hY0true_int : Integrable (S.Y0ofD true) P.μ :=
      hA.intY0ofD_false.congr (hA.noAnticipation.mono (fun _ h => h.symm))
    exact eventCondExp_sub P.μ (S.dEvent true)
      (hA.intY1ofD_true.sub hY0true_int).integrableOn
      (hA.intY1ofD_false.sub hA.intY0ofD_false).integrableOn
  -- Step 3: on `dEvent true`, consistency gives
  -- `Y₁(1) - Y₀(1) = factualY₁ - factualY₀`.
  have h_first :
      normalizedRestrictedIntegral P.μ (S.dEvent true)
          (fun ω => S.Y1ofD true ω - S.Y0ofD true ω)
        = normalizedRestrictedIntegral P.μ (S.dEvent true)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) :=
    (eventCondExp_congr_on P.μ (S.measurableSet_dEvent true)
      (fun ω hω => (S.factualDiff_eq_cfDiff_on_dEvent hA.consistency true ω hω).symm))
  -- Step 4: parallel trends rewrites the second term to condition on `D=0`.
  have h_pt : normalizedRestrictedIntegral P.μ (S.dEvent true)
        (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
      = normalizedRestrictedIntegral P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω) := hA.parallelTrends
  -- Step 5: on `dEvent false`, consistency gives
  -- `Y₁(0) - Y₀(0) = factualY₁ - factualY₀`.
  have h_second :
      normalizedRestrictedIntegral P.μ (S.dEvent false)
          (fun ω => S.Y1ofD false ω - S.Y0ofD false ω)
        = normalizedRestrictedIntegral P.μ (S.dEvent false)
            (fun ω => S.factualY₁ ω - S.factualY₀ ω) :=
    eventCondExp_congr_on P.μ (S.measurableSet_dEvent false)
      (fun ω hω => (S.factualDiff_eq_cfDiff_on_dEvent hA.consistency false ω hω).symm)
  rw [hATT_split, h_first, h_pt, h_second]

end PODIDSystem

end PO
end Causalean
