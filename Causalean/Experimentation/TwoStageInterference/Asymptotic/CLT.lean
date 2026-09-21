/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mixture transfer for a two-stage direct-effect CDF

Along a sequence of two-stage Hudgens–Halloran experiments (groups → ∞), the studentized
control-minus-treatment direct-effect contrast estimator has an unconditional Gaussian CDF limit
whenever the same limit holds uniformly for its conditional CDFs. This contrast is the negative of
the treatment-minus-control estimand used by Liu–Hudgens (2014). The argument here is only the
*mixture-lifting* step.
By the tower property of expectation, the joint (unconditional) law of any statistic is the
stage-1 average of its conditional law given the first-stage strategy selection `s`.  So the
unconditional studentized CDF equals the stage-1 expectation of the *conditional* studentized
CDF.  If the conditional CDFs converge to `Φ(t)` uniformly over selections `s` (with a vanishing
uniform bound `B n`), then averaging a uniformly-convergent family preserves the limit, giving
the unconditional `Φ(t)`.  That averaging is the entire content of this file.

The file provides two unconditional, reusable tools — the mixture-lifting lemma
`tendsto_E_of_uniformBound` (a uniformly-convergent family of design-functions has convergent
expectation) and the tower bridge `Pr_compound_eq_E_condPr` (a compound-design probability is the
stage-1 average of the stage-2 conditional probability) — and the direct-effect specialization
`directEffect_cdf_tendsto_of_uniform_conditional`, stated conditional on the uniform conditional-CDF
limit hypothesis `hcond`. It is not a formalization of Liu–Hudgens Proposition 5.1, because it
assumes rather than derives the conditional Gaussian limit.

`hcond` — the uniform conditional convergence of the within-selection studentized CDFs to `Φ` — is
now **discharged** in `CLTDischarge.lean` / `CLTDischargeMain.lean` from the independent-summands
Stein CLT of the design-based substrate (`prodDesign_clt`) together with strong homogeneity and
many-groups rate conditions, yielding the special-case `directEffect_clt_homogeneous`. This
mirrors how the Aronow–Samii layer first took `LocalDependenceCLT` as a premise before discharging
it; the lifting lemma and tower bridge below remain unconditional and reusable.
-/

module
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
public import Causalean.Experimentation.DesignBased.CompoundVariance
public import Causalean.Experimentation.DesignBased.EdgeVarianceBound
public import Causalean.Experimentation.DesignBased.GaussianCDF
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Direct-contrast conditional-to-unconditional CDF transfer

An unconditional CDF limit for the control-minus-treatment direct-effect contrast is obtained by
averaging uniformly convergent conditional laws across the first-stage strategy assignment. The
contrast is the negative of Liu–Hudgens' treatment-minus-control estimand.

The design-level lemmas are `FiniteDesign.tendsto_E_of_uniformBound`, which says expectations
preserve a uniform limit over finite assignment spaces, and `FiniteDesign.Pr_compound_eq_E_condPr`,
the tower bridge rewriting a compound-design probability as the stage-1 average of stage-2
conditional probabilities.

The theorem `directEffect_cdf_tendsto_of_uniform_conditional` is a mixture-transfer result: given
the uniform conditional studentized-CDF limit `hcond`, the joint-design CDF converges to
`stdNormalCdf t`. It does not derive the conditional limit required in Liu–Hudgens Proposition 5.1.
-/

public section

open scoped BigOperators Topology
open Finset Filter

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

/-- **Mixture-lifting lemma.** If a sequence of design random variables `F n : Ω n → ℝ` converges
to a constant `L` *uniformly* over the assignment space — `|F n s − L| ≤ B n` for every `s`, with
`B n → 0` — then their expectations converge to `L`: `(D n).E (F n) → L`.  Averaging a uniformly
convergent family preserves the limit, since the expectation of a `B n`-bounded deviation is itself
`B n`-bounded.  This is the abstract content of the two-stage mixture-lifting argument: the joint
law is the stage-1 average of conditional laws, and a uniform conditional limit lifts to the
average. -/
theorem tendsto_E_of_uniformBound {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (D : ∀ n, FiniteDesign (Ω n)) (F : ∀ n, Ω n → ℝ) (L : ℝ) (B : ℕ → ℝ)
    (hbound : ∀ n s, |F n s - L| ≤ B n) (hB : Tendsto B atTop (𝓝 0)) :
    Tendsto (fun n => (D n).E (F n)) atTop (𝓝 L) := by
  -- It suffices that `|(D n).E (F n) − L| → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Squeeze `‖(D n).E (F n) − L‖` between `0` and `B n → 0`.
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hB
  -- `(D n).E (F n) − L = (D n).E (fun s => F n s − L)` by linearity (`E_sub` + `E_const`).
  have hrecenter : (D n).E (F n) - L = (D n).E (fun s => F n s - L) := by
    rw [(D n).E_sub (F n) (fun _ => L), (D n).E_const]
  -- `|(D n).E (fun s => F n s − L)| ≤ B n` by the pointwise bound `hbound`.
  rw [Real.norm_eq_abs, hrecenter]
  exact (D n).abs_E_le (fun s => hbound n s)

/-- **Tower bridge for probabilities.** Under the two-stage `compound` design, the unconditional
probability of an event `P` equals the stage-1 expectation of its stage-2 conditional probability:

    (compound D₁ D₂).Pr P = D₁.E (fun s => (prodDesign (D₂ s)).Pr (fun w => P (s, w))).

This is the tower property of expectation (`E_compound_tower`) applied to the indicator of `P`,
together with the observation that the indicator of `P` at `(s, w)` is the indicator of the
fiber event `fun w => P (s, w)` at `w`. -/
lemma Pr_compound_eq_E_condPr {Ω₁ ι : Type*} [Fintype Ω₁] [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → ∀ i, FiniteDesign (α i))
    (P : (Ω₁ × ∀ i, α i) → Prop) [DecidablePred P] :
    (compound D₁ D₂).Pr P = D₁.E (fun s => (prodDesign (D₂ s)).Pr (fun w => P (s, w))) := by
  -- `Pr P = E (ind P)`, then push `E` through the tower.
  rw [FiniteDesign.Pr, E_compound_tower]
  -- The inner stage-2 expectation of `ind P (s, ·)` is exactly the conditional probability.
  apply D₁.E_congr
  intro s
  rw [FiniteDesign.Pr]
  -- `ind P (s, w) = ind (fun w => P (s, w)) w` definitionally (both `if … then 1 else 0`).
  apply (prodDesign (D₂ s)).E_congr
  intro w
  rfl

end FiniteDesign

end DesignBased

namespace TwoStageInterference

open DesignBased

open Classical in
/-- **Conditional-to-unconditional CDF transfer for the direct-effect statistic.** Along [a
sequence of two-stage Hudgens–Halloran experiments](hyp:Exp), at [a fixed threshold `t`](hyp:t),
let [`stud n` be the studentized statistic `(D̂E − DE̅)/√directVar` for the
control-minus-treatment direct-effect contrast](hyp:stud,_hstud), and let [`cond n s` be the
within-selection stage-two product design](hyp:cond,hcondDef). If [the conditional studentized CDFs
at `t` approach `Φ(t)` uniformly over selections, with a vanishing uniform bound](hyp:hcond), then
[the unconditional joint-design studentized CDF at `t` approaches `Φ(t)`](goal). The contrast is
the negative of Liu–Hudgens' treatment-minus-control estimand, and the conditional Gaussian limit
is an assumption rather than a conclusion.

    (Exp n).jointD.Pr (fun sw => stud n sw ≤ t) → Φ(t).

Proof (mixture lifting): the tower bridge `Pr_compound_eq_E_condPr` rewrites the joint probability
as the stage-1 average of the conditional probabilities `(cond n s).Pr (fun w => stud n (s, w) ≤
t)`; the mixture-lifting lemma `tendsto_E_of_uniformBound` then lifts the uniform conditional limit
`hcond` to the average.

The companion `CLTDischarge.lean` and `CLTDischargeMain.lean` files derive `hcond` only in a strong
homogeneous special case. -/
theorem directEffect_cdf_tendsto_of_uniform_conditional (Exp : ℕ → LHExperiment) (t : ℝ)
    (stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ)
    (_hstud : ∀ n sw,
      stud n sw = ((Exp n).estD sw - (Exp n).DEbar) / Real.sqrt ((Exp n).directVar))
    (cond : ∀ n, StratAssign (Exp n).ι →
      FiniteDesign (∀ i, Fin ((Exp n).gsize i) → Bool))
    (hcondDef : ∀ n s, cond n s
      = prodDesign (fun i => if s i then (Exp n).ψ i else (Exp n).φ i))
    (hcond : ∃ B, Tendsto B atTop (𝓝 0) ∧
      ∀ n s, |(cond n s).Pr (fun w => stud n (s, w) ≤ t) - stdNormalCdf t| ≤ B n) :
    Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ t)) atTop
      (𝓝 (stdNormalCdf t)) := by
  obtain ⟨B, hB, hbound⟩ := hcond
  -- Rewrite each unconditional CDF as the stage-1 average of conditional CDFs.
  have hrw : ∀ n, (Exp n).jointD.Pr (fun sw => stud n sw ≤ t)
      = (Exp n).D₁.E (fun s => (cond n s).Pr (fun w => stud n (s, w) ≤ t)) := by
    intro n
    rw [LHExperiment.jointD, jointDesign, FiniteDesign.Pr_compound_eq_E_condPr]
    apply (Exp n).D₁.E_congr
    intro s
    rw [hcondDef n s]
  simp_rw [hrw]
  -- Apply the mixture-lifting lemma with `F n s := (cond n s).Pr (…)`, `L := Φ(t)`, bound `B`.
  exact FiniteDesign.tendsto_E_of_uniformBound
    (fun n => (Exp n).D₁)
    (fun n s => (cond n s).Pr (fun w => stud n (s, w) ≤ t))
    (stdNormalCdf t) B hbound hB

end TwoStageInterference
end Experimentation
end Causalean
