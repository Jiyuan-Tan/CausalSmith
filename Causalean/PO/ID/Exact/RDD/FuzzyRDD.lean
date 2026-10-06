/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fuzzy regression-discontinuity identification

Implements the regression-representative formal counterpart of
def:po-fuzzy-rdd-system, def:po-fuzzy-rdd-assumptions, and prop:po-fuzzy-rdd
from Basic Concepts.tex.

The textbook fuzzy RDD estimand is the cutoff-local LATE.  In this file, as in
`SharpRDD.lean`, the formal target is stated using chosen regression-function
representatives:

    τ_FRD(c) = (μ_Y(1,c) - μ_Y(0,c)) / (μ_D(1,c) - μ_D(0,c)).

Here `μ_Y(z, ·)` represents `E[Y(D(z)) | X = ·]` and `μ_D(z, ·)` represents
`E[D(z) | X = ·]`.  Local exclusion is encoded by the available outcome
potential outcomes `Y(d)`.  The LATE bridge in this file assumes global a.s.
monotonicity, `D(0) ≤ D(1)`, which is stronger than the cutoff-neighborhood
monotonicity used in some textbook fuzzy RDD statements; the
regression-representative Wald identity itself does not use monotonicity
directly.

Two shared helper modules supply the heavy lifting:

* `Causalean.PO.Analysis.Regression` provides the `IsRegressionFunction` predicate and its
  pushforward-integrability lemma.
* `Causalean.PO.ID.Exact.RDD.RDDLimits` provides the one-sided limit
  identification engine (`oneSidedLimit_eq_right`/`_left`) used to convert
  a.e. agreement of observable and latent regressions on a half-line into
  pointwise equality of one-sided limits at the cutoff.
-/

module
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Analysis.Regression
public import Causalean.PO.ID.Exact.RDD.RDDLimits
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Topology.Order.Basic
public import Causalean.Tactic.Attr

/-! # Fuzzy Regression Discontinuity

This file identifies the fuzzy regression-discontinuity Wald ratio from one-sided outcome and
treatment regressions under consistency, deterministic cutoff eligibility, continuity, local
support, and a nonzero first stage. A separate bridge equates that ratio with a cutoff
complier-effect representative when treatment is globally monotone in eligibility; the bundled
local monotonicity assumption alone is not used for that stronger equality. -/

@[expose] public section

namespace Causalean
namespace PO

open Filter MeasureTheory
open scoped Topology

/-- **Data layout for fuzzy regression discontinuity.** The system records [a real-valued
running variable](hyp:Xvar), [a binary cutoff-eligibility indicator](hyp:Zvar), [binary treatment
take-up](hyp:Dvar), [a real outcome](hyp:Yvar), and [a cutoff](hyp:c), with [the required node
distinctness](hyp:hYD,hZD,hDY). The threshold rule for eligibility, discontinuous first stage,
continuity, support, and monotonicity conditions are imposed separately by `Assumptions`; they
are not properties of this bare variable bundle. -/
structure POFuzzyRDDSystem (P : POSystem) where
  /-- Running (forcing) variable `X`. -/
  Xvar : POVar P ℝ
  /-- Above-cutoff indicator `Z = 1{X ≥ c}`. -/
  Zvar : POVar P Bool
  /-- Binary treatment `D`. -/
  Dvar : POVar P Bool
  /-- Real outcome `Y`. -/
  Yvar : POVar P ℝ
  /-- Cutoff value of the running variable. -/
  c : ℝ
  hYD : Yvar.v ≠ Dvar.v
  hZD : Zvar.v ≠ Dvar.v
  hDY : Dvar.v ≠ Yvar.v

namespace POFuzzyRDDSystem

variable {P : POSystem} (S : POFuzzyRDDSystem P)

/-- The [observed running variable](goal) in [a fuzzy regression-discontinuity
design](hyp:S) [records each unit's realized forcing score](step:1), whose position around
the cutoff determines eligibility. -/
noncomputable def factualX : P.Ω → ℝ := S.Xvar.factual

/-- The [observed cutoff-eligibility indicator](goal) in [a fuzzy
regression-discontinuity design](hyp:S) [records whether each unit lies above the
cutoff](step:1), serving as the instrument for treatment take-up. -/
noncomputable def factualZ : P.Ω → Bool := S.Zvar.factual

/-- The [observed treatment](goal) in [a fuzzy regression-discontinuity design](hyp:S)
[records each unit's realized take-up](step:1), which may differ from cutoff eligibility. -/
noncomputable def factualD : P.Ω → Bool := S.Dvar.factual

/-- The [observed outcome](goal) in [a fuzzy regression-discontinuity design](hyp:S)
[records each unit's realized real-valued response](step:1). -/
noncomputable def factualY : P.Ω → ℝ := S.Yvar.factual

/-- The [eligibility-specific potential treatment](goal) in [a fuzzy
regression-discontinuity design](hyp:S) [records whether each unit would take treatment
under the selected eligibility state](step:1), with [that state](hyp:z) indexing the first
stage. -/
noncomputable def DofZ (z : Bool) : P.Ω → Bool :=
  S.Dvar.cfUnder S.Zvar z

/-- The [treatment-specific potential outcome](goal) in [a fuzzy
regression-discontinuity design](hyp:S) [records each unit's response if treatment were
set to the selected level](step:1), with [that level](hyp:d) defining the causal outcome
contrast. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ :=
  S.Yvar.cfUnder S.Dvar d

/-- The [outcome induced by an eligibility state](goal) in [a fuzzy
regression-discontinuity design](hyp:S) [selects each unit's treated or untreated potential
outcome according to the treatment that eligibility would induce](step:1), with [the
eligibility state](hyp:z) indexing the reduced form. -/
noncomputable def YofDofZ (z : Bool) : P.Ω → ℝ :=
  fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω

/-- The potential outcome under the treatment that an instrument value induces sends a unit to
that unit's treated potential outcome when the induced treatment is one, and to its untreated
potential outcome otherwise. -/
@[causal_defs_simps]
lemma YofDofZ_def (z : Bool) :
    S.YofDofZ z = fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω :=
  rfl

/-- The [complier-weighted potential-outcome contrast](goal) in [a fuzzy
regression-discontinuity design](hyp:S) [equals the individual treatment effect for
compliers and zero for everyone else](step:1).

Y-difference weighted by the complier indicator `1_{D(1)=1, D(0)=0}`.
Equals `Y(D(1)) − Y(D(0))` a.e. under monotonicity; used in the LATE bridge. -/
noncomputable def YdiffComplier : P.Ω → ℝ :=
  fun ω => (S.YofD true ω - S.YofD false ω) *
    if S.DofZ true ω = true ∧ S.DofZ false ω = false then 1 else 0

/-- [The running variable in a fuzzy regression-discontinuity design](hyp:S) is
[measurable, so cutoff neighborhoods and its marginal law are valid](goal). -/
@[fun_prop]
lemma measurable_factualX : Measurable S.factualX := S.Xvar.measurable_factual
/-- [The eligibility indicator in a fuzzy regression-discontinuity design](hyp:S) is
[measurable, so above- and below-cutoff groups form valid events](goal). -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.Zvar.measurable_factual
/-- [Treatment take-up in a fuzzy regression-discontinuity design](hyp:S) is
[measurable, so its discontinuity at the cutoff can be represented by a regression](goal). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.Dvar.measurable_factual
/-- [The outcome in a fuzzy regression-discontinuity design](hyp:S) is [measurable,
so its discontinuity at the cutoff can be represented by a regression](goal). -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.Yvar.measurable_factual

/-- In [a fuzzy regression-discontinuity design](hyp:S), [potential treatment under an
eligibility state](hyp:z) is [measurable, so the latent first-stage regression is
well-defined](goal). -/
@[fun_prop]
lemma measurable_DofZ (z : Bool) : Measurable (S.DofZ z) :=
  S.Dvar.measurable_cfUnder S.Zvar z

/-- In [a fuzzy regression-discontinuity design](hyp:S), [the potential outcome under a
treatment level](hyp:d) is [measurable, so latent outcome regressions are
well-defined](goal). -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.Yvar.measurable_cfUnder S.Dvar d

/-- In [a fuzzy regression-discontinuity design](hyp:S), [the outcome induced by an
eligibility state](hyp:z) is [measurable, so its reduced-form regression is
well-defined](goal). -/
@[fun_prop]
lemma measurable_YofDofZ (z : Bool) : Measurable (S.YofDofZ z) := by
  simp only [causal_defs_simps]
  exact Measurable.ite (S.measurable_DofZ z (MeasurableSet.singleton true))
    (S.measurable_YofD true) (S.measurable_YofD false)

/-- [The complier-weighted treatment effect in a fuzzy regression-discontinuity
design](hyp:S) is [measurable, so it admits a cutoff regression representative](goal). -/
@[fun_prop]
lemma measurable_YdiffComplier : Measurable S.YdiffComplier := by
  unfold YdiffComplier
  apply Measurable.mul
  · exact (S.measurable_YofD true).sub (S.measurable_YofD false)
  · exact Measurable.ite
      ((S.measurable_DofZ true (MeasurableSet.singleton true)).inter
        (S.measurable_DofZ false (MeasurableSet.singleton false)))
      measurable_const measurable_const

/-- The [observed eligibility group](goal) in [a fuzzy regression-discontinuity
design](hyp:S) [collects units with the selected cutoff-eligibility state](step:1), with
[that state](hyp:z) distinguishing the two sides. -/
def zEvent (z : Bool) : Set P.Ω := S.Zvar.event z

/-- In [a fuzzy regression-discontinuity design](hyp:S), [an observed eligibility
state](hyp:z) defines [a measurable event suitable for consistency arguments](goal). -/
lemma measurableSet_zEvent (z : Bool) : MeasurableSet (S.zEvent z) :=
  by simpa [zEvent] using S.Zvar.measurableSet_event z

/-- **Fuzzy RDD assumption bundle.** For a fuzzy regression-discontinuity system, this packages
[consistency (SUTVA)](hyp:consistency), [deterministic cutoff eligibility: the above-cutoff
indicator agrees almost surely with whether the running variable has crossed the
cutoff](hyp:cutoffEligibility), and [cutoff-neighborhood monotonicity: near the cutoff, a unit who
would take treatment under the untreated instrument value would also take it under the treated
instrument value](hyp:monotonicity). It supplies latent treatment and outcome regression
representatives `muD`/`muY` and observable regression representatives `nuD`/`nuY`, each
[certified as a genuine regression function of the corresponding response on the running
variable](hyp:muD_isReg,muY_isReg,nuD_isReg,nuY_isReg), with the latent representatives
[continuous at the cutoff](hyp:muD_continuousAt,muY_continuousAt); it also assumes [the running
variable has positive local probability mass on both sides of the
cutoff](hyp:support_right,support_left), and that [the observable treatment
regression](hyp:nuD_right_limit_exists,nuD_left_limit_exists) and [outcome regression have
well-defined one-sided limits at the cutoff](hyp:nuY_right_limit_exists,nuY_left_limit_exists).
Finally, a complier outcome-difference representative `mu_Ydiff_complier` is [likewise a
regression function](hyp:mu_Ydiff_complier_isReg) that is [continuous at the
cutoff](hyp:mu_Ydiff_complier_continuousAt), and [the first-stage treatment-take-up jump at the
cutoff is nonzero](hyp:firstStageJump).

The classical local-exclusion clause is represented by using only `Y(d)`
potential outcomes, rather than separate direct responses `Y(z,d)`.  The
monotonicity field is local to a neighborhood of the cutoff, matching the
standard fuzzy-RDD condition.  The final field phrases the first stage as a
nonzero jump of the latent treatment regression representatives at `c`; by the
limit-identification lemmas below, this is equivalent to the nonzero denominator
in the observable Wald ratio. -/
structure Assumptions (S : POFuzzyRDDSystem P) where
  consistency : P.Consistency
  cutoffEligibility : ∀ᵐ ω ∂P.μ, S.factualZ ω ↔ S.c ≤ S.factualX ω
  /-- In a neighborhood of the cutoff, units who would take treatment below the
  cutoff would also take treatment above the cutoff, up to a null set. -/
  monotonicity :
    ∃ ε > (0 : ℝ), ∀ᵐ ω ∂P.μ,
      |S.factualX ω - S.c| < ε → S.DofZ false ω = true → S.DofZ true ω = true
  muD : Bool → ℝ → ℝ
  muY : Bool → ℝ → ℝ
  nuD : ℝ → ℝ
  nuY : ℝ → ℝ
  muD_isReg : ∀ z, IsRegressionFunction P.μ S.factualX
    (fun ω => ((S.DofZ z ω).toNat : ℝ)) (muD z)
  muY_isReg : ∀ z, IsRegressionFunction P.μ S.factualX (S.YofDofZ z) (muY z)
  nuD_isReg : IsRegressionFunction P.μ S.factualX
    (fun ω => ((S.factualD ω).toNat : ℝ)) nuD
  nuY_isReg : IsRegressionFunction P.μ S.factualX S.factualY nuY
  muD_continuousAt : ∀ z, ContinuousAt (muD z) S.c
  muY_continuousAt : ∀ z, ContinuousAt (muY z) S.c
  support_right : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo S.c (S.c + ε)) ≠ 0
  support_left : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo (S.c - ε) S.c) ≠ 0
  nuD_right_limit_exists : ∃ L : ℝ, Tendsto nuD (𝓝[>] S.c) (𝓝 L)
  nuD_left_limit_exists : ∃ L : ℝ, Tendsto nuD (𝓝[<] S.c) (𝓝 L)
  nuY_right_limit_exists : ∃ L : ℝ, Tendsto nuY (𝓝[>] S.c) (𝓝 L)
  nuY_left_limit_exists : ∃ L : ℝ, Tendsto nuY (𝓝[<] S.c) (𝓝 L)
  mu_Ydiff_complier : ℝ → ℝ
  mu_Ydiff_complier_isReg : IsRegressionFunction P.μ S.factualX
    S.YdiffComplier mu_Ydiff_complier
  mu_Ydiff_complier_continuousAt : ContinuousAt mu_Ydiff_complier S.c
  firstStageJump : muD true S.c - muD false S.c ≠ 0

/-- The [cutoff fuzzy-RDD Wald estimand](goal) for [a fuzzy
regression-discontinuity design](hyp:S) under [the identifying assumptions](hyp:hA)
[divides the eligibility-induced outcome-regression jump by the first-stage treatment
jump](step:1). -/
noncomputable def tau_FRD (hA : S.Assumptions) : ℝ :=
  (hA.muY true S.c - hA.muY false S.c) /
    (hA.muD true S.c - hA.muD false S.c)

/-- The [cutoff complier-effect ratio](goal) for [a fuzzy regression-discontinuity
design](hyp:S) under [the identifying assumptions](hyp:hA) [divides the
complier-weighted outcome-difference regression by the latent first-stage jump](step:1).

Cutoff-local complier-effect ratio in regression-representative form.
It divides the complier outcome-difference representative at the cutoff by the
first-stage jump; `tau_late_identification_of_globalMonotonicity` connects this
ratio to `tau_FRD` under the fuzzy-RDD assumptions and a separate global
no-defiers condition. -/
noncomputable def tau_LATE (hA : S.Assumptions) : ℝ :=
  hA.mu_Ydiff_complier S.c / (hA.muD true S.c - hA.muD false S.c)

/-- The [right-hand treatment-regression limit](goal) for [a fuzzy
regression-discontinuity design](hyp:S) under [the identifying assumptions](hyp:hA)
[selects the take-up level approached from above the cutoff](step:1).

The right-hand treatment limit is the selected limit at the cutoff of the
observable treatment regression as the running variable approaches from above. -/
noncomputable def nuD_right_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuD_right_limit_exists

/-- The [left-hand treatment-regression limit](goal) for [a fuzzy
regression-discontinuity design](hyp:S) under [the identifying assumptions](hyp:hA)
[selects the take-up level approached from below the cutoff](step:1).

The left-hand treatment limit is the selected limit at the cutoff of the
observable treatment regression as the running variable approaches from below. -/
noncomputable def nuD_left_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuD_left_limit_exists

/-- The [right-hand outcome-regression limit](goal) for [a fuzzy
regression-discontinuity design](hyp:S) under [the identifying assumptions](hyp:hA)
[selects the outcome level approached from above the cutoff](step:1).

The right-hand outcome limit is the selected limit at the cutoff of the
observable outcome regression as the running variable approaches from above. -/
noncomputable def nuY_right_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuY_right_limit_exists

/-- The [left-hand outcome-regression limit](goal) for [a fuzzy
regression-discontinuity design](hyp:S) under [the identifying assumptions](hyp:hA)
[selects the outcome level approached from below the cutoff](step:1).

The left-hand outcome limit is the selected limit at the cutoff of the
observable outcome regression as the running variable approaches from below. -/
noncomputable def nuY_left_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nuY_left_limit_exists

/-- Under [the fuzzy-RDD assumptions](hyp:hA), [the selected right-hand treatment
limit for the design](hyp:S) [is attained by the observed take-up regression as the
running variable approaches the cutoff from above](goal). -/
lemma tendsto_nuD_right_limit (hA : S.Assumptions) :
    Tendsto hA.nuD (𝓝[>] S.c) (𝓝 (S.nuD_right_limit hA)) :=
  Classical.choose_spec hA.nuD_right_limit_exists

/-- Under [the fuzzy-RDD assumptions](hyp:hA), [the selected left-hand treatment
limit for the design](hyp:S) [is attained by the observed take-up regression as the
running variable approaches the cutoff from below](goal). -/
lemma tendsto_nuD_left_limit (hA : S.Assumptions) :
    Tendsto hA.nuD (𝓝[<] S.c) (𝓝 (S.nuD_left_limit hA)) :=
  Classical.choose_spec hA.nuD_left_limit_exists

/-- Under [the fuzzy-RDD assumptions](hyp:hA), [the selected right-hand outcome limit
for the design](hyp:S) [is attained by the observed outcome regression as the running
variable approaches the cutoff from above](goal). -/
lemma tendsto_nuY_right_limit (hA : S.Assumptions) :
    Tendsto hA.nuY (𝓝[>] S.c) (𝓝 (S.nuY_right_limit hA)) :=
  Classical.choose_spec hA.nuY_right_limit_exists

/-- Under [the fuzzy-RDD assumptions](hyp:hA), [the selected left-hand outcome limit
for the design](hyp:S) [is attained by the observed outcome regression as the running
variable approaches the cutoff from below](goal). -/
lemma tendsto_nuY_left_limit (hA : S.Assumptions) :
    Tendsto hA.nuY (𝓝[<] S.c) (𝓝 (S.nuY_left_limit hA)) :=
  Classical.choose_spec hA.nuY_left_limit_exists

/-- [The running variable in a fuzzy regression-discontinuity design](hyp:S) is
[almost-everywhere measurable under the population law](goal), allowing regression
representatives to be pushed forward to its marginal distribution. -/
@[fun_prop]
lemma aemeasurable_factualX (S : POFuzzyRDDSystem P) :
    AEMeasurable S.factualX P.μ := S.measurable_factualX.aemeasurable

/-! ### D-side bridges -/

private lemma factualD_eq_DofZ_on_zEvent
    (hC : P.Consistency) (z : Bool) :
    ∀ ω ∈ S.zEvent z, S.factualD ω = S.DofZ z ω := by
  intro ω hω
  exact (POVar.cf_eq_factual_on_event hC S.Dvar S.Zvar z S.hZD.symm hω).symm

private lemma factualD_eq_DofZ_true_ae_restrict_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (fun ω => ((S.factualD ω).toNat : ℝ))
      =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)]
        fun ω => ((S.DofZ true ω).toNat : ℝ) := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.c ≤ S.factualX ω := hAsub hωA
  have hZprop : S.factualZ ω := hcut.mpr hx
  have hZ : S.factualZ ω = true := by
    cases hZω : S.factualZ ω <;> simp_all
  rw [S.factualD_eq_DofZ_on_zEvent hA.consistency true ω hZ]

private lemma factualD_eq_DofZ_false_ae_restrict_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (fun ω => ((S.factualD ω).toNat : ℝ))
      =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)]
        fun ω => ((S.DofZ false ω).toNat : ℝ) := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.factualX ω < S.c := hAsub hωA
  have hnotZ : ¬ S.factualZ ω := by
    intro hZ
    exact (not_le_of_gt hx) (hcut.mp hZ)
  have hZ : S.factualZ ω = false := by
    cases hZω : S.factualZ ω <;> simp_all
  rw [S.factualD_eq_DofZ_on_zEvent hA.consistency false ω hZ]

private lemma integral_factualD_eq_DofZ_true_on_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ true ω).toNat : ℝ) ∂P.μ :=
  integral_congr_ae (S.factualD_eq_DofZ_true_ae_restrict_Ici hA hAsub hAmeas)

private lemma integral_factualD_eq_DofZ_false_on_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ false ω).toNat : ℝ) ∂P.μ :=
  integral_congr_ae (S.factualD_eq_DofZ_false_ae_restrict_Iio hA hAsub hAmeas)

private lemma regression_integral_bridge_D_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muD true (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ :=
          (hA.nuD_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ true ω).toNat : ℝ) ∂P.μ :=
          S.integral_factualD_eq_DofZ_true_on_Ici hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muD true (S.factualX ω) ∂P.μ :=
          (hA.muD_isReg true).integral_preimage_eq A hAmeas

private lemma regression_integral_bridge_D_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muD false (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuD (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, ((S.factualD ω).toNat : ℝ) ∂P.μ :=
          (hA.nuD_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, ((S.DofZ false ω).toNat : ℝ) ∂P.μ :=
          S.integral_factualD_eq_DofZ_false_on_Iio hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muD false (S.factualX ω) ∂P.μ :=
          (hA.muD_isReg false).integral_preimage_eq A hAmeas

/-! ### Y-side bridges -/

private lemma factualY_eq_YofDofZ_on_zEvent
    (hC : P.Consistency) (z : Bool) :
    ∀ ω ∈ S.zEvent z, S.factualY ω = S.YofDofZ z ω := by
  intro ω hω
  calc
    S.factualY ω = S.YofD (S.factualD ω) ω :=
      POVar.factual_eq_cfUnder_self_selected hC S.Yvar S.Dvar S.hDY.symm ω
    _ = S.YofD (S.DofZ z ω) ω := by
      rw [S.factualD_eq_DofZ_on_zEvent hC z ω hω]
    _ = S.YofDofZ z ω := by
      simp only [causal_defs_simps]
      cases S.DofZ z ω <;> rfl

private lemma factualY_eq_YofDofZ_true_ae_restrict_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofDofZ true := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.c ≤ S.factualX ω := hAsub hωA
  have hZprop : S.factualZ ω := hcut.mpr hx
  have hZ : S.factualZ ω = true := by
    cases hZω : S.factualZ ω <;> simp_all
  exact S.factualY_eq_YofDofZ_on_zEvent hA.consistency true ω hZ

private lemma factualY_eq_YofDofZ_false_ae_restrict_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofDofZ false := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.cutoffEligibility, self_mem_ae_restrict hslice]
    with ω hcut hωA
  have hx : S.factualX ω < S.c := hAsub hωA
  have hnotZ : ¬ S.factualZ ω := by
    intro hZ
    exact (not_le_of_gt hx) (hcut.mp hZ)
  have hZ : S.factualZ ω = false := by
    cases hZω : S.factualZ ω <;> simp_all
  exact S.factualY_eq_YofDofZ_on_zEvent hA.consistency false ω hZ

private lemma integral_factualY_eq_YofDofZ_true_on_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ true ω ∂P.μ :=
  integral_congr_ae (S.factualY_eq_YofDofZ_true_ae_restrict_Ici hA hAsub hAmeas)

private lemma integral_factualY_eq_YofDofZ_false_on_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ false ω ∂P.μ :=
  integral_congr_ae (S.factualY_eq_YofDofZ_false_ae_restrict_Iio hA hAsub hAmeas)

private lemma regression_integral_bridge_Y_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muY true (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nuY_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ true ω ∂P.μ :=
          S.integral_factualY_eq_YofDofZ_true_on_Ici hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muY true (S.factualX ω) ∂P.μ :=
          (hA.muY_isReg true).integral_preimage_eq A hAmeas

private lemma regression_integral_bridge_Y_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.muY false (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nuY (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nuY_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofDofZ false ω ∂P.μ :=
          S.integral_factualY_eq_YofDofZ_false_on_Iio hA hAsub hAmeas
    _ = ∫ ω in S.factualX ⁻¹' A, hA.muY false (S.factualX ω) ∂P.μ :=
          (hA.muY_isReg false).integral_preimage_eq A hAmeas

/-! ### A.e. agreement of observable and latent regressions on half-lines

A single generic helper `aeEq_pushforward_of_bridge` does the work: given two
regression representatives `ν`, `μ` over the same factual `X` and a slice-wise
integral bridge on a measurable half-line `H`, it deduces `ν =ᵐ[π.restrict H] μ`
where `π = P.μ.map S.factualX`. -/

private lemma aeEq_pushforward_of_bridge
    {ν μ : ℝ → ℝ} {gν gμ : P.Ω → ℝ} {H : Set ℝ}
    (hν : IsRegressionFunction P.μ S.factualX gν ν)
    (hμ : IsRegressionFunction P.μ S.factualX gμ μ)
    (hH : MeasurableSet H)
    (h_bridge : ∀ {A : Set ℝ}, A ⊆ H → MeasurableSet A →
      (∫ ω in S.factualX ⁻¹' A, gν ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, gμ ω ∂P.μ) :
    ν =ᵐ[(P.μ.map S.factualX).restrict H] μ := by
  set π := P.μ.map S.factualX with hπ
  set ρ := π.restrict H with hρ
  have hInt_ν : Integrable ν ρ :=
    (hν.integrable_pushforward).restrict
  have hInt_μ : Integrable μ ρ :=
    (hμ.integrable_pushforward).restrict
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    ν μ hInt_ν hInt_μ ?_
  intro s hs _
  have hslice : MeasurableSet (s ∩ H) := hs.inter hH
  have hsub : s ∩ H ⊆ H := Set.inter_subset_right
  -- Pushforward setIntegral identities on the slice s ∩ H.
  have hν_pull :
      (∫ x in s ∩ H, ν x ∂π) = ∫ ω in S.factualX ⁻¹' (s ∩ H), ν (S.factualX ω) ∂P.μ :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := ν) hslice
      hν.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hμ_pull :
      (∫ x in s ∩ H, μ x ∂π) = ∫ ω in S.factualX ⁻¹' (s ∩ H), μ (S.factualX ω) ∂P.μ :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := μ) hslice
      hμ.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hν_reg :
      (∫ ω in S.factualX ⁻¹' (s ∩ H), gν ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' (s ∩ H), ν (S.factualX ω) ∂P.μ :=
    hν.integral_preimage_eq (s ∩ H) hslice
  have hμ_reg :
      (∫ ω in S.factualX ⁻¹' (s ∩ H), gμ ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' (s ∩ H), μ (S.factualX ω) ∂P.μ :=
    hμ.integral_preimage_eq (s ∩ H) hslice
  have h_bridge' :
      (∫ ω in S.factualX ⁻¹' (s ∩ H), gν ω ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' (s ∩ H), gμ ω ∂P.μ :=
    h_bridge hsub hslice
  have h_restrict_ν : (∫ x in s, ν x ∂ρ) = ∫ x in s ∩ H, ν x ∂π := by
    rw [hρ, Measure.restrict_restrict hs]
  have h_restrict_μ : (∫ x in s, μ x ∂ρ) = ∫ x in s ∩ H, μ x ∂π := by
    rw [hρ, Measure.restrict_restrict hs]
  rw [h_restrict_ν, h_restrict_μ, hν_pull, hμ_pull, ← hν_reg, ← hμ_reg, h_bridge']

private lemma nuD_eq_muD_true_ae_restrict_Ici (hA : S.Assumptions) :
    hA.nuD =ᵐ[(P.μ.map S.factualX).restrict (Set.Ici S.c)] hA.muD true :=
  S.aeEq_pushforward_of_bridge hA.nuD_isReg (hA.muD_isReg true)
    measurableSet_Ici
    (fun {_A} hAsub hAmeas =>
      S.integral_factualD_eq_DofZ_true_on_Ici hA hAsub hAmeas)

private lemma nuD_eq_muD_false_ae_restrict_Iio (hA : S.Assumptions) :
    hA.nuD =ᵐ[(P.μ.map S.factualX).restrict (Set.Iio S.c)] hA.muD false :=
  S.aeEq_pushforward_of_bridge hA.nuD_isReg (hA.muD_isReg false)
    measurableSet_Iio
    (fun {_A} hAsub hAmeas =>
      S.integral_factualD_eq_DofZ_false_on_Iio hA hAsub hAmeas)

private lemma nuY_eq_muY_true_ae_restrict_Ici (hA : S.Assumptions) :
    hA.nuY =ᵐ[(P.μ.map S.factualX).restrict (Set.Ici S.c)] hA.muY true :=
  S.aeEq_pushforward_of_bridge hA.nuY_isReg (hA.muY_isReg true)
    measurableSet_Ici
    (fun {_A} hAsub hAmeas =>
      S.integral_factualY_eq_YofDofZ_true_on_Ici hA hAsub hAmeas)

private lemma nuY_eq_muY_false_ae_restrict_Iio (hA : S.Assumptions) :
    hA.nuY =ᵐ[(P.μ.map S.factualX).restrict (Set.Iio S.c)] hA.muY false :=
  S.aeEq_pushforward_of_bridge hA.nuY_isReg (hA.muY_isReg false)
    measurableSet_Iio
    (fun {_A} hAsub hAmeas =>
      S.integral_factualY_eq_YofDofZ_false_on_Iio hA hAsub hAmeas)

/-! ### Limits of observable regressions at the cutoff

Thin wrappers around the generic engine in
`Causalean.PO.RDDLimits` (`oneSidedLimit_eq_right`/`_left`).  Each lemma combines
the half-line a.e. agreement (proved above) with the corresponding continuity
and support hypotheses from the `Assumptions` bundle. -/

/-- Any right-hand observable treatment-regression limit at the cutoff equals
the treated latent treatment regression there. -/
theorem nuD_right_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuD (𝓝[>] S.c) (𝓝 L)) :
    L = hA.muD true S.c :=
  RDDLimits.oneSidedLimit_eq_right
    (S.nuD_eq_muD_true_ae_restrict_Ici hA)
    (hA.muD_continuousAt true)
    hA.support_right
    h

/-- Any left-hand observable treatment-regression limit at the cutoff equals the
untreated latent treatment regression there. -/
theorem nuD_left_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuD (𝓝[<] S.c) (𝓝 L)) :
    L = hA.muD false S.c :=
  RDDLimits.oneSidedLimit_eq_left
    (S.nuD_eq_muD_false_ae_restrict_Iio hA)
    (hA.muD_continuousAt false)
    hA.support_left
    h

/-- Any right-hand observable outcome-regression limit at the cutoff equals the
treated latent outcome regression there. -/
theorem nuY_right_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuY (𝓝[>] S.c) (𝓝 L)) :
    L = hA.muY true S.c :=
  RDDLimits.oneSidedLimit_eq_right
    (S.nuY_eq_muY_true_ae_restrict_Ici hA)
    (hA.muY_continuousAt true)
    hA.support_right
    h

/-- Any left-hand observable outcome-regression limit at the cutoff equals the
untreated latent outcome regression there. -/
theorem nuY_left_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nuY (𝓝[<] S.c) (𝓝 L)) :
    L = hA.muY false S.c :=
  RDDLimits.oneSidedLimit_eq_left
    (S.nuY_eq_muY_false_ae_restrict_Iio hA)
    (hA.muY_continuousAt false)
    hA.support_left
    h

/-! ### Fuzzy RDD identification — prop:po-fuzzy-rdd -/

/-- **Fuzzy RDD identification at the cutoff**, in regression-representative
form. For [a fuzzy regression-discontinuity design](hyp:S), under [the fuzzy-RDD
identifying assumption bundle](hyp:hA), [the Wald
ratio of the latent right- and left-hand representative jumps at the cutoff
equals the Wald ratio of the one-sided observable outcome- and
treatment-regression limits at the cutoff](goal):

    τ_FRD(c) =
      (lim_{x↓c} ν_Y(x) - lim_{x↑c} ν_Y(x)) /
      (lim_{x↓c} ν_D(x) - lim_{x↑c} ν_D(x)).
-/
theorem frd_identification (hA : S.Assumptions) :
    S.tau_FRD hA =
      (S.nuY_right_limit hA - S.nuY_left_limit hA) /
        (S.nuD_right_limit hA - S.nuD_left_limit hA) := by
  rw [show S.nuY_right_limit hA = hA.muY true S.c from
        S.nuY_right_limit_eq hA (S.tendsto_nuY_right_limit hA),
      show S.nuY_left_limit hA = hA.muY false S.c from
        S.nuY_left_limit_eq hA (S.tendsto_nuY_left_limit hA),
      show S.nuD_right_limit hA = hA.muD true S.c from
        S.nuD_right_limit_eq hA (S.tendsto_nuD_right_limit hA),
      show S.nuD_left_limit hA = hA.muD false S.c from
        S.nuD_left_limit_eq hA (S.tendsto_nuD_left_limit hA)]
  rfl

/-! ### LATE bridge — strengthened global-monotonicity variant of prop:po-fuzzy-rdd

Under monotonicity, defiers have measure zero, so `Y(D(1)) − Y(D(0))` agrees
a.e. with `YdiffComplier`.  Both have continuous regression representatives at
`c`, giving a pointwise equality that makes `τ_FRD = τ_LATE`. -/

/-- Under monotonicity, `Y(D(1)) − Y(D(0)) =ᵐ[P.μ] YdiffComplier`. -/
private lemma YofDofZ_diff_eq_YdiffComplier_ae
    (hmono : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true) :
    (fun ω => S.YofDofZ true ω - S.YofDofZ false ω) =ᵐ[P.μ] S.YdiffComplier := by
  filter_upwards [hmono] with ω hmonoω
  simp only [YofDofZ, YdiffComplier]
  cases h1 : S.DofZ true ω <;> cases h0 : S.DofZ false ω <;>
    simp_all [mul_zero, mul_one]

/-- The Y-jump of latent regressions equals `μ_Ydiff_complier` at the cutoff. -/
private lemma muY_diff_eq_mu_Ydiff_complier_at_cutoff (hA : S.Assumptions)
    (hmono : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true) :
    hA.muY true S.c - hA.muY false S.c = hA.mu_Ydiff_complier S.c := by
  have h_ae : (fun x => hA.muY true x - hA.muY false x) =ᵐ[P.μ.map S.factualX]
      hA.mu_Ydiff_complier :=
    IsRegressionFunction.aeEq_of_aeEq_response
      (S.YofDofZ_diff_eq_YdiffComplier_ae hmono)
      ((hA.muY_isReg true).sub (hA.muY_isReg false))
      hA.mu_Ydiff_complier_isReg
  exact RDDLimits.value_eq_of_aeEq_right
    (ae_restrict_of_ae h_ae)
    ((hA.muY_continuousAt true).sub (hA.muY_continuousAt false))
    hA.mu_Ydiff_complier_continuousAt
    hA.support_right

/-- **Fuzzy RDD identifies a cutoff representative complier ratio under an
extra global monotonicity bridge.** For [a fuzzy regression-discontinuity
design](hyp:S), under [the fuzzy-RDD identifying bundle — consistency, deterministic
cutoff eligibility, local monotonicity and exclusion, valid regression representatives,
cutoff continuity and support, well-defined one-sided limits, and a nonzero first
stage](hyp:hA), and additionally assuming
[treatment is almost-surely monotone in the instrument, i.e. whenever the
potential treatment under the untreated instrument value is realized as
true, the potential treatment under the treated instrument value is true as
well (no defiers)](hyp:hmono), [the complier-weighted local average treatment
effect at the cutoff `tau_LATE` equals the fuzzy-RDD Wald-ratio functional
`tau_FRD`, i.e. the observable Wald ratio at the cutoff equals the
complier-weighted outcome-difference representative divided by the
first-stage jump](goal).

-- TODO(faithfulness): fuzzy RDD source statement — to reach the local
-- cutoff-complier claim from the standard local monotonicity assumption, the
-- library needs a local-regression bridge from neighborhood a.e. monotonicity to
-- equality of the cutoff regression representatives. -/
theorem tau_late_identification_of_globalMonotonicity (hA : S.Assumptions)
    (hmono : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true) :
    S.tau_LATE hA = S.tau_FRD hA := by
  simp only [tau_LATE, tau_FRD]
  congr 1
  exact (S.muY_diff_eq_mu_Ydiff_complier_at_cutoff hA hmono).symm

end POFuzzyRDDSystem

end PO
end Causalean
