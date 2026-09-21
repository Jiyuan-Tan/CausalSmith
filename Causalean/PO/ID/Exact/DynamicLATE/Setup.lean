/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-Period Dynamic LATE: data layer

The `PODynLATESystem` structure (def:po-dynamic-late-system) plus all basic
accessors, regimes, counterfactual maps, history bundles, observable
nested-regression functionals, the assumption bundle (def:po-dynamic-late-assumptions),
and the target functionals (def:po-dynamic-late) for the two-period dynamic
IV/LATE setting of Sojitra (2025).  No proof of the bridge identities or
ratio identifications lives here -- see `Bridges.lean` and `WhenToTreat.lean`.

Generalises `PO/ID/Exact/LATE.lean` to two periods with sequential
encouragements `Z₁, Z₂` and noncompliant treatments `D₁, D₂`, plus baseline /
intermediate state covariates `S₀ : POVar P γ₀`, `S₁ : POVar P γ₁`.
-/

module
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.PO.Conditioning.EventCondExp
public import Causalean.PO.Conditioning.CondExpTooling
public import Causalean.PO.Conditioning.Bundle
public import Causalean.Mathlib.Probability.Independence.Conditional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Causalean.Tactic.Attr

/-! # Two-Period Dynamic LATE Setup

This file defines the data, regimes, counterfactual variables, history
information, observable nested regressions, assumptions, and target parameters
for a two-period dynamic instrumental-variables LATE design. It supplies the
common interface used by the bridge and ratio-identification files.

The design has sequential binary encouragements and treatments, a baseline
state, an intermediate state, and a real outcome. It supports observable nested
regressions, dynamic LATE targets, when-to-treat targets, mixture targets, and
the dynamic IV/LATE assumption bundle. -/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A two-period dynamic instrumental-variable model in a potential-outcome system contains
[baseline covariates](hyp:S0), [an intermediate state](hyp:S1),
[two encouragement nodes](hyp:Z1,Z2), [two treatment nodes](hyp:D1,D2), and
[a real-valued outcome node](hyp:Y), together with
[binary encouragement identifications](hyp:hZ1bool,hZ2bool),
[binary treatment identifications](hyp:hD1bool,hD2bool),
[a real-valued outcome identification](hyp:hYreal), and
[pairwise distinctness of all seven nodes](hyp:vars_inj). These variables support dynamic
complier treatment effects; identification requires separate assumptions and Wald identities.

`γ₀, γ₁` are the value spaces of the baseline and intermediate state covariates
`S₀, S₁`.  Encouragements `Z₁, Z₂` and treatments `D₁, D₂` are binary; the
outcome `Y` is real-valued.  All seven nodes are pairwise distinct, packaged via
`Function.Injective` on a `Fin 7 → P.V` accessor. -/
structure PODynLATESystem (P : POSystem) (γ₀ γ₁ : Type)
    [MeasurableSpace γ₀] [MeasurableSpace γ₁] where
  S0 : POVar P γ₀
  S1 : POVar P γ₁
  Z1 : P.V
  D1 : P.V
  Z2 : P.V
  D2 : P.V
  Y  : P.V
  hZ1bool : P.X Z1 ≃ᵐ Bool
  hD1bool : P.X D1 ≃ᵐ Bool
  hZ2bool : P.X Z2 ≃ᵐ Bool
  hD2bool : P.X D2 ≃ᵐ Bool
  hYreal  : P.X Y  ≃ᵐ ℝ
  /-- Pairwise distinctness of all seven atomic nodes. -/
  vars_inj : Function.Injective
    (![S0.v, S1.v, Z1, D1, Z2, D2, Y] : Fin 7 → P.V)

namespace PODynLATESystem

variable {P : POSystem} {γ₀ γ₁ : Type}
variable [MeasurableSpace γ₀] [MeasurableSpace γ₁]
variable (S : PODynLATESystem P γ₀ γ₁)

/-! ### POVar wrappers and factual maps -/

/-- [The first-period encouragement variable](goal) exposes the initial binary instrument in [a
two-period dynamic LATE system](hyp:S). -/
def z1Var : POVar P Bool := ⟨S.Z1, S.hZ1bool⟩
/-- [The second-period encouragement variable](goal) exposes the later binary instrument in [a
two-period dynamic LATE system](hyp:S). -/
def z2Var : POVar P Bool := ⟨S.Z2, S.hZ2bool⟩
/-- [The first-period treatment variable](goal) exposes initial binary uptake in [a two-period
dynamic LATE system](hyp:S). -/
def d1Var : POVar P Bool := ⟨S.D1, S.hD1bool⟩
/-- [The second-period treatment variable](goal) exposes later binary uptake in [a two-period
dynamic LATE system](hyp:S). -/
def d2Var : POVar P Bool := ⟨S.D2, S.hD2bool⟩
/-- [The real-valued outcome variable](goal) exposes the terminal response in [a two-period
dynamic LATE system](hyp:S). -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- [The observed baseline state](goal) records pre-encouragement covariates for each unit in [a
two-period dynamic LATE system](hyp:S). -/
noncomputable def factualS0 : P.Ω → γ₀ := S.S0.factual
/-- [The observed intermediate state](goal) records the covariates available between periods in
[a two-period dynamic LATE system](hyp:S). -/
noncomputable def factualS1 : P.Ω → γ₁ := S.S1.factual
/-- [The observed first-period encouragement](goal) records each unit's initial instrument value
in [a two-period dynamic LATE system](hyp:S). -/
noncomputable def factualZ1 : P.Ω → Bool := S.z1Var.factual
/-- [The observed second-period encouragement](goal) records each unit's later instrument value
in [a two-period dynamic LATE system](hyp:S). -/
noncomputable def factualZ2 : P.Ω → Bool := S.z2Var.factual
/-- [The observed first-period treatment](goal) records initial uptake for each unit in [a
two-period dynamic LATE system](hyp:S). -/
noncomputable def factualD1 : P.Ω → Bool := S.d1Var.factual
/-- [The observed second-period treatment](goal) records later uptake for each unit in [a
two-period dynamic LATE system](hyp:S). -/
noncomputable def factualD2 : P.Ω → Bool := S.d2Var.factual
/-- [The observed terminal outcome](goal) records each unit's realized response in [a two-period
dynamic LATE system](hyp:S). -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-! ### Pairwise distinctness lemmas (extracted from `vars_inj`) -/

private abbrev varVec : Fin 7 → P.V :=
  ![S.S0.v, S.S1.v, S.Z1, S.D1, S.Z2, S.D2, S.Y]

private lemma varVec_apply_zero : S.varVec 0 = S.S0.v := rfl
private lemma varVec_apply_one : S.varVec 1 = S.S1.v := rfl
private lemma varVec_apply_two : S.varVec 2 = S.Z1 := rfl
private lemma varVec_apply_three : S.varVec 3 = S.D1 := rfl
private lemma varVec_apply_four : S.varVec 4 = S.Z2 := rfl
private lemma varVec_apply_five : S.varVec 5 = S.D2 := rfl
private lemma varVec_apply_six : S.varVec 6 = S.Y := rfl

/-- [The two encouragements occupy distinct nodes](goal) in [the dynamic LATE system](hyp:S), so
their joint intervention cannot assign one variable twice. -/
lemma Z1_ne_Z2 : S.Z1 ≠ S.Z2 := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 4 by decide)
  simpa [varVec_apply_two, varVec_apply_four] using this

/-- [The two treatments occupy distinct nodes](goal) in [the dynamic LATE system](hyp:S), so a
treatment-path intervention is well defined. -/
lemma D1_ne_D2 : S.D1 ≠ S.D2 := by
  have := S.vars_inj.ne (show (3 : Fin 7) ≠ 5 by decide)
  simpa [varVec_apply_three, varVec_apply_five] using this

/-- [First-period treatment and the terminal outcome occupy distinct nodes](goal) in [the dynamic
LATE system](hyp:S), separating intervention from response. -/
lemma D1_ne_Y : S.D1 ≠ S.Y := by
  have := S.vars_inj.ne (show (3 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_three, varVec_apply_six] using this

/-- [Second-period treatment and the terminal outcome occupy distinct nodes](goal) in [the
dynamic LATE system](hyp:S), separating intervention from response. -/
lemma D2_ne_Y : S.D2 ≠ S.Y := by
  have := S.vars_inj.ne (show (5 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_five, varVec_apply_six] using this

/-- [First-period encouragement and the terminal outcome occupy distinct nodes](goal) in [the
dynamic LATE system](hyp:S), separating assignment from response. -/
lemma Z1_ne_Y : S.Z1 ≠ S.Y := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_two, varVec_apply_six] using this

/-- [Second-period encouragement and the terminal outcome occupy distinct nodes](goal) in [the
dynamic LATE system](hyp:S), separating assignment from response. -/
lemma Z2_ne_Y : S.Z2 ≠ S.Y := by
  have := S.vars_inj.ne (show (4 : Fin 7) ≠ 6 by decide)
  simpa [varVec_apply_four, varVec_apply_six] using this

/-- [First-period encouragement and treatment occupy distinct nodes](goal) in [the dynamic LATE
system](hyp:S), allowing the instrument to shift rather than equal uptake. -/
lemma Z1_ne_D1 : S.Z1 ≠ S.D1 := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 3 by decide)
  simpa [varVec_apply_two, varVec_apply_three] using this

/-- [First-period encouragement and second-period treatment occupy distinct nodes](goal) in [the
dynamic LATE system](hyp:S), keeping the sequential intervention targets separate. -/
lemma Z1_ne_D2 : S.Z1 ≠ S.D2 := by
  have := S.vars_inj.ne (show (2 : Fin 7) ≠ 5 by decide)
  simpa [varVec_apply_two, varVec_apply_five] using this

/-- [Second-period encouragement and first-period treatment occupy distinct nodes](goal) in [the
dynamic LATE system](hyp:S), keeping the sequential intervention targets separate. -/
lemma Z2_ne_D1 : S.Z2 ≠ S.D1 := by
  have := S.vars_inj.ne (show (4 : Fin 7) ≠ 3 by decide)
  simpa [varVec_apply_four, varVec_apply_three] using this

/-- [Second-period encouragement and treatment occupy distinct nodes](goal) in [the dynamic LATE
system](hyp:S), allowing the later instrument to shift rather than equal uptake. -/
lemma Z2_ne_D2 : S.Z2 ≠ S.D2 := by
  have := S.vars_inj.ne (show (4 : Fin 7) ≠ 5 by decide)
  simpa [varVec_apply_four, varVec_apply_five] using this

/-! ### Two-target encouragement and treatment regimes (`Regime.ofList`) -/

/-- [The joint encouragement regime](goal) fixes both period-specific instruments in [a
two-period dynamic LATE system](hyp:S) to [a chosen binary path](hyp:z). -/
noncomputable def encouragementRegime (z : Fin 2 → Bool) : Regime P.V P.X :=
  Regime.ofList
    [⟨S.Z1, S.hZ1bool.symm (z 0)⟩, ⟨S.Z2, S.hZ2bool.symm (z 1)⟩]
    (by
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
      exact S.Z1_ne_Z2)

/-- [The joint treatment regime](goal) fixes both period-specific treatments in [a two-period
dynamic LATE system](hyp:S) to [a chosen binary path](hyp:d). -/
noncomputable def treatmentRegime (d : Fin 2 → Bool) : Regime P.V P.X :=
  Regime.ofList
    [⟨S.D1, S.hD1bool.symm (d 0)⟩, ⟨S.D2, S.hD2bool.symm (d 1)⟩]
    (by
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
      exact S.D1_ne_D2)

/-- [The second-stage-only encouragement regime](goal) intervenes on the later instrument in [a
two-period dynamic LATE system](hyp:S) at [a chosen binary value](hyp:z₂), leaving period one
natural.

Used in the
stage-2 ignorability condition where `Z₁` remains factual. -/
noncomputable def encZ2Regime (z₂ : Bool) : Regime P.V P.X :=
  Regime.single S.Z2 (S.hZ2bool.symm z₂)

/-- [Joint encouragement and treatment interventions target disjoint node sets](goal) for [any
chosen encouragement and treatment paths](hyp:z,d), so the two regimes can be combined without a
conflicting assignment. -/
lemma encouragementRegime_disjoint_treatmentRegime (z d : Fin 2 → Bool) :
    (S.encouragementRegime z).Disjoint (S.treatmentRegime d) := by
  unfold encouragementRegime treatmentRegime Regime.Disjoint
  rw [Regime.ofList_target, Regime.ofList_target]
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_insert] at hv hv'
  rcases hv with hv | hv | hv
  · subst hv
    rcases hv' with hv' | hv' | hv'
    · exact S.Z1_ne_D1 hv'
    · exact S.Z1_ne_D2 hv'
    · exact (Finset.notMem_empty _ hv').elim
  · subst hv
    rcases hv' with hv' | hv' | hv'
    · exact S.Z2_ne_D1 hv'
    · exact S.Z2_ne_D2 hv'
    · exact (Finset.notMem_empty _ hv').elim
  · exact (Finset.notMem_empty _ hv).elim

/-- [The combined encouragement-and-treatment regime](goal) fixes all four period-specific
variables in [a two-period dynamic LATE system](hyp:S) to [the selected encouragement](hyp:z) and
[treatment](hyp:d) paths.

Fixing
`Z₁,Z₂,D₁,D₂` simultaneously. -/
noncomputable def encTreatRegime (z d : Fin 2 → Bool) : Regime P.V P.X :=
  (S.encouragementRegime z).sqcup (S.treatmentRegime d)
    (S.encouragementRegime_disjoint_treatmentRegime z d)

/-! ### Counterfactual variables under encouragement / treatment regimes -/

/-- [First-period treatment under encouragement](goal) records initial uptake in [a two-period
dynamic LATE system](hyp:S) when both instruments follow [the selected path](hyp:z).

`D₁(z) := D₁` evaluated under the encouragement regime fixing both `Z`'s.
By exclusion (`D₁` has no `Z₂` parent in the primitive process), this equals
`D₁(z 0)`; we keep the two-coordinate form to avoid splitting cases. -/
noncomputable def D1ofZ (z : Fin 2 → Bool) : P.Ω → Bool :=
  S.d1Var.cf (S.encouragementRegime z)

/-- [Second-period treatment under encouragement](goal) records later uptake in [a two-period
dynamic LATE system](hyp:S) when both instruments follow [the selected path](hyp:z). -/
noncomputable def D2ofZ (z : Fin 2 → Bool) : P.Ω → Bool :=
  S.d2Var.cf (S.encouragementRegime z)

/-- [The treatment path induced by encouragement](goal) joins both potential treatment decisions
in [a two-period dynamic LATE system](hyp:S) under [the selected instrument path](hyp:z). -/
noncomputable def DofZ (z : Fin 2 → Bool) : P.Ω → (Fin 2 → Bool) :=
  fun ω i => Fin.cases (S.D1ofZ z ω) (fun _ => S.D2ofZ z ω) i

/-- [Second-period treatment under a late encouragement intervention](goal) records later uptake
in [a two-period dynamic LATE system](hyp:S) when only [the second instrument](hyp:z₂) is fixed.

`D₂(Z₁, z₂)`: stage-2 treatment when only `Z₂` is fixed (and `Z₁`
remains factual).  Used in the stage-2 ignorability bundle. -/
noncomputable def D2ofZ2 (z₂ : Bool) : P.Ω → Bool :=
  S.d2Var.cf (S.encZ2Regime z₂)

/-- [Outcome under a treatment path](goal) records the terminal response in [a two-period dynamic
LATE system](hyp:S) when both treatments follow [the selected path](hyp:d). -/
noncomputable def YofD (d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.yVar.cf (S.treatmentRegime d)

/-- [Outcome under an encouragement path](goal) records the terminal response in [a two-period
dynamic LATE system](hyp:S) when both instruments follow [the selected path](hyp:z).

`Y(D(z))` defined directly via the encouragement regime: under the
two-target encouragement intervention, `D₁` and `D₂` are computed from `z`
via the structural recursion, and `Y` is then computed from the resulting
treatment vector.  This is the natural "outcome under encouragement `z`"
map; `composition` consistency identifies it with the explicit composition. -/
noncomputable def YofDofZ (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.yVar.cf (S.encouragementRegime z)

/-- [Outcome under a joint encouragement path is exactly the counterfactual outcome evaluated in
that intervention regime](goal) for [the dynamic LATE system](hyp:S) and [chosen instrument
path](hyp:z), connecting the economic notation to the regime semantics. -/
@[causal_defs_simps]
lemma YofDofZ_eq (z : Fin 2 → Bool) :
    S.YofDofZ z = S.yVar.cf (S.encouragementRegime z) :=
  rfl

/-- [Outcome under a late encouragement intervention](goal) records the terminal response in [a
two-period dynamic LATE system](hyp:S) when only [the second instrument](hyp:z₂) is fixed.

`Y(D₁, D₂(Z₁, z₂))` realised as `Y` under the regime fixing only
`Z₂ = z₂`. -/
noncomputable def YofZ2 (z₂ : Bool) : P.Ω → ℝ := S.yVar.cf (S.encZ2Regime z₂)

/-- [First-period treatment under an encouragement path is measurable](goal), so [a dynamic LATE
system](hyp:S) can form events and moments for [that path](hyp:z). -/
@[fun_prop]
lemma measurable_D1ofZ (z : Fin 2 → Bool) : Measurable (S.D1ofZ z) :=
  S.d1Var.measurable_cf _
/-- [Second-period treatment under an encouragement path is measurable](goal), so [a dynamic
LATE system](hyp:S) can form events and moments for [that path](hyp:z). -/
@[fun_prop]
lemma measurable_D2ofZ (z : Fin 2 → Bool) : Measurable (S.D2ofZ z) :=
  S.d2Var.measurable_cf _
/-- [The induced treatment path is measurable](goal), so [the dynamic LATE system](hyp:S) has
measurable dynamic-complier events for [each encouragement path](hyp:z). -/
@[fun_prop]
lemma measurable_DofZ (z : Fin 2 → Bool) : Measurable (S.DofZ z) := by
  refine measurable_pi_lambda _ ?_
  intro i
  refine i.cases ?_ ?_
  · simpa [DofZ] using S.measurable_D1ofZ z
  · intro _; simpa [DofZ] using S.measurable_D2ofZ z
/-- [Later treatment under a second-stage-only intervention is measurable](goal), so [the
system](hyp:S) supports conditional treatment probabilities for [that late
encouragement](hyp:z₂). -/
@[fun_prop]
lemma measurable_D2ofZ2 (z₂ : Bool) : Measurable (S.D2ofZ2 z₂) :=
  S.d2Var.measurable_cf _
/-- [Outcome under a fixed treatment path is measurable](goal), permitting causal outcome
averages in [the system](hyp:S) for [that path](hyp:d). -/
@[fun_prop]
lemma measurable_YofD (d : Fin 2 → Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cf _
/-- [Outcome under a fixed encouragement path is measurable](goal), permitting g-formula moments
in [the system](hyp:S) for [that path](hyp:z). -/
@[fun_prop]
lemma measurable_YofDofZ (z : Fin 2 → Bool) : Measurable (S.YofDofZ z) :=
  S.yVar.measurable_cf _
/-- [Outcome under a second-stage-only intervention is measurable](goal), permitting sequential
regression in [the system](hyp:S) for [that late encouragement](hyp:z₂). -/
@[fun_prop]
lemma measurable_YofZ2 (z₂ : Bool) : Measurable (S.YofZ2 z₂) :=
  S.yVar.measurable_cf _
/-- [The observed baseline state is measurable](goal), so [the system](hyp:S) can condition its
first-stage regression on pre-encouragement information. -/
@[fun_prop]
lemma measurable_factualS0 : Measurable S.factualS0 := S.S0.measurable_factual
/-- [The observed intermediate state is measurable](goal), so [the system](hyp:S) can include it
in the second-stage history. -/
@[fun_prop]
lemma measurable_factualS1 : Measurable S.factualS1 := S.S1.measurable_factual
/-- [The observed first encouragement is measurable](goal), making initial assignment cells
available in [the system](hyp:S). -/
@[fun_prop]
lemma measurable_factualZ1 : Measurable S.factualZ1 := S.z1Var.measurable_factual
/-- [The observed second encouragement is measurable](goal), making later assignment cells
available in [the system](hyp:S). -/
@[fun_prop]
lemma measurable_factualZ2 : Measurable S.factualZ2 := S.z2Var.measurable_factual
/-- [The observed first treatment is measurable](goal), so initial uptake can enter the later
history in [the system](hyp:S). -/
@[fun_prop]
lemma measurable_factualD1 : Measurable S.factualD1 := S.d1Var.measurable_factual
/-- [The observed second treatment is measurable](goal), making realized treatment paths events
in [the system](hyp:S). -/
@[fun_prop]
lemma measurable_factualD2 : Measurable S.factualD2 := S.d2Var.measurable_factual
/-- [The observed terminal outcome is measurable](goal), so its nested conditional means are
defined in [the system](hyp:S). -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- [The observed outcome is integrable](goal) whenever [consistency](hyp:hC) links it to [the
integrable potential outcomes under both second-period encouragement values](hyp:hY) in [the
dynamic LATE system](hyp:S). This licenses the observable outcome regressions. -/
lemma integrable_factualY_of_consistency_integrable_YofZ2 [IsFiniteMeasure P.μ]
    (hC : P.Consistency) (hY : ∀ z₂ : Bool, Integrable (S.YofZ2 z₂) P.μ) :
    Integrable S.factualY P.μ := by
  have htrue_int : Integrable (fun ω => S.YofZ2 true ω * S.z2Var.indicator true ω) P.μ :=
    S.z2Var.integrable_mul_indicator true (measurableSet_singleton _) (hY true)
  have hfalse_int : Integrable (fun ω => S.YofZ2 false ω * S.z2Var.indicator false ω) P.μ :=
    S.z2Var.integrable_mul_indicator false (measurableSet_singleton _) (hY false)
  have hsum_int : Integrable
      ((fun ω => S.YofZ2 true ω * S.z2Var.indicator true ω) +
        fun ω => S.YofZ2 false ω * S.z2Var.indicator false ω) P.μ :=
    htrue_int.add hfalse_int
  refine hsum_int.congr (Filter.Eventually.of_forall ?_)
  intro ω
  by_cases hω : S.factualZ2 ω = true
  · have hcf : S.YofZ2 true ω = S.factualY ω :=
      POVar.cf_eq_factual_on_event hC S.yVar S.z2Var true S.Z2_ne_Y.symm hω
    have hind_true : S.z2Var.indicator true ω = 1 := by
      exact S.z2Var.indicator_apply_eq_one hω
    have hfalse : S.factualZ2 ω ≠ false := by
      rw [hω]
      decide
    have hind_false : S.z2Var.indicator false ω = 0 := by
      exact S.z2Var.indicator_apply_eq_zero hfalse
    simp [Pi.add_apply, hcf, hind_true, hind_false]
  · have hω_false : S.factualZ2 ω = false := by
      cases hz : S.factualZ2 ω <;> simp_all
    have hcf : S.YofZ2 false ω = S.factualY ω :=
      POVar.cf_eq_factual_on_event hC S.yVar S.z2Var false S.Z2_ne_Y.symm hω_false
    have hind_true : S.z2Var.indicator true ω = 0 := by
      exact S.z2Var.indicator_apply_eq_zero hω
    have hind_false : S.z2Var.indicator false ω = 1 := by
      exact S.z2Var.indicator_apply_eq_one hω_false
    simp [Pi.add_apply, hcf, hind_true, hind_false]

/-! ### Regimed variables for ignorability bundles -/

/-- [The regimed outcome under encouragement](goal) couples the terminal response in [a
two-period dynamic LATE system](hyp:S) with [the joint instrument path](hyp:z) that generates it. -/
noncomputable def yUnderZ (z : Fin 2 → Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, S.encouragementRegime z⟩

/-- [The regimed first-period treatment](goal) couples initial uptake in [a two-period dynamic
LATE system](hyp:S) with [the joint instrument path](hyp:z) that generates it. -/
noncomputable def d1UnderZ (z : Fin 2 → Bool) : RegimedVar P Bool :=
  ⟨S.d1Var, S.encouragementRegime z⟩

/-- [The regimed second-period treatment](goal) couples later uptake in [a two-period dynamic
LATE system](hyp:S) with [the joint instrument path](hyp:z) that generates it. -/
noncomputable def d2UnderZ (z : Fin 2 → Bool) : RegimedVar P Bool :=
  ⟨S.d2Var, S.encouragementRegime z⟩

/-- [The regimed outcome under a late intervention](goal) couples the terminal response in [a
two-period dynamic LATE system](hyp:S) with [the second-period encouragement](hyp:z₂) that is
fixed. -/
noncomputable def yUnderZ2 (z₂ : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, S.encZ2Regime z₂⟩

/-- [The regimed second-period treatment under a late intervention](goal) couples later uptake in
[a two-period dynamic LATE system](hyp:S) with [the second-period encouragement](hyp:z₂) that is
fixed. -/
noncomputable def d2UnderZ2 (z₂ : Bool) : RegimedVar P Bool :=
  ⟨S.d2Var, S.encZ2Regime z₂⟩

/-! ### History bundles (sequential conditioning σ-algebras) -/

/-- [The first-stage observed history](goal) in [a two-period dynamic LATE system](hyp:S)
contains exactly the baseline state available before the initial encouragement.

Conditioning on this
σ-algebra realises `· | S₀` in the outer regression. -/
noncomputable def historyBundle1 : POCFBundle P :=
  POCFBundle.cons (RegimedVar.ofFactual S.S0) (POCFBundle.nil P)

/-- [The second-stage observed history](goal) in [a two-period dynamic LATE system](hyp:S)
contains baseline and intermediate states together with the first encouragement and treatment.

Conditioning on this
σ-algebra realises `· | S, D₁, Z₁` in the inner regression (the stage-2
encouragement `Z₂` is *not* in the conditioning set; it is restricted via
an indicator). -/
noncomputable def historyBundle2 : POCFBundle P :=
  POCFBundle.cons (RegimedVar.ofFactual S.S0) <|
  POCFBundle.cons (RegimedVar.ofFactual S.S1) <|
  POCFBundle.cons (RegimedVar.ofFactual S.z1Var) <|
  POCFBundle.cons (RegimedVar.ofFactual S.d1Var) <|
  POCFBundle.nil P

/-! ### Counterfactual bundles for sequential ignorability -/

/-- [The first-stage counterfactual bundle](goal) collects the outcome and both treatment
responses in [a two-period dynamic LATE system](hyp:S) under [the selected encouragement
path](hyp:z), the joint object required for initial sequential ignorability.

Stage-1 ignorability bundle `(Y(D(z)), D₁(z), D₂(z))`, the counterfactual
target of `Z₁ ⟂ · | S₀`. -/
noncomputable def cfBundle1 (z : Fin 2 → Bool) : POCFBundle P :=
  POCFBundle.cons (S.yUnderZ z) <|
  POCFBundle.cons (S.d1UnderZ z) <|
  POCFBundle.cons (S.d2UnderZ z) <|
  POCFBundle.nil P

/-- [The second-stage counterfactual bundle](goal) collects the outcome and later treatment
response in [a two-period dynamic LATE system](hyp:S) under [the selected late
encouragement](hyp:z₂), the object required for second-stage ignorability.

Stage-2 ignorability bundle `(Y(D₁, D₂(Z₁, z₂)), D₂(Z₁, z₂))`, the
counterfactual target of `Z₂ ⟂ · | S, D₁, Z₁`. -/
noncomputable def cfBundle2 (z₂ : Bool) : POCFBundle P :=
  POCFBundle.cons (S.yUnderZ2 z₂) <|
  POCFBundle.cons (S.d2UnderZ2 z₂) <|
  POCFBundle.nil P

/-! ### Joint-treatment indicator and joint-encouragement indicator -/

/-- [The observed treatment-path indicator](goal) selects units in [a two-period dynamic LATE
system](hyp:S) whose two realized treatments match [the chosen path](hyp:d). -/
noncomputable def indD (d : Fin 2 → Bool) : P.Ω → ℝ :=
  fun ω => S.d1Var.indicator (d 0) ω * S.d2Var.indicator (d 1) ω

/-- [The observed encouragement-path indicator](goal) selects units in [a two-period dynamic LATE
system](hyp:S) whose two realized instruments match [the chosen path](hyp:z). -/
noncomputable def indZ (z : Fin 2 → Bool) : P.Ω → ℝ :=
  fun ω => S.z1Var.indicator (z 0) ω * S.z2Var.indicator (z 1) ω

/-- [The treatment-path indicator is measurable](goal), so [the dynamic LATE system](hyp:S) can
condition on matching [a chosen treatment path](hyp:d). -/
@[fun_prop]
lemma measurable_indD (d : Fin 2 → Bool) : Measurable (S.indD d) :=
  (S.d1Var.measurable_indicator _ (MeasurableSet.singleton _)).mul
    (S.d2Var.measurable_indicator _ (MeasurableSet.singleton _))

/-- [The encouragement-path indicator is measurable](goal), so [the dynamic LATE system](hyp:S)
can condition on matching [a chosen instrument path](hyp:z). -/
@[fun_prop]
lemma measurable_indZ (z : Fin 2 → Bool) : Measurable (S.indZ z) :=
  (S.z1Var.measurable_indicator _ (MeasurableSet.singleton _)).mul
    (S.z2Var.measurable_indicator _ (MeasurableSet.singleton _))

/-! ### Observable nested-regression functionals
    (def:po-dynamic-late-observable-functionals) -/

/-- [The inner observable outcome regression](goal) conditions the terminal outcome in [a
two-period dynamic LATE system](hyp:S) on the full second-stage history and [the selected
encouragement path](hyp:z), forming the first layer of the g-formula bridge.

Inner regression `E[Y | S, D₁, Z = z]` realised as the bundle ratio
`E[Y · 1_{Z=z} | history2] / E[1_{Z=z} | history2]`. -/
noncomputable def innerCondY (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle2.condExpRatio
    (fun ω => S.factualY ω * S.indZ z ω) (S.indZ z) P.μ

/-- [The inner observable treatment-path regression](goal) gives the conditional probability of
[a selected treatment path](hyp:d) in [a two-period dynamic LATE system](hyp:S), given the full
second-stage history and [encouragement path](hyp:z).

Inner regression `P(D = d | S, D₁, Z = z)` realised as the bundle ratio
`E[1_{D=d} · 1_{Z=z} | history2] / E[1_{Z=z} | history2]`. -/
noncomputable def innerCondD (z d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle2.condExpRatio
    (fun ω => S.indD d ω * S.indZ z ω) (S.indZ z) P.μ

/-- [The baseline-conditional observable outcome mean](goal) averages the inner outcome
regression in [a two-period dynamic LATE system](hyp:S) over post-baseline history for [the
selected encouragement path](hyp:z).

Outer regression of `innerCondY z` over `(S₀, Z₁ = z₁)`, as a function of
`S₀`.  This is `cObsMean(z; S₀)`. -/
noncomputable def cObsMean (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => S.innerCondY z ω * S.z1Var.indicator (z 0) ω)
    (S.z1Var.indicator (z 0)) P.μ

/-- [The baseline-conditional observable treatment-path probability](goal) averages the inner
probability for [a treatment path](hyp:d) in [a two-period dynamic LATE system](hyp:S) over
post-baseline history under [the selected encouragement path](hyp:z). -/
noncomputable def cObsProb (z d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => S.innerCondD z d ω * S.z1Var.indicator (z 0) ω)
    (S.z1Var.indicator (z 0)) P.μ

/-- [The observable g-formula mean](goal) averages the baseline-conditional nested regression in
[a two-period dynamic LATE system](hyp:S) for [the selected encouragement path](hyp:z). -/
noncomputable def obsMean (z : Fin 2 → Bool) : ℝ := ∫ ω, S.cObsMean z ω ∂P.μ

/-- [The observable g-formula treatment-path probability](goal) averages the nested regression
for [a selected treatment path](hyp:d) in [a two-period dynamic LATE system](hyp:S) under [the
selected encouragement path](hyp:z). -/
noncomputable def obsProb (z d : Fin 2 → Bool) : ℝ := ∫ ω, S.cObsProb z d ω ∂P.μ

/-! ### Target functionals (def:po-dynamic-late) -/

/-- [The dynamic-complier event](goal) selects units in [a two-period dynamic LATE
system](hyp:S) whose treatment response to [an encouragement path](hyp:z) equals [the target
treatment path](hyp:d). -/
def DofZEq (z d : Fin 2 → Bool) : Set P.Ω := { ω | S.DofZ z ω = d }

/-- [Each dynamic-complier subgroup is measurable](goal), so [the dynamic LATE system](hyp:S) can
average outcomes among units induced by [an encouragement path](hyp:z) to [a treatment
path](hyp:d). -/
lemma measurableSet_DofZEq (z d : Fin 2 → Bool) : MeasurableSet (S.DofZEq z d) := by
  have hsing : MeasurableSet ({d} : Set (Fin 2 → Bool)) := MeasurableSet.singleton _
  exact S.measurable_DofZ z hsing

/-- [The dynamic local average treatment effect](goal) in [a two-period dynamic LATE
system](hyp:S) averages the outcome contrast between [a target treatment path](hyp:d) and no
treatment among units induced to that path by [the selected encouragement](hyp:z), using zero
when the subgroup is empty.

Dynamic LATE `θ(z, d) := E[Y(d) - Y(0) | D(z) = d]`, totalised as
`(∫_{D(z)=d} (Y(d) - Y(0)) dμ) / μ({D(z) = d}).toReal`. -/
noncomputable def LATE (z d : Fin 2 → Bool) : ℝ :=
  (∫ ω in S.DofZEq z d, (S.YofD d ω - S.YofD ![false, false] ω) ∂P.μ) /
    (P.μ (S.DofZEq z d)).toReal

/-- [The baseline-conditional dynamic LATE](goal) in [a two-period dynamic LATE system](hyp:S)
localizes the effect of [a target treatment path](hyp:d) versus no treatment among units induced
by [the selected encouragement path](hyp:z) to each baseline state.

Heterogeneous dynamic LATE `θ(z, d, S₀)`: the bundle conditional version
of `LATE z d`, realised as `historyBundle1.condExpRatio` of the
indicator-weighted contrast. -/
noncomputable def cLATE (z d : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => (S.YofD d ω - S.YofD ![false, false] ω) *
              (S.DofZEq z d).indicator (fun _ => (1 : ℝ)) ω)
    ((S.DofZEq z d).indicator (fun _ => (1 : ℝ))) P.μ

/-- [The when-to-treat LATE](goal) in [a two-period dynamic LATE system](hyp:S) evaluates [a
single path](hyp:d) both as the encouragement schedule and as the treatment timing it induces. -/
noncomputable def whenToTreatLATE (d : Fin 2 → Bool) : ℝ := S.LATE d d

/-- [The baseline-conditional when-to-treat LATE](goal) in [a two-period dynamic LATE
system](hyp:S) evaluates [a single path](hyp:d) as both encouragement and induced treatment timing
within each baseline stratum. -/
noncomputable def cWhenToTreatLATE (d : Fin 2 → Bool) : P.Ω → ℝ := S.cLATE d d

/-- [The mixture LATE](goal) in [a two-period dynamic LATE system](hyp:S) averages the outcome
gain induced by [an encouragement path](hyp:z) among all units moved to any nonzero treatment
path. -/
noncomputable def mixtureLATE (z : Fin 2 → Bool) : ℝ :=
  (∫ ω in {ω | S.DofZ z ω ≠ ![false, false]},
      (S.YofDofZ z ω - S.YofD ![false, false] ω) ∂P.μ) /
    (P.μ {ω | S.DofZ z ω ≠ ![false, false]}).toReal

/-- [The baseline-conditional mixture LATE](goal) in [a two-period dynamic LATE system](hyp:S)
localizes the outcome gain induced by [an encouragement path](hyp:z) among units moved to any
nonzero treatment path. -/
noncomputable def cMixtureLATE (z : Fin 2 → Bool) : P.Ω → ℝ :=
  S.historyBundle1.condExpRatio
    (fun ω => (S.YofDofZ z ω - S.YofD ![false, false] ω) *
              ({ω | S.DofZ z ω ≠ ![false, false]}).indicator (fun _ => (1 : ℝ)) ω)
    (({ω | S.DofZ z ω ≠ ![false, false]}).indicator (fun _ => (1 : ℝ))) P.μ

/-! ### Coordinate-wise order on `Fin 2 → Bool` -/

/-- [Coordinatewise path order](goal) records that [one binary path](hyp:d) never exceeds [a
second path](hyp:z), the comparison used to express one-sided noncompliance period by period. -/
def Preceq (d z : Fin 2 → Bool) : Prop := d 0 ≤ z 0 ∧ d 1 ≤ z 1

/-! ### Assumption bundle (def:po-dynamic-late-assumptions) -/

/-- The dynamic instrumental-variable / LATE assumptions for the two-period system
(`def:po-dynamic-late-assumptions`): [factual potential-outcome consistency for the
ambient system](hyp:consistency); [composition consistency for its sequential
encouragement and treatment regimes](hyp:compositionConsistency); [conditional
independence of the stage-1 encouragement from the counterfactual outcome and treatment
path given the baseline state](hyp:ignorability1),
and [conditional independence of the stage-2 encouragement from its counterfactual
outcome and treatment given the full stage-2 history](hyp:ignorability2); [positive
stage-1](hyp:overlap1) and [positive stage-2](hyp:overlap2) propensities almost
surely; [a positive stage-1](hyp:relevance1) and [a positive stage-2](hyp:relevance2)
first-stage effect of encouragement on treatment, almost surely; [one-sided
noncompliance, whereby each stage's counterfactual treatment never exceeds its
encouragement](hyp:oneSidedNoncompliance); an exclusion restriction under which [the
outcome depends on the encouragements only through the resulting
treatments](hyp:exclusion), [the first-stage treatment does not depend on the
second-period encouragement](hyp:exclusion_D1), and [the first-period encouragement
does not depend on the second-period encouragement](hyp:exclusion_Z1); and
integrability of [the counterfactual outcome under every fixed treatment
vector](hyp:integrable_YofD), [under every fixed encouragement
vector](hyp:integrable_YofDofZ), and [under every fixed second-period
encouragement](hyp:integrable_YofZ2).

* **consistency**: factual PO consistency for the underlying system.
* **compositionConsistency**: composition consistency for nested/sequential regimes.
* **ignorability1**: `{Y(D(z)), D₁(z), D₂(z)} ⟂ Z₁ | S₀` for every `z`.
* **ignorability2**: `{Y(D₁, D₂(Z₁, z₂)), D₂(Z₁, z₂)} ⟂ Z₂ | (S₀, S₁, Z₁, D₁)`
  for every `z₂`.
* **overlap1**: positive stage-1 propensity given `S₀`, a.s.
* **overlap2**: positive stage-2 propensity given `(S, D₁, Z₁)`, a.s.
* **relevance1**: positive stage-1 first stage `E[D₁(1) - D₁(0) | S₀] > 0`, a.s.
* **relevance2**: positive stage-2 first stage given the stage-2 history, a.s.
* **oneSidedNoncompliance**: `D₁(z) ≤ z 0` and `D₂(z) ≤ z 1` a.s., for every `z`.
* **exclusion**: `Y` depends on `(D, S)` only, not on `Z`.  In regime terms,
  the value of `Y` under the joint encouragement-and-treatment regime
  agrees pointwise with the value of `Y` under the treatment-only regime.
  This corresponds to the note's primitive-process clause `Y(D, S)`
  (encouragements affect the terminal outcome only through treatment
  and state histories).
* **integrability**: `Y(d)` is integrable for every fixed treatment vector. -/
structure Assumptions (S : PODynLATESystem P γ₀ γ₁)
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] : Prop where
  consistency : P.Consistency
  compositionConsistency : P.CompositionConsistency
  ignorability1 : ∀ z : Fin 2 → Bool,
    P.CondIndepCFBundle (RegimedVar.ofFactual S.z1Var) (S.cfBundle1 z)
      S.historyBundle1 P.μ
  ignorability2 : ∀ z₂ : Bool,
    P.CondIndepCFBundle (RegimedVar.ofFactual S.z2Var) (S.cfBundle2 z₂)
      S.historyBundle2 P.μ
  overlap1 : ∀ z₁ : Bool, ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle1.condExpGiven (S.z1Var.indicator z₁) P.μ ω
  overlap2 : ∀ z₂ : Bool, ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle2.condExpGiven (S.z2Var.indicator z₂) P.μ ω
  relevance1 : ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle1.condExpGiven
        (fun ω' => ((S.D1ofZ ![true, false] ω').toNat : ℝ) -
                   ((S.D1ofZ ![false, false] ω').toNat : ℝ)) P.μ ω
  relevance2 : ∀ᵐ ω ∂P.μ,
    0 < S.historyBundle2.condExpGiven
        (fun ω' => ((S.D2ofZ ![S.factualZ1 ω', true] ω').toNat : ℝ) -
                   ((S.D2ofZ ![S.factualZ1 ω', false] ω').toNat : ℝ)) P.μ ω
  oneSidedNoncompliance : ∀ z : Fin 2 → Bool, ∀ᵐ ω ∂P.μ,
    S.D1ofZ z ω ≤ z 0 ∧ S.D2ofZ z ω ≤ z 1
  /-- Exclusion: `Y` under the joint encouragement-and-treatment regime
  equals `Y` under the treatment-only regime (pointwise).  Captures the
  primitive-process clause `Y(D, S)`. -/
  exclusion : ∀ (z d : Fin 2 → Bool) (ω : P.Ω),
    S.yVar.cf (S.encTreatRegime z d) ω = S.YofD d ω
  /-- **Primitive-process clause for `D₁`** (def:po-dynamic-late-assumptions
  primitive process `D₁(Z₁, S₀)`).  `D₁` does not depend on `Z₂`: the value
  of `D₁` under the joint encouragement regime fixing both `Z`'s agrees
  pointwise with its value under the regime fixing only `Z₁`.  This is the
  Lean-level encoding of the doc's "encouragements affect the terminal
  outcome only through treatment and state histories" applied at `D₁`. -/
  exclusion_D1 : ∀ (z : Fin 2 → Bool) (ω : P.Ω),
    S.d1Var.cf (S.encouragementRegime z) ω
      = S.d1Var.cf (Regime.single S.Z1 (S.hZ1bool.symm (z 0))) ω
  /-- **Primitive-process clause for `Z₁`** (def:po-dynamic-late-assumptions
  primitive process `Z₁(S₀)`).  `Z₁` does not depend on `Z₂`: the structural
  eval of `Z₁` under any regime fixing only `Z₂` agrees with its factual
  eval (under the empty regime).  Used by the stage-1 composition consistency
  rewrite `YofDofZ_eq_YofZ2_on_z1Event` to apply `CompositionConsistency.composition`
  with `r₁ := encZ2Regime z₂`, `r₂ := Regime.single Z₁ (...)` on the event
  `{Z₁ = z 0}` (the `IntermediateAgrees` premise asks that `P.eval (encZ2Regime z₂) ω S.Z1`
  equals the assigned value, which by this clause + factual `Z₁ = z 0` is
  exactly `S.hZ1bool.symm (z 0)`). -/
  exclusion_Z1 : ∀ (z₂ : Bool) (ω : P.Ω),
    P.eval (S.encZ2Regime z₂) ω S.Z1 = P.eval Regime.empty ω S.Z1
  integrable_YofD : ∀ d : Fin 2 → Bool, Integrable (S.YofD d) P.μ
  integrable_YofDofZ : ∀ z : Fin 2 → Bool, Integrable (S.YofDofZ z) P.μ
  integrable_YofZ2 : ∀ z₂ : Bool, Integrable (S.YofZ2 z₂) P.μ

namespace Assumptions

/-- Compatibility projection for older call sites: factual outcome integrability
is derived from consistency plus integrability of the two `YofZ2` cells. -/
@[fun_prop]
lemma integrable_factualY [StandardBorelSpace P.Ω] (As : S.Assumptions) :
    Integrable S.factualY P.μ :=
  S.integrable_factualY_of_consistency_integrable_YofZ2 As.consistency As.integrable_YofZ2

end Assumptions

end PODynLATESystem

end PO
end Causalean
