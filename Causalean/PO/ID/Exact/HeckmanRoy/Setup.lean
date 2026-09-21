/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Heckman–Vytlacil IV / generalized Roy selection model: data layer

The `POHeckmanRoySystem` structure (def:po-iv-heckman-roy-system) plus all
basic accessors, measurability lemmas, the counterfactual bundle, the
assumption bundle, the interval complier event, and the latent interval
average treatment effect.

Generalises `PO/ID/Exact/LATE.lean` to:
  * an arbitrary measurable instrument value space `α` (with
    `MeasurableSingletonClass`), instead of `Bool`;
  * a latent uniform rank `U : Ω → ℝ` (`U ~ Unif[0,1]`) plus a propensity
    map `p : α → ℝ`, replacing the implicit binary `D` potentials and
    monotonicity by threshold crossing `D(z) = 1_{U ≤ p(z)}`.

No proof of the Wald identity lives here — see `Wald.lean`.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.Tactic.Attr
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

/-! # Heckman-Roy IV Setup

This file defines the potential-outcome data layer for the
Heckman-Vytlacil generalized Roy instrumental-variables model. It packages the
instrument, treatment, outcome, latent selection rank, threshold-crossing
assumptions, interval-complier event, and latent interval average treatment
effect used by the Wald identification proof. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- The Heckman–Vytlacil / generalized Roy instrumental-variable model in the potential-outcome
framework, packaging [an instrument](hyp:Z), [a binary treatment](hyp:D) taken when a latent
selection rank [U](hyp:U) falls below [a propensity threshold `p(Z)` valued in
`[0,1]`](hyp:p,hp_mem), and [a real outcome](hyp:Y) with potential outcomes `Y(0)` and `Y(1)`,
where [the four nodes are pairwise distinct](hyp:hZD,hZY,hZU,hDY,hDU,hYU). This is the setup
behind pairwise-Wald / LATE-type identification of treatment effects from instrument-induced
variation in participation (`def:po-iv-heckman-roy-system`).

`α` is the value space of the instrument; `MeasurableSingletonClass α` makes the
events `{Z = z}` measurable, which the event-conditional pairwise Wald identity
needs. -/
structure POHeckmanRoySystem (P : POSystem) (α : Type*)
    [MeasurableSpace α] [MeasurableSingletonClass α] where
  Z : P.V
  D : P.V
  Y : P.V
  /-- Latent selection rank. -/
  U : P.V
  hZ      : P.X Z ≃ᵐ α
  hDbool  : P.X D ≃ᵐ Bool
  hYreal  : P.X Y ≃ᵐ ℝ
  hUreal  : P.X U ≃ᵐ ℝ
  hZD : Z ≠ D
  hZY : Z ≠ Y
  hZU : Z ≠ U
  hDY : D ≠ Y
  hDU : D ≠ U
  hYU : Y ≠ U
  /-- Propensity-score map `p : α → [0,1]`. -/
  p : α → ℝ
  hp_mem : ∀ z, p z ∈ Set.Icc (0:ℝ) 1

namespace POHeckmanRoySystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POHeckmanRoySystem P α)

/-! ### POVar wrappers -/

/-- [The instrument variable](goal) in [a Heckman--Roy model](hyp:S)
[represents the model's instrument node on its observable value space](step:1). -/
def zVar : POVar P α := ⟨S.Z, S.hZ⟩

/-- [The treatment variable](goal) in [a Heckman--Roy model](hyp:S)
[represents participation as a binary decision](step:1). -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- [The outcome variable](goal) in [a Heckman--Roy model](hyp:S)
[represents the model's outcome node on the real line](step:1). -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- [The latent selection-rank variable](goal) in [a Heckman--Roy model](hyp:S)
[represents the unobserved participation rank on the real line](step:1). -/
def uVar : POVar P ℝ := ⟨S.U, S.hUreal⟩

/-! ### Regimes and counterfactual variables -/

/-- [The instrument intervention](goal) for [a Heckman--Roy model](hyp:S)
[sets the instrument to the selected value](hyp:z) [and leaves all other nodes free](step:1). -/
noncomputable def instrumentRegime (z : α) : Regime P.V P.X :=
  Regime.single S.Z (S.hZ.symm z)

/-- [The treatment intervention](goal) for [a Heckman--Roy model](hyp:S)
[sets participation to the selected treatment state](hyp:d)
[and leaves all other nodes free](step:1). -/
noncomputable def treatmentRegime (d : Bool) : Regime P.V P.X :=
  Regime.single S.D (S.hDbool.symm d)

/-- [The instrument-specific potential treatment](goal) in [a Heckman--Roy model](hyp:S)
[records whether each unit would participate at the selected instrument value](hyp:z)
[under the corresponding instrument intervention](step:1). -/
noncomputable def DofZ (z : α) : P.Ω → Bool := S.dVar.cfUnder S.zVar z

/-- [The treatment-specific potential outcome](goal) in [a Heckman--Roy model](hyp:S)
[records each unit's outcome at the selected participation state](hyp:d)
[under a treatment intervention](step:1). -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- [The factual instrument](goal) [records each unit's observed instrument value](step:1)
in [the Heckman--Roy model](hyp:S). -/
noncomputable def factualZ : P.Ω → α := S.zVar.factual

/-- [The factual treatment](goal) [records each unit's observed participation decision](step:1)
in [the Heckman--Roy model](hyp:S). -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- [The factual outcome](goal) [records each unit's observed real response](step:1)
in [the Heckman--Roy model](hyp:S). -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- [The factual latent rank](goal) [records each unit's unobserved participation rank](step:1)
in [the Heckman--Roy model](hyp:S). -/
noncomputable def factualU : P.Ω → ℝ := S.uVar.factual

/-- [The instrument cell](goal) in [a Heckman--Roy model](hyp:S)
[uses the selected instrument value](hyp:z) and
[contains exactly the units observed at that value](step:1). -/
def zEvent (z : α) : Set P.Ω := S.zVar.event z

/-- [The interval-complier population](goal) for [a Heckman--Roy model](hyp:S)
[is indexed by two instrument values](hyp:z₀,z₁) and [consists of units whose latent rank
lies above the first threshold and at or below the second](step:1). -/
def intervalComplierEvent (z₀ z₁ : α) : Set P.Ω :=
  { ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁ }

/-! ### Measurability -/

/-- [The potential treatment at an instrument value](hyp:S,z) [is measurable](goal), so
its participation event can enter probability and conditional-mean calculations. -/
@[fun_prop]
lemma measurable_DofZ (z : α) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- [The potential outcome at a treatment state](hyp:S,d) [is measurable](goal), so its
population and complier means are well defined. -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- [The observed instrument in the Heckman--Roy model](hyp:S) [is measurable](goal),
making instrument cells observable events. -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual
/-- [The observed participation decision in the Heckman--Roy model](hyp:S)
[is measurable](goal), so first-stage moments are defined. -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- [The observed outcome in the Heckman--Roy model](hyp:S) [is measurable](goal), so
reduced-form moments are defined. -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual
/-- [The latent selection rank in the Heckman--Roy model](hyp:S) [is measurable](goal),
making threshold and interval-complier events measurable. -/
@[fun_prop]
lemma measurable_factualU : Measurable S.factualU := S.uVar.measurable_factual

/-- [The cell for an observed instrument value](hyp:S,z) [is measurable](goal), which is
needed to condition outcome and treatment means on that cell. -/
lemma measurableSet_zEvent (z : α) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _ (measurableSet_singleton _)

/-- [The interval-complier population between two instrument thresholds](hyp:S,z₀,z₁)
[is measurable](goal), so its probability and average treatment effect are defined. -/
lemma measurableSet_intervalComplierEvent (z₀ z₁ : α) :
    MeasurableSet (S.intervalComplierEvent z₀ z₁) := by
  unfold intervalComplierEvent
  exact (measurableSet_lt measurable_const S.measurable_factualU).inter
    (measurableSet_le S.measurable_factualU measurable_const)

/-! ### `Y` composed with `D(z)` and event-conditional means -/

/-- [The outcome induced by an instrument value](goal) in [a Heckman--Roy model](hyp:S)
[uses the selected instrument value](hyp:z) and [chooses each unit's treated or untreated
potential outcome according to the treatment that value would induce](step:1). -/
noncomputable def YofDofZ (z : α) : P.Ω → ℝ :=
  fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω

/-- The potential outcome under the treatment that an instrument value induces sends a unit to
that unit's treated potential outcome when the induced treatment is one, and to its untreated
potential outcome otherwise. -/
@[causal_defs_simps]
lemma YofDofZ_def (z : α) :
    S.YofDofZ z = fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω :=
  rfl

/-- [The outcome induced by an instrument value](hyp:S,z) [is measurable](goal), allowing
its population mean to represent the reduced form. -/
@[fun_prop]
lemma measurable_YofDofZ (z : α) : Measurable (S.YofDofZ z) := by
  unfold YofDofZ
  exact Measurable.ite (S.measurable_DofZ z (MeasurableSet.singleton true))
    (S.measurable_YofD true) (S.measurable_YofD false)

/-- [The instrument-cell treatment mean](goal) for [a Heckman--Roy model](hyp:S)
[uses the selected instrument value](hyp:z) and
[averages observed participation within that cell](step:1).

`E[D | Z = z]`, the treated share among units with instrument value `z`,
as the PO event-conditional expectation `normalizedRestrictedIntegral` over the event `{Z = z}`. -/
noncomputable def condExpDZ (z : α) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.zEvent z) (fun ω => ((S.factualD ω).toNat : ℝ))

/-- [The instrument-cell outcome mean](goal) for [a Heckman--Roy model](hyp:S)
[uses the selected instrument value](hyp:z) and
[averages observed outcomes within that cell](step:1).

`E[Y | Z = z]`, the mean outcome among units with instrument value `z`,
as the PO event-conditional expectation `normalizedRestrictedIntegral` over the event `{Z = z}`. -/
noncomputable def condExpYZ (z : α) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.zEvent z) S.factualY

/-! ### Counterfactual bundle for `Z ⟂ (U, Y(1), Y(0))` -/

/-- [The regime-indexed outcome](goal) in [a Heckman--Roy model](hyp:S)
[uses the selected treatment state](hyp:d) and
[pairs the outcome variable with the intervention fixing that state](step:1). -/
def yUnderD (d : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-- [The counterfactual vector used for instrument exogeneity](goal) in
[a Heckman--Roy model](hyp:S) [collects the latent rank and both treatment-state potential
outcomes](step:1).

Counterfactual bundle `(U, Y(1), Y(0))` -- target of the instrument-
independence assumption.

`D(z)` is *not* bundled because it is determined by `U` via threshold
crossing; instrument-independence from `(U, Y(1), Y(0))` already entails
independence from `D(z)` once threshold crossing is invoked. -/
noncomputable def cfBundle : POCFBundle P :=
  POCFBundle.cons (RegimedVar.ofFactual S.uVar) <|
  POCFBundle.cons (S.yUnderD true) <|
  POCFBundle.cons (S.yUnderD false) <|
  POCFBundle.nil P

/-! ### Assumptions -- def:po-iv-heckman-roy-assumptions -/

/-- **Heckman–Roy IV identifying assumptions** (`def:po-iv-heckman-roy-assumptions`). For
[a Heckman--Roy model](hyp:S), these bundle
[consistency of the underlying potential-outcome system](hyp:consistency), [exogeneity of the
instrument, independent of the latent selection rank and the two potential
outcomes](hyp:instrumentIndep), [threshold-crossing selection: the potential treatment under
instrument value `z` equals `true` exactly when the latent rank falls at or below the propensity
`p(z)`](hyp:thresholdCrossing), and [the latent rank being uniformly distributed on
`[0,1]`](hyp:uniformU).

Exclusion is encoded by the `Y(d)` potential-outcome interface (no `z`
argument).  The classical `Y(z, d) = Y(d)` exclusion is implicit in the
shape of `POHeckmanRoySystem`. -/
structure Assumptions (S : POHeckmanRoySystem P α) : Prop where
  /-- Consistency of the underlying PO system. -/
  consistency : P.Consistency
  /-- Instrument exogeneity: `Z ⟂ (U, Y(1), Y(0))`. -/
  instrumentIndep : P.IndepCF (RegimedVar.ofFactual S.zVar) S.cfBundle P.μ
  /-- Threshold crossing: `D(z) = 1_{U ≤ p(z)}` a.s., for every `z : α`. -/
  thresholdCrossing : ∀ z : α, ∀ᵐ ω ∂P.μ,
      (S.DofZ z ω = true ↔ S.factualU ω ≤ S.p z)
  /-- Uniform-rank lemma: `μ {U ≤ q} = ENNReal.ofReal q` for `q ∈ [0,1]`.
  Captures `U ~ Unif[0,1]` exactly at the granularity used in the proof
  (avoids a Mathlib `IsUniform` detour); see remark
  rem:po-iv-heckman-roy-uniform. -/
  uniformU : ∀ q ∈ Set.Icc (0:ℝ) 1,
      P.μ {ω | S.factualU ω ≤ q} = ENNReal.ofReal q

/-! ### Latent interval average treatment effect -/

/-- [The latent interval average treatment effect](goal) in [a Heckman--Roy model](hyp:S)
[is indexed by a pair of instrument values](hyp:z₀,z₁) and [averages the
treated-minus-untreated potential outcome among units between their propensity thresholds,
returning zero for an empty cell](step:1).

Latent interval average treatment effect at `(z₀, z₁)` --
def:po-iv-heckman-roy-late.

Totalised as `E[Y(1) - Y(0) | C(z₀,z₁)]
  = (∫_C Y(1)-Y(0) dμ) / μ(C).toReal`.

Equals the informal `E[Y(1)-Y(0) | C(z₀,z₁)]` when `μ(C) > 0`. -/
noncomputable def LATE (z₀ z₁ : α) : ℝ :=
  (∫ ω in S.intervalComplierEvent z₀ z₁,
      (S.YofD true ω - S.YofD false ω) ∂P.μ)
    / (P.μ (S.intervalComplierEvent z₀ z₁)).toReal

end POHeckmanRoySystem

end PO
end Causalean
