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

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Causalean.Tactic.Attr

/-! # Heckman-Roy IV Setup

This file defines the potential-outcome data layer for the
Heckman-Vytlacil generalized Roy instrumental-variables model. It packages the
instrument, treatment, outcome, latent selection rank, threshold-crossing
assumptions, interval-complier event, and latent interval average treatment
effect used by the Wald identification proof. -/

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

/-- For [a Heckman--Roy system](hyp:S), the [instrument potential-outcome variable](goal) is its instrument node with its instrument-value representation. -/
def zVar : POVar P α := ⟨S.Z, S.hZ⟩

/-- For [a Heckman--Roy system](hyp:S), the [binary treatment potential-outcome variable](goal) is its treatment node with its binary representation. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- For [a Heckman--Roy system](hyp:S), the [real-valued outcome potential-outcome variable](goal) is its outcome node with its real-valued representation. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- For [a Heckman--Roy system](hyp:S), the [latent-rank potential-outcome variable](goal) is its latent selection-rank node with its real-valued representation. -/
def uVar : POVar P ℝ := ⟨S.U, S.hUreal⟩

/-! ### Regimes and counterfactual variables -/

/-- For [a Heckman--Roy system](hyp:S) and [an instrument value](hyp:z), the [instrument intervention regime](goal) fixes the instrument to that value. -/
noncomputable def instrumentRegime (z : α) : Regime P.V P.X :=
  Regime.single S.Z (S.hZ.symm z)

/-- For [a Heckman--Roy system](hyp:S) and [a treatment value](hyp:d), the [treatment intervention regime](goal) fixes treatment to that value. -/
noncomputable def treatmentRegime (d : Bool) : Regime P.V P.X :=
  Regime.single S.D (S.hDbool.symm d)

/-- For [a Heckman--Roy system](hyp:S) and [an instrument value](hyp:z), the [potential treatment](goal) assigns each unit the treatment it would take under that instrument value. -/
noncomputable def DofZ (z : α) : P.Ω → Bool := S.dVar.cfUnder S.zVar z

/-- For [a Heckman--Roy system](hyp:S) and [a treatment value](hyp:d), the [potential outcome](goal) assigns each unit the outcome it would have under that treatment value. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- For [a Heckman--Roy system](hyp:S), the [factual instrument](goal) assigns each unit its observed instrument value. -/
noncomputable def factualZ : P.Ω → α := S.zVar.factual

/-- For [a Heckman--Roy system](hyp:S), the [factual treatment](goal) assigns each unit its observed binary treatment. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- For [a Heckman--Roy system](hyp:S), the [factual outcome](goal) assigns each unit its observed real outcome. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- For [a Heckman--Roy system](hyp:S), the [factual latent selection rank](goal) assigns each unit its latent real-valued rank. -/
noncomputable def factualU : P.Ω → ℝ := S.uVar.factual

/-- For [a Heckman--Roy system](hyp:S) and [an instrument value](hyp:z), the [instrument event](goal) is the set of units whose observed instrument equals that value. -/
def zEvent (z : α) : Set P.Ω := S.zVar.event z

/-- For [a Heckman--Roy system](hyp:S) and [two instrument values](hyp:z₀,z₁), the [interval-complier event](goal) is the set of units whose latent rank is strictly above the first propensity threshold and no greater than the second. -/
def intervalComplierEvent (z₀ z₁ : α) : Set P.Ω :=
  { ω | S.p z₀ < S.factualU ω ∧ S.factualU ω ≤ S.p z₁ }

/-! ### Measurability -/

/-- For [a fixed instrument value `z`](hyp:z), [the potential treatment `D(z)` is
measurable](goal). -/
@[fun_prop]
lemma measurable_DofZ (z : α) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- The potential outcome under a fixed treatment value is measurable. -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- The factual instrument is measurable. -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual
/-- The factual treatment is measurable. -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- The factual outcome is measurable. -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual
/-- The factual latent rank is measurable. -/
@[fun_prop]
lemma measurable_factualU : Measurable S.factualU := S.uVar.measurable_factual

/-- The factual instrument event is measurable. -/
lemma measurableSet_zEvent (z : α) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _ (measurableSet_singleton _)

/-- The latent interval complier event is measurable. -/
lemma measurableSet_intervalComplierEvent (z₀ z₁ : α) :
    MeasurableSet (S.intervalComplierEvent z₀ z₁) := by
  unfold intervalComplierEvent
  exact (measurableSet_lt measurable_const S.measurable_factualU).inter
    (measurableSet_le S.measurable_factualU measurable_const)

/-! ### `Y` composed with `D(z)` and event-conditional means -/

/-- For [a Heckman--Roy system](hyp:S) and [an instrument value](hyp:z), the [outcome under the instrument-induced treatment](goal) assigns each unit its treated potential outcome if that instrument induces treatment and its untreated potential outcome otherwise. -/
noncomputable def YofDofZ (z : α) : P.Ω → ℝ :=
  fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω

/-- The potential outcome under the treatment that an instrument value induces sends a unit to
that unit's treated potential outcome when the induced treatment is one, and to its untreated
potential outcome otherwise. -/
@[causal_defs_simps]
lemma YofDofZ_def (z : α) :
    S.YofDofZ z = fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω :=
  rfl

/-- The outcome composed with the instrument-induced treatment is measurable. -/
@[fun_prop]
lemma measurable_YofDofZ (z : α) : Measurable (S.YofDofZ z) := by
  unfold YofDofZ
  exact Measurable.ite (S.measurable_DofZ z (MeasurableSet.singleton true))
    (S.measurable_YofD true) (S.measurable_YofD false)

/-- For [a Heckman--Roy system](hyp:S) and [an instrument value](hyp:z), the [conditional treatment mean](goal) is the event-conditional mean of observed treatment among units with that instrument value.

`E[D | Z = z]`, the treated share among units with instrument value `z`,
as the PO event-conditional expectation `eventCondExp` over the event `{Z = z}`. -/
noncomputable def condExpDZ (z : α) : ℝ :=
  eventCondExp P.μ (S.zEvent z) (fun ω => ((S.factualD ω).toNat : ℝ))

/-- For [a Heckman--Roy system](hyp:S) and [an instrument value](hyp:z), the [conditional outcome mean](goal) is the event-conditional mean of the observed outcome among units with that instrument value.

`E[Y | Z = z]`, the mean outcome among units with instrument value `z`,
as the PO event-conditional expectation `eventCondExp` over the event `{Z = z}`. -/
noncomputable def condExpYZ (z : α) : ℝ :=
  eventCondExp P.μ (S.zEvent z) S.factualY

/-! ### Counterfactual bundle for `Z ⟂ (U, Y(1), Y(0))` -/

/-- For [a Heckman--Roy system](hyp:S) and [a treatment value](hyp:d), the [outcome under the treatment regime](goal) is the potential outcome represented together with the intervention fixing treatment to that value. -/
def yUnderD (d : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-- For [a Heckman--Roy system](hyp:S), the [counterfactual bundle](goal) contains the latent rank and the potential outcomes under treatment and control.

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

/-- **Heckman–Roy IV identifying assumptions** (`def:po-iv-heckman-roy-assumptions`). Bundles
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

/-- For [a Heckman--Roy system](hyp:S) and [two instrument values](hyp:z₀,z₁), the [latent interval average treatment effect](goal) is the mean difference between treated and untreated potential outcomes among units whose latent ranks lie strictly above the first propensity threshold and no greater than the second, with value zero when that event has zero probability.

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
