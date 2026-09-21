/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# IV System and LATE in the Potential Outcome Framework

Implements def:po-iv-system, def:po-iv-assumptions, def:po-late,
prop:po-late, and rem:po-late from Basic Concepts.tex.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.PO.Conditioning.EventCondExp
public import Causalean.Tactic.Attr
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

/-! # Instrumental Variables LATE

This file formalizes the binary-instrument local average treatment effect in
the potential-outcome framework. It defines the IV subsystem `POIVSystem`,
potential treatments `DofZ`, potential outcomes `YofD`, the complier event,
event-conditional observable means, the IV assumption bundle, and the target
`LATE`.

The proof surface decomposes the Wald argument into public identities:
`first_stage_identity`, `reduced_form_identity`, `pointwise_monotonicity`, and
`event_conditioning_identity`. The theorem `late_wald` assembles these pieces
to identify the observable Wald ratio with the complier average treatment
effect. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A binary instrumental-variables subsystem (`def:po-iv-system`) records, within an ambient
potential-outcome system, [an instrument](hyp:Z), [a treatment](hyp:D), and [an
outcome](hyp:Y), where [the three nodes are required to be pairwise distinct](hyp:hZD,hDY,hZY). -/
structure POIVSystem (P : POSystem) where
  Z : P.V
  D : P.V
  Y : P.V
  hZbool : P.X Z ≃ᵐ Bool
  hDbool : P.X D ≃ᵐ Bool
  hYreal : P.X Y ≃ᵐ ℝ
  hZD : Z ≠ D
  hDY : D ≠ Y
  hZY : Z ≠ Y

namespace POIVSystem

variable {P : POSystem} (S : POIVSystem P)

/-- [The binary instrument variable](goal) exposes the instrument node of [an IV
system](hyp:S) on the zero-one scale used by the LATE model. -/
def zVar : POVar P Bool := ⟨S.Z, S.hZbool⟩

/-- [The binary treatment variable](goal) exposes the treatment node of [an IV
system](hyp:S) on the zero-one scale used to define compliance types. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- [The real-valued outcome variable](goal) exposes the outcome node of [an IV
system](hyp:S) on the scale over which treatment effects are averaged. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- [The instrument intervention](goal) fixes [an IV system](hyp:S) at [one binary
instrument value](hyp:z), defining the counterfactual world used for the first stage. -/
noncomputable def instrumentRegime (z : Bool) : Regime P.V P.X :=
  Regime.single S.Z (S.hZbool.symm z)

/-- [The treatment intervention](goal) fixes [an IV system](hyp:S) at [one binary
treatment value](hyp:d), defining the counterfactual world used for causal outcomes. -/
noncomputable def treatmentRegime (d : Bool) : Regime P.V P.X :=
  Regime.single S.D (S.hDbool.symm d)

/-- [Potential treatment](goal) records what each unit in [the IV system](hyp:S) would
choose under [a fixed binary instrument value](hyp:z), which determines compliance type.

The potential treatment under an instrument value is the treatment that
would be observed if the instrument were fixed to that value.

`D(z) : P.Ω → Bool`. -/
noncomputable def DofZ (z : Bool) : P.Ω → Bool :=
  S.dVar.cfUnder S.zVar z

/-- [Potential outcome](goal) records what each unit in [the IV system](hyp:S) would
experience under [a fixed binary treatment value](hyp:d), the primitive contrast averaged by
LATE.

The potential outcome under a treatment value is the outcome that would be
observed if treatment were fixed to that value.

`Y(d) : P.Ω → ℝ`. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ :=
  S.yVar.cfUnder S.dVar d

/-- [The observed instrument](goal) extracts each unit's realized assignment from [the IV
system](hyp:S). -/
noncomputable def factualZ : P.Ω → Bool := S.zVar.factual

/-- [The observed treatment](goal) extracts each unit's realized uptake from [the IV
system](hyp:S). -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- [The observed outcome](goal) extracts each unit's realized response from [the IV
system](hyp:S). -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- [The complier population](goal) in [a binary IV system](hyp:S) consists of units induced
into treatment by switching the instrument on and not treated when it is off. -/
def complierEvent : Set P.Ω :=
  { ω | S.DofZ true ω = true ∧ S.DofZ false ω = false }

/-- [An observed instrument cell](goal) selects units in [the IV system](hyp:S) whose
realized instrument equals [the chosen binary value](hyp:z). -/
def zEvent (z : Bool) : Set P.Ω := S.zVar.event z

/-- [Potential treatment under a fixed instrument value is measurable](goal), so [the IV
system](hyp:S) admits probabilities and expectations involving treatment response to [that
value](hyp:z). -/
@[fun_prop]
lemma measurable_DofZ (z : Bool) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- [The observed instrument is measurable](goal), making its assignment cells observable in
[the IV system](hyp:S). -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual

/-- [The observed treatment is measurable](goal), so treatment-cell probabilities are defined
for [the IV system](hyp:S). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- [The observed outcome is measurable](goal), so its population moments are defined for [the
IV system](hyp:S). -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- [Potential outcome under a fixed treatment value is measurable](goal), permitting causal
outcome averages in [the IV system](hyp:S) for [that treatment arm](hyp:d). -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- [The complier population is a measurable event](goal), so [the IV system](hyp:S) assigns it
a probability and supports complier-conditional outcome means. -/
lemma measurableSet_complierEvent : MeasurableSet S.complierEvent :=
  (S.measurable_DofZ true (MeasurableSpace.measurableSet_top (s := {true}))).inter
    (S.measurable_DofZ false (MeasurableSpace.measurableSet_top (s := {false})))

/-- [Each observed instrument cell is measurable](goal), allowing [the IV system](hyp:S) to
condition observed moments on [the selected assignment](hyp:z). -/
lemma measurableSet_zEvent (z : Bool) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _ (measurableSet_singleton _)

/-- [Outcome under instrument-induced treatment](goal) selects each unit's treated or untreated
potential outcome in [the IV system](hyp:S) according to uptake under [the chosen instrument
value](hyp:z). -/
noncomputable def YofDofZ (z : Bool) : P.Ω → ℝ :=
  fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω

/-- [Instrument-induced outcome equals the treated potential outcome when uptake occurs and the
untreated potential outcome otherwise](goal) in [the IV system](hyp:S) under [the selected
instrument value](hyp:z). -/
@[causal_defs_simps]
lemma YofDofZ_def (z : Bool) :
    S.YofDofZ z = fun ω => if S.DofZ z ω then S.YofD true ω else S.YofD false ω :=
  rfl

/-- [The observed first-stage cell mean](goal) averages treatment uptake in [the IV
system](hyp:S) among units receiving [the selected instrument value](hyp:z).

`E[D | Z = z]`, the event-level conditional expectation of the (0/1-coded)
factual treatment on `{Z = z}`. Uses the shared PO conditioning tool
`normalizedRestrictedIntegral` (definitionally `(∫_A g)/μ(A)`). -/
noncomputable def condExpDZ (z : Bool) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.zEvent z) (fun ω => ((S.factualD ω).toNat : ℝ))

/-- [The observed reduced-form cell mean](goal) averages outcomes in [the IV system](hyp:S)
among units receiving [the selected instrument value](hyp:z).

`E[Y | Z = z]`, the event-level conditional expectation of the factual outcome
on `{Z = z}`, via the shared PO conditioning tool `normalizedRestrictedIntegral`. -/
noncomputable def condExpYZ (z : Bool) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.zEvent z) S.factualY

/-- [Treatment under an instrument intervention](goal) packages the treatment response in [the
IV system](hyp:S) with [the assignment value that generates it](hyp:z), enabling exogeneity
statements about that counterfactual. -/
def dUnderZ (z : Bool) : RegimedVar P Bool :=
  ⟨S.dVar, Regime.single S.Z (S.hZbool.symm z)⟩

/-- [Outcome under a treatment intervention](goal) packages the potential response in [the IV
system](hyp:S) with [the treatment arm that generates it](hyp:d), enabling joint exogeneity
statements.
-/
def yUnderD (d : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-- [The full LATE counterfactual bundle](goal) collects both potential treatments and both
potential outcomes from [the binary IV system](hyp:S), making instrument independence a single
joint assumption. -/
noncomputable def cfBundle : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ true) <|
  POCFBundle.cons (S.dUnderZ false) <|
  POCFBundle.cons (S.yUnderD true) <|
  POCFBundle.cons (S.yUnderD false) <|
  POCFBundle.nil P

/-- **Classical binary-instrument IV assumptions** (`def:po-iv-assumptions`). Bundles
[consistency (SUTVA): the observed treatment and outcome equal the realized potential treatment
and outcome](hyp:consistency), [instrument exogeneity: the instrument is independent of the full
counterfactual bundle of potential treatments and outcomes](hyp:instrumentIndep),
[monotonicity (no defiers): turning the instrument on never moves a unit out of
treatment](hyp:monotonicity), and [relevance: the complier event has positive
probability](hyp:relevance).

Exclusion is encoded by the `Y(d)` potential-outcome interface: outcomes
have no `z` argument, so the instrument cannot affect `Y` except through `D`.
The classical `Y(z, d)` formulation with explicit exclusion `Y(z, d) = Y(d)`
is equivalent under this ontology, and is implicit in our definition of
`POIVSystem`. -/
structure Assumptions (S : POIVSystem P) : Prop where
  /-- Consistency (SUTVA): the observed `D`/`Y` equal the realized potential
      treatment/outcome (`D = D(Z)`, `Y = Y(D)`). Links observed data to the
      counterfactuals. (Exclusion — `Z` affects `Y` only through `D` — is built
      into the `Y(d)` interface: outcomes carry no `z` argument, see the type
      docstring above.) -/
  consistency : P.Consistency
  /-- Instrument independence (random/ignorable instrument): the instrument is
      independent of the full counterfactual bundle, `Z ⟂ (D(1), D(0), Y(1), Y(0))`.
      Phrased as independence of the factual instrument from the counterfactual
      bundle. This is the IV exogeneity condition. -/
  instrumentIndep : P.IndepCF (RegimedVar.ofFactual S.zVar) S.cfBundle P.μ
  /-- Monotonicity (no defiers): turning the instrument on never moves a unit out
      of treatment — `D(1) ≥ D(0)` a.s. On `Bool` this is `D(0)=1 → D(1)=1`. Rules
      out defiers so the IV ratio identifies the complier effect. -/
  monotonicity : ∀ᵐ ω ∂P.μ, S.DofZ false ω = true → S.DofZ true ω = true
  /-- Relevance (non-trivial first stage): the complier event `C = {D(1)=1, D(0)=0}`
      has positive probability, so the instrument actually shifts treatment for a
      positive mass of units (the LATE denominator is non-zero). -/
  relevance : 0 < (P.μ S.complierEvent).toReal

/-- [The local average treatment effect](goal) in [a binary IV system](hyp:S) is the mean treated-
versus-untreated outcome contrast among compliers, with the zero convention when that population
has zero probability.

Local Average Treatment Effect -- def:po-late.

    `E[Y(1) - Y(0) | C]`, the average treatment effect over the complier event
    `C`, via the shared PO conditioning tool `normalizedRestrictedIntegral` (definitionally
    `(∫_C (Y(1)-Y(0)))/P(C)`). Equals the informal `E[Y(1)-Y(0) | C]` when
    `P(C) > 0`. -/
noncomputable def LATE : ℝ :=
  normalizedRestrictedIntegral P.μ S.complierEvent (fun ω => S.YofD true ω - S.YofD false ω)

/-- [Consistency identifies potential treatment with observed treatment](goal) for [an IV system
satisfying the identifying assumptions](hyp:hA), at [an instrument value](hyp:z), and for [a unit
observed in that instrument cell](hyp:ω,hω). -/
lemma DofZ_eq_factualD_on_zEvent (hA : S.Assumptions) (z : Bool)
    {ω : P.Ω} (hω : ω ∈ S.zEvent z) :
    S.DofZ z ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hA.consistency S.dVar S.zVar z S.hZD.symm hω

/-- [Consistency identifies each observed outcome with the potential outcome under realized
treatment](goal) for [an IV system satisfying the identifying assumptions](hyp:hA) and [the unit
being evaluated](hyp:ω). -/
lemma factualY_eq_YofD_factualD (hA : S.Assumptions) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hA.consistency S.yVar S.dVar S.hDY.symm ω

/-- [The observed first-stage contrast equals the complier share](goal) under [the binary-IV
identifying assumptions](hyp:hA) when [both instrument-on](hyp:hZ1) and [instrument-off](hyp:hZ0)
cells have positive probability. Monotonicity is needed to exclude cancellation by defiers. -/
theorem first_stage_identity (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal) :
    S.condExpDZ true - S.condExpDZ false = (P.μ S.complierEvent).toReal := by
  -- Step 1: `condExpDZ z = ∫ (DofZ z ω).toNat ∂μ`.
  have hμne_zero : ∀ z, 0 < (P.μ (S.zEvent z)).toReal →
      P.μ (S.zVar.event z) ≠ 0 := fun z hZ h =>
    absurd hZ (by simp [show S.zEvent z = S.zVar.event z from rfl, h])
  have hμne_top : ∀ z, P.μ (S.zVar.event z) ≠ ⊤ := fun _ => measure_ne_top _ _
  have hCE : ∀ z (_hZ : 0 < (P.μ (S.zEvent z)).toReal),
      S.condExpDZ z = ∫ ω, ((S.DofZ z ω).toNat : ℝ) ∂P.μ := by
    intro z hZ
    -- `h_proj` on the bundle `jointValue`: indices 0,1 are `D(1),D(0)`.
    let h_proj : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
      fun f => ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)).toNat : ℝ)
    have hh_meas : Measurable h_proj := by
      let instCf : ∀ a : Fin 4, MeasurableSpace (S.cfBundle.type a) :=
        fun a => S.cfBundle.inst a
      change Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
        ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)).toNat : ℝ)
      cases z
      · exact (by fun_prop : Measurable fun n : ℕ => (n : ℝ)).comp
          ((by fun_prop : Measurable Bool.toNat).comp
            (measurable_pi_apply (1 : Fin 4)))
      · exact (by fun_prop : Measurable fun n : ℕ => (n : ℝ)).comp
          ((by fun_prop : Measurable Bool.toNat).comp
            (measurable_pi_apply (0 : Fin 4)))
    have h_cons : ∀ ω ∈ S.zVar.event z,
        ((S.factualD ω).toNat : ℝ) = h_proj (S.cfBundle.jointValue ω) := by
      intro ω hω
      rw [← S.DofZ_eq_factualD_on_zEvent hA z hω]
      change ((S.DofZ z ω).toNat : ℝ)
        = ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
              ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)).toNat : ℝ)
      cases z <;> rfl
    have hbridge : S.condExpDZ z =
        normalizedRestrictedIntegral P.μ (S.zVar.event z) (fun ω => ((S.factualD ω).toNat : ℝ)) := rfl
    rw [hbridge,
      POSystem.eventCondExp_of_ae_eq_IndepCF hA.instrumentIndep
        (a := S.zVar) hh_meas
        (measurableSet_singleton z)
        (ae_restrict_of_forall_mem (S.measurableSet_zEvent z) h_cons)
        (hμne_zero z hZ) (hμne_top z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
            ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)).toNat : ℝ)
        = ((S.DofZ z ω).toNat : ℝ)
    cases z <;> rfl
  rw [hCE true hZ1, hCE false hZ0]
  -- Step 2: fold the two integrals into `∫ ((DofZ true).toNat - (DofZ false).toNat) ∂μ`.
  have hDbdd : ∀ z, ∀ ω, |((S.DofZ z ω).toNat : ℝ)| ≤ 1 := fun z ω => by
    cases S.DofZ z ω <;> simp
  have hDint : ∀ z, Integrable (fun ω => ((S.DofZ z ω).toNat : ℝ)) P.μ := fun z =>
    (MeasureTheory.integrable_const (1:ℝ)).mono'
      ((by fun_prop : Measurable (fun n : ℕ => (n : ℝ))).comp
        ((by fun_prop : Measurable Bool.toNat).comp (S.measurable_DofZ z)) |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall (hDbdd z))
  rw [← MeasureTheory.integral_sub (hDint true) (hDint false)]
  -- Step 3: under monotonicity, `(DofZ true).toNat - (DofZ false).toNat = 1_C a.s.`.
  have hInd : ∀ᵐ ω ∂P.μ,
      ((S.DofZ true ω).toNat : ℝ) - ((S.DofZ false ω).toNat : ℝ)
        = S.complierEvent.indicator (fun _ => (1:ℝ)) ω := by
    refine hA.monotonicity.mono (fun ω hω => ?_)
    by_cases h1 : S.DofZ true ω = true
    · by_cases h0 : S.DofZ false ω = true
      · have hnC : ω ∉ S.complierEvent := by
          intro ⟨_, h0'⟩; rw [h0] at h0'; exact Bool.noConfusion h0'
        simp [h1, h0, Set.indicator_of_notMem hnC]
      · have h0' : S.DofZ false ω = false := Bool.not_eq_true _ |>.mp h0
        have hC : ω ∈ S.complierEvent := ⟨h1, h0'⟩
        simp [h1, h0', Set.indicator_of_mem hC]
    · have h1' : S.DofZ true ω = false := Bool.not_eq_true _ |>.mp h1
      by_cases h0 : S.DofZ false ω = true
      · exfalso; rw [hω h0] at h1'; exact Bool.noConfusion h1'.symm
      · have h0' : S.DofZ false ω = false := Bool.not_eq_true _ |>.mp h0
        have hnC : ω ∉ S.complierEvent := by
          intro ⟨h1'', _⟩; rw [h1'] at h1''; exact Bool.false_ne_true h1''
        simp [h1', h0', Set.indicator_of_notMem hnC]
  rw [MeasureTheory.integral_congr_ae hInd]
  rw [MeasureTheory.integral_indicator_const (1:ℝ) S.measurableSet_complierEvent]
  simp [MeasureTheory.measureReal_def]

/-- [The observed outcome contrast across instrument cells equals the population contrast between
instrument-induced potential outcomes](goal) under [the binary-IV identifying
assumptions](hyp:hA), [positive instrument-on](hyp:hZ1) and [instrument-off](hyp:hZ0) cells, and
[integrable treated](hyp:hY1) and [untreated](hyp:hY0) potential outcomes. -/
theorem reduced_form_identity (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    S.condExpYZ true - S.condExpYZ false =
      ∫ ω, (S.YofDofZ true ω - S.YofDofZ false ω) ∂P.μ := by
  -- Measurability and integrability of `YofDofZ z`.
  have hYDZ_meas : ∀ z, Measurable (S.YofDofZ z) := fun z => by
    unfold YofDofZ
    exact Measurable.ite (S.measurable_DofZ z (MeasurableSet.singleton true))
      (S.measurable_YofD true) (S.measurable_YofD false)
  have hYDZ_bdd : ∀ z, ∀ ω,
      |S.YofDofZ z ω| ≤ |S.YofD true ω| + |S.YofD false ω| := fun z ω => by
    have h1 := abs_nonneg (S.YofD true ω)
    have h0 := abs_nonneg (S.YofD false ω)
    unfold YofDofZ; cases S.DofZ z ω <;> simp [h1, h0]
  have hYDZ_int : ∀ z, Integrable (S.YofDofZ z) P.μ := fun z =>
    (hY1.norm.add hY0.norm).mono' (hYDZ_meas z).aestronglyMeasurable
      (Filter.Eventually.of_forall (hYDZ_bdd z))
  -- Step 1: `condExpYZ z = ∫ YofDofZ z ω ∂μ`.
  have hμne_zero : ∀ z, 0 < (P.μ (S.zEvent z)).toReal →
      P.μ (S.zVar.event z) ≠ 0 := fun z hZ h =>
    absurd hZ (by simp [show S.zEvent z = S.zVar.event z from rfl, h])
  have hμne_top : ∀ z, P.μ (S.zVar.event z) ≠ ⊤ := fun _ => measure_ne_top _ _
  have hCE : ∀ z (_hZ : 0 < (P.μ (S.zEvent z)).toReal),
      S.condExpYZ z = ∫ ω, S.YofDofZ z ω ∂P.μ := by
    intro z hZ
    -- `h_proj` on the bundle: indices 0,1 are `D(1),D(0)`; 2,3 are `Y(1),Y(0)`.
    let h_proj : (∀ i : Fin S.cfBundle.n, S.cfBundle.type i) → ℝ :=
      fun f => if ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)) : Bool)
               then ((f (2 : Fin 4)) : ℝ) else ((f (3 : Fin 4)) : ℝ)
    have hh_meas : Measurable h_proj := by
      let instCf : ∀ a : Fin 4, MeasurableSpace (S.cfBundle.type a) :=
        fun a => S.cfBundle.inst a
      change Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
        if ((cond z ((f (0 : Fin 4)) : Bool) ((f (1 : Fin 4)) : Bool)) : Bool)
        then ((f (2 : Fin 4)) : ℝ) else ((f (3 : Fin 4)) : ℝ)
      cases z
      · refine Measurable.ite ?_ ?_ ?_
        · exact (by fun_prop :
            Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
              ((f (1 : Fin 4)) : Bool)) (MeasurableSet.singleton true)
        · exact measurable_pi_apply (2 : Fin 4)
        · exact measurable_pi_apply (3 : Fin 4)
      · refine Measurable.ite ?_ ?_ ?_
        · exact (by fun_prop :
            Measurable fun f : ∀ i : Fin S.cfBundle.n, S.cfBundle.type i =>
              ((f (0 : Fin 4)) : Bool)) (MeasurableSet.singleton true)
        · exact measurable_pi_apply (2 : Fin 4)
        · exact measurable_pi_apply (3 : Fin 4)
    have h_cons : ∀ ω ∈ S.zVar.event z,
        S.factualY ω = h_proj (S.cfBundle.jointValue ω) := by
      intro ω hω
      rw [S.factualY_eq_YofD_factualD hA ω, ← S.DofZ_eq_factualD_on_zEvent hA z hω]
      have hJV0 : (S.cfBundle.jointValue ω (0 : Fin 4) : Bool) = S.DofZ true ω := rfl
      have hJV1 : (S.cfBundle.jointValue ω (1 : Fin 4) : Bool) = S.DofZ false ω := rfl
      have hJV2 : (S.cfBundle.jointValue ω (2 : Fin 4) : ℝ) = S.YofD true ω := rfl
      have hJV3 : (S.cfBundle.jointValue ω (3 : Fin 4) : ℝ) = S.YofD false ω := rfl
      change S.YofD (S.DofZ z ω) ω
        = if ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
                      ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)) : Bool)
          then ((S.cfBundle.jointValue ω (2 : Fin 4)) : ℝ)
          else ((S.cfBundle.jointValue ω (3 : Fin 4)) : ℝ)
      rw [hJV0, hJV1, hJV2, hJV3]
      cases z <;> cases S.DofZ _ ω <;> simp
    have hbridge : S.condExpYZ z =
        normalizedRestrictedIntegral P.μ (S.zVar.event z) S.factualY := rfl
    rw [hbridge,
      POSystem.eventCondExp_of_ae_eq_IndepCF hA.instrumentIndep
        (a := S.zVar) hh_meas
        (measurableSet_singleton z)
        (ae_restrict_of_forall_mem (S.measurableSet_zEvent z) h_cons)
        (hμne_zero z hZ) (hμne_top z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change (if ((cond z ((S.cfBundle.jointValue ω (0 : Fin 4)) : Bool)
                        ((S.cfBundle.jointValue ω (1 : Fin 4)) : Bool)) : Bool)
            then ((S.cfBundle.jointValue ω (2 : Fin 4)) : ℝ)
            else ((S.cfBundle.jointValue ω (3 : Fin 4)) : ℝ)) = S.YofDofZ z ω
    unfold YofDofZ
    cases z <;> rfl
  rw [hCE true hZ1, hCE false hZ0]
  rw [← MeasureTheory.integral_sub (hYDZ_int true) (hYDZ_int false)]

/-- [The instrument-induced outcome change equals the treatment effect on compliers and vanishes
for everyone else, almost surely](goal) under [the binary-IV identifying assumptions](hyp:hA).
This isolates the population whose effect survives in the reduced form. -/
theorem pointwise_monotonicity (hA : S.Assumptions) :
    ∀ᵐ ω ∂P.μ,
      S.YofDofZ true ω - S.YofDofZ false ω
        = (S.YofD true ω - S.YofD false ω) *
            S.complierEvent.indicator (fun _ => (1:ℝ)) ω := by
  refine hA.monotonicity.mono (fun ω hω => ?_)
  unfold YofDofZ complierEvent
  rcases hD1 : S.DofZ true ω <;> rcases hD0 : S.DofZ false ω <;>
    simp_all [Set.indicator]

/-- [The population mean of the complier-restricted treatment effect factors into the complier
share times LATE](goal) for [the binary IV system](hyp:S), converting the reduced-form numerator
into the target estimand. -/
theorem event_conditioning_identity :
    ∫ ω, (S.YofD true ω - S.YofD false ω) *
           S.complierEvent.indicator (fun _ => (1:ℝ)) ω ∂P.μ
      = (P.μ S.complierEvent).toReal * S.LATE := by
  unfold LATE
  have hC : MeasurableSet S.complierEvent := S.measurableSet_complierEvent
  have h_rw :
      (fun ω => (S.YofD true ω - S.YofD false ω) *
                S.complierEvent.indicator (fun _ => (1:ℝ)) ω)
      = S.complierEvent.indicator (fun ω => S.YofD true ω - S.YofD false ω) := by
    funext ω
    by_cases hω : ω ∈ S.complierEvent
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [h_rw, MeasureTheory.integral_indicator hC]
  simpa [mul_comm] using
    (eventCondExp_mul_measure_toReal P.μ S.complierEvent
      (measure_ne_top _ _) (fun ω => S.YofD true ω - S.YofD false ω)).symm

/-- **Wald identification of LATE** (`prop:po-late`). Under [the binary-
instrument LATE identifying assumption bundle](hyp:hA), when [the event
`{Z=1}` has positive probability](hyp:hZ1), [the event `{Z=0}` has positive
probability](hyp:hZ0), and [the potential outcomes under treatment](hyp:hY1)
and [under control](hyp:hY0) are integrable, [the Wald ratio
`(E[Y|Z=1] − E[Y|Z=0]) / (E[D|Z=1] − E[D|Z=0])` equals the local average
treatment effect `LATE`](goal). -/
theorem late_wald (hA : S.Assumptions)
    (hZ1 : 0 < (P.μ (S.zEvent true)).toReal)
    (hZ0 : 0 < (P.μ (S.zEvent false)).toReal)
    (hY1 : Integrable (S.YofD true) P.μ)
    (hY0 : Integrable (S.YofD false) P.μ) :
    (S.condExpYZ true - S.condExpYZ false) /
      (S.condExpDZ true - S.condExpDZ false)
      = S.LATE := by
  rw [S.first_stage_identity hA hZ1 hZ0]
  rw [S.reduced_form_identity hA hZ1 hZ0 hY1 hY0]
  have heq : ∀ᵐ ω ∂P.μ, S.YofDofZ true ω - S.YofDofZ false ω
      = (S.YofD true ω - S.YofD false ω) *
          S.complierEvent.indicator (fun _ => (1:ℝ)) ω := S.pointwise_monotonicity hA
  rw [MeasureTheory.integral_congr_ae heq]
  rw [S.event_conditioning_identity]
  have hC : (P.μ S.complierEvent).toReal ≠ 0 := ne_of_gt hA.relevance
  field_simp

end POIVSystem

end PO
end Causalean
