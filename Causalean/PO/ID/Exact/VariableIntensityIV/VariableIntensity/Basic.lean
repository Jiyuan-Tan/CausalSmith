/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity instrumental variables

A directed-pair Wald specialization of the Angrist--Imbens causal-response
algebra for finite ordered treatment intensities: one directed instrument
contrast identifies an average causal response over the treatment-intensity
margins crossed by that contrast. This file does not derive the paper's general
population 2SLS characterization for multivalued instruments.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.PO.ID.Exact.VariableIntensityIV.OrderedTreatment
public import Causalean.Tactic.Attr

/-! # Variable-intensity IV definitions and counterfactual bundles

This part defines the ordered-treatment IV system, its factual and counterfactual variables,
margin-crossing quantities, population contrasts, and validity assumptions. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO.ID.Exact
namespace VariableIntensityIV

open Finset MeasureTheory ProbabilityTheory

noncomputable section

/-- A variable-intensity IV system on [an ambient potential-outcome model, finite instrument
support, and ordered dose scale](hyp:P,𝒵,J) records [an instrument](hyp:Z), [an ordered
treatment intensity](hyp:D), and [a real outcome](hyp:Y), with [at least one treatment
margin](hyp:hJ_pos), [the stated value-space identifications](hyp:hZ𝒵,hDintensity,hYreal), and
[distinct instrument, treatment, and outcome nodes](hyp:hZD,hDY,hZY).

The structure identifies the instrument, treatment, and outcome value spaces. It does not relate
outcomes under joint instrument-and-treatment interventions to treatment-only outcomes, so it
does not impose an ambient no-direct-effect restriction. -/
structure VariableIntensityIVSystem (P : POSystem) (𝒵 : Type*) [MeasurableSpace 𝒵]
    [Fintype 𝒵] [MeasurableSingletonClass 𝒵] (J : ℕ) where
  /-- The ordered treatment has at least one margin. -/
  hJ_pos : 0 < J
  /-- Instrument system variable. -/
  Z : P.V
  /-- Treatment-intensity system variable. -/
  D : P.V
  /-- Outcome system variable. -/
  Y : P.V
  /-- The instrument value space is identified with the finite set `𝒵`. -/
  hZ𝒵 : P.X Z ≃ᵐ 𝒵
  /-- The treatment value space is identified with the ordered levels `Fin (J+1)`. -/
  hDintensity : P.X D ≃ᵐ Fin (J + 1)
  /-- The outcome value space is identified with `ℝ`. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- Instrument and treatment are distinct variables. -/
  hZD : Z ≠ D
  /-- Treatment and outcome are distinct variables. -/
  hDY : D ≠ Y
  /-- Instrument and outcome are distinct variables. -/
  hZY : Z ≠ Y

namespace VariableIntensityIVSystem

variable {P : POSystem} {𝒵 : Type*} [MeasurableSpace 𝒵]
variable [Fintype 𝒵] [MeasurableSingletonClass 𝒵]
variable {J : ℕ} (S : VariableIntensityIVSystem P 𝒵 J)

/-- [The finite-valued instrument variable](goal) exposes the assignment node of [a
variable-intensity IV system](hyp:S) on its observed support. -/
def zVar : POVar P 𝒵 := ⟨S.Z, S.hZ𝒵⟩

/-- [The ordered treatment-intensity variable](goal) exposes uptake in [a variable-intensity IV
system](hyp:S) on levels from zero through the maximum dose. -/
def dVar : POVar P (Fin (J + 1)) := ⟨S.D, S.hDintensity⟩

/-- [The real-valued outcome variable](goal) exposes the response node of [a variable-intensity
IV system](hyp:S) on the scale used for causal contrasts. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- [Potential treatment intensity](goal) records the dose each unit in [a variable-intensity IV
system](hyp:S) would take under [a fixed instrument value](hyp:z), determining which dose margins
the instrument moves that unit across.

It is a genuine single-intervention counterfactual. -/
def DofZ (z : 𝒵) : P.Ω → Fin (J + 1) := S.dVar.cfUnder S.zVar z

/-- [Treatment-indexed potential outcome](goal) records the response each unit in [a
variable-intensity IV system](hyp:S) would have under an intervention fixing [the dose](hyp:d).

This treatment-only response schedule does not by itself constrain outcomes under joint
instrument-and-treatment interventions. -/
def YofD (d : Fin (J + 1)) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- [The observed instrument](goal) records each unit's realized assignment in [a
variable-intensity IV system](hyp:S). -/
def factualZ : P.Ω → 𝒵 := S.zVar.factual

/-- [The observed treatment intensity](goal) records each unit's realized dose in [a
variable-intensity IV system](hyp:S). -/
def factualD : P.Ω → Fin (J + 1) := S.dVar.factual

/-- [The observed outcome](goal) records each unit's realized response in [a variable-intensity IV
system](hyp:S). -/
def factualY : P.Ω → ℝ := S.yVar.factual

/-- [An observed instrument cell](goal) selects units in [a variable-intensity IV
system](hyp:S) whose realized assignment equals [the chosen support value](hyp:z). -/
def zEvent (z : 𝒵) : Set P.Ω := S.zVar.event z

/-- [Potential treatment at a fixed instrument value is measurable](goal), so [the IV
system](hyp:S) can form treatment-response probabilities for [that assignment](hyp:z). -/
@[fun_prop]
lemma measurable_DofZ (z : 𝒵) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- [Potential outcome at a fixed dose is measurable](goal), permitting causal response averages
in [the IV system](hyp:S) at [that treatment level](hyp:d). -/
@[fun_prop]
lemma measurable_YofD (d : Fin (J + 1)) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- [The observed instrument is measurable](goal), making assignment cells observable in [the IV
system](hyp:S). -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual

/-- [The observed treatment intensity is measurable](goal), so realized dose events are defined
in [the IV system](hyp:S). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- [The observed outcome is measurable](goal), so its population moments are defined in [the IV
system](hyp:S). -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- [Each observed instrument cell is measurable](goal), allowing [the IV system](hyp:S) to
condition observed moments on [the selected assignment](hyp:z). -/
lemma measurableSet_zEvent (z : 𝒵) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event z (MeasurableSet.singleton z)

/-! ### Counterfactual bundle for a directed contrast

The IV-validity independence hypothesis is `Z ⟂ (Y(0),…,Y(J), D(z0), D(z1))`.
We package the right-hand side as a `POCFBundle`: two `Fin (J+1)`-valued
components `D(z0), D(z1)` at indices `0, 1`, followed by `J+1` real-valued
outcome components `Y(0),…,Y(J)` at indices `2,…,J+2`. -/

/-- [The regimed treatment response](goal) couples potential dose in [a variable-intensity IV
system](hyp:S) with [the fixed instrument value](hyp:z) that generates it, enabling exogeneity
statements. -/
def dUnderZ (z : 𝒵) : RegimedVar P (Fin (J + 1)) :=
  ⟨S.dVar, Regime.single S.Z (S.hZ𝒵.symm z)⟩

/-- [The regimed outcome response](goal) couples potential outcome in [a variable-intensity IV
system](hyp:S) with [the fixed treatment level](hyp:d) that generates it. -/
def yUnderD (d : Fin (J + 1)) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDintensity.symm d)⟩

/-- [The dose-response counterfactual bundle](goal) collects potential outcomes at every ordered
treatment level in [a variable-intensity IV system](hyp:S), allowing joint instrument
independence to cover the whole response schedule. -/
def outcomeBundle : POCFBundle P where
  n := J + 1
  type := fun _ => ℝ
  inst := fun _ => inferInstance
  vars := fun d => S.yUnderD d

/-- [The directed-contrast counterfactual bundle](goal) joins both potential treatments and the
full dose-response schedule in [a variable-intensity IV system](hyp:S) for [the two instrument
values being compared](hyp:z0,z1).

For the contrast
`(z0, z1)`.  Index `0` is `D(z0)`, index `1` is `D(z1)`, index `d+2` is `Y(d)`. -/
def cfContrastBundle (z0 z1 : 𝒵) : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ z0) (POCFBundle.cons (S.dUnderZ z1) S.outcomeBundle)

/-- [The unit-level causal response on a treatment margin](goal) is the potential-outcome change
across [that adjacent dose increment](hyp:j) in [a variable-intensity IV system](hyp:S). -/
def marginResponse (j : Fin J) : P.Ω → ℝ :=
  fun ω => S.YofD (OrderedTreatment.upperLevel j) ω -
    S.YofD (OrderedTreatment.lowerLevel j) ω

/-- [A margin-crossing subgroup](goal) contains units in [a variable-intensity IV
system](hyp:S) whose potential dose crosses [the selected treatment margin](hyp:j) when the
instrument moves between [the two selected values](hyp:z0,z1). -/
def crossingEvent (z0 z1 : 𝒵) (j : Fin J) : Set P.Ω :=
  {ω | OrderedTreatment.Crossing (S.DofZ z0 ω) (S.DofZ z1 ω) j}

/-- [The margin-crossing probability](goal) is the population share in [a variable-intensity IV
system](hyp:S) moved across [the selected treatment margin](hyp:j) by [the directed instrument
contrast](hyp:z0,z1). -/
def crossingProb (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  (P.μ (S.crossingEvent z0 z1 j)).toReal

/-- [The numeric encoding of ordered treatment levels is measurable](goal) for [the finite dose
scale](hyp:J), allowing treatment intensity to enter population moments. -/
@[fun_prop]
lemma measurable_intensityValue :
    Measurable (fun d : Fin (J + 1) => OrderedTreatment.intensityValue d) := by
  exact (by fun_prop : Measurable fun n : ℕ => (n : ℝ)).comp
    (by fun_prop : Measurable fun d : Fin (J + 1) => d.val)

/-- [Potential treatment intensity at a fixed instrument value is measurable](goal), so [the IV
system](hyp:S) can use it in first-stage moments for [that assignment](hyp:z). -/
@[fun_prop]
lemma measurable_intensityValue_DofZ (z : 𝒵) :
    Measurable (fun ω => OrderedTreatment.intensityValue (S.DofZ z ω)) :=
  (measurable_intensityValue (J := J)).comp (S.measurable_DofZ z)

/-- [Potential treatment intensity at a fixed instrument value is integrable](goal) in [the IV
system](hyp:S) for [that assignment](hyp:z), because the finite ordered dose scale is bounded. -/
@[fun_prop]
lemma integrable_intensityValue_DofZ (z : 𝒵) :
    Integrable (fun ω => OrderedTreatment.intensityValue (S.DofZ z ω)) P.μ := by
  have hbdd : ∀ ω,
      ‖OrderedTreatment.intensityValue (S.DofZ z ω)‖ ≤ (J : ℝ) := by
    intro ω
    change |((S.DofZ z ω).val : ℝ)| ≤ (J : ℝ)
    rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le (S.DofZ z ω).val)]
    exact_mod_cast Nat.le_of_lt_succ (S.DofZ z ω).isLt
  exact (MeasureTheory.integrable_const (J : ℝ)).mono'
    (S.measurable_intensityValue_DofZ z).aestronglyMeasurable
    (Filter.Eventually.of_forall hbdd)

/-- [Each treatment-margin crossing subgroup is measurable](goal) for [the potential-outcome
system, instrument support, ordered dose scale, IV system, directed instrument contrast, and
margin](hyp:P,𝒵,J,S,z0,z1,j), so its population share is well defined. -/
lemma measurableSet_crossingEvent (z0 z1 : 𝒵) (j : Fin J) :
    MeasurableSet (S.crossingEvent z0 z1 j) := by
  unfold crossingEvent OrderedTreatment.Crossing
  have hA : MeasurableSet {d : Fin (J + 1) | OrderedTreatment.upperLevel j ≤ d} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have hB : MeasurableSet {d : Fin (J + 1) | d < OrderedTreatment.upperLevel j} :=
    Set.Finite.measurableSet (Set.toFinite _)
  exact (hA.preimage (S.measurable_DofZ z1)).inter (hB.preimage (S.measurable_DofZ z0))

/-- [The algebraic margin-crossing indicator equals the indicator of the corresponding crossing
subgroup](goal) for [the potential-outcome system, instrument support, ordered dose scale, IV
system, directed contrast, and margin](hyp:P,𝒵,J,S,z0,z1,j), linking telescoping algebra to
event probabilities. -/
lemma crossingIndicator_fun_eq_indicator (z0 z1 : 𝒵) (j : Fin J) :
    (fun ω => OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j)
      = (S.crossingEvent z0 z1 j).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hC : OrderedTreatment.Crossing (S.DofZ z0 ω) (S.DofZ z1 ω) j
  · have hω : ω ∈ S.crossingEvent z0 z1 j := hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_mem hω]
  · have hω : ω ∉ S.crossingEvent z0 z1 j := by
      simpa [crossingEvent] using hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_notMem hω]

/-- [Weighting a margin response by the crossing indicator is exactly restriction to the
margin-crossing subgroup](goal) for [the potential-outcome system, instrument support, ordered
dose scale, IV system, directed contrast, and margin](hyp:P,𝒵,J,S,z0,z1,j). This turns
telescoped outcome changes into subgroup integrals. -/
lemma marginResponse_mul_crossingIndicator_eq_indicator (z0 z1 : 𝒵)
    (j : Fin J) :
    (fun ω => S.marginResponse j ω *
        OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j)
      = (S.crossingEvent z0 z1 j).indicator (S.marginResponse j) := by
  funext ω
  by_cases hC : OrderedTreatment.Crossing (S.DofZ z0 ω) (S.DofZ z1 ω) j
  · have hω : ω ∈ S.crossingEvent z0 z1 j := hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_mem hω]
  · have hω : ω ∉ S.crossingEvent z0 z1 j := by
      simpa [crossingEvent] using hC
    simp [OrderedTreatment.crossingIndicator, hC,
      Set.indicator_of_notMem hω]

/-- [Total crossing probability](goal) is the sum of the shares moved across each treatment
margin in [a variable-intensity IV system](hyp:S) by [the directed instrument
contrast](hyp:z0,z1); under monotonicity it is the first-stage denominator.

It is equivalently the first-stage denominator under
directed monotonicity. -/
def totalCrossingProb (z0 z1 : 𝒵) : ℝ :=
  ∑ j : Fin J, S.crossingProb z0 z1 j

/-- [A normalized margin-crossing weight](goal) is the share of the total first stage contributed
by [one treatment margin](hyp:j) in [a variable-intensity IV system](hyp:S) for [the directed
instrument contrast](hyp:z0,z1). -/
def crossingWeight (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  OrderedTreatment.normalizedWeight (S.crossingProb z0 z1) j

/-- [The indicator-weighted margin effect](goal) is the population contribution from [one causal
dose margin](hyp:j) among units in [a variable-intensity IV system](hyp:S) moved across it by [the
directed instrument contrast](hyp:z0,z1).

It is represented as a set
integral over the crossing event. -/
def indicatorWeightedEffect (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  ∫ ω in S.crossingEvent z0 z1 j, S.marginResponse j ω ∂P.μ

/-- [The unnormalized average-causal-response contrast](goal) sums causal responses over every
margin crossed in [a variable-intensity IV system](hyp:S) by [the directed instrument
contrast](hyp:z0,z1). -/
def unnormalizedACRContrast (z0 z1 : 𝒵) : ℝ :=
  ∑ j : Fin J, S.indicatorWeightedEffect z0 z1 j

/-- [The indicator-weighted average causal response](goal) divides the aggregate crossed-margin
effect in [a variable-intensity IV system](hyp:S) by the total crossing probability for [the
directed instrument contrast](hyp:z0,z1).

This ratio avoids partial conditional means in the
core algebra. -/
def indicatorWeightedACR (z0 z1 : 𝒵) : ℝ :=
  S.unnormalizedACRContrast z0 z1 / S.totalCrossingProb z0 z1

/-- [The conditional margin response](goal) averages the unit causal response on [one treatment
margin](hyp:j) among units in [a variable-intensity IV system](hyp:S) whose dose crosses it under
[the directed instrument contrast](hyp:z0,z1).

No positivity or integrability side condition is required for this definition. -/
def conditionalMarginResponse (z0 z1 : 𝒵) (j : Fin J) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.crossingEvent z0 z1 j) (S.marginResponse j)

/-- [The Angrist--Imbens average causal response](goal) averages margin-specific causal responses
in [a variable-intensity IV system](hyp:S) with weights equal to their shares of [the directed
instrument contrast's](hyp:z0,z1) first stage. -/
def averageCausalResponse (z0 z1 : 𝒵) : ℝ :=
  ∑ j : Fin J, S.crossingWeight z0 z1 j * S.conditionalMarginResponse z0 z1 j

/-- [The composed dose-response schedule](goal) evaluates each unit's treatment-indexed response
in [a variable-intensity IV system](hyp:S) at the potential dose selected by [the chosen
instrument value](hyp:z).

It is the pointwise composition `Y(D(z))`. Without a separate exclusion or composition
assumption, it is not identified with the ambient outcome under an intervention on the
instrument. -/
def YofDofZ (z : 𝒵) : P.Ω → ℝ :=
  fun ω => S.YofD (S.DofZ z ω) ω

/-- [The composed dose-response schedule equals the treatment-indexed response evaluated at the
selected potential dose](goal) for [the potential-outcome system, finite instrument support, and
ordered dose scale](hyp:P,𝒵,J), [the variable-intensity IV system](hyp:S), and [the chosen
instrument value](hyp:z). -/
@[causal_defs_simps]
lemma YofDofZ_def (z : 𝒵) :
    S.YofDofZ z = fun ω => S.YofD (S.DofZ z ω) ω :=
  rfl

/-- [The composed dose-response schedule is measurable](goal), so [the variable-intensity IV
system](hyp:S) admits moments of that schedule for [the chosen instrument value](hyp:z). -/
@[fun_prop]
lemma measurable_YofDofZ (z : 𝒵) :
    Measurable (S.YofDofZ z) := by
  classical
  unfold YofDofZ
  have hsum : (fun ω => S.YofD (S.DofZ z ω) ω)
      = fun ω => ∑ d : Fin (J + 1),
          ({d} : Set (Fin (J + 1))).indicator (fun _ => S.YofD d ω) (S.DofZ z ω) := by
    funext ω
    rw [Finset.sum_eq_single (S.DofZ z ω)]
    · simp
    · intro d _ hd
      simp [hd]
    · intro h
      simp at h
  rw [hsum]
  refine Finset.measurable_sum _ ?_
  intro d _
  exact (S.measurable_YofD d).indicator
    ((MeasurableSet.singleton d).preimage (S.measurable_DofZ z))

/-- [The potential first-stage contrast](goal) is the mean dose change induced in [a
variable-intensity IV system](hyp:S) by moving between [two instrument values](hyp:z0,z1).

It is `E[D(z1) − D(z0)]` using potential
treatment intensities. -/
def firstStageContrast (z0 z1 : 𝒵) : ℝ :=
  ∫ ω, (OrderedTreatment.intensityValue (S.DofZ z1 ω) -
    OrderedTreatment.intensityValue (S.DofZ z0 ω)) ∂P.μ

/-- [The composed-response contrast](goal) is the mean difference between the treatment-indexed
response schedules selected in [a variable-intensity IV system](hyp:S) by [two instrument
values](hyp:z0,z1). -/
def reducedFormContrast (z0 z1 : 𝒵) : ℝ :=
  ∫ ω, (S.YofDofZ z1 ω - S.YofDofZ z0 ω) ∂P.μ

/-- [The observed first-stage cell mean](goal) averages realized treatment intensity in [a
variable-intensity IV system](hyp:S) among units receiving [the selected instrument
value](hyp:z).

It is `E[D | Z = z]`, defined via `normalizedRestrictedIntegral` over the cell `{Z = z}`. -/
def condExpDZ (z : 𝒵) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.zEvent z)
    (fun ω => OrderedTreatment.intensityValue (S.factualD ω))

/-- [The observed reduced-form cell mean](goal) averages realized outcomes in [a
variable-intensity IV system](hyp:S) among units receiving [the selected instrument
value](hyp:z).

It is `E[Y | Z = z]`, defined via `normalizedRestrictedIntegral` over the cell `{Z = z}`. -/
def condExpYZ (z : 𝒵) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.zEvent z) S.factualY

/-- [The directed Wald estimand](goal) divides the observed outcome-cell contrast in [a
variable-intensity IV system](hyp:S) by the corresponding treatment-intensity contrast between
[two instrument values](hyp:z0,z1). -/
def wald (z0 z1 : 𝒵) : ℝ :=
  (S.condExpYZ z1 - S.condExpYZ z0) /
    (S.condExpDZ z1 - S.condExpDZ z0)

/-- IV validity for [a directed instrument contrast in a variable-intensity
system](hyp:S,z0,z1) combines [consistency of observed and potential treatment and
outcome](hyp:consistency), [joint instrument independence from the relevant treatment and outcome
responses](hyp:hIndependence), [monotone dose movement](hyp:hMonotone), [a positive first
stage](hyp:hRelevance), and [integrable potential outcomes at every dose](hyp:hIntegrableY).

Consistency (`D = D(Z)`, `Y = Y(D)`) is the project's canonical PO consistency assumption, and
instrument independence makes the factual instrument independent of the contrast's treatment and
treatment-indexed outcome schedules. The record does not add a relation between joint
instrument-and-treatment interventions and treatment-only outcomes. -/
structure ValidContrastAssumptions (z0 z1 : 𝒵) : Prop where
  /-- Consistency (SUTVA): observed `D`/`Y` equal the realized potential
  intensity/outcome, `D = D(Z)`, `Y = Y(D)`. -/
  consistency : P.Consistency
  /-- The instrument is independent of the contrast-relevant treatment and outcome schedules. -/
  hIndependence : P.IndepCF (RegimedVar.ofFactual S.zVar) (S.cfContrastBundle z0 z1) P.μ
  /-- Potential treatment weakly increases along the directed instrument contrast almost surely. -/
  hMonotone : ∀ᵐ ω ∂P.μ, S.DofZ z0 ω ≤ S.DofZ z1 ω
  /-- The directed potential first-stage contrast is strictly positive. -/
  hRelevance : 0 < S.firstStageContrast z0 z1
  /-- The potential outcome at every treatment level is integrable. -/
  hIntegrableY : ∀ d, Integrable (S.YofD d) P.μ

/-- [Each unit-level margin response is integrable](goal) in [the variable-intensity IV
system](hyp:S) under [the contrast's outcome-integrability assumption](hyp:hValid), for [the
selected treatment margin](hyp:j). This licenses margin-specific causal averages. -/
lemma integrable_marginResponse {z0 z1 : 𝒵} (hValid : S.ValidContrastAssumptions z0 z1)
    (j : Fin J) :
    Integrable (S.marginResponse j) P.μ := by
  exact
    (hValid.hIntegrableY (OrderedTreatment.upperLevel j)).sub
      (hValid.hIntegrableY (OrderedTreatment.lowerLevel j))

/-- [The composed dose-response schedule is integrable](goal) for [the potential-outcome system,
finite instrument support, ordered dose scale, IV system, and contrast
endpoints](hyp:P,𝒵,J,S,z0,z1) whenever [the contrast assumptions hold](hyp:hValid), at [any
instrument value](hyp:z). This licenses the composed-response contrast. -/
lemma integrable_YofDofZ {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) (z : 𝒵) :
    Integrable (S.YofDofZ z) P.μ := by
  have hbound : ∀ᵐ ω ∂P.μ,
      ‖S.YofDofZ z ω‖ ≤ (fun ω => ∑ d : Fin (J + 1), ‖S.YofD d ω‖) ω :=
    Filter.Eventually.of_forall fun ω => by
      unfold YofDofZ
      exact Finset.single_le_sum
        (fun d _ => norm_nonneg (S.YofD d ω)) (Finset.mem_univ _)
  have hsum_int : Integrable (fun ω => ∑ d : Fin (J + 1), ‖S.YofD d ω‖) P.μ := by
    classical
    induction (Finset.univ : Finset (Fin (J + 1))) using Finset.induction_on with
    | empty =>
        simp
    | insert a s has ih =>
        simp only [Finset.sum_insert has]
        exact (hValid.hIntegrableY a).norm.add ih
  exact hsum_int.mono' (S.measurable_YofDofZ z).aestronglyMeasurable hbound

end VariableIntensityIVSystem
end
end VariableIntensityIV
end PO.ID.Exact
end Causalean
