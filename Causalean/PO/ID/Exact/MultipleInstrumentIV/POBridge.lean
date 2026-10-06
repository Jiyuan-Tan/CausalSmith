/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Potential-outcome layer for finite multiple-IV response-type algebra

This file puts the finite response-type algebra (`FiniteIndex`,
`ResponseTypeStats`, `PopulationBridge`, `ObservedBridge`) on top of an explicit
potential-outcome system. It discharges the two transferred-assumption fields of
`ObservedBridge` (`outcome_cell`, `treatment_cell`) by deriving
the instrument-cell conditional means from consistency and instrument
independence, exactly as `PO/ID/Exact/LATE.lean` does for the binary-instrument
Wald ratio.

The construction:

* `POMultipleIVSystem` records a `Fin K`-valued instrument `Z`, a binary
  treatment `D`, and a real outcome `Y` inside a `POSystem`.
* The response type of a unit is `G = (D(z⁰), …, D(z^{K-1}))`, a genuine
  counterfactual object; its masses and within-type conditional effects
  `Δ_g = E[Y(1)-Y(0) | G=g]` populate the finite `ResponseTypeStats`.
* `Assumptions` requires consistency and, for each support point, instrument
  independence `Z ⟂ (D(zᵏ), Y(1), Y(0))` (the IV exogeneity condition).
* The end result restates the observed centered-score IV ratio `E[h(Z)Y]/E[h(Z)D]` as the
  response-type weighted sum `Σ_g ω_g Δ_g` in real PO language. It does not
  derive the score from a first-stage projection or derive sign alignment from
  MTW partial monotonicity.

Background labels: `def:po-estimand-mtw-system`, `ass:po-estimand-mtw-iv-validity`,
`def:po-estimand-mtw-population-2sls`, `thm:po-estimand-mtw-signed-decomposition`,
`prop:po-estimand-mtw-response-type-form`. The cited 2SLS results require the fitted
first-stage score; the generic score endpoint below does not establish that premise.
NL artifact: `doc/basic_concepts/po/estimand_characterization/mogstad_torgovitsky_walters_multiple_iv.md`.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.PO.Conditioning.EventCondExp
public import Causalean.PO.ID.Exact.MultipleInstrumentIV.Main
public import Causalean.Tactic.Attr

/-! # Multiple-Instrument IV Potential-Outcome Bridge

This file grounds a multiple-instrument finite response-type algebra in a
potential-outcome system. The structure `POMultipleIVSystem` records a finite
instrument, binary treatment, and real outcome; `responseType`, `mass`,
`effect`, `toStats`, and `toPopulationBridge` turn its counterfactual response
types into the finite response-type algebra.

The bridge lemmas `treatmentDrop` and `outcomeDrop` derive instrument-cell
conditional means from consistency and instrument independence. The definitions
`toObservedBridge` and theorem
`observedCenteredScoreIV_eq_responseTypeWeightedSum` assemble those derived cell
identities into an observed finite-support centered-score response-type identity. The
behavioral and empirical conditions of the full MTW characterization are not
formalized here, nor is the supplied score proved to be a first-stage fit. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset MeasureTheory ProbabilityTheory Causalean.PO

noncomputable section

/-- A multiple-instrument IV potential-outcome subsystem within [a potential-outcome
system](hyp:P) and [finite instrument support](hyp:K) records [an instrument node with that
support](hyp:Z,hZfin), [a binary treatment node](hyp:D,hDbool), and [a real-valued outcome
node](hyp:Y,hYreal), subject to [the three nodes being pairwise distinct](hyp:hZD,hDY,hZY). -/
structure POMultipleIVSystem (P : Causalean.PO.POSystem) (K : ℕ) where
  /-- Instrument node. -/
  Z : P.V
  /-- Treatment node. -/
  D : P.V
  /-- Outcome node. -/
  Y : P.V
  /-- The instrument value space is a `Fin K` support. -/
  hZfin : P.X Z ≃ᵐ Fin K
  /-- The treatment is binary. -/
  hDbool : P.X D ≃ᵐ Bool
  /-- The outcome is real. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- The instrument and treatment are distinct nodes. -/
  hZD : Z ≠ D
  /-- The treatment and outcome are distinct nodes. -/
  hDY : D ≠ Y
  /-- The instrument and outcome are distinct nodes. -/
  hZY : Z ≠ Y

namespace POMultipleIVSystem

variable {P : Causalean.PO.POSystem} {K : ℕ} (S : POMultipleIVSystem P K)

/-- [The finite-valued instrument variable](goal) exposes the assignment node of [a
multiple-instrument IV subsystem](hyp:S) inside [the potential-outcome system](hyp:P) on [its
finite support](hyp:K). -/
def zVar : POVar P (Fin K) := ⟨S.Z, S.hZfin⟩

/-- [The binary treatment variable](goal) exposes uptake from [a multiple-instrument IV
subsystem](hyp:S) inside [the potential-outcome system](hyp:P) with [finite instrument
support](hyp:K). -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- [The real-valued outcome variable](goal) exposes the response from [a multiple-instrument IV
subsystem](hyp:S) inside [the potential-outcome system](hyp:P) with [finite instrument
support](hyp:K). -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- [Potential treatment](goal) records binary uptake in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) under [a fixed instrument support
point](hyp:k) from [the finite support](hyp:K). -/
def DofZ (k : Fin K) : P.Ω → Bool := S.dVar.cfUnder S.zVar k

/-- [Potential outcome](goal) records the response in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) under [a fixed treatment arm](hyp:d),
with exclusion encoded structurally over [the finite instrument support](hyp:K). -/
def YofD (d : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- [The observed instrument](goal) records realized assignment in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) on [the finite support](hyp:K). -/
def factualZ : P.Ω → Fin K := S.zVar.factual

/-- [The observed treatment](goal) records realized binary uptake in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) with [finite instrument
support](hyp:K). -/
def factualD : P.Ω → Bool := S.dVar.factual

/-- [The observed outcome](goal) records realized response in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) with [finite instrument
support](hyp:K). -/
def factualY : P.Ω → ℝ := S.yVar.factual

/-- [The treatment response-type map](goal) collects each unit's potential uptake at every point
of [the finite instrument support](hyp:K) in [a multiple-instrument IV subsystem](hyp:S) of [the
potential-outcome system](hyp:P). -/
def responseType : P.Ω → ResponseType K := fun ω k => S.DofZ k ω

/-- [A response-type subgroup](goal) selects units in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) whose treatment-response vector equals
[the chosen type](hyp:g) on [the finite support](hyp:K). -/
def gEvent (g : ResponseType K) : Set P.Ω := S.responseType ⁻¹' {g}

/-- [An observed instrument cell](goal) selects units in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) assigned to [one support
point](hyp:k) in [the finite support](hyp:K). -/
def zEvent (k : Fin K) : Set P.Ω := S.zVar.event k

/-- [Outcome under instrument-induced treatment](goal) selects the treated or untreated
potential outcome in [a multiple-instrument IV subsystem](hyp:S) of [the potential-outcome
system](hyp:P) according to uptake induced by [one support point](hyp:k) in [the finite
support](hyp:K). -/
def YofDofZ (k : Fin K) : P.Ω → ℝ :=
  fun ω => if S.DofZ k ω then S.YofD true ω else S.YofD false ω

/-- [Instrument-induced outcome equals the treated potential outcome when uptake occurs and the
untreated potential outcome otherwise](goal) in [a multiple-instrument IV subsystem](hyp:S), at
[the chosen support point](hyp:k) of [the finite support](hyp:K). -/
@[causal_defs_simps]
lemma YofDofZ_def (k : Fin K) :
    S.YofDofZ k = fun ω => if S.DofZ k ω then S.YofD true ω else S.YofD false ω :=
  rfl

/-- [The regimed treatment response](goal) couples potential uptake in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) with [the support point](hyp:k) fixed
from [the finite instrument support](hyp:K). -/
def dUnderZ (k : Fin K) : RegimedVar P Bool :=
  ⟨S.dVar, Regime.single S.Z (S.hZfin.symm k)⟩

/-- [The regimed outcome response](goal) couples potential outcome in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) with [the fixed treatment arm](hyp:d),
over [the finite instrument support](hyp:K). -/
def yUnderD (d : Bool) : RegimedVar P ℝ :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-- [The support-point counterfactual cell](goal) bundles potential treatment under [one
instrument value](hyp:k) with both treatment-arm outcomes in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) on [the finite support](hyp:K). -/
def cfCell (k : Fin K) : POCFBundle P :=
  POCFBundle.cons (S.dUnderZ k) <|
  POCFBundle.cons (S.yUnderD true) <|
  POCFBundle.cons (S.yUnderD false) <|
  POCFBundle.nil P

/-! ### Measurability -/

/-- [Potential treatment at an instrument support point is measurable](goal) in [a
multiple-instrument IV subsystem](hyp:S), for [that point](hyp:k) of [the finite
support](hyp:K) in [the potential-outcome system](hyp:P). -/
@[fun_prop]
lemma measurable_DofZ (k : Fin K) : Measurable (S.DofZ k) :=
  S.dVar.measurable_cfUnder S.zVar k

/-- [Potential outcome under a treatment arm is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S), for [that arm](hyp:d) within [the potential-outcome system](hyp:P) and [finite
instrument support](hyp:K). -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- [The observed instrument is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) on [the finite support](hyp:K), making
instrument cells observable. -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual

/-- [The observed treatment is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) with [finite instrument
support](hyp:K). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual

/-- [The observed outcome is measurable](goal) in [a multiple-instrument IV subsystem](hyp:S) of
[the potential-outcome system](hyp:P) with [finite instrument support](hyp:K), so its moments are
defined. -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- [The full treatment response-type map is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S) of [the potential-outcome system](hyp:P) on [the finite support](hyp:K), making
latent type cells measurable. -/
@[fun_prop]
lemma measurable_responseType : Measurable S.responseType :=
  measurable_pi_lambda _ (fun k => S.measurable_DofZ k)

/-- [Each response-type subgroup is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S), for [the selected type](hyp:g) on [the finite support](hyp:K) within [the
potential-outcome system](hyp:P). -/
lemma measurableSet_gEvent (g : ResponseType K) : MeasurableSet (S.gEvent g) :=
  S.measurable_responseType (measurableSet_singleton g)

/-- [Each observed instrument cell is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S), for [the selected point](hyp:k) of [the finite support](hyp:K) within [the
potential-outcome system](hyp:P). -/
lemma measurableSet_zEvent (k : Fin K) : MeasurableSet (S.zEvent k) :=
  S.zVar.measurableSet_event k (measurableSet_singleton k)

/-- [Outcome under instrument-induced treatment is measurable](goal) in [a multiple-instrument IV
subsystem](hyp:S), for [the selected point](hyp:k) of [the finite support](hyp:K) within [the
potential-outcome system](hyp:P). -/
@[fun_prop]
lemma measurable_YofDofZ (k : Fin K) : Measurable (S.YofDofZ k) := by
  unfold YofDofZ
  exact Measurable.ite (S.measurable_DofZ k (MeasurableSet.singleton true))
    (S.measurable_YofD true) (S.measurable_YofD false)

/-! ### Assumptions -/

/-- **Local multi-instrument bridge assumptions.** [A multiple-instrument subsystem](hyp:S) in
[a potential-outcome system](hyp:P) with [finite instrument support](hyp:K) assumes [the observed
treatment and outcome equal the potential treatment and outcome realized under the actual
instrument value](hyp:consistency), and [at each support point the instrument is independent of
the potential treatment there and both treatment-arm potential outcomes](hyp:instrumentIndep).

Exclusion is encoded by the `Y(d)` interface (outcomes carry no `z` argument, so
the instrument cannot affect `Y` except through `D`), exactly as in
`PO.POIVSystem`. Unlike `ass:po-estimand-mtw-iv-validity`, this structure uses
support-pointwise independence rather than full joint independence and does not
store overlap; the endpoint below supplies positive cell mass separately. -/
structure Assumptions (S : POMultipleIVSystem P K) : Prop where
  /-- Consistency (SUTVA): observed `D`/`Y` equal the realized potential
  treatment/outcome. -/
  consistency : P.Consistency
  /-- Instrument independence (IV exogeneity): for each support point, the
  instrument is independent of the counterfactual cell `(D(zᵏ), Y(1), Y(0))`.
  This is implied by (and weaker than) full joint independence of `Z` from all
  potential outcomes; it is exactly what the cell-conditional-mean derivations
  below consume. -/
  instrumentIndep :
    ∀ k : Fin K, P.IndepCF (RegimedVar.ofFactual S.zVar) (S.cfCell k) P.μ

/-! ### Consistency-on-cell rewrites -/

/-- [Consistency identifies potential treatment with observed treatment inside an instrument
cell](goal) under [the local multi-instrument assumptions](hyp:hA), for [the support
point](hyp:k) and [a unit observed in its cell](hyp:ω,hω). -/
lemma DofZ_eq_factualD_on_zEvent (hA : S.Assumptions) (k : Fin K)
    {ω : P.Ω} (hω : ω ∈ S.zEvent k) :
    S.DofZ k ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hA.consistency S.dVar S.zVar k S.hZD.symm hω

/-- [Consistency identifies observed outcome with potential outcome under realized
treatment](goal) under [the local multi-instrument assumptions](hyp:hA), for [the unit being
evaluated](hyp:ω). -/
lemma factualY_eq_YofD_factualD (hA : S.Assumptions) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hA.consistency S.yVar S.dVar S.hDY.symm ω

/-- [Within a response-type subgroup, potential treatment at a support point equals that type's
recorded response](goal) for [the response type](hyp:g), [support point](hyp:k), and [unit in the
type cell](hyp:ω,hω). This makes cell means expandable over latent types. -/
lemma DofZ_eq_on_gEvent (g : ResponseType K) (k : Fin K)
    {ω : P.Ω} (hω : ω ∈ S.gEvent g) :
    S.DofZ k ω = g k := by
  have : S.responseType ω = g := hω
  calc S.DofZ k ω = S.responseType ω k := rfl
    _ = g k := by rw [this]

/-! ### Drop-of-conditioning at the instrument cell (uses `instrumentIndep`)

These two lemmas are the `Fin K` analogues of the LATE first-stage / reduced-form
"Step 1" computations. On `{Z = zᵏ}`, consistency rewrites the factual integrand
into a measurable projection of the counterfactual cell `(D(zᵏ), Y(1), Y(0))`,
and instrument independence drops the conditioning. -/

/-- [The observed treatment mean in an instrument cell equals mean potential treatment under
that support value](goal) under [the local multi-instrument assumptions](hyp:hA), for [the support
point](hyp:k) when [its observed cell has positive mass](hyp:hZk). -/
theorem treatmentDrop [IsFiniteMeasure P.μ] (hA : S.Assumptions) (k : Fin K)
    (hZk : P.μ (S.zEvent k) ≠ 0) :
    normalizedRestrictedIntegral P.μ (S.zEvent k) (fun ω => boolToReal (S.factualD ω))
      = ∫ ω, boolToReal (S.DofZ k ω) ∂P.μ := by
  let h_proj : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => boolToReal ((f (0 : Fin 3)) : Bool)
  have hh_meas : Measurable h_proj := by
    -- Instance search no longer unfolds `cfCell` to see `n = 3`, so supply the
    -- coordinate measurable-space family at index type `Fin 3` directly.
    let _ : ∀ i : Fin 3, MeasurableSpace ((S.cfCell k).type i) :=
      fun i => (S.cfCell k).inst i
    change Measurable fun f : ∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i =>
      boolToReal ((f (0 : Fin 3)) : Bool)
    exact (by fun_prop : Measurable fun b : Bool => boolToReal b).comp
      (measurable_pi_apply (0 : Fin 3))
  have hF_eq : ∀ ω ∈ S.zVar.event k,
      boolToReal (S.factualD ω) = h_proj ((S.cfCell k).jointValue ω) := by
    intro ω hω
    rw [← S.DofZ_eq_factualD_on_zEvent hA k hω]
    dsimp [h_proj]
    have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
    rw [hJV0]
  change normalizedRestrictedIntegral P.μ (S.zVar.event k) (fun ω => boolToReal (S.factualD ω))
      = ∫ ω, boolToReal (S.DofZ k ω) ∂P.μ
  rw [POSystem.eventCondExp_of_ae_eq_IndepCF (hA.instrumentIndep k)
    (a := S.zVar) hh_meas
    (measurableSet_singleton k)
    (ae_restrict_of_forall_mem (μ := P.μ) (S.measurableSet_zEvent k) hF_eq)
    hZk (measure_ne_top _ _)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  dsimp [h_proj]
  have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
  rw [hJV0]

/-- [The observed outcome mean in an instrument cell equals mean outcome under the treatment
induced by that support value](goal) under [the local multi-instrument assumptions](hyp:hA), for
[the support point](hyp:k), when [its cell has positive mass](hyp:hZk) and [treated](hyp:hY1) and
[untreated](hyp:hY0) potential outcomes are integrable. -/
theorem outcomeDrop [IsFiniteMeasure P.μ] (hA : S.Assumptions) (k : Fin K)
    (hZk : P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ) :
    normalizedRestrictedIntegral P.μ (S.zEvent k) S.factualY = ∫ ω, S.YofDofZ k ω ∂P.μ := by
  have _hY1 : Integrable (S.YofD true) P.μ := hY1
  have _hY0 : Integrable (S.YofD false) P.μ := hY0
  let getD : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → Bool :=
    fun f => ((f (0 : Fin 3)) : Bool)
  let getY1 : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => ((f (1 : Fin 3)) : ℝ)
  let getY0 : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => ((f (2 : Fin 3)) : ℝ)
  let h_proj : (∀ i : Fin (S.cfCell k).n, (S.cfCell k).type i) → ℝ :=
    fun f => cond (getD f) (getY1 f) (getY0 f)
  have hh_meas : Measurable h_proj := by
    -- Instance search no longer unfolds `cfCell` to see `n = 3`, so supply the
    -- coordinate measurable-space family at index type `Fin 3` directly.
    let _ : ∀ i : Fin 3, MeasurableSpace ((S.cfCell k).type i) :=
      fun i => (S.cfCell k).inst i
    have hD_meas : Measurable getD := by
      dsimp [getD]
      exact measurable_pi_apply (0 : Fin 3)
    have hY1_meas : Measurable getY1 := by
      dsimp [getY1]
      exact measurable_pi_apply (1 : Fin 3)
    have hY0_meas : Measurable getY0 := by
      dsimp [getY0]
      exact measurable_pi_apply (2 : Fin 3)
    have hif : Measurable fun f =>
        if getD f = true then getY1 f else getY0 f := by
      refine Measurable.ite ?_ ?_ ?_
      · exact hD_meas (MeasurableSet.singleton true)
      · exact hY1_meas
      · exact hY0_meas
    simpa [h_proj, Bool.cond_eq_ite] using hif
  have hF_eq : ∀ ω ∈ S.zVar.event k,
      S.factualY ω = h_proj ((S.cfCell k).jointValue ω) := by
    intro ω hω
    rw [S.factualY_eq_YofD_factualD hA ω,
      ← S.DofZ_eq_factualD_on_zEvent hA k hω]
    dsimp [h_proj, getD, getY1, getY0]
    have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
    have hJV1 : ((S.cfCell k).jointValue ω (1 : Fin 3) : ℝ) = S.YofD true ω := rfl
    have hJV2 : ((S.cfCell k).jointValue ω (2 : Fin 3) : ℝ) = S.YofD false ω := rfl
    rw [hJV0, hJV1, hJV2]
    cases S.DofZ k ω <;> simp
  change normalizedRestrictedIntegral P.μ (S.zVar.event k) S.factualY = ∫ ω, S.YofDofZ k ω ∂P.μ
  rw [POSystem.eventCondExp_of_ae_eq_IndepCF (hA.instrumentIndep k)
    (a := S.zVar) hh_meas
    (measurableSet_singleton k)
    (ae_restrict_of_forall_mem (μ := P.μ) (S.measurableSet_zEvent k) hF_eq)
    hZk (measure_ne_top _ _)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  dsimp [h_proj, getD, getY1, getY0]
  have hJV0 : ((S.cfCell k).jointValue ω (0 : Fin 3) : Bool) = S.DofZ k ω := rfl
  have hJV1 : ((S.cfCell k).jointValue ω (1 : Fin 3) : ℝ) = S.YofD true ω := rfl
  have hJV2 : ((S.cfCell k).jointValue ω (2 : Fin 3) : ℝ) = S.YofD false ω := rfl
  rw [hJV0, hJV1, hJV2]
  unfold YofDofZ
  cases S.DofZ k ω <;> simp

/-! ### Response-type total-law partition (pure measure theory, no independence)

The response type `G` partitions the sample space; the law of total expectation
rewrites the unconditional integrals from the drop step as finite sums over
response types. -/

/-- [Distinct response-type subgroups are disjoint](goal) in [a multiple-instrument IV
subsystem](hyp:S), so latent types form nonoverlapping population cells. -/
lemma gEvent_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint S.gEvent) := by
  intro g h hgh
  refine Set.disjoint_left.mpr ?_
  intro ω hg hh
  exact hgh ((Set.mem_singleton_iff.mp hg).symm.trans (Set.mem_singleton_iff.mp hh))

/-- [The response-type subgroups cover the full population](goal) in [a multiple-instrument IV
subsystem](hyp:S), so every unit belongs to exactly one latent treatment-response type. -/
lemma gEvent_iUnion : (⋃ g : ResponseType K, S.gEvent g) = Set.univ := by
  ext ω; simp [gEvent]

/-- [A population integral equals the sum of response-type masses times within-type
means](goal) in [a multiple-instrument IV subsystem](hyp:S), for [an integrable
quantity](hyp:f,hf). This is the finite total law used to expand observed moments. -/
lemma integral_partition [IsFiniteMeasure P.μ] {f : P.Ω → ℝ} (hf : Integrable f P.μ) :
    ∫ ω, f ω ∂P.μ
      = ∑ g : ResponseType K, (P.μ (S.gEvent g)).toReal * normalizedRestrictedIntegral P.μ (S.gEvent g) f :=
  integral_eq_sum_measure_mul_eventCondExp P.μ S.gEvent S.measurableSet_gEvent
    S.gEvent_pairwise_disjoint S.gEvent_iUnion f hf

/-! ### Finite masses, effects, and baseline terms populating the algebra -/

/-- [A response-type mass](goal) is the population probability of [the selected treatment-response
type](hyp:g) in [a multiple-instrument IV subsystem](hyp:S) of [the potential-outcome
system](hyp:P) on [the finite support](hyp:K). -/
def mass (g : ResponseType K) : ℝ := (P.μ (S.gEvent g)).toReal

/-- [The within-type causal effect](goal) averages the treated-minus-untreated outcome contrast
among units of [one response type](hyp:g) in [a multiple-instrument IV subsystem](hyp:S) of [the
potential-outcome system](hyp:P) on [the finite support](hyp:K). -/
def effect (g : ResponseType K) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => S.YofD true ω - S.YofD false ω)

/-- [The reference instrument value](goal) is the first point of [a nonempty finite
support](hyp:K,hK) for [a multiple-instrument IV subsystem](hyp:_S) in [the potential-outcome
system](hyp:P). -/
def z0 (_S : POMultipleIVSystem P K) (hK : 0 < K) : Fin K := ⟨0, hK⟩

/-- [A response type's baseline outcome](goal) is its mean outcome under treatment induced by the
first point of [a nonempty finite support](hyp:K,hK), for [the selected type](hyp:g) in [a
multiple-instrument IV subsystem](hyp:S) of [the potential-outcome system](hyp:P). -/
def baseOutcome (hK : 0 < K) (g : ResponseType K) : ℝ :=
  normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofDofZ (S.z0 hK))

/-- [The baseline treatment mean](goal) is average uptake induced by the first point of [a
nonempty finite support](hyp:K,hK) in [a multiple-instrument IV subsystem](hyp:S) of [the
potential-outcome system](hyp:P). -/
def baseTreatment (hK : 0 < K) : ℝ :=
  ∫ ω, boolToReal (S.DofZ (S.z0 hK) ω) ∂P.μ

/-- [Every response-type mass is nonnegative](goal) in [a multiple-instrument IV
subsystem](hyp:S), for [the selected response type](hyp:g), because it is a population
probability. -/
lemma mass_nonneg (g : ResponseType K) : 0 ≤ S.mass g := ENNReal.toReal_nonneg

/-- [Response-type masses sum to one](goal) in [a multiple-instrument IV subsystem](hyp:S), so
they form population weights over the exhaustive latent-type partition. -/
lemma mass_sum_one : ∑ g : ResponseType K, S.mass g = 1 := by
  have hsum :
      (Finset.univ).sum
          (fun g : ResponseType K =>
            (P.μ (S.responseType ⁻¹' ({g} : Set (ResponseType K)))).toReal) =
        (P.μ (S.responseType ⁻¹' (Set.univ : Set (ResponseType K)))).toReal := by
    simpa [Measure.real] using
      (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := P.μ) (s := (Finset.univ : Finset (ResponseType K)))
        (f := S.responseType)
        (hf := by
          intro g _hg
          exact S.measurable_responseType (measurableSet_singleton g))
        (h := by
          intro g _hg
          exact measure_ne_top _ _))
  simpa [mass, gEvent, Set.preimage_univ, IsProbabilityMeasure.measure_univ] using hsum

/-- [Finite response-type statistics](goal) collect type masses and within-type causal effects
from [a multiple-instrument IV subsystem](hyp:S) of [the potential-outcome system](hyp:P) on [the
finite support](hyp:K). -/
def toStats : ResponseTypeStats K where
  mass := S.mass
  effect := S.effect
  mass_nonneg := S.mass_nonneg
  mass_sum_one := S.mass_sum_one

/-- [The finite-support response-type population bridge](goal) combines type statistics and
baseline outcomes from [a multiple-instrument IV subsystem](hyp:S) of [the potential-outcome
system](hyp:P) on [a nonempty finite support](hyp:K,hK). -/
def toPopulationBridge (hK : 0 < K) : ResponseTypeStats.PopulationBridge K where
  stats := S.toStats
  baseOutcome := S.baseOutcome hK

/-- [The subsystem's ordered finite score index](goal) combines its instrument-cell probabilities
with [a supplied support score](hyp:dhat) that is [weakly increasing](hyp:hmono), for [a
multiple-instrument IV subsystem](hyp:S) of [the potential-outcome system](hyp:P) on [the finite
support](hyp:K). -/
def toFiniteIndex (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l) :
    FiniteIndex K :=
  FiniteIndex.fromMeasureScore P.μ S.factualZ S.measurable_factualZ dhat hmono

/-! ### Telescoping identity -/

/-- [Cumulative adjacent treatment changes equal the response difference between a support point
and the reference point](goal) in [a multiple-instrument IV subsystem](hyp:S), for [a nonempty
support](hyp:hK), [response type](hyp:g), and [support point](hyp:k). -/
lemma telescoped_eq (hK : 0 < K) (g : ResponseType K) (k : Fin K) :
    ResponseTypeStats.PopulationBridge.telescopedTypeStep g k
      = boolToReal (g k) - boolToReal (g (S.z0 hK)) := by
  classical
  let a : ℕ → ℝ := fun n => if h : n < K then boolToReal (g ⟨n, h⟩) else 0
  have htel : ∀ n : ℕ, (∑ r ∈ Finset.range n, (a (r + 1) - a r)) = a n - a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hsum :
      (∑ j ∈ (Finset.univ.filter fun j : Adj K => j.1.val ≤ k.val), typeStep g j)
        = ∑ r ∈ Finset.range k.val, (a (r + 1) - a r) := by
    refine Finset.sum_nbij (fun j : Adj K => j.1.val - 1) ?_ ?_ ?_ ?_
    · intro j hj
      have hjle : j.1.val ≤ k.val := by simpa using hj
      rw [Finset.mem_range]
      have hpos : 0 < j.1.val := j.2
      omega
    · intro j1 hj1 j2 hj2 h
      apply Subtype.ext
      apply Fin.ext
      have hj1le : j1.1.val ≤ k.val := by simpa using hj1
      have hj2le : j2.1.val ≤ k.val := by simpa using hj2
      have hpos1 : 0 < j1.1.val := j1.2
      have hpos2 : 0 < j2.1.val := j2.2
      change j1.1.val - 1 = j2.1.val - 1 at h
      omega
    · intro r hr
      have hrlt : r < k.val := by simpa using hr
      refine ⟨⟨⟨r + 1, ?_⟩, ?_⟩, ?_, ?_⟩
      · exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hrlt) k.isLt
      · exact Nat.succ_pos r
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        show r + 1 ≤ k.val
        omega
      · change r + 1 - 1 = r
        omega
    · intro j hj
      have hjle : j.1.val ≤ k.val := by simpa using hj
      have hsucc : j.1.val - 1 + 1 = j.1.val :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt j.2)
      have hpred_lt : j.1.val - 1 < K :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.1.isLt
      simp [typeStep, Adj.upper, Adj.lower, a, hpred_lt, hsucc]
  unfold ResponseTypeStats.PopulationBridge.telescopedTypeStep
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [hsum, htel]
  have hak : a k.val = boolToReal (g k) := by
    simp [a, k.isLt]
  have ha0 : a 0 = boolToReal (g (S.z0 hK)) := by
    simp [a, hK, z0]
  rw [hak, ha0]

/-! ### Cell identities discharging the ObservedBridge transferred assumptions -/

/-- [The observed treatment mean in an instrument cell equals the common baseline treatment mean
plus its response-type treatment expansion](goal) for [a nonempty support](hyp:hK), under [the
local IV assumptions](hyp:hA), at [a support point](hyp:k) whose [cell has positive
mass](hyp:hZk). -/
theorem treatment_cell_eq [IsFiniteMeasure P.μ] (hK : 0 < K) (hA : S.Assumptions)
    (k : Fin K) (hZk : P.μ (S.zEvent k) ≠ 0) :
    normalizedRestrictedIntegral P.μ (S.zEvent k) (fun ω => boolToReal (S.factualD ω))
      = S.baseTreatment hK
        + (S.toPopulationBridge hK).treatmentAtSupport k := by
  have hDint : ∀ q : Fin K, Integrable (fun ω => boolToReal (S.DofZ q ω)) P.μ := by
    intro q
    have hbdd : ∀ ω, |boolToReal (S.DofZ q ω)| ≤ (1 : ℝ) := by
      intro ω
      cases S.DofZ q ω <;> simp [boolToReal]
    exact (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (((by fun_prop : Measurable fun b : Bool => boolToReal b).comp
        (S.measurable_DofZ q)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd)
  have hCell : ∀ (q : Fin K) (g : ResponseType K),
      S.mass g * normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => boolToReal (S.DofZ q ω)) =
        S.mass g * boolToReal (g q) := by
    intro q g
    calc
      S.mass g * normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => boolToReal (S.DofZ q ω)) =
          normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => boolToReal (S.DofZ q ω)) * S.mass g := by
        ring
      _ = ∫ ω in S.gEvent g, boolToReal (S.DofZ q ω) ∂P.μ := by
        rw [mass, eventCondExp_mul_measure_toReal _ _ (measure_ne_top _ _)]
      _ = ∫ ω in S.gEvent g, boolToReal (g q) ∂P.μ := by
        refine MeasureTheory.setIntegral_congr_fun (S.measurableSet_gEvent g) ?_
        intro ω hω
        dsimp
        rw [S.DofZ_eq_on_gEvent g q hω]
      _ = boolToReal (g q) * S.mass g := by
        simp [mass, Measure.real, mul_comm]
      _ = S.mass g * boolToReal (g q) := by
        ring
  have hInt : ∫ ω, boolToReal (S.DofZ k ω) ∂P.μ =
      ∑ g : ResponseType K, S.mass g * boolToReal (g k) := by
    rw [S.integral_partition (hDint k)]
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa [mass] using hCell k g
  have hBase : S.baseTreatment hK =
      ∑ g : ResponseType K, S.mass g * boolToReal (g (S.z0 hK)) := by
    unfold baseTreatment
    rw [S.integral_partition (hDint (S.z0 hK))]
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa [mass] using hCell (S.z0 hK) g
  have hTreat : (S.toPopulationBridge hK).treatmentAtSupport k =
      ∑ g : ResponseType K,
        S.mass g * (boolToReal (g k) - boolToReal (g (S.z0 hK))) := by
    unfold ResponseTypeStats.PopulationBridge.treatmentAtSupport toPopulationBridge toStats
    refine Finset.sum_congr rfl ?_
    intro g _
    rw [S.telescoped_eq hK g k]
  rw [S.treatmentDrop hA k hZk, hInt, hBase, hTreat]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro g _
  ring

/-- [The observed outcome mean in an instrument cell equals its response-type outcome
expansion](goal) for [a nonempty support](hyp:hK), under [the local IV assumptions](hyp:hA), at [a
support point](hyp:k) whose [cell has positive mass](hyp:hZk), with [integrable treated](hyp:hY1)
and [untreated](hyp:hY0) potential outcomes. -/
theorem outcome_cell_eq [IsFiniteMeasure P.μ] (hK : 0 < K) (hA : S.Assumptions)
    (k : Fin K) (hZk : P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ) :
    normalizedRestrictedIntegral P.μ (S.zEvent k) S.factualY
      = (S.toPopulationBridge hK).outcomeAtSupport k := by
  have hYDZ_bdd : ∀ q : Fin K, ∀ ω,
      |S.YofDofZ q ω| ≤ |S.YofD true ω| + |S.YofD false ω| := by
    intro q ω
    have h1 := abs_nonneg (S.YofD true ω)
    have h0 := abs_nonneg (S.YofD false ω)
    unfold YofDofZ
    cases S.DofZ q ω <;> simp [h1, h0]
  have hYDZ_int : ∀ q : Fin K, Integrable (S.YofDofZ q) P.μ := by
    intro q
    exact (hY1.norm.add hY0.norm).mono' (S.measurable_YofDofZ q).aestronglyMeasurable
      (Filter.Eventually.of_forall (hYDZ_bdd q))
  have hCE : ∀ (q : Fin K) (g : ResponseType K),
      normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofDofZ q) =
        normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofD false) +
          boolToReal (g q) * S.effect g := by
    intro q g
    let c : ℝ := boolToReal (g q)
    have hcongr : normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofDofZ q) =
        normalizedRestrictedIntegral P.μ (S.gEvent g)
          (fun ω => S.YofD false ω + c * (S.YofD true ω - S.YofD false ω)) := by
      apply eventCondExp_congr_on P.μ (S.measurableSet_gEvent g)
      intro ω hω
      unfold YofDofZ
      rw [S.DofZ_eq_on_gEvent g q hω]
      dsimp [c]
      cases g q <;> simp [boolToReal]
    calc
      normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofDofZ q) =
          normalizedRestrictedIntegral P.μ (S.gEvent g)
            (fun ω => S.YofD false ω + c * (S.YofD true ω - S.YofD false ω)) := hcongr
      _ = normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofD false) +
            normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => c * (S.YofD true ω - S.YofD false ω)) := by
        change normalizedRestrictedIntegral P.μ (S.gEvent g)
            ((S.YofD false) + fun ω => c * (S.YofD true ω - S.YofD false ω)) =
          normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofD false) +
            normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => c * (S.YofD true ω - S.YofD false ω))
        rw [eventCondExp_add]
        · exact hY0.integrableOn
        · exact (hY1.integrableOn.sub hY0.integrableOn).const_mul c
      _ = normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofD false) +
            c * normalizedRestrictedIntegral P.μ (S.gEvent g) (fun ω => S.YofD true ω - S.YofD false ω) := by
        rw [eventCondExp_smul]
      _ = normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofD false) + boolToReal (g q) * S.effect g := by
        rfl
  have hTerm : ∀ g : ResponseType K,
      normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofDofZ k) =
        S.baseOutcome hK g +
          ResponseTypeStats.PopulationBridge.telescopedTypeStep g k * S.effect g := by
    intro g
    unfold baseOutcome
    rw [hCE k g, hCE (S.z0 hK) g, S.telescoped_eq hK g k]
    ring
  have hInt : ∫ ω, S.YofDofZ k ω ∂P.μ =
      ∑ g : ResponseType K,
        S.mass g * normalizedRestrictedIntegral P.μ (S.gEvent g) (S.YofDofZ k) := by
    rw [S.integral_partition (hYDZ_int k)]
    refine Finset.sum_congr rfl ?_
    intro g _
    rfl
  rw [S.outcomeDrop hA k hZk hY1 hY0, hInt]
  unfold ResponseTypeStats.PopulationBridge.outcomeAtSupport toPopulationBridge toStats
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [hTerm g]

/-! ### Assembled observed bridge and the potential-outcome centered-score identity -/

/-- [The ordered index's support masses equal the observed instrument-cell probabilities](goal)
for [the supplied score](hyp:dhat), [its monotonicity certificate](hyp:hmono), and [the selected
support point](hyp:k) in [the multiple-instrument IV subsystem](hyp:S). -/
lemma rho_eq_zMass (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l) (k : Fin K) :
    (S.toFiniteIndex dhat hmono).rho k
      = (P.μ (ResponseTypeStats.PopulationBridge.zEvent S.factualZ k)).toReal := by
  rfl

/-- [The observed population bridge](goal) links factual moments to the finite response-type
representation for [a multiple-instrument IV subsystem](hyp:S) of [the potential-outcome
system](hyp:P) on [a nonempty support](hyp:K,hK), under [the local IV assumptions](hyp:hA), [a
weakly increasing support score](hyp:dhat,hmono), [positive instrument-cell mass](hyp:hZpos), and
[integrable treated and untreated potential outcomes](hyp:hY1,hY0).

The two conditional-mean bridge conditions are derived from consistency and instrument independence. -/
def toObservedBridge (hK : 0 < K) (hA : S.Assumptions)
    (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l)
    (hZpos : ∀ k : Fin K, P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ) :
    ResponseTypeStats.PopulationBridge.ObservedBridge P.μ S.factualZ S.factualD
      S.factualY (S.toFiniteIndex dhat hmono) (S.toPopulationBridge hK) where
  isProbability := P.isProb
  rho_eq_zMass := S.rho_eq_zMass dhat hmono
  outcome_cell := fun k =>
    S.outcome_cell_eq hK hA k (hZpos k) hY1 hY0
  baseTreatment := S.baseTreatment hK
  treatment_cell := fun k =>
    S.treatment_cell_eq hK hA k (hZpos k)

/-- **Potential-outcome finite-support centered-score IV identity.** Consider [a nonempty
finite instrument support](hyp:hK) together with [a real support
score](hyp:dhat) that is [weakly increasing in the support order](hyp:hmono), under
[the local consistency and pointwise-exogeneity bundle](hyp:hA). If [every
instrument-support cell has positive probability](hyp:hZpos), [the potential
outcome under treatment](hyp:hY1) and [under control](hyp:hY0) are
integrable, [the centered-instrument-weighted outcome](hyp:hYInt) and
[treatment](hyp:hDInt) are integrable, and [the observed first-stage moment
is nonzero](hyp:hden), then [the observed centered-score IV estimand equals the
response-type-weighted average of within-type causal effects](goal).

The conditional-mean bridges are derived from consistency and instrument
independence. The statement does not identify `dhat` with a saturated
first-stage propensity score or another linear-projection fitted value. -/
theorem observedCenteredScoreIV_eq_responseTypeWeightedSum
    [IsFiniteMeasure P.μ] (hK : 0 < K) (hA : S.Assumptions)
    (dhat : Fin K → ℝ)
    (hmono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l)
    (hZpos : ∀ k : Fin K, P.μ (S.zEvent k) ≠ 0)
    (hY1 : Integrable (S.YofD true) P.μ) (hY0 : Integrable (S.YofD false) P.μ)
    (hYInt : Integrable
      (fun ω => (S.toFiniteIndex dhat hmono).centeredIndex (S.factualZ ω) * S.factualY ω) P.μ)
    (hDInt : Integrable
      (fun ω => (S.toFiniteIndex dhat hmono).centeredIndex (S.factualZ ω)
        * boolToReal (S.factualD ω)) P.μ)
    (hden : ResponseTypeStats.PopulationBridge.observedFirstStageMoment
      P.μ S.factualZ S.factualD (S.toFiniteIndex dhat hmono) ≠ 0) :
    ResponseTypeStats.PopulationBridge.observedCenteredScoreIV
        P.μ S.factualZ S.factualD S.factualY (S.toFiniteIndex dhat hmono)
      = (S.toPopulationBridge hK).stats.responseTypeEstimand (S.toFiniteIndex dhat hmono) :=
  (S.toObservedBridge hK hA dhat hmono hZpos hY1 hY0).observedCenteredScoreIV_eq_responseTypeWeightedSum
    S.measurable_factualZ hYInt hDInt hden

end POMultipleIVSystem

end

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
