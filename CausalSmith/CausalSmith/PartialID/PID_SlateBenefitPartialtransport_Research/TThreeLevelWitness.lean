import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TFullLawEndpointAttainment
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Explicit three-level witness

An exact rational one-cell observed table and latent allocation demonstrate a
nontrivial interval with upper endpoint seven tenths.
-/

open scoped BigOperators ENNReal
open MeasureTheory Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

set_option maxRecDepth 10000
set_option maxHeartbeats 200000

/-- The witness observed weight is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def witnessObservedWeight (o : ObservedDatum Unit 3) : ℝ :=
  if o.cell = () ∧ o.instrument = false ∧ o.treatment = false ∧
      o.selected = true ∧ o.outcome = some 0 then (3 : ℝ) / 80
  else if o.cell = () ∧ o.instrument = false ∧ o.treatment = false ∧
      o.selected = true ∧ o.outcome = some 1 then (1 : ℝ) / 20
  else if o.cell = () ∧ o.instrument = false ∧ o.treatment = false ∧
      o.selected = true ∧ o.outcome = some 2 then (3 : ℝ) / 80
  else if o.cell = () ∧ o.instrument = false ∧ o.treatment = false ∧
      o.selected = false ∧ o.outcome = none then (3 : ℝ) / 8
  else if o.cell = () ∧ o.instrument = true ∧ o.treatment = true ∧
      o.selected = true ∧ o.outcome = some 0 then (1 : ℝ) / 20
  else if o.cell = () ∧ o.instrument = true ∧ o.treatment = true ∧
      o.selected = true ∧ o.outcome = some 1 then (1 : ℝ) / 8
  else if o.cell = () ∧ o.instrument = true ∧ o.treatment = true ∧
      o.selected = true ∧ o.outcome = some 2 then (3 : ℝ) / 40
  else if o.cell = () ∧ o.instrument = true ∧ o.treatment = true ∧
      o.selected = false ∧ o.outcome = none then (1 : ℝ) / 4
  else 0

/-- The witness observed measure is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def witnessObservedMeasure : Measure (ObservedDatum Unit 3) :=
  ((3 : ENNReal) / 80) • Measure.dirac ⟨(), false, false, true, some 0⟩ +
  ((1 : ENNReal) / 20) • Measure.dirac ⟨(), false, false, true, some 1⟩ +
  ((3 : ENNReal) / 80) • Measure.dirac ⟨(), false, false, true, some 2⟩ +
  ((3 : ENNReal) / 8) • Measure.dirac ⟨(), false, false, false, none⟩ +
  ((1 : ENNReal) / 20) • Measure.dirac ⟨(), true, true, true, some 0⟩ +
  ((1 : ENNReal) / 8) • Measure.dirac ⟨(), true, true, true, some 1⟩ +
  ((3 : ENNReal) / 40) • Measure.dirac ⟨(), true, true, true, some 2⟩ +
  ((1 : ENNReal) / 4) • Measure.dirac ⟨(), true, true, false, none⟩
  -- @realizes P_{\mathrm{obs}}^{\star}(fully specified observed witness law)

/-- The witness latent table is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def witnessLatentTable : LatentCellTable 3 :=
  fun d0 d1 s0 s1 y0 y1 =>
    if d0 = false ∧ d1 = true ∧ s0 = true ∧ s1 = true ∧ y0 = 0 ∧ y1 = 0
      then (3 : ℝ) / 40
    else if d0 = false ∧ d1 = true ∧ s0 = true ∧ s1 = true ∧ y0 = 1 ∧ y1 = 1
      then (1 : ℝ) / 10
    else if d0 = false ∧ d1 = true ∧ s0 = true ∧ s1 = true ∧ y0 = 2 ∧ y1 = 2
      then (3 : ℝ) / 40
    else if d0 = false ∧ d1 = true ∧ s0 = false ∧ s1 = true ∧ y0 = 0 ∧ y1 = 0
      then (1 : ℝ) / 40
    else if d0 = false ∧ d1 = true ∧ s0 = false ∧ s1 = true ∧ y0 = 0 ∧ y1 = 1
      then (3 : ℝ) / 20
    else if d0 = false ∧ d1 = true ∧ s0 = false ∧ s1 = true ∧ y0 = 0 ∧ y1 = 2
      then (3 : ℝ) / 40
    else if d0 = false ∧ d1 = true ∧ s0 = false ∧ s1 = false ∧ y0 = 0 ∧ y1 = 0
      then (1 : ℝ) / 2
    else 0
  -- A canonical representative; hidden outcome coordinates are quotiented below.

/-- The witness latent state is the object specified here for the slate-benefit partial-transport construction. -/
abbrev WitnessLatentState := Bool × Bool × Bool × Bool × Fin 3 × Fin 3

/-- The witness latent measure is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def witnessLatentMeasure : Measure WitnessLatentState :=
  ∑ u, ENNReal.ofReal (witnessLatentTable u.1 u.2.1 u.2.2.1 u.2.2.2.1
    u.2.2.2.2.1 u.2.2.2.2.2) • Measure.dirac u

/-- The witness instrument measure is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def witnessInstrumentMeasure : Measure Bool :=
  ((1 : ENNReal) / 2) • Measure.dirac false +
  ((1 : ENNReal) / 2) • Measure.dirac true

/-- The witness full measure is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def witnessFullMeasure : Measure (Bool × WitnessLatentState) :=
  witnessInstrumentMeasure.prod witnessLatentMeasure

/-- Latent coordinates after outcomes hidden by selection have been erased. -/
structure WitnessVisibleLatentState where
  d0 : Bool
  d1 : Bool
  s0 : Bool
  s1 : Bool
  y0 : Option (Fin 3)
  y1 : Option (Fin 3)
  deriving DecidableEq

/-- Visible latent states have decidable equality. -/
add_decl_doc instDecidableEqWitnessVisibleLatentState

/-- This declaration supplies the canonical canonical measurable space witness visible latent state typeclass instance for the finite slate-benefit construction. -/
instance : MeasurableSpace WitnessVisibleLatentState := ⊤

/-- The witness visible latent is the object specified here for the slate-benefit partial-transport construction. -/
def witnessVisibleLatent (u : WitnessLatentState) : WitnessVisibleLatentState where
  d0 := u.1
  d1 := u.2.1
  s0 := u.2.2.1
  s1 := u.2.2.2.1
  y0 := if u.2.2.1 then some u.2.2.2.2.1 else none
  y1 := if u.2.2.2.1 then some u.2.2.2.2.2 else none

/-- All latent laws with the displayed masses on visible coordinates.  Within
each fibre of `witnessVisibleLatent`, outcomes hidden by selection are free. -/
def witnessLatentMeasureFamily : Set (Measure WitnessLatentState) :=
  {ν | IsProbabilityMeasure ν ∧
    ν.map witnessVisibleLatent = witnessLatentMeasure.map witnessVisibleLatent}

/-- Fair independent instrument assignments joined to any admissible hidden-
outcome completion of the displayed latent masses. -/
def witnessFullMeasureFamily : Set (Measure (Bool × WitnessLatentState)) :=
  {Q | ∃ ν ∈ witnessLatentMeasureFamily,
    Q = witnessInstrumentMeasure.prod ν}
  -- @realizes P^{\star}(family modulo off-selection latent outcomes)

/-- The witness encoding is the object specified here for the slate-benefit partial-transport construction. -/
def witnessEncoding {P : POSystem} (S : POSlateSystem P Unit 3) :
    P.Ω → Bool × WitnessLatentState :=
  fun ω => (S.factualZ ω, S.D0 ω, S.D1 ω, S.S0 ω, S.S1 ω, S.Y0 ω, S.Y1 ω)

/-- The witness full law realization condition is the stated property of the slate-benefit partial-transport model. -/
def WitnessFullLawRealization : Prop :=
  ∃ (Pstar : POSystem.{0, 0, 0}) (Sstar : POSlateSystem Pstar Unit 3),
    let _ : StandardBorelSpace Pstar.Ω := Sstar.borel
    TieSafeSurvivorModel Sstar (1 / 4) (fun _ => true) ∧
    Sstar.observedLaw = witnessObservedMeasure ∧
    Pstar.μ.map (witnessEncoding Sstar) = witnessFullMeasure ∧
    (∀ᵐ ω ∂Pstar.μ, Sstar.D0 ω = false ∧ Sstar.D1 ω = true) ∧
    (∀ᵐ ω ∂Pstar.μ, Sstar.S0 ω ≤ Sstar.S1 ω)

/-- The fully specified observed and latent witness tables. -/
-- @node: def:three-level-witness
noncomputable def threeLevelWitness :
    Measure (ObservedDatum Unit 3) × Set (Measure (Bool × WitnessLatentState)) :=
  (witnessObservedMeasure, witnessFullMeasureFamily)

/-- The w node type enumerates the alternatives used by the slate-benefit partial-transport construction. -/
inductive WNode | x | z | d | s | y

/-- This declaration supplies the canonical canonical decidable eq w node typeclass instance for the finite slate-benefit construction. -/
instance instDecidableEqWNode : DecidableEq WNode
  | .x, .x | .z, .z | .d, .d | .s, .s | .y, .y => isTrue rfl
  | .x, .z | .x, .d | .x, .s | .x, .y
  | .z, .x | .z, .d | .z, .s | .z, .y
  | .d, .x | .d, .z | .d, .s | .d, .y
  | .s, .x | .s, .z | .s, .d | .s, .y
  | .y, .x | .y, .z | .y, .d | .y, .s => isFalse (by intro h; cases h)

/-- This declaration supplies the canonical canonical fintype w node typeclass instance for the finite slate-benefit construction. -/
instance instFintypeWNode : Fintype WNode :=
  ⟨{.x, .z, .d, .s, .y}, by intro a; cases a <;> simp⟩

/-- The w value is the object specified here for the slate-benefit partial-transport construction. -/
abbrev WValue : WNode → Type
  | .x => Unit
  | .z | .d | .s => Bool
  | .y => Fin 3

/-- The witness measurable space is the object specified here for the slate-benefit partial-transport construction. -/
def wMeasurableSpace (v : WNode) : MeasurableSpace (WValue v) := by
  cases v <;> exact ⊤

/-- This declaration supplies the canonical canonical measurable space w value typeclass instance for the finite slate-benefit construction. -/
instance instMeasurableSpaceWValue (v : WNode) : MeasurableSpace (WValue v) :=
  wMeasurableSpace v

/-- The witness eval is the object specified here for the slate-benefit partial-transport construction. -/
def wEval (r : Regime WNode WValue) (z : Bool) : ∀ v, WValue v := by
  intro v
  if h : v ∈ r.target then exact r.assign v h
  else cases v with
    | x => exact ()
    | z => exact z
    | d => exact false
    | s => exact false
    | y => exact ⟨0, by omega⟩

/-- The witness seed p is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable abbrev wSeedP : POSystem := by
  let p : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure true false p
  letI : IsProbabilityMeasure μ := by infer_instance
  exact
    { V := WNode
      X := WValue
      Ω := Bool
      μ := μ
      eval := wEval
      measurable_eval := fun _ => measurable_from_top }

/-- The witness seed s is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable abbrev wSeedS : POSlateSystem wSeedP Unit 3 where
  hK := by omega
  xNode := .x
  zNode := .z
  dNode := .d
  sNode := .s
  yNode := .y
  hX := MeasurableEquiv.refl Unit
  hZ := MeasurableEquiv.refl Bool
  hD := MeasurableEquiv.refl Bool
  hS := MeasurableEquiv.refl Bool
  hY := MeasurableEquiv.refl (Fin 3)
  hXZ := by intro h; cases h
  hXD := by intro h; cases h
  hXS := by intro h; cases h
  hXY := by intro h; cases h
  hZD := by intro h; cases h
  hZS := by intro h; cases h
  hZY := by intro h; cases h
  hDS := by intro h; cases h
  hDY := by intro h; cases h
  hSY := by intro h; cases h
  borel := by change StandardBorelSpace Bool; infer_instance

/-- [the witness seed p property holds](goal). -/
theorem wSeed_p : wSeedS.p () = 1 := by
  unfold POSlateSystem.p
  rw [show wSeedS.xEvent () = Set.univ by
    ext z
    simp [POSlateSystem.xEvent, POSlateSystem.factualX,
      POSlateSystem.xVar, POVar.factual, POVar.cf, wSeedS, wSeedP, wEval]]
  simp [Measure.real]

/-- [the witness seed propensity property holds](goal). -/
theorem wSeed_propensity : wSeedS.propensity () = (1 : ℝ) / 2 := by
  unfold POSlateSystem.propensity
  rw [show wSeedS.xEvent () = Set.univ by
    ext z
    simp [POSlateSystem.xEvent, POSlateSystem.factualX,
      POSlateSystem.xVar, POVar.factual, POVar.cf, wSeedS, wSeedP, wEval]]
  have hz : {z | wSeedS.factualZ z = true} = ({true} : Set Bool) := by
    change ({z : Bool | wEval Regime.empty z WNode.z = true} : Set Bool) = {true}
    ext z
    change wEval Regime.empty z WNode.z = true ↔ z = true
    simp only [wEval]
    rw [dif_neg]
    intro h
    simpa [Regime.empty] using h
  rw [hz]
  unfold conditionalReal
  dsimp [wSeedP]
  rw [Set.inter_univ]
  norm_num [POSlateSystem.propensity, conditionalReal, POSlateSystem.factualZ,
    POSlateSystem.zVar, POVar.factual, POVar.cf, wSeedS, wSeedP, wEval,
    ProbabilityTheory.bernoulliMeasure_real_apply]

/-- The witness table is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable abbrev wTable : ThresholdCellTable Unit 3 := fun _ => witnessLatentTable

/-- [every witness latent weight is nonnegative](goal). -/
theorem wNN : wTable.Nonnegative := by
  intro x d0 d1 s0 s1 y0 y1
  fin_cases d0 <;> fin_cases d1 <;> fin_cases s0 <;> fin_cases s1 <;>
    fin_cases y0 <;> fin_cases y1 <;>
    simp [wTable, witnessLatentTable] <;> norm_num

/-- Given [the stated hypotheses](hyp:h), [the witness latent table complier support property holds](goal). -/
theorem witnessLatentTable_complier_support
    (d0 d1 s0 s1 : Bool) (y0 y1 : Fin 3)
    (h : witnessLatentTable d0 d1 s0 s1 y0 y1 ≠ 0) :
    d0 = false ∧ d1 = true := by
  fin_cases d0 <;> fin_cases d1 <;> fin_cases s0 <;> fin_cases s1 <;>
    simp [witnessLatentTable] at h ⊢

/-- Given [the stated hypotheses](hyp:h), [the witness latent table selection support property holds](goal). -/
theorem witnessLatentTable_selection_support
    (d0 d1 s0 s1 : Bool) (y0 y1 : Fin 3)
    (h : witnessLatentTable d0 d1 s0 s1 y0 y1 ≠ 0) : s0 ≤ s1 := by
  fin_cases d0 <;> fin_cases d1 <;> fin_cases s0 <;> fin_cases s1 <;>
    simp [witnessLatentTable] at h ⊢

/-- [the witness latent weights sum to one](goal). -/
theorem wNorm : wTable.Normalized := by
  intro x
  simp [wTable, witnessLatentTable, Fin.sum_univ_succ] <;> norm_num

/-- [the witness model has the claimed covariate-cell probabilities](goal). -/
theorem wHp : ∀ x, 0 ≤ wSeedS.p x := by
  intro x
  rw [show x = () by cases x; rfl, wSeed_p]
  norm_num

/-- [the witness model has the claimed instrument propensity](goal). -/
theorem wHprop : ∀ x, 0 ≤ wSeedS.propensity x ∧ wSeedS.propensity x ≤ 1 := by
  intro x
  rw [show x = () by cases x; rfl, wSeed_propensity]
  norm_num

/-- [the witness instrument measure atom property holds](goal). -/
theorem witnessInstrumentMeasure_atom (z : Bool) :
    witnessInstrumentMeasure.real {z} = (1 : ℝ) / 2 := by
  fin_cases z <;>
    norm_num [witnessInstrumentMeasure, Measure.real, Measure.add_apply,
      Measure.smul_apply, Set.indicator, ENNReal.toReal_add]

/-- [the witness latent measure atom property holds](goal). -/
theorem witnessLatentMeasure_atom (u : WitnessLatentState) :
    witnessLatentMeasure.real {u} =
      witnessLatentTable u.1 u.2.1 u.2.2.1 u.2.2.2.1
        u.2.2.2.2.1 u.2.2.2.2.2 := by
  unfold witnessLatentMeasure Measure.real
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single u]
  · simp [Measure.dirac_apply']
    exact wNN () u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2
  · intro v _ hv
    simp [Measure.dirac_apply', hv]
  · simp

/-- [the witness latent measure univ property holds](goal). -/
theorem witnessLatentMeasure_univ : witnessLatentMeasure Set.univ = 1 := by
  unfold witnessLatentMeasure
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ, if_true,
    mul_one]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  change (∑ x : WitnessLatentState,
    ENNReal.ofReal (witnessLatentTable x.1 x.2.1 x.2.2.1 x.2.2.2.1
      x.2.2.2.2.1 x.2.2.2.2.2)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [show (∑ u : WitnessLatentState,
        witnessLatentTable u.1 u.2.1 u.2.2.1 u.2.2.2.1
          u.2.2.2.2.1 u.2.2.2.2.2) = 1 by
      simpa [Fintype.sum_prod_type] using wNorm ()]
    norm_num
  · intro u _
    exact wNN () u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2

/-- This declaration supplies the canonical canonical is probability measure witness latent typeclass instance for the finite slate-benefit construction. -/
noncomputable instance instIsProbabilityMeasureWitnessLatent :
    IsProbabilityMeasure witnessLatentMeasure := ⟨witnessLatentMeasure_univ⟩

/-- [the witness latent measure ae compliers property holds](goal). -/
theorem witnessLatentMeasure_ae_compliers : ∀ᵐ u ∂witnessLatentMeasure,
    u.1 = false ∧ u.2.1 = true := by
  unfold witnessLatentMeasure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  intro u
  by_cases h : witnessLatentTable u.1 u.2.1 u.2.2.1 u.2.2.2.1
      u.2.2.2.2.1 u.2.2.2.2.2 = 0
  · simp [h]
  · have hs := witnessLatentTable_complier_support u.1 u.2.1 u.2.2.1
      u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2 h
    apply Measure.ae_smul_measure
    rw [MeasureTheory.ae_dirac_iff MeasurableSet.of_discrete]
    exact hs

/-- [the witness latent measure ae selection property holds](goal). -/
theorem witnessLatentMeasure_ae_selection : ∀ᵐ u ∂witnessLatentMeasure,
    u.2.2.1 ≤ u.2.2.2.1 := by
  unfold witnessLatentMeasure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  intro u
  by_cases h : witnessLatentTable u.1 u.2.1 u.2.2.1 u.2.2.2.1
      u.2.2.2.2.1 u.2.2.2.2.2 = 0
  · simp [h]
  · have hs := witnessLatentTable_selection_support u.1 u.2.1 u.2.2.1
      u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2 h
    apply Measure.ae_smul_measure
    rw [MeasureTheory.ae_dirac_iff MeasurableSet.of_discrete]
    exact hs

/-- [the witness instrument measure univ property holds](goal). -/
theorem witnessInstrumentMeasure_univ : witnessInstrumentMeasure Set.univ = 1 := by
  norm_num [witnessInstrumentMeasure, Measure.add_apply, Measure.smul_apply,
    Set.indicator]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

/-- This declaration supplies the canonical canonical is probability measure witness instrument typeclass instance for the finite slate-benefit construction. -/
noncomputable instance instIsProbabilityMeasureWitnessInstrument :
    IsProbabilityMeasure witnessInstrumentMeasure := ⟨witnessInstrumentMeasure_univ⟩

/-- This declaration supplies the canonical canonical is probability measure witness full typeclass instance for the finite slate-benefit construction. -/
noncomputable instance instIsProbabilityMeasureWitnessFull :
    IsProbabilityMeasure witnessFullMeasure := by
  unfold witnessFullMeasure
  infer_instance

/-- This declaration supplies the canonical canonical is finite measure witness full typeclass instance for the finite slate-benefit construction. -/
noncomputable instance instIsFiniteMeasureWitnessFull :
    IsFiniteMeasure witnessFullMeasure := by
  unfold witnessFullMeasure
  infer_instance

/-- [the witness observed measure univ property holds](goal). -/
theorem witnessObservedMeasure_univ : witnessObservedMeasure Set.univ = 1 := by
  norm_num [witnessObservedMeasure, Measure.add_apply, Measure.smul_apply,
    Set.indicator, ENNReal.toReal_add]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

/-- This declaration supplies the canonical canonical is probability measure witness observed typeclass instance for the finite slate-benefit construction. -/
noncomputable instance instIsProbabilityMeasureWitnessObserved :
    IsProbabilityMeasure witnessObservedMeasure := ⟨witnessObservedMeasure_univ⟩

/-- [the witness observed measure atom property holds](goal). -/
theorem witnessObservedMeasure_atom (o : ObservedDatum Unit 3) :
    witnessObservedMeasure.real {o} = witnessObservedWeight o := by
  rcases o with ⟨x, z, d, s, y⟩
  cases x
  fin_cases z <;> fin_cases d <;> fin_cases s <;> cases y with
  | none =>
      norm_num [witnessObservedMeasure, witnessObservedWeight, Measure.real,
        Measure.add_apply, Measure.smul_apply, Set.indicator, Fin.ext_iff,
        ENNReal.toReal_add] <;> simp
  | some y =>
      fin_cases y <;>
      norm_num [witnessObservedMeasure, witnessObservedWeight, Measure.real,
        Measure.add_apply, Measure.smul_apply, Set.indicator, Fin.ext_iff,
        ENNReal.toReal_add] <;> simp

/-- The witness candidate is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable abbrev wCandidate :=
  canonicalThresholdCandidate wSeedS wTable wHp wHprop wNN wNorm

/-- [the witness observed law equals the displayed finite law](goal). -/
theorem wObservedLaw : wCandidate.slate.observedLaw = witnessObservedMeasure := by
  letI : IsProbabilityMeasure wCandidate.slate.observedLaw :=
    Measure.isProbabilityMeasure_map
      (measurable_observedDatum wCandidate.slate).aemeasurable
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro o
  have hc := canonicalThresholdCandidate_observedSingleton
    wSeedS wTable wHp wHprop wNN wNorm o
  rw [show wCandidate.slate.observedLaw.real {o} =
      ∑ a, if thresholdObservedDatum a = o then thresholdPastedWeight wSeedS wTable a else 0 by
    simpa [wCandidate] using hc]
  rw [thresholdPastedWeight_observedSum, witnessObservedMeasure_atom]
  rcases o with ⟨x, z, d, s, y⟩
  cases x
  fin_cases z <;> fin_cases d <;> fin_cases s <;> cases y with
  | none =>
      simp [wSeed_p, wSeed_propensity, atomInstrumentMass,
        thresholdObservedTableMargin_false_false_unselected,
        thresholdObservedTableMargin_false_true_unselected,
        thresholdObservedTableMargin_true_false_unselected,
        thresholdObservedTableMargin_true_true_unselected,
        thresholdObservedTableMargin_invalid, wTable,
        witnessLatentTable, witnessObservedWeight,
        Fintype.sum_bool, Fin.sum_univ_succ] <;> norm_num
  | some y =>
      fin_cases y <;>
      simp [wSeed_p, wSeed_propensity, atomInstrumentMass,
        thresholdObservedTableMargin_false_false_selected,
        thresholdObservedTableMargin_false_true_selected,
        thresholdObservedTableMargin_true_false_selected,
        thresholdObservedTableMargin_true_true_selected,
        thresholdObservedTableMargin_invalid, wTable,
        witnessLatentTable, witnessObservedWeight,
        Fintype.sum_bool, Fin.sum_univ_succ] <;> norm_num

/-- [the witness lower endpoint has the claimed value](goal). -/
theorem wLower (i : Fin 3) : (observableCapacities witnessObservedMeasure).lower () i =
    ![(3 : ℝ) / 40, (1 : ℝ) / 10, (3 : ℝ) / 40] i := by
  fin_cases i
  all_goals
    unfold observableCapacities observableCapacityContrasts
    change conditionalReal witnessObservedMeasure
      {o | o.cell = () ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some _}
      {o | o.cell = () ∧ o.instrument = false} -
      conditionalReal witnessObservedMeasure
      {o | o.cell = () ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some _}
      {o | o.cell = () ∧ o.instrument = true} = _
    norm_num [conditionalReal, witnessObservedMeasure, Measure.real,
      Measure.add_apply, Measure.smul_apply, Set.indicator] <;>
      simp [Fin.ext_iff]
  all_goals
    have hden : ((3 / 80 + 20⁻¹ + 3 / 80 + 3 / 8 : ENNReal)).toReal =
        (1 : ℝ) / 2 := by
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    rw [hden]
    norm_num

/-- [the witness upper endpoint has the claimed value](goal). -/
theorem wUpper (i : Fin 3) : (observableCapacities witnessObservedMeasure).upper () i =
    ![(1 : ℝ) / 10, (1 : ℝ) / 4, (3 : ℝ) / 20] i := by
  fin_cases i
  all_goals
    unfold observableCapacities observableCapacityContrasts
    change conditionalReal witnessObservedMeasure
      {o | o.cell = () ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some _}
      {o | o.cell = () ∧ o.instrument = true} -
      conditionalReal witnessObservedMeasure
      {o | o.cell = () ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some _}
      {o | o.cell = () ∧ o.instrument = false} = _
    norm_num [conditionalReal, witnessObservedMeasure, Measure.real,
      Measure.add_apply, Measure.smul_apply, Set.indicator] <;>
      simp [Fin.ext_iff]
  all_goals
    have hden : ((20⁻¹ + 8⁻¹ + 3 / 40 + 4⁻¹ : ENNReal)).toReal =
        (1 : ℝ) / 2 := by
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    rw [hden]
    norm_num

/-- [the witness benefit lower property holds](goal). -/
theorem wBenefitLower :
    (observableCapacities witnessObservedMeasure).benefitLower () = 0 := by
  unfold Capacities.benefitLower
  change Finset.univ.sup' Finset.univ_nonempty
    (fun t : Option (Fin 3) => match t with
      | none => 0
      | some k =>
          (observableCapacities witnessObservedMeasure).lowerLe () k -
          (observableCapacities witnessObservedMeasure).upperLe () k +
          min ((observableCapacities witnessObservedMeasure).gap ()) 0) = 0
  apply le_antisymm
  · apply Finset.sup'_le
    intro t _
    cases t with
    | none => norm_num
    | some k =>
        fin_cases k <;>
          simp [Capacities.lowerLe, Capacities.upperLe, Capacities.gap,
            Capacities.q0, Capacities.q1, wLower, wUpper,
            Finset.sum_filter, Fin.sum_univ_three] <;> norm_num
  · exact Finset.le_sup'
      (fun t : Option (Fin 3) => match t with
        | none => 0
        | some k =>
            (observableCapacities witnessObservedMeasure).lowerLe () k -
            (observableCapacities witnessObservedMeasure).upperLe () k +
            min ((observableCapacities witnessObservedMeasure).gap ()) 0)
      (show none ∈ (Finset.univ : Finset (Option (Fin 3))) by simp)

/-- [the witness benefit upper property holds](goal). -/
theorem wBenefitUpper :
    (observableCapacities witnessObservedMeasure).benefitUpper () = (7 : ℝ) / 40 := by
  unfold Capacities.benefitUpper
  change Finset.univ.inf' Finset.univ_nonempty
    (fun t : Option (Fin 3) => match t with
      | none => (observableCapacities witnessObservedMeasure).mass ()
      | some k =>
          (observableCapacities witnessObservedMeasure).lowerLt () k +
          (observableCapacities witnessObservedMeasure).upperGt () k) = (7 : ℝ) / 40
  apply le_antisymm
  · have hle := Finset.inf'_le
      (s := (Finset.univ : Finset (Option (Fin 3))))
      (f := fun t : Option (Fin 3) => match t with
        | none => (observableCapacities witnessObservedMeasure).mass ()
        | some k => (observableCapacities witnessObservedMeasure).lowerLt () k +
          (observableCapacities witnessObservedMeasure).upperGt () k)
      (b := some (2 : Fin 3)) (by simp)
    have heval :
        (observableCapacities witnessObservedMeasure).lowerLt () (2 : Fin 3) +
          (observableCapacities witnessObservedMeasure).upperGt () (2 : Fin 3) =
            (7 : ℝ) / 40 := by
      simp [Capacities.lowerLt, Capacities.upperGt, wLower, wUpper,
        Finset.sum_filter, Fin.sum_univ_three]
      norm_num
    exact hle.trans_eq heval
  · apply Finset.le_inf'
    intro t _
    cases t with
    | none =>
        simp [Capacities.mass, Capacities.q0, Capacities.q1, wLower, wUpper,
          Finset.sum_filter, Fin.sum_univ_three] <;> norm_num
    | some k =>
        fin_cases k <;>
          simp [Capacities.lowerLt, Capacities.upperGt, wLower, wUpper,
            Finset.sum_filter, Fin.sum_univ_three] <;> norm_num

/-- [the witness capacities have the displayed masses and endpoints](goal). -/
theorem wCapacityFacts :
    let c := observableCapacities witnessObservedMeasure
    c.q0 () = (1 : ℝ) / 4 ∧ c.mass () = (1 : ℝ) / 4 ∧
    c.q1 () = (1 : ℝ) / 2 ∧ c.gap () = (1 : ℝ) / 4 ∧
    c.benefitLower () = 0 ∧ c.benefitUpper () = (7 : ℝ) / 40 := by
  dsimp only
  exact ⟨by simp [Capacities.q0, wLower, Fin.sum_univ_succ] <;> norm_num,
    by simp [Capacities.mass, Capacities.q0, Capacities.q1, wLower, wUpper,
      Fin.sum_univ_succ] <;> norm_num,
    by simp [Capacities.q1, wUpper, Fin.sum_univ_succ] <;> norm_num,
    by simp [Capacities.gap, Capacities.q0, Capacities.q1, wLower, wUpper,
      Fin.sum_univ_succ] <;> norm_num,
    wBenefitLower, wBenefitUpper⟩

/-- [the witness construction defines the stated full-data probability law](goal). -/
theorem wFullLaw : wCandidate.system.μ.map (witnessEncoding wCandidate.slate) =
    witnessFullMeasure := by
  apply Measure.ext_of_singleton
  intro u
  have hm : Measurable (witnessEncoding wCandidate.slate) := measurable_from_top
  rw [Measure.map_apply hm (MeasurableSet.singleton _)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rcases u with ⟨z, d0, d1, s0, s1, y0, y1⟩
  let a : ThresholdAtom Unit 3 := ⟨(), z, d0, d1, s0, s1, y0, y1⟩
  have hc := canonicalThresholdCandidate_fullAtom
    wSeedS wTable wHp wHprop wNN wNorm a
  change wCandidate.system.μ.real
    ((witnessEncoding wCandidate.slate) ⁻¹' {(z, d0, d1, s0, s1, y0, y1)}) = _
  rw [show wCandidate.system.μ.real
      ((witnessEncoding wCandidate.slate) ⁻¹' {(z, d0, d1, s0, s1, y0, y1)}) =
      thresholdPastedWeight wSeedS wTable a by
    rw [← hc]
    congr 1
    ext ω
    simp [witnessEncoding, a]]
  change thresholdPastedWeight wSeedS wTable a =
    witnessFullMeasure.real {(z, d0, d1, s0, s1, y0, y1)}
  rw [show witnessFullMeasure.real {(z, d0, d1, s0, s1, y0, y1)} =
      (1 / 2 : ℝ) * witnessLatentTable d0 d1 s0 s1 y0 y1 by
    unfold witnessFullMeasure Measure.real
    rw [show ({(z, d0, d1, s0, s1, y0, y1)} :
        Set (Bool × WitnessLatentState)) =
        ({z} : Set Bool) ×ˢ ({(d0, d1, s0, s1, y0, y1)} :
          Set WitnessLatentState) by ext v; simp]
    rw [Measure.prod_prod, ENNReal.toReal_mul,
      show (witnessInstrumentMeasure {z}).toReal = (1 : ℝ) / 2 by
        exact witnessInstrumentMeasure_atom z,
      show (witnessLatentMeasure {(d0, d1, s0, s1, y0, y1)}).toReal =
          witnessLatentTable d0 d1 s0 s1 y0 y1 by
        exact witnessLatentMeasure_atom _]]
  cases z <;> simp [a, wTable, thresholdPastedWeight, atomInstrumentMass,
    wSeed_p, wSeed_propensity] <;> norm_num

/-- [the witness candidate cell probability equals the stated value](goal). -/
theorem wCandidate_p : wCandidate.slate.p () = 1 := by
  rw [← wSeed_p]
  exact canonicalThresholdCandidate_cellMass wSeedS wTable wHp wHprop wNN wNorm ()

/-- This declaration supplies the canonical canonical standard borel space w candidate typeclass instance for the finite slate-benefit construction. -/
noncomputable instance instStandardBorelSpaceWCandidate :
    StandardBorelSpace wCandidate.system.Ω := wCandidate.slate.borel

/-- [the witness candidate propensity equals the stated value](goal). -/
theorem wCandidate_propensity : wCandidate.slate.propensity () = (1 : ℝ) / 2 := by
  unfold POSlateSystem.propensity conditionalReal
  rw [show wCandidate.slate.xEvent () = Set.univ by
    ext ω
    simp [POSlateSystem.xEvent]]
  rw [if_pos (by simp [Measure.real])]
  rw [Set.inter_univ]
  have hm : Measurable (witnessEncoding wCandidate.slate) := measurable_from_top
  have hz : wCandidate.system.μ.real {w | wCandidate.slate.factualZ w = true} =
      witnessFullMeasure.real {u : Bool × WitnessLatentState | u.1 = true} := by
    rw [← wFullLaw]
    unfold Measure.real
    rw [Measure.map_apply hm MeasurableSet.of_discrete]
    congr 1
  rw [hz]
  unfold witnessFullMeasure Measure.real
  rw [show ({u : Bool × WitnessLatentState | u.1 = true} :
      Set (Bool × WitnessLatentState)) =
      ({true} : Set Bool) ×ˢ Set.univ by ext u; simp]
  rw [Measure.prod_prod, witnessLatentMeasure_univ]
  norm_num [witnessInstrumentMeasure, Measure.add_apply, Measure.smul_apply,
    Set.indicator, ENNReal.toReal_add]

/-- [the witness model has no defiers](goal). -/
theorem wCompliers : ∀ᵐ w ∂wCandidate.system.μ,
    wCandidate.slate.D0 w = false ∧ wCandidate.slate.D1 w = true := by
  have h : ∀ᵐ u ∂wCandidate.system.μ.map (witnessEncoding wCandidate.slate),
      u.2.1 = false ∧ u.2.2.1 = true := by
    rw [wFullLaw]
    unfold witnessFullMeasure
    rw [Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete]
    exact Filter.Eventually.of_forall (fun _ => witnessLatentMeasure_ae_compliers)
  change ∀ᵐ w ∂wCandidate.system.μ,
    (witnessEncoding wCandidate.slate w).2.1 = false ∧
      (witnessEncoding wCandidate.slate w).2.2.1 = true
  exact ae_of_ae_map
    ((measurable_from_top : Measurable (witnessEncoding wCandidate.slate)).aemeasurable) h

/-- [the witness selection response is weakly increasing](goal). -/
theorem wSelectionIncreasing : ∀ᵐ w ∂wCandidate.system.μ,
    wCandidate.slate.S0 w ≤ wCandidate.slate.S1 w := by
  have h : ∀ᵐ u ∂wCandidate.system.μ.map (witnessEncoding wCandidate.slate),
      u.2.2.2.1 ≤ u.2.2.2.2.1 := by
    rw [wFullLaw]
    unfold witnessFullMeasure
    rw [Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete]
    exact Filter.Eventually.of_forall (fun _ => witnessLatentMeasure_ae_selection)
  change ∀ᵐ w ∂wCandidate.system.μ,
    (witnessEncoding wCandidate.slate w).2.2.2.1 ≤
      (witnessEncoding wCandidate.slate w).2.2.2.2.1
  exact ae_of_ae_map
    ((measurable_from_top : Measurable (witnessEncoding wCandidate.slate)).aemeasurable) h

/-- [the witness capacity table is valid](goal). -/
theorem wValid : ValidCapacities (observableCapacities witnessObservedMeasure) := by
  constructor
  · intro x i
    cases x
    rw [wLower i]
    fin_cases i <;> norm_num
  · intro x i
    cases x
    rw [wUpper i]
    fin_cases i <;> norm_num

/-- [the witness construction satisfies the maintained structural model](goal). -/
theorem wModel : TieSafeSurvivorModel wCandidate.slate (1 / 4) (fun _ => true) := by
  have hcons := canonicalThresholdCandidate_consistency
    wSeedS wTable wHp wHprop wNN wNorm
  refine
    { ivIndependence := canonicalThresholdCandidate_ivIndependence
        wSeedS wTable wHp wHprop wNN wNorm
      treatmentConsistency := hcons.1
      selectionExclusion := hcons.2.1
      outcomeExclusion := hcons.2.2
      instrumentOverlap := ?_
      noDefiers := ?_
      weakSelectionMonotonicity := ?_
      positiveAggregateSurvivors := ?_ }
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro x hx
    cases x
    rw [wCandidate_propensity]
    norm_num
  · filter_upwards [wCompliers] with w hw
    intro _
    exact hw.2
  · apply canonicalThresholdCandidate_weakSelectionMonotonicity
      wSeedS wTable wHp wHprop wNN wNorm (fun _ => true)
    · intro x y0 y1 hd
      simp [wTable, witnessLatentTable]
    · intro x y0 y1 hd
      simp at hd
  · unfold PositiveAggregateSurvivors Capacities.aggregateMass
    rw [wObservedLaw]
    simp [wCandidate_p]
    rw [wCapacityFacts.2.1]
    norm_num

/-- [the witness candidate realizes its own observed law](goal). -/
theorem wRealization : WitnessFullLawRealization := by
  exact ⟨wCandidate.system, wCandidate.slate, wModel, wObservedLaw,
    wFullLaw, wCompliers, wSelectionIncreasing⟩

/-- [the witness candidate has valid capacities](goal). -/
theorem wCandidateValid :
    ValidCapacities (observableCapacities wCandidate.slate.observedLaw) := by
  rw [wObservedLaw]
  exact wValid

/-- [every witness candidate cell probability is nonnegative](goal). -/
theorem wCandidatePNonnegative : ∀ x, 0 ≤ wCandidate.slate.p x := by
  intro x
  rw [wCandidate_p]
  norm_num

/-- [the witness observed cell weights property holds](goal). -/
theorem witnessObservedCellWeights :
    (fun _ : Unit => (1 : ℝ)) =
      Capacities.observedCellWeights witnessObservedMeasure := by
  funext x
  cases x
  rw [← wObservedLaw]
  rw [← congrFun (p_eq_observedCellWeights wCandidate.slate) ()]
  exact wCandidate_p.symm

/-- [the witness candidate has positive aggregate survivor mass](goal). -/
theorem wCandidateMassPositive :
    0 < (observableCapacities wCandidate.slate.observedLaw).aggregateMass
      wCandidate.slate.p :=
  wModel.positiveAggregateSurvivors

/-- [the witness observed law belongs to the admissible observed-law domain](goal). -/
theorem wObservedLawDomain : ObservedLawDomain witnessObservedMeasure := by
  rw [← wObservedLaw]
  exact observedLawDomain wCandidate.slate

/-- [the witness endpoint lies at the claimed boundary](goal). -/
theorem wEndpoint :
    ((observableCapacities wCandidate.slate.observedLaw).endpointMap
      wCandidate.slate.p wCandidate.slate.observedLaw rfl
      (p_eq_observedCellWeights wCandidate.slate) wCandidateValid wCandidatePNonnegative
      wCandidateMassPositive (observedLawDomain wCandidate.slate)).endpoints =
        (0, (7 : ℝ) / 10) := by
  unfold Capacities.endpointMap
  dsimp only
  rw [wObservedLaw]
  simp [Capacities.endpointMap, Capacities.aggregateMass, wCandidate_p,
    wCapacityFacts.2.1, wCapacityFacts.2.2.2.2.1,
    wCapacityFacts.2.2.2.2.2] <;> norm_num

/-- [the witness identified interval has the claimed endpoints](goal). -/
theorem wInterval :
    let c := observableCapacities witnessObservedMeasure
    ∃ (hValid : ValidCapacities c) (hp : ∀ x, 0 ≤ (fun _ : Unit => (1 : ℝ)) x)
      (hMass : 0 < c.aggregateMass (fun _ => 1)),
      c.identifiedIcc (fun _ => 1) witnessObservedMeasure rfl
        witnessObservedCellWeights hValid hp hMass wObservedLawDomain =
        Set.Icc 0 ((7 : ℝ) / 10) := by
  dsimp only
  refine ⟨wValid, by intro x; norm_num, ?_, ?_⟩
  · simp [Capacities.aggregateMass]
    rw [wCapacityFacts.2.1]
    norm_num
  · simp [Capacities.identifiedIcc, Capacities.endpointMap,
      Capacities.aggregateMass, wCapacityFacts.1, wCapacityFacts.2.1,
      wCapacityFacts.2.2.1, wCapacityFacts.2.2.2.1,
      wCapacityFacts.2.2.2.2.1, wCapacityFacts.2.2.2.2.2]
    norm_num

/-- [the two witness laws attain the lower and upper endpoints](goal). -/
theorem wEndpointWitnesses : ∃ (PL : POSystem.{0, 0, 0}) (SL : POSlateSystem PL Unit 3)
      (PU : POSystem.{0, 0, 0}) (SU : POSlateSystem PU Unit 3),
      IsEndpointWitness witnessObservedMeasure (1 / 4) (fun _ => true)
        0 PL SL ∧
      IsEndpointWitness witnessObservedMeasure (1 / 4) (fun _ => true)
        ((7 : ℝ) / 10) PU SU := by
  obtain ⟨baseline, PL, SL, PU, SU, hL, hU, hRL, hRU⟩ :=
    full_law_endpoint_attainment wCandidate.slate (1 / 4) (fun _ => true)
      wModel.ivIndependence wModel.noDefiers wModel.weakSelectionMonotonicity wModel
  refine ⟨PL, SL, PU, SU, ?_, ?_⟩
  · rw [wEndpoint] at hL
    rw [wObservedLaw] at hL
    exact hL
  · rw [wEndpoint] at hU
    rw [wObservedLaw] at hU
    exact hU

/-- The explicit witness belongs to the model class, gives capacities `(3/40,1/10,3/40)` and `(1/10,1/4,3/20)`, and has sharp interval `[0,7/10]` with both endpoints attained by full laws. [the stated conclusion follows](goal). -/
-- @node: prop:three-level-witness
theorem three_level_witness_sharp :
    let c := observableCapacities witnessObservedMeasure
    WitnessFullLawRealization ∧
    (∀ i, c.lower () i = ![(3 : ℝ) / 40, (1 : ℝ) / 10, (3 : ℝ) / 40] i) ∧
    (∀ j, c.upper () j = ![(1 : ℝ) / 10, (1 : ℝ) / 4, (3 : ℝ) / 20] j) ∧
    c.q0 () = (1 : ℝ) / 4 ∧ c.mass () = (1 : ℝ) / 4 ∧
    c.q1 () = (1 : ℝ) / 2 ∧ c.gap () = (1 : ℝ) / 4 ∧
    c.benefitLower () = 0 ∧ c.benefitUpper () = (7 : ℝ) / 40 ∧
    (∃ (hValid : ValidCapacities c) (hp : ∀ x, 0 ≤ (fun _ : Unit => (1 : ℝ)) x)
      (hMass : 0 < c.aggregateMass (fun _ => 1)),
      c.identifiedIcc (fun _ => 1) witnessObservedMeasure rfl
        witnessObservedCellWeights hValid hp hMass wObservedLawDomain =
        Set.Icc 0 ((7 : ℝ) / 10)) ∧
    (∃ (PL : POSystem.{0, 0, 0}) (SL : POSlateSystem PL Unit 3)
      (PU : POSystem.{0, 0, 0}) (SU : POSlateSystem PU Unit 3),
      IsEndpointWitness witnessObservedMeasure (1 / 4) (fun _ => true)
        0 PL SL ∧
      IsEndpointWitness witnessObservedMeasure (1 / 4) (fun _ => true)
        ((7 : ℝ) / 10) PU SU) := by
  dsimp only
  exact ⟨wRealization, wLower, wUpper, wCapacityFacts.1,
    wCapacityFacts.2.1, wCapacityFacts.2.2.1, wCapacityFacts.2.2.2.1,
    wCapacityFacts.2.2.2.2.1, wCapacityFacts.2.2.2.2.2,
    wInterval, wEndpointWitnesses⟩

end CausalSmith.PartialID.SlateBenefitPartialTransport
