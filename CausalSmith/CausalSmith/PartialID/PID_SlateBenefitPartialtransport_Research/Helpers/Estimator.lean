import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Capacities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite-cell plug-in endpoints and guarded confidence set

All empirical probabilities are finite averages of event indicators. Conditional
ratios use zero when their empirical denominator is zero.
-/

open scoped BigOperators
open MeasureTheory Set

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

-- @env: S3
variable {𝒳 Ω : Type*} [Fintype 𝒳] [DecidableEq 𝒳]
variable {K : ℕ}

/-- The empirical freq is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def empiricalFreq (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (E : ObservedDatum 𝒳 K → Bool) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ r ∈ Finset.range n, if E (O r ω) then 1 else 0
  -- @realizes \widehat P_n(empirical law evaluated at an event)

/-- The empirical probability vector is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def empiricalProbabilityVector
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (n : ℕ) (ω : Ω) :
    ObservedDatum 𝒳 K → ℝ :=
  fun o => empiricalFreq O (fun u => decide (u = o)) n ω

private noncomputable def empiricalArm (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (n : ℕ) (ω : Ω) (x : 𝒳) (z : Bool) : ℝ :=
  empiricalFreq O (fun o => decide (o.cell = x ∧ o.instrument = z)) n ω

private noncomputable def empiricalSelectedOutcome (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (n : ℕ) (ω : Ω) (x : 𝒳) (d z : Bool) (i : Fin K) : ℝ :=
  empiricalFreq O (fun o => decide (o.cell = x ∧ o.instrument = z ∧
    o.treatment = d ∧ o.selected = true ∧ o.outcome = some i)) n ω

/-- The empirical conditional is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def empiricalConditional (num den : ℝ) : ℝ :=
  if 0 < den then num / den else 0

/-- The empirical cell mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def empiricalCellMass (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (n : ℕ) (ω : Ω) (x : 𝒳) : ℝ :=
  empiricalFreq O (fun o => decide (o.cell = x)) n ω
  -- @realizes \widehat p_x(empirical cell probability)

/-- The raw capacities is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def rawCapacities (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (n : ℕ) (ω : Ω) : Capacities 𝒳 K where
  lower x i :=
    empiricalConditional (empiricalSelectedOutcome O n ω x false false i)
        (empiricalArm O n ω x false) -
      empiricalConditional (empiricalSelectedOutcome O n ω x false true i)
        (empiricalArm O n ω x true)
      -- @realizes \widetilde\ell_i(x)(raw lower-arm contrast)
  upper x j :=
    empiricalConditional (empiricalSelectedOutcome O n ω x true true j)
        (empiricalArm O n ω x true) -
      empiricalConditional (empiricalSelectedOutcome O n ω x true false j)
        (empiricalArm O n ω x false)
      -- @realizes \widetilde h_j(x)(raw upper-arm contrast)
  -- @realizes \widetilde c_n(stacked raw capacity vector)

/-- The projected capacities is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def projectedCapacities (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (n : ℕ) (ω : Ω) : Capacities 𝒳 K where
  lower x i := max ((rawCapacities O n ω).lower x i) 0
    -- @realizes \widehat\ell_i(x)(positive part of raw lower contrast)
  upper x j := max ((rawCapacities O n ω).upper x j) 0
    -- @realizes \widehat h_j(x)(positive part of raw upper contrast)
  -- @realizes \widehat c_n(coordinatewise Euclidean projection onto \mathfrak C)

/-- The screened cell condition is the stated property of the slate-benefit partial-transport model. -/
noncomputable def screenedCell (O : ℕ → Ω → ObservedDatum 𝒳 K) (η : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (x : 𝒳) : Prop :=
  η n < empiricalCellMass O n ω x * (projectedCapacities O n ω).mass x
  -- @realizes \widehat r_x(empirical cell survivor mass) @realizes \eta_n(screening threshold)

-- @node: def:plugin-endpoint-estimator
/-- The plug in endpoints is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def plugInEndpoints (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (η : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ × ℝ := by
  classical
  let ĉ := projectedCapacities O n ω
  let px := empiricalCellMass O n ω
  let keep := fun x => if screenedCell O η n ω x then (1 : ℝ) else 0
  let Mhat := ∑ x, keep x * px x * ĉ.mass x
  let NLhat := ∑ x, keep x * px x * ĉ.benefitLower x
  let NUhat := ∑ x, keep x * px x * ĉ.benefitUpper x
  exact if 0 < Mhat then (NLhat / Mhat, NUhat / Mhat) else (0, 1)
  -- @realizes \widehat q_0(x)(q0 of projected capacities)
  -- @realizes \widehat q_1(x)(q1 of projected capacities)
  -- @realizes \widehat{\Delta q}(x)(gap of projected capacities)
  -- @realizes \widehat m(x)(mass of projected capacities)
  -- @realizes \widehat B_L(x)(branch-free lower cut at projected capacities)
  -- @realizes \widehat B_U(x)(branch-free upper cut at projected capacities)
  -- @realizes \widehat M_n(screened denominator)
  -- @realizes \widehat N_{L,n}(screened lower numerator)
  -- @realizes \widehat N_{U,n}(screened upper numerator)
  -- @realizes \widehat\Psi_n(total plug-in endpoint estimator with fallback)

/-- The positive support is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def positiveSupport (c : Capacities 𝒳 K) (p : 𝒳 → ℝ) : Finset 𝒳 := by
  classical
  exact Finset.univ.filter fun x => 0 < p x * c.mass x
  -- @realizes \mathcal X_+(P)(positive-survivor covariate support)

/-- The screened support is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def screenedSupport (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (η : ℕ → ℝ) (n : ℕ) (ω : Ω) : Finset 𝒳 := by
  classical
  exact Finset.univ.filter fun x => screenedCell O η n ω x

/-- The mass vector sum is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def massVectorSum (v : ObservedDatum 𝒳 K → ℝ)
    (E : ObservedDatum 𝒳 K → Bool) : ℝ :=
  ∑ o with E o, v o

/-- [the mass vector sum empirical probability vector property holds](goal). -/
theorem massVectorSum_empiricalProbabilityVector
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (E : ObservedDatum 𝒳 K → Bool)
    (n : ℕ) (ω : Ω) :
    massVectorSum (empiricalProbabilityVector O n ω) E = empiricalFreq O E n ω := by
  classical
  unfold massVectorSum empiricalProbabilityVector empiricalFreq
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hE : E (O r ω) = true
  · simp only [hE, Bool.true_eq, ↓reduceIte]
    rw [Finset.sum_eq_single (O r ω)]
    · simp
    · intro b hb hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (by simp [hE])).elim
  · have hEf : E (O r ω) = false := Bool.eq_false_of_not_eq_true hE
    simp only [hEf, Bool.false_eq]
    rw [if_neg (by decide), mul_zero]
    apply Finset.sum_eq_zero
    intro o ho
    by_cases hor : O r ω = o
    · subst o
      exfalso
      exact hE (by simpa using ho)
    · simp [hor]

/-- Summing the atom vector of a finite law over a Boolean event recovers the real measure of that event. [the stated conclusion follows](goal). -/
theorem massVectorSum_measureReal [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    (Pobs : Measure (ObservedDatum 𝒳 K)) [IsFiniteMeasure Pobs]
    (E : ObservedDatum 𝒳 K → Bool) :
    massVectorSum (fun o => Pobs.real {o}) E = Pobs.real {o | E o = true} := by
  classical
  unfold massVectorSum
  rw [MeasureTheory.sum_measureReal_singleton]
  congr 1
  ext o
  simp

/-- The capacities from mass vector is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def capacitiesFromMassVector (v : ObservedDatum 𝒳 K → ℝ) :
    Capacities 𝒳 K where
  lower x i :=
    empiricalConditional
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = false ∧
        o.treatment = false ∧ o.selected = true ∧ o.outcome = some i)))
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = false))) -
    empiricalConditional
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = true ∧
        o.treatment = false ∧ o.selected = true ∧ o.outcome = some i)))
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = true)))
  upper x j :=
    empiricalConditional
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = true ∧
        o.treatment = true ∧ o.selected = true ∧ o.outcome = some j)))
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = true))) -
    empiricalConditional
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = false ∧
        o.treatment = true ∧ o.selected = true ∧ o.outcome = some j)))
      (massVectorSum v (fun o => decide (o.cell = x ∧ o.instrument = false)))

/-- The endpoint from mass vector on is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def endpointFromMassVectorOn (support : Finset 𝒳)
    (v : ObservedDatum 𝒳 K → ℝ) : ℝ × ℝ :=
  let raw := capacitiesFromMassVector v
  let c : Capacities 𝒳 K :=
    { lower := fun x i => max (raw.lower x i) 0
      upper := fun x j => max (raw.upper x j) 0 }
  let p := fun x => massVectorSum v (fun o => decide (o.cell = x))
  let M := ∑ x ∈ support, p x * c.mass x
  ((∑ x ∈ support, p x * c.benefitLower x) / M,
    (∑ x ∈ support, p x * c.benefitUpper x) / M)

/-- Definitional expansion of the lower finite threshold envelope. [the stated conclusion follows](goal). -/
theorem benefitLower_eq_sup_explicit (c : Capacities 𝒳 K) (x : 𝒳) :
    c.benefitLower x =
      Finset.univ.sup' Finset.univ_nonempty (fun t : Option (Fin K) =>
        match t with
        | none => 0
        | some k => c.lowerLe x k - c.upperLe x k + min (c.gap x) 0) :=
  rfl

/-- Definitional expansion of the upper finite threshold envelope. [the stated conclusion follows](goal). -/
theorem benefitUpper_eq_inf_explicit (c : Capacities 𝒳 K) (x : 𝒳) :
    c.benefitUpper x =
      Finset.univ.inf' Finset.univ_nonempty (fun t : Option (Fin K) =>
        match t with
        | none => c.mass x
        | some k => c.lowerLt x k + c.upperGt x k) :=
  rfl

/-- The localization tol is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def localizationTol (n : ℕ) (η : ℕ → ℝ) : ℝ :=
  ((n : ℝ) * η n) ^ (-(1 : ℝ) / 4)
  -- @realizes a_n(near-active-face localization tolerance)

/-- The estimated active lower is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def estimatedActiveLower (c : Capacities 𝒳 K) (x : 𝒳) (a : ℝ) :
    Finset (Option (Fin K)) := by
  classical
  exact Finset.univ.filter fun t =>
    match t with
    | none => c.benefitLower x ≤ a
    | some k => c.benefitLower x -
        (c.lowerLe x k - c.upperLe x k + min (c.gap x) 0) ≤ a
  -- @realizes \widehat{\mathcal A}_{L,n}(x;a_n)(near-active lower cuts)

/-- The estimated active upper is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def estimatedActiveUpper (c : Capacities 𝒳 K) (x : 𝒳) (a : ℝ) :
    Finset (Option (Fin K)) := by
  classical
  exact Finset.univ.filter fun t =>
    match t with
    | none => c.mass x - c.benefitUpper x ≤ a
    | some k => c.lowerLt x k + c.upperGt x k - c.benefitUpper x ≤ a
  -- @realizes \widehat{\mathcal A}_{U,n}(x;a_n)(near-active upper cuts)

/-- The multiplier process is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def multiplierProcess (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (o : ObservedDatum 𝒳 K) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 2) *
    ∑ r ∈ Finset.range n, ξ r ω *
      ((if O r ω = o then 1 else 0) - empiricalFreq O (fun u => decide (u = o)) n ω)
  -- @realizes \xi_r(conditionally centered unit-variance multiplier input)
  -- @realizes \mathbb G_n^{\xi}(finite conditional multiplier process)

/-- Indices for the three finite families of observable events used by the guard. -/
inductive GuardEventIndex (𝒳 : Type*) (K : ℕ)
  | cell (x : 𝒳)
  | arm (x : 𝒳) (z : Bool)
  | selectedOutcome (x : 𝒳) (z d : Bool) (k : Fin K)
  deriving DecidableEq, Fintype

/-- Guard-event indices have decidable equality. -/
add_decl_doc instDecidableEqGuardEventIndex

/-- The guard-event index type has a canonical finite enumeration. -/
add_decl_doc instFintypeGuardEventIndex

/-- The guard event is the event specified by the stated potential-outcome conditions. -/
def guardEvent (e : GuardEventIndex 𝒳 K) (o : ObservedDatum 𝒳 K) : Bool :=
  match e with
  | .cell x => decide (o.cell = x)
  | .arm x z => decide (o.cell = x ∧ o.instrument = z)
  | .selectedOutcome x z d k => decide (o.cell = x ∧ o.instrument = z ∧
      o.treatment = d ∧ o.selected = true ∧ o.outcome = some k)

/-- The guard events is the event specified by the stated potential-outcome conditions. -/
noncomputable def guardEvents (𝒳 : Type*) [Fintype 𝒳] [DecidableEq 𝒳] (K : ℕ) :
    Finset (GuardEventIndex 𝒳 K) :=
  Finset.univ
  -- @realizes \mathcal E(finite observable event collection)

/-- The max deviation is the measure produced by the stated finite slate-benefit construction. -/
noncomputable def maxDeviation (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : Measure (ObservedDatum 𝒳 K)) [IsProbabilityMeasure Pobs]
    (n : ℕ) (ω : Ω) : ℝ := by
  classical
  exact if h : (guardEvents 𝒳 K).Nonempty then
    (guardEvents 𝒳 K).sup' h fun E =>
      |empiricalFreq O (guardEvent E) n ω - Pobs.real {o | guardEvent E o = true}|
  else 0
  -- @realizes \delta_n(maximum empirical deviation over \mathcal E)

/-- The union threshold is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def unionThreshold (𝒳 : Type*) [Fintype 𝒳] [DecidableEq 𝒳]
    (K n : ℕ) (α : ℝ) : ℝ :=
  Real.sqrt ((guardEvents 𝒳 K).card / (4 * (n : ℝ) * α))
  -- @realizes b_{n,\alpha}(finite union second-moment threshold)

/-- The error envelope is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def errorEnvelope (𝒳 : Type*) [Fintype 𝒳] [DecidableEq 𝒳]
    (K n : ℕ) (η : ℕ → ℝ) (εZ α : ℝ) : ℝ :=
  (64 * (K : ℝ) * (Fintype.card 𝒳 : ℝ) / εZ ^ 2) *
      unionThreshold 𝒳 K n α + (Fintype.card 𝒳 : ℝ) * η n
  -- @realizes A_{n,\alpha}(capacity and screening error envelope)

/-- The guard radius is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def guardRadius (𝒳 : Type*) [Fintype 𝒳] [DecidableEq 𝒳]
    [Nonempty 𝒳] (K n : ℕ) (η : ℕ → ℝ) (mstar εZ α : ℝ)
    (_hK : 3 ≤ K) (_hn : 1 ≤ n) (_hEta : 0 < η n) (_hmstar : 0 < mstar)
    (_hEpsilon : 0 < εZ ∧ εZ < (1 : ℝ) / 2)
    (_hAlpha : 0 < α ∧ α < 1) : ℝ :=
  min 1 (4 * errorEnvelope 𝒳 K n η εZ α / mstar)
  -- @realizes g_{n,\alpha}(positive alpha-indexed deterministic guard capped at one)

/-- The finite near-active diagnostic retained alongside the conservative set. -/
structure GuardedInferenceHandle (𝒳 : Type*) (K : ℕ) where
  confidenceSet : Set ℝ
  lowerThresholdFaces : 𝒳 → Finset (Option (Fin K))
  upperThresholdFaces : 𝒳 → Finset (Option (Fin K))
  zeroGapFaces : Finset 𝒳
  massMinimumFaces : Finset 𝒳
  projectionFaces : Finset (𝒳 × Bool × Fin K)
  multiplierEnvelope : ObservedDatum 𝒳 K → ℝ

-- @node: def:face-aware-inference-handle
/-- The guarded confidence set is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def guardedConfidenceSet [Nonempty 𝒳]
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (ξ : ℕ → Ω → ℝ) (η : ℕ → ℝ) (mstar εZ α : ℝ)
    (hα : 0 < α ∧ α < 1) (hmstar : 0 < mstar)
    (hεZ : 0 < εZ ∧ εZ < (1 : ℝ) / 2) (n : ℕ) (hK : 3 ≤ K) (hn : 1 ≤ n)
    (hη : 0 < η n) (ω : Ω) :
    GuardedInferenceHandle 𝒳 K := by
  classical
  let c := projectedCapacities O n ω
  let a := localizationTol n η
  let ψ := plugInEndpoints O η n ω
  let g := guardRadius 𝒳 K n η mstar εZ α hK hn hη hmstar hεZ hα
  exact
    { confidenceSet := Set.Icc (max 0 (ψ.1 - g)) (min 1 (ψ.2 + g))
      lowerThresholdFaces := fun x =>
        if screenedCell O η n ω x then estimatedActiveLower c x a else ∅
      upperThresholdFaces := fun x =>
        if screenedCell O η n ω x then estimatedActiveUpper c x a else ∅
      zeroGapFaces := Finset.univ.filter fun x =>
        screenedCell O η n ω x ∧ c.gap x = 0
      massMinimumFaces := Finset.univ.filter fun x =>
        screenedCell O η n ω x ∧ c.q0 x = c.q1 x
      projectionFaces := (Finset.univ.product (Finset.univ.product Finset.univ)).filter
        fun xbi => screenedCell O η n ω xbi.1 ∧
          if xbi.2.1 then (rawCapacities O n ω).upper xbi.1 xbi.2.2 ≤ 0
          else (rawCapacities O n ω).lower xbi.1 xbi.2.2 ≤ 0
      multiplierEnvelope := fun o =>
        if screenedCell O η n ω o.cell then multiplierProcess O ξ n ω o else 0 }
  -- @realizes \alpha(nominal error level in the open unit interval)
  -- @realizes \mathcal C_{1-\alpha,n}(guarded interval with finite face diagnostic)

/-- The guarded confidence interval is the event specified by the stated potential-outcome conditions. -/
noncomputable def guardedConfidenceInterval [Nonempty 𝒳]
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (ξ : ℕ → Ω → ℝ) (η : ℕ → ℝ) (mstar εZ α : ℝ)
    (hα : 0 < α ∧ α < 1) (hmstar : 0 < mstar)
    (hεZ : 0 < εZ ∧ εZ < (1 : ℝ) / 2) (n : ℕ) (hK : 3 ≤ K) (hn : 1 ≤ n)
    (hη : 0 < η n) (ω : Ω) : Set ℝ :=
  (guardedConfidenceSet O ξ η mstar εZ α hα hmstar hεZ n hK hn hη ω).confidenceSet

end CausalSmith.PartialID.SlateBenefitPartialTransport
