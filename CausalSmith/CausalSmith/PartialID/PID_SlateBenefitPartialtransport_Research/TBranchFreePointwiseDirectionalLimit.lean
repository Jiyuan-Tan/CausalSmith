import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Estimator
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.CitedGates
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.EndpointDirectional
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.WeakConvergenceTools
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TSharpExactMassThresholdInterval

/-!
# Branch-free pointwise directional limit

At each fixed finite-support law, screening recovers the positive-survivor
support, the endpoint estimator is consistent, and its scaled error has the
directional delta-method limit, including all tie faces.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open Causalean PO Causalean.Stat

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

universe uΩ u𝒳

variable {𝒳 : Type u𝒳} {Ω : Type uΩ} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳] [MeasurableSpace Ω]
variable {K : ℕ} {P : POSystem} [StandardBorelSpace P.Ω]
variable {μ : Measure Ω}

/-- The endpoint converges in probability condition is the stated property of the slate-benefit partial-transport model. -/
def EndpointConvergesInProbability
    (Xn : ℕ → Ω → ℝ × ℝ) (target : ℝ × ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε > 0, Tendsto (fun n => μ.real {ω | ε < max |(Xn n ω).1 - target.1|
    |(Xn n ω).2 - target.2|}) atTop (𝓝 0)

/-- Conditional on the disclosed finite-multinomial CLT and general directional delta-method gates, the branch-free plug-in estimator recovers the fixed support, is consistent, and has the Gaussian directional limit without a direction-separation premise. Given [the stated hypotheses](hyp:_hIid,_hEtaPositive,_hSqrtEta,hFiniteMultinomialCLT_of_gate,hHadamardDirectionalDeltaMethod_of_gate), [the stated conclusion follows](goal). -/
-- @node: thm:branch-free-pointwise-directional-limit
theorem branch_free_pointwise_directional_limit
    (Sys : POSlateSystem P 𝒳 K) (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (η : ℕ → ℝ) (εZ : ℝ) (d : 𝒳 → Bool)
    (_hIid : ∀ n, IidSampling n μ Sys.observedLaw O)
    (_hOverlap : InstrumentOverlap Sys εZ)
    (model : TieSafeSurvivorModel Sys εZ d)
    (_hEtaPositive : ∀ n, 0 < η n)
    (_hEtaZero : Tendsto η atTop (𝓝 0))
    (_hSqrtEta : Tendsto (fun n : ℕ => Real.sqrt n * η n) atTop atTop)
    (hFiniteMultinomialCLT_of_gate : FiniteMultinomialCLT.{uΩ, u𝒳})
    (hHadamardDirectionalDeltaMethod_of_gate :
      HadamardDirectionalDeltaMethod.{uΩ, u𝒳, 0}) :
    let c := observableCapacities Sys.observedLaw
    let hIdentification := capacity_identification Sys εZ d model.ivIndependence
      model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
      model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
    let hValid : ValidCapacities c := hIdentification.1.2
    let hp : ∀ x, 0 ≤ Sys.p x := hIdentification.2.1
    let hMass : 0 < c.aggregateMass Sys.p := model.positiveAggregateSurvivors
    let support := positiveSupport c Sys.p
    Tendsto
      (fun n => μ.real {ω | screenedSupport O η n ω = support})
      atTop (𝓝 1) ∧
    EndpointConvergesInProbability (fun n => plugInEndpoints O η n)
      (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
        hValid hp hMass (observedLawDomain Sys)).endpoints μ ∧
    ∃ (Q : Measure (ObservedDatum 𝒳 K → ℝ))
      (Dψ : (ObservedDatum 𝒳 K → ℝ) → ℝ × ℝ),
      IsGaussian Q ∧
      (∫ z, z ∂Q = 0) ∧
      (∀ a b,
        ∫ z, z a * z b ∂Q =
          if a = b then Sys.observedLaw.real {a} * (1 - Sys.observedLaw.real {a})
          else -(Sys.observedLaw.real {a} * Sys.observedLaw.real {b})) ∧
      HasHadamardDirDerivAt (endpointFromMassVectorOn support) Dψ
        (fun o => Sys.observedLaw.real {o}) ∧
      WeakConverges
        (fun n ω => Real.sqrt n •
          (plugInEndpoints O η n ω -
            (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
              hValid hp hMass (observedLawDomain Sys)).endpoints))
        (Q.map Dψ) μ := by
  dsimp
  classical
  let c := observableCapacities Sys.observedLaw
  let support := positiveSupport c Sys.p
  let θ : ObservedDatum 𝒳 K → ℝ := fun o => Sys.observedLaw.real {o}
  have hIdentification := capacity_identification Sys εZ d model.ivIndependence
    model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
    model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
  have hValid : ValidCapacities c := hIdentification.1.2
  have hp : ∀ x, 0 ≤ Sys.p x := hIdentification.2.1
  have hMass : 0 < c.aggregateMass Sys.p := model.positiveAggregateSurvivors
  letI : IsProbabilityMeasure Sys.observedLaw := hIdentification.1.1
  letI : IsProbabilityMeasure μ := (_hIid 1).isProbabilityMeasure
  obtain ⟨Q, hQ, hQmean, hQcov, hweak⟩ :=
    hFiniteMultinomialCLT_of_gate μ Sys.observedLaw O inferInstance inferInstance _hIid
  have hArm : ∀ x ∈ support, ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z)) := by
    intro x hx z
    have hprod : 0 < Sys.p x * c.mass x := by
      simpa [support, positiveSupport] using hx
    have hpxne : Sys.p x ≠ 0 := by
      intro hpzero
      simp [hpzero] at hprod
    have hpx : 0 < Sys.p x := lt_of_le_of_ne (hIdentification.2.1 x) hpxne.symm
    rw [massVectorSum_measureReal]
    unfold POSlateSystem.observedLaw
    rw [Measure.real, Measure.map_apply
      (observedDatum_measurable_for_identification Sys)
      ((Set.toFinite _).measurableSet)]
    have hevent : Sys.observedDatum ⁻¹'
        {o | decide (o.cell = x ∧ o.instrument = z) = true} =
        Sys.xEvent x ∩ Sys.zVar.event z := by
      ext w
      simp [POSlateSystem.observedDatum, POSlateSystem.xEvent, POVar.event,
        POSlateSystem.factualX, POSlateSystem.factualZ]
    rw [hevent]
    exact arm_cell_positive_of_overlap Sys _hOverlap x hpx z
  have hcapRaw : capacitiesFromMassVector θ = c := by
    unfold c observableCapacities observableCapacityContrasts
    rw [Capacities.mk.injEq]
    constructor
    · funext x i
      have hden (z : Bool) :
          {o : ObservedDatum 𝒳 K | decide (o.cell = x ∧ o.instrument = z) = true} =
            {o | o.cell = x ∧ o.instrument = z} := by
        ext o
        simp
      have hnum (z treatment : Bool) :
          {o : ObservedDatum 𝒳 K |
              decide (o.cell = x ∧ o.instrument = z ∧ o.treatment = treatment ∧
                o.selected = true ∧ o.outcome = some i) = true} =
            {o | o.cell = x ∧ o.treatment = treatment ∧ o.selected = true ∧
                o.outcome = some i} ∩
              {o | o.cell = x ∧ o.instrument = z} := by
        ext o
        simp [and_assoc, and_left_comm, and_comm]
      change empiricalConditional
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = false ∧
            o.treatment = false ∧ o.selected = true ∧ o.outcome = some i)))
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = false))) -
        empiricalConditional
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = true ∧
            o.treatment = false ∧ o.selected = true ∧ o.outcome = some i)))
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = true))) =
        conditionalReal Sys.observedLaw
            {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some i}
            {o | o.cell = x ∧ o.instrument = false} -
          conditionalReal Sys.observedLaw
            {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some i}
            {o | o.cell = x ∧ o.instrument = true}
      unfold empiricalConditional conditionalReal
      unfold θ
      simp_rw [massVectorSum_measureReal]
      rw [hden false, hden true, hnum false false, hnum true false]
    · funext x i
      have hden (z : Bool) :
          {o : ObservedDatum 𝒳 K | decide (o.cell = x ∧ o.instrument = z) = true} =
            {o | o.cell = x ∧ o.instrument = z} := by
        ext o
        simp
      have hnum (z treatment : Bool) :
          {o : ObservedDatum 𝒳 K |
              decide (o.cell = x ∧ o.instrument = z ∧ o.treatment = treatment ∧
                o.selected = true ∧ o.outcome = some i) = true} =
            {o | o.cell = x ∧ o.treatment = treatment ∧ o.selected = true ∧
                o.outcome = some i} ∩
              {o | o.cell = x ∧ o.instrument = z} := by
        ext o
        simp [and_assoc, and_left_comm, and_comm]
      change empiricalConditional
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = true ∧
            o.treatment = true ∧ o.selected = true ∧ o.outcome = some i)))
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = true))) -
        empiricalConditional
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = false ∧
            o.treatment = true ∧ o.selected = true ∧ o.outcome = some i)))
          (massVectorSum θ (fun o => decide (o.cell = x ∧ o.instrument = false))) =
        conditionalReal Sys.observedLaw
            {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some i}
            {o | o.cell = x ∧ o.instrument = true} -
          conditionalReal Sys.observedLaw
            {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some i}
            {o | o.cell = x ∧ o.instrument = false}
      unfold empiricalConditional conditionalReal
      unfold θ
      simp_rw [massVectorSum_measureReal]
      rw [hden true, hden false, hnum true true, hnum false true]
  have hcap : projectedMassCapacity θ = c := by
    unfold projectedMassCapacity
    rw [hcapRaw, Capacities.mk.injEq]
    constructor
    · funext x i
      exact max_eq_left (hIdentification.1.2.1 x i)
    · funext x i
      exact max_eq_left (hIdentification.1.2.2 x i)
  have hcell : ∀ x, massVectorSum θ (fun o => decide (o.cell = x)) = Sys.p x := by
    intro x
    rw [massVectorSum_measureReal]
    unfold POSlateSystem.observedLaw
    rw [Measure.real, Measure.map_apply
      (observedDatum_measurable_for_identification Sys)
      ((Set.toFinite _).measurableSet)]
    have hevent : Sys.observedDatum ⁻¹' {o | decide (o.cell = x) = true} =
        Sys.xEvent x := by
      ext w
      simp [POSlateSystem.observedDatum, POSlateSystem.xEvent,
        POSlateSystem.factualX]
    rw [hevent]
    rfl
  have hmassNonneg : ∀ x, 0 ≤ c.mass x := by
    intro x
    unfold Capacities.mass
    apply le_min
    · exact Finset.sum_nonneg fun i _ => hIdentification.1.2.1 x i
    · exact Finset.sum_nonneg fun i _ => hIdentification.1.2.2 x i
  have hsupportMass : 0 < ∑ x ∈ support,
      massVectorSum θ (fun o => decide (o.cell = x)) *
        (projectedMassCapacity θ).mass x := by
    simp_rw [hcell, hcap]
    have hsum : (∑ x ∈ support, Sys.p x * c.mass x) = c.aggregateMass Sys.p := by
      unfold support positiveSupport Capacities.aggregateMass
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      have hnonneg : 0 ≤ Sys.p x * c.mass x :=
        mul_nonneg (hIdentification.2.1 x) (hmassNonneg x)
      by_cases hpos : 0 < Sys.p x * c.mass x
      · simp [hpos]
      · have hz : Sys.p x * c.mass x = 0 :=
          le_antisymm (le_of_not_gt hpos) hnonneg
        simp [hpos, hz]
    rw [hsum]
    exact model.positiveAggregateSurvivors
  obtain ⟨Dψ, hDψcont, hDψ⟩ := endpointFromMassVectorOn_chd θ support hArm hsupportMass
  let θhat : ℕ → Ω → (ObservedDatum 𝒳 K → ℝ) :=
    fun n => empiricalProbabilityVector O n
  have hOmeas : ∀ i, Measurable (O i) :=
    measurable_observations_of_iidSampling_all O _hIid
  have hθhatMeas : ∀ n, Measurable (θhat n) := by
    intro n
    exact measurable_empiricalProbabilityVector O hOmeas n
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun n : ℕ => (n : ℝ)) atTop atTop
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hweakScaled : WeakConverges
      (fun n ω => Real.sqrt n • (θhat n ω - θ)) Q μ := by
    intro f hf hfb
    simpa only [θhat, θ, empiricalAtomVector_eq_smul_sub] using hweak f hf hfb
  letI : IsProbabilityMeasure Q :=
    CausalSmith.PartialID.SlateBenefitPartialTransport.IsGaussian.isProbabilityMeasure_of_normed
      Q hQ
  have hTangential : HasTangentialHadamardDirDerivAt Set.univ Set.univ
      (endpointFromMassVectorOn support) Dψ θ := by
    refine ⟨Set.mem_univ _, hDψcont.continuousOn, ?_⟩
    intro h hh hn tn hhn htn htnpos hdomain
    exact hDψ h hn tn hhn htn htnpos
  have hSupported : SupportedIn Q (Set.univ : Set (ObservedDatum 𝒳 K → ℝ)) := by
    simp [SupportedIn]
  obtain ⟨hEndpointExpansion, hFixedWeak⟩ :=
    hHadamardDirectionalDeltaMethod_of_gate μ Set.univ Set.univ
      (endpointFromMassVectorOn support) Dψ Dψ θ θhat
      (fun n : ℕ => Real.sqrt n) Q inferInstance inferInstance hTangential
      hDψcont (fun h hh => rfl) hθhatMeas (fun n ω => Set.mem_univ _)
      hsqrt hweakScaled (tightProbabilityLaw_of_probability Q) hSupported
  have hArmPos (x : 𝒳) (hpx : 0 < Sys.p x) : ∀ z,
      0 < massVectorSum θ
        (fun o => decide (o.cell = x ∧ o.instrument = z)) := by
    intro z
    rw [massVectorSum_measureReal]
    unfold POSlateSystem.observedLaw
    rw [Measure.real, Measure.map_apply
      (observedDatum_measurable_for_identification Sys)
      ((Set.toFinite _).measurableSet)]
    have hevent : Sys.observedDatum ⁻¹'
        {o | decide (o.cell = x ∧ o.instrument = z) = true} =
        Sys.xEvent x ∩ Sys.zVar.event z := by
      ext w
      simp [POSlateSystem.observedDatum, POSlateSystem.xEvent, POVar.event,
        POSlateSystem.factualX, POSlateSystem.factualZ]
    rw [hevent]
    exact arm_cell_positive_of_overlap Sys _hOverlap x hpx z
  have hScoreWeak (x : 𝒳) (hpx : 0 < Sys.p x) :
      ∃ Dx : (ObservedDatum 𝒳 K → ℝ) → ℝ,
        Continuous Dx ∧
        HasHadamardDirDerivAt (fun v => survivorMassFromMassVector v x) Dx θ ∧
        WeakConverges
          (fun n ω => Real.sqrt n •
            (survivorMassFromMassVector (θhat n ω) x -
              survivorMassFromMassVector θ x))
          (Q.map Dx) μ := by
    obtain ⟨Dx, hDxcont, hDx⟩ :=
      survivorMassFromMassVector_chd θ x (hArmPos x hpx)
    have hTangentialX : HasTangentialHadamardDirDerivAt Set.univ Set.univ
        (fun v => survivorMassFromMassVector v x) Dx θ := by
      refine ⟨Set.mem_univ _, hDxcont.continuousOn, ?_⟩
      intro h hh hn tn hhn htn htnpos hdomain
      exact hDx h hn tn hhn htn htnpos
    letI : IsProbabilityMeasure (Q.map Dx) :=
      Measure.isProbabilityMeasure_map hDxcont.measurable.aemeasurable
    obtain ⟨hexpansion, hscore⟩ :=
      hHadamardDirectionalDeltaMethod_of_gate μ Set.univ Set.univ
        (fun v => survivorMassFromMassVector v x) Dx Dx θ θhat
        (fun n : ℕ => Real.sqrt n) Q inferInstance inferInstance hTangentialX
        hDxcont (fun h hh => rfl) hθhatMeas (fun n ω => Set.mem_univ _)
        hsqrt hweakScaled (tightProbabilityLaw_of_probability Q) hSupported
    exact ⟨Dx, hDxcont, hDx, hscore⟩
  have hScoreMeas (x : 𝒳) (n : ℕ) : Measurable
      (fun ω => Real.sqrt n •
        (survivorMassFromMassVector (θhat n ω) x -
          survivorMassFromMassVector θ x)) := by
    have hs : Measurable
        (fun v : ObservedDatum 𝒳 K → ℝ => survivorMassFromMassVector v x) := by
      exact measurable_survivorMassFromMassVector x
    change Measurable (fun ω => Real.sqrt n *
      (survivorMassFromMassVector (θhat n ω) x -
        survivorMassFromMassVector θ x))
    exact measurable_const.mul ((hs.comp (hθhatMeas n)).sub measurable_const)
  have hZeroCell (x : 𝒳) (hpx : Sys.p x = 0) (n : ℕ) :
      ∀ᵐ ω ∂μ, empiricalCellMass O n ω x = 0 := by
    have hpobsReal : Sys.observedLaw.real {o | o.cell = x} = 0 := by
      have hx := hcell x
      rw [massVectorSum_measureReal] at hx
      simpa only [decide_eq_true_eq] using hx.trans hpx
    have hpobs : Sys.observedLaw {o | o.cell = x} = 0 := by
      have hzeroOrTop := (ENNReal.toReal_eq_zero_iff _).mp hpobsReal
      exact hzeroOrTop.resolve_right (measure_ne_top _ _)
    have hone (i : ℕ) : ∀ᵐ ω ∂μ, (O i ω).cell ≠ x := by
      rw [ae_iff]
      have hset : {ω | ¬(O i ω).cell ≠ x} = O i ⁻¹' {o | o.cell = x} := by
        ext ω
        simp
      rw [hset, ← Measure.map_apply (hOmeas i) ((Set.toFinite _).measurableSet)]
      have hmap : μ.map (O i) = Sys.observedLaw := by
        exact (_hIid (i + 1)).law i (by omega)
      rw [hmap, hpobs]
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, (O i ω).cell ≠ x := by
      rw [Finset.eventually_all]
      intro i hi
      exact hone i
    filter_upwards [hall] with ω hω
    unfold empiricalCellMass empiricalFreq
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i hi
    simp [hω i hi]
  have hScoreTight (x : 𝒳) (hpx : 0 < Sys.p x) (e : ℝ) (he : 0 < e) :
      ∃ R : ℝ, ∀ n : ℕ, μ.real {ω | R < ‖Real.sqrt n •
        (survivorMassFromMassVector (θhat n ω) x -
          survivorMassFromMassVector θ x)‖} ≤ e := by
    obtain ⟨Dx, hDxcont, hDx, hwx⟩ := hScoreWeak x hpx
    letI : IsProbabilityMeasure (Q.map Dx) :=
      Measure.isProbabilityMeasure_map hDxcont.measurable.aemeasurable
    exact hwx.eventually_norm_le (hScoreMeas x) e he
  have hScorePop (x : 𝒳) : survivorMassFromMassVector θ x =
      Sys.p x * c.mass x := by
    unfold survivorMassFromMassVector
    rw [hcell x, hcap]
  have hScreenScore (x : 𝒳) (n : ℕ) (ω : Ω) :
      screenedCell O η n ω x ↔
        η n < survivorMassFromMassVector (θhat n ω) x := by
    rw [survivorMassFromMassVector_empiricalProbabilityVector]
    rfl
  have hCellError : ∀ (x : 𝒳) (e : ℝ), 0 < e →
      ∀ᶠ n in atTop, μ.real {ω |
        (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)} ≤ e := by
    intro x e he
    by_cases hpx0 : Sys.p x = 0
    · filter_upwards [] with n
      have hae := hZeroCell x hpx0 n
      have hnull : μ {ω | (x ∈ screenedSupport O η n ω) ≠
          (x ∈ support)} = 0 := by
        change μ {ω | ¬ ((x ∈ screenedSupport O η n ω) =
          (x ∈ support))} = 0
        rw [← ae_iff]
        filter_upwards [hae] with ω hzero
        have hnotScreen : x ∉ screenedSupport O η n ω := by
          simp only [screenedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hs
          have hs' := (hScreenScore x n ω).mp hs
          change η n < survivorMassFromMassVector
            (empiricalProbabilityVector O n ω) x at hs'
          rw [survivorMassFromMassVector_empiricalProbabilityVector, hzero, zero_mul] at hs'
          exact (not_lt_of_ge (_hEtaPositive n).le) hs'
        have hnotSupport : x ∉ support := by
          simp [support, positiveSupport, hpx0]
        simp [hnotScreen, hnotSupport]
      unfold Measure.real
      rw [hnull]
      simp only [ENNReal.toReal_zero]
      exact he.le
    · have hpx : 0 < Sys.p x := lt_of_le_of_ne
        (hIdentification.2.1 x) (Ne.symm hpx0)
      obtain ⟨R, hR⟩ := hScoreTight x hpx e he
      let R' := max R 0
      have hRle (n : ℕ) : μ.real {ω | R' < ‖Real.sqrt n •
          (survivorMassFromMassVector (θhat n ω) x -
            survivorMassFromMassVector θ x)‖} ≤ e := by
        have hsubset : {ω : Ω | R' < ‖Real.sqrt n •
            (survivorMassFromMassVector (θhat n ω) x -
              survivorMassFromMassVector θ x)‖} ⊆
            {ω : Ω | R < ‖Real.sqrt n •
              (survivorMassFromMassVector (θhat n ω) x -
                survivorMassFromMassVector θ x)‖} := by
          intro ω hω
          change R' < ‖Real.sqrt n •
            (survivorMassFromMassVector (θhat n ω) x -
              survivorMassFromMassVector θ x)‖ at hω
          exact lt_of_le_of_lt (le_max_left _ _) hω
        exact (measureReal_mono hsubset).trans (hR n)
      by_cases hsx : x ∈ support
      · have hr : 0 < Sys.p x * c.mass x := by
          simpa [support, positiveSupport] using hsx
        have heta : ∀ᶠ n in atTop, η n < (Sys.p x * c.mass x) / 2 :=
          (tendsto_order.1 _hEtaZero).2 _ (half_pos hr)
        have hsqr : ∀ᶠ (n : ℕ) in atTop,
            2 * R' / (Sys.p x * c.mass x) < Real.sqrt n :=
          by
            filter_upwards [(tendsto_atTop.1 hsqrt)
              (2 * R' / (Sys.p x * c.mass x) + 1)] with n hn
            linarith
        filter_upwards [heta, hsqr] with n hneta hnsqrt
        apply (measureReal_mono ?_).trans (hRle n)
        intro ω hω
        have hnScreen : ¬ screenedCell O η n ω x := by
          have hnmem : x ∉ screenedSupport O η n ω := by
            exact fun hmem => hω (by simpa [hsx] using hmem)
          simpa only [screenedSupport, Finset.mem_filter, Finset.mem_univ,
            true_and] using hnmem
        have hω' : ¬ η n < survivorMassFromMassVector (θhat n ω) x := by
          exact fun hs => hnScreen ((hScreenScore x n ω).mpr hs)
        change R' < ‖Real.sqrt n •
          (survivorMassFromMassVector (θhat n ω) x -
            survivorMassFromMassVector θ x)‖
        rw [hScorePop]
        simp only [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have hsle : survivorMassFromMassVector (θhat n ω) x ≤ η n :=
          le_of_not_gt hω'
        have hdnonpos : survivorMassFromMassVector (θhat n ω) x -
            Sys.p x * c.mass x ≤ 0 := by
          linarith
        rw [abs_of_nonpos hdnonpos]
        have hbound : 2 * R' < Real.sqrt n * (Sys.p x * c.mass x) :=
          (div_lt_iff₀ hr).mp hnsqrt
        have hsqrtPos : 0 < Real.sqrt n := by
          by_contra hz
          have hzero : Real.sqrt n = 0 :=
            le_antisymm (le_of_not_gt hz) (Real.sqrt_nonneg _)
          rw [hzero, zero_mul] at hbound
          nlinarith [le_max_right R 0]
        have hdiff : (Sys.p x * c.mass x) / 2 <
            Sys.p x * c.mass x - survivorMassFromMassVector (θhat n ω) x := by
          linarith
        have hmul := mul_lt_mul_of_pos_left hdiff hsqrtPos
        nlinarith
      · have hrzero : Sys.p x * c.mass x = 0 := by
          have hnpos : ¬ 0 < Sys.p x * c.mass x := by
            simpa [support, positiveSupport] using hsx
          exact le_antisymm (le_of_not_gt hnpos)
            (mul_nonneg (hIdentification.2.1 x) (hmassNonneg x))
        have hthreshold : ∀ᶠ (n : ℕ) in atTop, R' < Real.sqrt n * η n :=
          by
            filter_upwards [(tendsto_atTop.1 _hSqrtEta) (R' + 1)] with n hn
            linarith
        filter_upwards [hthreshold] with n hn
        apply (measureReal_mono ?_).trans (hRle n)
        intro ω hω
        have hscreen : screenedCell O η n ω x := by
          have hmem : x ∈ screenedSupport O η n ω := by
            by_contra hnmem
            exact hω (by simpa [hsx, hnmem])
          simpa only [screenedSupport, Finset.mem_filter, Finset.mem_univ,
            true_and] using hmem
        have hω' := (hScreenScore x n ω).mp hscreen
        change R' < ‖Real.sqrt n •
          (survivorMassFromMassVector (θhat n ω) x -
            survivorMassFromMassVector θ x)‖
        rw [hScorePop, hrzero]
        simp only [sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have hscorePos : 0 < survivorMassFromMassVector (θhat n ω) x :=
          lt_trans (_hEtaPositive n) hω'
        rw [abs_of_pos hscorePos]
        change R' < Real.sqrt n * survivorMassFromMassVector (θhat n ω) x
        have hsqrtPos : 0 < Real.sqrt n := by
          by_contra hz
          have : Real.sqrt n = 0 := le_antisymm (le_of_not_gt hz) (Real.sqrt_nonneg _)
          rw [this, zero_mul] at hn
          exact (not_lt_of_ge (le_max_right R 0)) hn
        nlinarith
  have hScreenMemMeas (x : 𝒳) (n : ℕ) :
      MeasurableSet {ω | x ∈ screenedSupport O η n ω} := by
    have hs := measurable_survivorMassFromMassVector (K := K) x
    have hscore : Measurable
        (fun ω => survivorMassFromMassVector (θhat n ω) x) :=
      hs.comp (hθhatMeas n)
    have hevent : {ω | x ∈ screenedSupport O η n ω} =
        {ω | η n < survivorMassFromMassVector (θhat n ω) x} := by
      ext ω
      simp only [Set.mem_setOf_eq, screenedSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hScreenScore x n ω
    rw [hevent]
    exact measurableSet_lt measurable_const hscore
  have hBadSet (n : ℕ) : {ω | screenedSupport O η n ω ≠ support} =
      ⋃ x : 𝒳, {ω | (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hne
      by_contra hall
      push_neg at hall
      exact hne (Finset.ext fun x => iff_of_eq (hall x))
    · rintro ⟨x, hx⟩ heq
      exact hx (by rw [heq])
  have hBadMeas (n : ℕ) :
      MeasurableSet {ω | screenedSupport O η n ω ≠ support} := by
    rw [hBadSet]
    apply MeasurableSet.iUnion
    intro x
    by_cases hsx : x ∈ support
    · have heq : {ω | (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)} =
          {ω | x ∈ screenedSupport O η n ω}ᶜ := by
        ext ω
        simp [hsx]
      rw [heq]
      exact (hScreenMemMeas x n).compl
    · have heq : {ω | (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)} =
          {ω | x ∈ screenedSupport O η n ω} := by
        ext ω
        simp [hsx]
      rw [heq]
      exact hScreenMemMeas x n
  have hBadTendsto : Tendsto
      (fun n => μ.real {ω | screenedSupport O η n ω ≠ support})
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    let δ : ℝ := e / (Fintype.card 𝒳 + 1)
    have hδ : 0 < δ := div_pos he (by positivity)
    have hall : ∀ᶠ n in atTop, ∀ x ∈ (Finset.univ : Finset 𝒳),
        μ.real {ω | (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)} ≤ δ := by
      rw [Finset.eventually_all]
      intro x hx
      exact hCellError x δ hδ
    rw [eventually_atTop] at hall
    obtain ⟨N, hN⟩ := hall
    refine ⟨N, fun n hnN => ?_⟩
    have hn := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    rw [hBadSet]
    calc
      μ.real (⋃ x : 𝒳,
          {ω | (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)}) ≤
          ∑ x : 𝒳, μ.real
            {ω | (x ∈ screenedSupport O η n ω) ≠ (x ∈ support)} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _x : 𝒳, δ := Finset.sum_le_sum fun x hx => hn x (by simp)
      _ < e := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [δ]
        have hc : (0 : ℝ) ≤ Fintype.card 𝒳 := by positivity
        field_simp
        nlinarith
  have hSupportRecovery : Tendsto
      (fun n => μ.real {ω | screenedSupport O η n ω = support})
      atTop (𝓝 1) := by
    have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).sub hBadTendsto
    convert hsub using 1
    · funext n
      have heq : {ω | screenedSupport O η n ω = support} =
          {ω | screenedSupport O η n ω ≠ support}ᶜ := by
        ext ω
        simp
      rw [heq, measureReal_compl (hBadMeas n)]
      simp
    · norm_num
  have hRestrict (b : 𝒳 → ℝ) (hb0 : ∀ x, 0 ≤ b x)
      (hbm : ∀ x, b x ≤ c.mass x) :
      (∑ x ∈ support, Sys.p x * b x) = ∑ x, Sys.p x * b x := by
    unfold support positiveSupport
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hpos : 0 < Sys.p x * c.mass x
    · simp [hpos]
    · have hpm0 : Sys.p x * c.mass x = 0 := le_antisymm
          (le_of_not_gt hpos) (mul_nonneg (hIdentification.2.1 x) (hmassNonneg x))
      have hpb0 : Sys.p x * b x = 0 := le_antisymm
        (le_trans (mul_le_mul_of_nonneg_left (hbm x) (hIdentification.2.1 x))
          hpm0.le) (mul_nonneg (hIdentification.2.1 x) (hb0 x))
      simp [hpos, hpb0]
  have hEndpointPop : endpointFromMassVectorOn support θ =
      (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
        hValid hp hMass (observedLawDomain Sys)).endpoints := by
    have hmRestrict := hRestrict (fun x => c.mass x) hmassNonneg (fun x => le_rfl)
    have hlRestrict := hRestrict (fun x => c.benefitLower x)
      (fun x => benefitLower_nonneg c x)
      (fun x => benefitLower_le_mass c hIdentification.1.2 x)
    have huRestrict := hRestrict (fun x => c.benefitUpper x)
      (fun x => benefitUpper_nonneg c hIdentification.1.2 x)
      (fun x => benefitUpper_le_mass c x)
    unfold endpointFromMassVectorOn Capacities.endpointMap Capacities.aggregateMass
    dsimp only
    rw [hcapRaw]
    have hcproj : Capacities.mk (fun x i => max (c.lower x i) 0)
        (fun x j => max (c.upper x j) 0) = c := by
      rw [Capacities.mk.injEq]
      constructor
      · funext x i
        exact max_eq_left (hIdentification.1.2.1 x i)
      · funext x i
        exact max_eq_left (hIdentification.1.2.2 x i)
    rw [hcproj]
    simp_rw [hcell]
    rw [hlRestrict, huRestrict, hmRestrict]
  have hSupportNonempty : support.Nonempty := by
    by_contra hne
    have hempty : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hsupportMass
    simp at hsupportMass
  have hPluginMeas (n : ℕ) : Measurable (plugInEndpoints O η n) := by
    have hsumMeas (E : ObservedDatum 𝒳 K → Bool) : Measurable
        (fun v : ObservedDatum 𝒳 K → ℝ => massVectorSum v E) := by
      unfold massVectorSum
      fun_prop
    have hEmpCell (x : 𝒳) : Measurable (fun ω => empiricalCellMass O n ω x) := by
      have h := (hsumMeas (fun o => decide (o.cell = x))).comp (hθhatMeas n)
      convert h using 1
      funext ω
      change empiricalCellMass O n ω x =
        massVectorSum (empiricalProbabilityVector O n ω)
          (fun o => decide (o.cell = x))
      unfold empiricalCellMass
      rw [massVectorSum_empiricalProbabilityVector]
    obtain ⟨hmProj, hlProj, huProj⟩ :=
      measurable_projected_components (𝒳 := 𝒳) (K := K)
    have hProjMass (x : 𝒳) : Measurable
        (fun ω => (projectedCapacities O n ω).mass x) := by
      convert (hmProj x).comp (hθhatMeas n) using 1
      funext ω
      change (projectedCapacities O n ω).mass x =
        (projectedMassCapacity (empiricalProbabilityVector O n ω)).mass x
      rw [projectedMassCapacity_empiricalProbabilityVector]
    have hProjLower (x : 𝒳) : Measurable
        (fun ω => (projectedCapacities O n ω).benefitLower x) := by
      convert (hlProj x).comp (hθhatMeas n) using 1
      funext ω
      change (projectedCapacities O n ω).benefitLower x =
        (projectedMassCapacity (empiricalProbabilityVector O n ω)).benefitLower x
      rw [projectedMassCapacity_empiricalProbabilityVector]
    have hProjUpper (x : 𝒳) : Measurable
        (fun ω => (projectedCapacities O n ω).benefitUpper x) := by
      convert (huProj x).comp (hθhatMeas n) using 1
      funext ω
      change (projectedCapacities O n ω).benefitUpper x =
        (projectedMassCapacity (empiricalProbabilityVector O n ω)).benefitUpper x
      rw [projectedMassCapacity_empiricalProbabilityVector]
    unfold plugInEndpoints
    dsimp only
    have hkeep (x : 𝒳) : Measurable
        (fun ω => if screenedCell O η n ω x then (1 : ℝ) else 0) := by
      have hsc : MeasurableSet {ω | screenedCell O η n ω x} := by
        convert hScreenMemMeas x n using 1
        ext ω
        simp [screenedSupport]
      exact Measurable.ite hsc measurable_const measurable_const
    have hM : Measurable (fun ω => ∑ x,
        (if screenedCell O η n ω x then (1 : ℝ) else 0) *
          empiricalCellMass O n ω x * (projectedCapacities O n ω).mass x) := by
      apply Finset.measurable_sum
      intro x hx
      exact ((hkeep x).mul (hEmpCell x)).mul (hProjMass x)
    have hNL : Measurable (fun ω => ∑ x,
        (if screenedCell O η n ω x then (1 : ℝ) else 0) *
          empiricalCellMass O n ω x * (projectedCapacities O n ω).benefitLower x) := by
      apply Finset.measurable_sum
      intro x hx
      exact ((hkeep x).mul (hEmpCell x)).mul (hProjLower x)
    have hNU : Measurable (fun ω => ∑ x,
        (if screenedCell O η n ω x then (1 : ℝ) else 0) *
          empiricalCellMass O n ω x * (projectedCapacities O n ω).benefitUpper x) := by
      apply Finset.measurable_sum
      intro x hx
      exact ((hkeep x).mul (hEmpCell x)).mul (hProjUpper x)
    apply Measurable.ite
    · exact measurableSet_lt measurable_const hM
    · exact (hNL.div hM).prodMk (hNU.div hM)
    · exact measurable_const
  have hFixedMeas (n : ℕ) : Measurable (fun ω => Real.sqrt n •
      (endpointFromMassVectorOn support (θhat n ω) -
        endpointFromMassVectorOn support θ)) := by
    have he : Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
        endpointFromMassVectorOn support v) := by
      have hsumMeas (E : ObservedDatum 𝒳 K → Bool) : Measurable
          (fun v : ObservedDatum 𝒳 K → ℝ => massVectorSum v E) := by
        unfold massVectorSum
        fun_prop
      obtain ⟨hmProj, hlProj, huProj⟩ :=
        measurable_projected_components (𝒳 := 𝒳) (K := K)
      have hM : Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
          ∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
            (projectedMassCapacity v).mass x) := by
        apply Finset.measurable_sum
        intro x hx
        exact (hsumMeas _).mul (hmProj x)
      have hNL : Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
          ∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
            (projectedMassCapacity v).benefitLower x) := by
        apply Finset.measurable_sum
        intro x hx
        exact (hsumMeas _).mul (hlProj x)
      have hNU : Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
          ∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
            (projectedMassCapacity v).benefitUpper x) := by
        apply Finset.measurable_sum
        intro x hx
        exact (hsumMeas _).mul (huProj x)
      unfold endpointFromMassVectorOn
      dsimp only
      exact (hNL.div hM).prodMk (hNU.div hM)
    change Measurable ((fun _ : Ω => Real.sqrt n) •
      ((fun v => endpointFromMassVectorOn support v) ∘ θhat n -
        fun _ => endpointFromMassVectorOn support θ))
    exact measurable_const.smul ((he.comp (hθhatMeas n)).sub measurable_const)
  have hActualMeas (n : ℕ) : Measurable (fun ω => Real.sqrt n •
      (plugInEndpoints O η n ω -
        (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
          hValid hp hMass (observedLawDomain Sys)).endpoints)) :=
    by
      change Measurable ((fun _ : Ω => Real.sqrt n) •
        (plugInEndpoints O η n - fun _ =>
          (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
            hValid hp hMass (observedLawDomain Sys)).endpoints))
      exact measurable_const.smul ((hPluginMeas n).sub measurable_const)
  have hScaledEq : Tendsto (fun n : ℕ => μ.real {ω |
      Real.sqrt n • (endpointFromMassVectorOn support (θhat n ω) -
        endpointFromMassVectorOn support θ) =
      Real.sqrt n • (plugInEndpoints O η n ω -
        (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
          hValid hp hMass (observedLawDomain Sys)).endpoints)}) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hSupportRecovery tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun n => measureReal_mono fun ω hs => by
        change screenedSupport O η n ω = support at hs
        change Real.sqrt n • (endpointFromMassVectorOn support (θhat n ω) -
            endpointFromMassVectorOn support θ) =
          Real.sqrt n • (plugInEndpoints O η n ω -
            (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
              hValid hp hMass (observedLawDomain Sys)).endpoints)
        have hp := plugInEndpoints_eq_endpointFromMassVectorOn_of_screenedSupport_eq
          O η n ω support (_hEtaPositive n) hSupportNonempty hs
        rw [show θhat n ω = empiricalProbabilityVector O n ω from rfl,
          hp, hEndpointPop]
    · exact Filter.Eventually.of_forall fun n => by
        simpa using measureReal_le_one (μ := μ)
  letI : IsProbabilityMeasure (Q.map Dψ) :=
    Measure.isProbabilityMeasure_map hDψcont.measurable.aemeasurable
  have hActualWeak : WeakConverges
      (fun n ω => Real.sqrt n •
        (plugInEndpoints O η n ω -
          (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
            hValid hp hMass (observedLawDomain Sys)).endpoints))
      (Q.map Dψ) μ := by
    apply hFixedWeak.congr_of_tendstoInMeasure_sub hFixedMeas hActualMeas
    exact tendstoInMeasure_sub_of_probability_eq_one hFixedMeas hActualMeas hScaledEq
  have hConsistency : EndpointConvergesInProbability
      (fun n => plugInEndpoints O η n)
        (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
          hValid hp hMass (observedLawDomain Sys)).endpoints μ := by
    intro ε hε
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨R, hR⟩ := hActualWeak.eventually_norm_le hActualMeas
      (δ / 2) (half_pos hδ)
    let R' := max R 0
    have hsqrEventually : ∀ᶠ n : ℕ in atTop, R' / ε + 1 ≤ Real.sqrt n :=
      (tendsto_atTop.1 hsqrt) (R' / ε + 1)
    rw [eventually_atTop] at hsqrEventually
    obtain ⟨N, hN⟩ := hsqrEventually
    refine ⟨N, fun n hnN => ?_⟩
    have hn := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    refine lt_of_le_of_lt ((measureReal_mono ?_).trans (hR n)) (half_lt_self hδ)
    intro ω hω
    have hnorm : ε < ‖plugInEndpoints O η n ω -
        (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
          hValid hp hMass (observedLawDomain Sys)).endpoints‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using hω
    have hdiv : R' / ε < Real.sqrt n :=
      lt_of_lt_of_le (lt_add_one (R' / ε)) hn
    have hmul : R' < Real.sqrt n * ε := (div_lt_iff₀ hε).mp hdiv
    have hsqrtPos : 0 < Real.sqrt n := lt_of_le_of_lt
      (div_nonneg (le_max_right R 0) hε.le) hdiv
    change R < ‖Real.sqrt n •
      (plugInEndpoints O η n ω -
        (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
          hValid hp hMass (observedLawDomain Sys)).endpoints)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      R ≤ R' := le_max_left _ _
      _ < Real.sqrt n * ε := hmul
      _ < Real.sqrt n * ‖plugInEndpoints O η n ω -
          (c.endpointMap Sys.p Sys.observedLaw rfl (p_eq_observedCellWeights Sys)
            hValid hp hMass (observedLawDomain Sys)).endpoints‖ :=
        mul_lt_mul_of_pos_left hnorm hsqrtPos
  refine ⟨hSupportRecovery, hConsistency, Q, Dψ, hQ, hQmean, hQcov, ?_, hActualWeak⟩
  simpa only [θ] using hDψ

end CausalSmith.PartialID.SlateBenefitPartialTransport
