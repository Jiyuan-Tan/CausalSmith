import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.FullLawPasting
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Full-law endpoint attainment

The cellwise threshold flows are completed into genuine potential-outcome laws
that preserve the observed distribution and attain both aggregate endpoints.
-/

open MeasureTheory Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ}

/-- The benefit probability is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def benefitProbability {P : POSystem} (S : POSlateSystem P 𝒳 K) : ℝ :=
  benefitProbabilityOf ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
  -- @realizes \theta(survivor-complier probability of strict benefit)

/-- The is endpoint witness condition is the stated property of the slate-benefit partial-transport model. -/
def IsEndpointWitness (Pobs : Measure (ObservedDatum 𝒳 K))
    (εZ : ℝ) (d : 𝒳 → Bool) (target : ℝ)
    (P' : POSystem) (S' : POSlateSystem P' 𝒳 K) : Prop :=
  let _ : StandardBorelSpace P'.Ω := S'.borel
  TieSafeSurvivorModel S' εZ d ∧ S'.observedLaw = Pobs ∧
    benefitProbability S' = target

/-- The full law selected only under zero is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def fullLawSelectedOnlyUnderZero {P₀ : POSystem}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) (i : Fin K) : ℝ :=
  conditionalReal W.system.μ
    {ω | W.slate.Y0 ω = i ∧ W.slate.S0 ω = true ∧ W.slate.S1 ω = false ∧
      ω ∈ W.slate.complierEvent} (W.slate.xEvent x)

/-- The full law selected only under one is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def fullLawSelectedOnlyUnderOne {P₀ : POSystem}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) (j : Fin K) : ℝ :=
  conditionalReal W.system.μ
    {ω | W.slate.Y1 ω = j ∧ W.slate.S0 ω = false ∧ W.slate.S1 ω = true ∧
      ω ∈ W.slate.complierEvent} (W.slate.xEvent x)

/-- The full law never selected mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def fullLawNeverSelectedMass {P₀ : POSystem}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) : ℝ :=
  conditionalReal W.system.μ
    {ω | W.slate.S0 ω = false ∧ W.slate.S1 ω = false ∧
      ω ∈ W.slate.complierEvent} (W.slate.xEvent x)

private lemma selectedComplierMass_le_complierMass
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (z : Bool) (x : 𝒳) :
    selectedComplierMass S z x ≤
      conditionalReal P.μ S.complierEvent (S.xEvent x) := by
  unfold selectedComplierMass conditionalReal
  split_ifs with hx
  · apply div_le_div_of_nonneg_right _ (le_of_lt hx)
    exact measureReal_mono (by
      intro ω hω
      exact ⟨hω.1.2, hω.2⟩)
  · exact le_refl 0

private lemma propensity_mem_unitInterval {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (x : 𝒳) :
    0 ≤ S.propensity x ∧ S.propensity x ≤ 1 := by
  unfold POSlateSystem.propensity conditionalReal
  split_ifs with hx
  · constructor
    · positivity
    · apply (div_le_one hx).2
      exact measureReal_mono Set.inter_subset_right
  · exact ⟨le_refl 0, zero_le_one⟩

private lemma sum_outcomeComplierMass
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (z : Bool) (x : 𝒳) :
    (∑ i : Fin K, P.μ.real
      ({ω | S.YofD z ω = i ∧ S.SofD z ω = true ∧ ω ∈ S.complierEvent} ∩
        S.xEvent x)) =
      P.μ.real ({ω | S.SofD z ω = true ∧ ω ∈ S.complierEvent} ∩
        S.xEvent x) := by
  let E : Fin K → Set P.Ω := fun i =>
    {ω | S.YofD z ω = i ∧ S.SofD z ω = true ∧ ω ∈ S.complierEvent} ∩
      S.xEvent x
  have hmeas : ∀ i, MeasurableSet (E i) := by
    intro i
    dsimp [E, POSlateSystem.complierEvent]
    exact (((S.yVar.measurable_cfUnder S.dVar z) (measurableSet_singleton i)).inter
      (((S.sVar.measurable_cfUnder S.dVar z) (measurableSet_singleton true)).inter
        (((S.dVar.measurable_cfUnder S.zVar false) (measurableSet_singleton false)).inter
          ((S.dVar.measurable_cfUnder S.zVar true) (measurableSet_singleton true))))).inter
      (S.xVar.measurable_factual (measurableSet_singleton x))
  have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro ω hωi hωj
    dsimp [E] at hωi hωj
    exact hij (hωi.1.1.symm.trans hωj.1.1)
  rw [← measureReal_iUnion_fintype hdisj hmeas]
  congr 1
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨_, hs, hc⟩, hx⟩
    exact ⟨⟨hs, hc⟩, hx⟩
  · rintro ⟨⟨hs, hc⟩, hx⟩
    exact ⟨S.YofD z ω, ⟨rfl, hs, hc⟩, hx⟩

private lemma sum_latentMass_eq_selectedComplierMass
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (z : Bool) (x : 𝒳) :
    (∑ i : Fin K, if z then upperLatentMass S x i else lowerLatentMass S x i) =
      selectedComplierMass S z x := by
  cases z with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold lowerLatentMass selectedComplierMass conditionalReal
      split_ifs with hx
      · rw [← Finset.sum_div, sum_outcomeComplierMass S false x]
      · simp
  | true =>
      simp only [↓reduceIte]
      unfold upperLatentMass selectedComplierMass conditionalReal
      split_ifs with hx
      · rw [← Finset.sum_div, sum_outcomeComplierMass S true x]
      · simp

private lemma sum_principal_component
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (d0 d1 : Bool) (x : 𝒳) :
    (∑ s0, ∑ s1, ∑ y0, ∑ y1, conditionalReal P.μ
      {ω | S.D0 ω = d0 ∧ S.D1 ω = d1 ∧ S.S0 ω = s0 ∧ S.S1 ω = s1 ∧
        S.Y0 ω = y0 ∧ S.Y1 ω = y1} (S.xEvent x)) =
      conditionalReal P.μ {ω | S.D0 ω = d0 ∧ S.D1 ω = d1} (S.xEvent x) := by
  let A := Bool × Bool × Fin K × Fin K
  let E : A → Set P.Ω := fun a =>
    {ω | S.D0 ω = d0 ∧ S.D1 ω = d1 ∧ S.S0 ω = a.1 ∧ S.S1 ω = a.2.1 ∧
      S.Y0 ω = a.2.2.1 ∧ S.Y1 ω = a.2.2.2} ∩ S.xEvent x
  have hmeas : ∀ a, MeasurableSet (E a) := by
    intro a
    dsimp [E, POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S0,
      POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1]
    have h := (((((S.dVar.measurable_cfUnder S.zVar false (measurableSet_singleton d0)).inter
      (S.dVar.measurable_cfUnder S.zVar true (measurableSet_singleton d1))).inter
      (S.sVar.measurable_cfUnder S.dVar false (measurableSet_singleton a.1))).inter
      (S.sVar.measurable_cfUnder S.dVar true (measurableSet_singleton a.2.1))).inter
      (S.yVar.measurable_cfUnder S.dVar false (measurableSet_singleton a.2.2.1))).inter
      (S.yVar.measurable_cfUnder S.dVar true (measurableSet_singleton a.2.2.2)) |>.inter
      (S.xVar.measurable_factual (measurableSet_singleton x))
    convert h using 1 <;> ext ω <;>
      simp [POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S0,
        POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1,
        POSlateSystem.DofZ, POSlateSystem.SofD, POSlateSystem.YofD,
        POSlateSystem.xEvent, POSlateSystem.factualX, and_assoc]
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    apply hab
    rcases a with ⟨s0, s1, y0, y1⟩
    rcases b with ⟨s0', s1', y0', y1'⟩
    simp only [E, Set.mem_inter_iff, Set.mem_setOf_eq] at ha hb
    congr
    · exact ha.1.2.2.1.symm.trans hb.1.2.2.1
    · exact ha.1.2.2.2.1.symm.trans hb.1.2.2.2.1
    · exact ha.1.2.2.2.2.1.symm.trans hb.1.2.2.2.2.1
    · exact ha.1.2.2.2.2.2.symm.trans hb.1.2.2.2.2.2
  unfold conditionalReal
  split_ifs with hx
  · simp_rw [← Finset.sum_div]
    congr 1
    rw [show (∑ s0, ∑ s1, ∑ y0, ∑ y1,
        P.μ.real
          ({ω | S.D0 ω = d0 ∧ S.D1 ω = d1 ∧ S.S0 ω = s0 ∧ S.S1 ω = s1 ∧
            S.Y0 ω = y0 ∧ S.Y1 ω = y1} ∩ S.xEvent x)) =
        ∑ a : A, P.μ.real (E a) by simp [A, E, Fintype.sum_prod_type]]
    rw [← measureReal_iUnion_fintype hdisj hmeas]
    congr 1
    ext ω
    simp only [Set.mem_iUnion, E, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨s0, s1, y0, y1⟩, ⟨hd0, hd1, -, -, -, -⟩, hx⟩
      exact ⟨⟨hd0, hd1⟩, hx⟩
    · rintro ⟨⟨hd0, hd1⟩, hx⟩
      exact ⟨⟨S.S0 ω, S.S1 ω, S.Y0 ω, S.Y1 ω⟩,
        ⟨hd0, hd1, rfl, rfl, rfl, rfl⟩, hx⟩
  · simp

private lemma sum_treatment_strata
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (x : 𝒳) :
    (∑ d0 : Bool, ∑ d1 : Bool,
      P.μ.real ({ω | S.D0 ω = d0 ∧ S.D1 ω = d1} ∩ S.xEvent x)) =
      P.μ.real (S.xEvent x) := by
  let E : Bool × Bool → Set P.Ω := fun a =>
    {ω | S.D0 ω = a.1 ∧ S.D1 ω = a.2} ∩ S.xEvent x
  have hmeas : ∀ a, MeasurableSet (E a) := by
    intro a
    dsimp [E, POSlateSystem.D0, POSlateSystem.D1]
    have h := (S.dVar.measurable_cfUnder S.zVar false
      (measurableSet_singleton a.1)).inter
      (S.dVar.measurable_cfUnder S.zVar true
        (measurableSet_singleton a.2)) |>.inter
      (S.xVar.measurable_factual (measurableSet_singleton x))
    convert h using 1 <;> ext ω <;>
      simp [POSlateSystem.DofZ, POSlateSystem.xEvent, POSlateSystem.factualX]
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    apply hab
    rcases a with ⟨d0, d1⟩
    rcases b with ⟨d0', d1'⟩
    simp only [E, Set.mem_inter_iff, Set.mem_setOf_eq] at ha hb
    exact Prod.ext (ha.1.1.symm.trans hb.1.1) (ha.1.2.symm.trans hb.1.2)
  rw [show (∑ d0 : Bool, ∑ d1 : Bool,
      P.μ.real ({ω | S.D0 ω = d0 ∧ S.D1 ω = d1} ∩ S.xEvent x)) =
      ∑ a : Bool × Bool, P.μ.real (E a) by
        simp [E, Fintype.sum_prod_type]]
  rw [← measureReal_iUnion_fintype hdisj hmeas]
  congr 1
  ext ω
  simp only [Set.mem_iUnion, E, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨d0, d1⟩, ⟨-, -⟩, hx⟩
    exact hx
  · intro hx
    exact ⟨⟨S.D0 ω, S.D1 ω⟩, ⟨rfl, rfl⟩, hx⟩

private lemma baseline_principal_partition
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (x : 𝒳)
    (hNoDefiers : NoDefiers S) (hx : 0 < S.p x) :
    (∑ s0, ∑ s1, ∑ y0, ∑ y1,
        baselineNeverTakerComponent
          ({ system := P, slate := S } : FullLawCandidate P 𝒳 K) x s0 s1 y0 y1) +
      conditionalReal P.μ S.complierEvent (S.xEvent x) +
      (∑ s0, ∑ s1, ∑ y0, ∑ y1,
        baselineAlwaysTakerComponent
          ({ system := P, slate := S } : FullLawCandidate P 𝒳 K) x s0 s1 y0 y1) = 1 := by
  rw [show (∑ s0, ∑ s1, ∑ y0, ∑ y1,
      baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K) x s0 s1 y0 y1) =
      conditionalReal P.μ {ω | S.D0 ω = false ∧ S.D1 ω = false}
        (S.xEvent x) by
      simpa [baselineNeverTakerComponent] using
        sum_principal_component S false false x]
  rw [show (∑ s0, ∑ s1, ∑ y0, ∑ y1,
      baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K) x s0 s1 y0 y1) =
      conditionalReal P.μ {ω | S.D0 ω = true ∧ S.D1 ω = true}
        (S.xEvent x) by
      simpa [baselineAlwaysTakerComponent] using
        sum_principal_component S true true x]
  have hdefier : P.μ.real
      ({ω | S.D0 ω = true ∧ S.D1 ω = false} ∩ S.xEvent x) = 0 := by
    have hz : P.μ ({ω | S.D0 ω = true ∧ S.D1 ω = false} ∩ S.xEvent x) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hNoDefiers] with ω hω
      intro hmem
      have hcontra : true = false := (hω hmem.1.1).symm.trans hmem.1.2
      cases hcontra
    simp [Measure.real, hz]
  have hpart := sum_treatment_strata S x
  simp only [Fintype.sum_bool] at hpart
  simp only [POSlateSystem.D0, POSlateSystem.D1] at hpart hdefier
  simp only [POSlateSystem.D0, POSlateSystem.D1]
  unfold POSlateSystem.complierEvent conditionalReal POSlateSystem.p at *
  rw [if_pos hx, if_pos hx, if_pos hx]
  field_simp
  linarith

private lemma observableCapacity_eq_zero_of_p_eq_zero
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (x : 𝒳)
    (hx : S.p x = 0) :
    (∀ i, (observableCapacities S.observedLaw).lower x i = 0) ∧
      ∀ j, (observableCapacities S.observedLaw).upper x j = 0 := by
  have hxreal : P.μ.real (S.xEvent x) = 0 := by
    simpa [POSlateSystem.p] using hx
  have hmeas : Measurable S.observedDatum := by
    intro t _
    rw [show S.observedDatum ⁻¹' t = ⋃ o : t, S.observedDatum ⁻¹' {o.1} by ext; simp]
    apply MeasurableSet.iUnion
    rintro ⟨⟨x', z, d, s, y⟩, _⟩
    have hout : MeasurableSet { ω |
        (if S.factualS ω then some (S.factualY ω) else none) = y } := by
      cases y with
      | none =>
          convert S.sVar.measurable_factual (measurableSet_singleton false) using 1 <;>
            ext ω <;> cases h : S.sVar.factual ω <;>
              simp [POSlateSystem.factualS, h]
      | some k =>
          convert (S.sVar.measurable_factual (measurableSet_singleton true)).inter
            (S.yVar.measurable_factual (measurableSet_singleton k)) using 1 <;>
            ext ω <;> cases h : S.sVar.factual ω <;>
              simp [POSlateSystem.factualS, POSlateSystem.factualY, h]
    have hm : MeasurableSet { ω | S.factualX ω = x' ∧ S.factualZ ω = z ∧
        S.factualD ω = d ∧ S.factualS ω = s ∧
        (if S.factualS ω then some (S.factualY ω) else none) = y } := by
      have h := ((((S.xVar.measurable_factual (measurableSet_singleton x')).inter
        (S.zVar.measurable_factual (measurableSet_singleton z))).inter
        (S.dVar.measurable_factual (measurableSet_singleton d))).inter
        (S.sVar.measurable_factual (measurableSet_singleton s))).inter hout
      convert h using 1 <;> ext ω <;>
        simp [POSlateSystem.factualX, POSlateSystem.factualZ,
          POSlateSystem.factualD, POSlateSystem.factualS, and_assoc]
    convert hm using 1 <;> ext ω <;>
      simp [POSlateSystem.observedDatum, ObservedDatum.mk.injEq, and_assoc]
  have harm (z : Bool) :
      P.μ.real (S.observedDatum ⁻¹' {o | o.cell = x ∧ o.instrument = z}) = 0 := by
    apply le_antisymm
    · exact (measureReal_mono (by
        intro ω hω
        exact hω.1)).trans_eq hxreal
    · exact measureReal_nonneg
  have harm' (z : Bool) :
      P.μ.real {ω | (S.observedDatum ω).cell = x ∧
        (S.observedDatum ω).instrument = z} = 0 := harm z
  constructor
  · intro i
    unfold observableCapacities observableCapacityContrasts POSlateSystem.observedLaw
    change conditionalReal (P.μ.map S.observedDatum)
        {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some i}
          {o | o.cell = x ∧ o.instrument = false} -
      conditionalReal (P.μ.map S.observedDatum)
        {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some i}
          {o | o.cell = x ∧ o.instrument = true} = 0
    rw [conditionalReal_map P.μ S.observedDatum hmeas _ _ MeasurableSet.of_discrete
        MeasurableSet.of_discrete,
      conditionalReal_map P.μ S.observedDatum hmeas _ _ MeasurableSet.of_discrete
        MeasurableSet.of_discrete]
    simp [conditionalReal, harm']
  · intro j
    unfold observableCapacities observableCapacityContrasts POSlateSystem.observedLaw
    change conditionalReal (P.μ.map S.observedDatum)
        {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some j}
          {o | o.cell = x ∧ o.instrument = true} -
      conditionalReal (P.μ.map S.observedDatum)
        {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some j}
          {o | o.cell = x ∧ o.instrument = false} = 0
    rw [conditionalReal_map P.μ S.observedDatum hmeas _ _ MeasurableSet.of_discrete
        MeasurableSet.of_discrete,
      conditionalReal_map P.μ S.observedDatum hmeas _ _ MeasurableSet.of_discrete
        MeasurableSet.of_discrete]
    simp [conditionalReal, harm']

private noncomputable def originalCompatibleBaseline
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (model : TieSafeSurvivorModel S εZ d) :
    CompatibleBaseline P S.observedLaw (observableCapacities S.observedLaw) where
  law := ⟨P, S⟩
  feasible := ⟨εZ, d, model, rfl⟩
  capacities_eq := rfl
  complierMass := fun x => conditionalReal P.μ S.complierEvent (S.xEvent x)
  complierMass_eq := fun _ => rfl
  qMax_le_complierMass := by
    let c := observableCapacities S.observedLaw
    have hIdentification := capacity_identification S εZ d model.ivIndependence
      model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
      model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
    intro x
    by_cases hx : 0 < S.p x
    · have hq0 : c.q0 x = selectedComplierMass S false x := by
        rw [Capacities.q0, Finset.sum_congr rfl
          (fun i _ => hIdentification.2.2.1 x hx i)]
        simpa using sum_latentMass_eq_selectedComplierMass S false x
      have hq1 : c.q1 x = selectedComplierMass S true x := by
        rw [Capacities.q1, Finset.sum_congr rfl
          (fun j _ => hIdentification.2.2.2.1 x hx j)]
        simpa using sum_latentMass_eq_selectedComplierMass S true x
      rw [hq0, hq1]
      exact max_le (selectedComplierMass_le_complierMass S false x)
        (selectedComplierMass_le_complierMass S true x)
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      rcases observableCapacity_eq_zero_of_p_eq_zero S x hx0 with ⟨hlower, hupper⟩
      have hq0 : c.q0 x = 0 := by simp [c, Capacities.q0, hlower]
      have hq1 : c.q1 x = 0 := by simp [c, Capacities.q1, hupper]
      rw [hq0, hq1, max_self]
      unfold conditionalReal
      split_ifs <;> positivity
  neverTakerComponent := fun x => baselineNeverTakerComponent ⟨P, S⟩ x
  neverTaker_eq := fun _ => rfl
  alwaysTakerComponent := fun x => baselineAlwaysTakerComponent ⟨P, S⟩ x
  alwaysTaker_eq := fun _ => rfl

/-- A full law realizes every component of a threshold latent completion, not
only its survivor coupling. -/
def RealizesThresholdLatentCompletion {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳)
    (completion : ThresholdLatentCompletion P₀ Pobs c) : Prop :=
  fullLawSurvivorCoupling W x = completion.survivor ∧
  (∀ i, fullLawSelectedOnlyUnderZero W x i = completion.selectedOnlyUnderZero i) ∧
  (∀ j, fullLawSelectedOnlyUnderOne W x j = completion.selectedOnlyUnderOne j) ∧
  fullLawNeverSelectedMass W x = completion.neverSelectedMass ∧
  baselineNeverTakerComponent W x = completion.neverTakerComponent ∧
  baselineAlwaysTakerComponent W x = completion.alwaysTakerComponent

/-- Assemble the six components of each threshold completion into a complete
latent table. Unobserved outcomes in one-sided and never-selected strata are
pinned to an arbitrary reference level. -/
def thresholdCompletionCellTable {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (reference : Fin K) (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c) :
    ThresholdCellTable 𝒳 K :=
  fun x d0 d1 s0 s1 y0 y1 =>
    if d0 then
      if d1 then completion x |>.alwaysTakerComponent s0 s1 y0 y1 else 0
    else if d1 then
      if s0 then
        if s1 then completion x |>.survivor y0 y1
        else if y1 = reference then completion x |>.selectedOnlyUnderZero y0 else 0
      else if s1 then
        if y0 = reference then completion x |>.selectedOnlyUnderOne y1 else 0
      else if y0 = reference ∧ y1 = reference then completion x |>.neverSelectedMass else 0
    else completion x |>.neverTakerComponent s0 s1 y0 y1

/-- Given [the stated hypotheses](hyp:completion,hsurvivor,hzero,hone,hnever,hNT,hAT), [threshold completion cell table is nonnegative](goal). -/
theorem thresholdCompletionCellTable_nonnegative {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (reference : Fin K) (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c)
    (hsurvivor : ∀ x i j, 0 ≤ (completion x).survivor i j)
    (hzero : ∀ x i, 0 ≤ (completion x).selectedOnlyUnderZero i)
    (hone : ∀ x j, 0 ≤ (completion x).selectedOnlyUnderOne j)
    (hnever : ∀ x, 0 ≤ (completion x).neverSelectedMass)
    (hNT : ∀ x s0 s1 y0 y1, 0 ≤ (completion x).neverTakerComponent s0 s1 y0 y1)
    (hAT : ∀ x s0 s1 y0 y1, 0 ≤ (completion x).alwaysTakerComponent s0 s1 y0 y1) :
    (thresholdCompletionCellTable reference completion).Nonnegative := by
  intro x d0 d1 s0 s1 y0 y1
  unfold thresholdCompletionCellTable
  repeat
    first
    | split
    | exact hsurvivor _ _ _
    | exact hzero _ _
    | exact hone _ _
    | exact hnever _
    | exact hNT _ _ _ _ _
    | exact hAT _ _ _ _ _
    | positivity

/-- Given [the stated hypotheses](hyp:completion), [the threshold completion cell table total property holds](goal). -/
theorem thresholdCompletionCellTable_total {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (reference : Fin K) (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c)
    (x : 𝒳) :
    (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
        thresholdCompletionCellTable reference completion x d0 d1 s0 s1 y0 y1) =
      (∑ s0, ∑ s1, ∑ y0, ∑ y1,
        (completion x).neverTakerComponent s0 s1 y0 y1) +
      (∑ i, ∑ j, (completion x).survivor i j) +
      (∑ i, (completion x).selectedOnlyUnderZero i) +
      (∑ j, (completion x).selectedOnlyUnderOne j) +
      (completion x).neverSelectedMass +
      (∑ s0, ∑ s1, ∑ y0, ∑ y1,
        (completion x).alwaysTakerComponent s0 s1 y0 y1) := by
  have hsingle : (∑ y0 : Fin K, ∑ y1 : Fin K,
      if y0 = reference ∧ y1 = reference then
        (completion x).neverSelectedMass else 0) =
      (completion x).neverSelectedMass := by
    calc
      _ = ∑ y0 : Fin K, if y0 = reference then
          (completion x).neverSelectedMass else 0 := by
        apply Fintype.sum_congr
        intro y0
        by_cases hy0 : y0 = reference <;> simp [hy0]
      _ = (completion x).neverSelectedMass := by simp
  simp [thresholdCompletionCellTable, Fintype.sum_bool, hsingle]
  ring

private theorem thresholdLatentCompletion_complier_total {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (x : 𝒳) (gamma : Coupling K)
    (hgamma : gamma ∈ branchFreePolytope c hValid x) :
    (∑ i, ∑ j, (thresholdLatentCompletion baseline hValid x gamma).survivor i j) +
      (∑ i, (thresholdLatentCompletion baseline hValid x gamma).selectedOnlyUnderZero i) +
      (∑ j, (thresholdLatentCompletion baseline hValid x gamma).selectedOnlyUnderOne j) +
      (thresholdLatentCompletion baseline hValid x gamma).neverSelectedMass =
      baseline.complierMass x := by
  have htotal : (∑ i, ∑ j, gamma i j) = c.mass x := hgamma.2.2.2
  have hrows : (∑ i, rowMass gamma i) = c.mass x := by
    rw [sum_rowMass_eq_totalMass, hgamma.2.2.2]
  have hcolumns : (∑ j, columnMass gamma j) = c.mass x := by
    rw [sum_columnMass_eq_totalMass, hgamma.2.2.2]
  have hlower : (∑ i, c.lower x i) = c.q0 x := rfl
  have hupper : (∑ j, c.upper x j) = c.q1 x := rfl
  by_cases hneg : c.gap x < 0
  · have hq : c.q1 x < c.q0 x := by simpa [Capacities.gap] using hneg
    have hnpos : ¬ 0 < c.gap x := not_lt_of_ge (le_of_lt hneg)
    simp only [thresholdLatentCompletion, hneg, if_pos, hnpos, if_false]
    rw [Finset.sum_sub_distrib, hlower, hrows, htotal,
      Capacities.mass, min_eq_right hq.le, max_eq_left hq.le]
    simp
  · by_cases hpos : 0 < c.gap x
    · have hq : c.q0 x < c.q1 x := by simpa [Capacities.gap] using hpos
      simp only [thresholdLatentCompletion, hneg, if_false, hpos, if_pos]
      rw [Finset.sum_sub_distrib, hupper, hcolumns, htotal,
        Capacities.mass, min_eq_left hq.le, max_eq_right hq.le]
      simp
    · have hgap : c.gap x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      have hq : c.q0 x = c.q1 x := by
        unfold Capacities.gap at hgap
        linarith
      simp only [thresholdLatentCompletion, hneg, if_false, hpos]
      rw [htotal, Capacities.mass, hq, min_self, max_self]
      simp

private lemma branchFree_row_eq_of_gap_nonnegative
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳)
    (gamma : Coupling K) (hgamma : gamma ∈ branchFreePolytope c hValid x)
    (hgap : 0 ≤ c.gap x) : ∀ i, rowMass gamma i = c.lower x i := by
  change matrixNonnegative gamma ∧ (∀ i, rowMass gamma i ≤ c.lower x i) ∧
    (∀ j, columnMass gamma j ≤ c.upper x j) ∧
    totalMass gamma = c.mass x at hgamma
  have hq : c.q0 x ≤ c.q1 x := by simpa [Capacities.gap] using hgap
  have hmass : c.mass x = c.q0 x := by simp [Capacities.mass, min_eq_left hq]
  have hsumrow : (∑ i, rowMass gamma i) = totalMass gamma := by
    simp [rowMass, totalMass]
  have hzero : (∑ i, (c.lower x i - rowMass gamma i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Capacities.q0, hsumrow, hgamma.2.2.2, hmass]
    ring
  have hall := (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ sub_nonneg.mpr (hgamma.2.1 i))).mp hzero
  intro i
  have hi := congrFun hall i
  simp only [Pi.zero_apply] at hi
  linarith

private lemma branchFree_column_eq_of_gap_nonpositive
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳)
    (gamma : Coupling K) (hgamma : gamma ∈ branchFreePolytope c hValid x)
    (hgap : c.gap x ≤ 0) : ∀ j, columnMass gamma j = c.upper x j := by
  change matrixNonnegative gamma ∧ (∀ i, rowMass gamma i ≤ c.lower x i) ∧
    (∀ j, columnMass gamma j ≤ c.upper x j) ∧
    totalMass gamma = c.mass x at hgamma
  have hq : c.q1 x ≤ c.q0 x := by simpa [Capacities.gap] using hgap
  have hmass : c.mass x = c.q1 x := by simp [Capacities.mass, min_eq_right hq]
  have hsumcolumn : (∑ j, columnMass gamma j) = totalMass gamma := by
    simp [columnMass, totalMass, Finset.sum_comm]
  have hzero : (∑ j, (c.upper x j - columnMass gamma j)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Capacities.q1, hsumcolumn, hgamma.2.2.2, hmass]
    ring
  have hall := (Fintype.sum_eq_zero_iff_of_nonneg
    (fun j ↦ sub_nonneg.mpr (hgamma.2.2.1 j))).mp hzero
  intro j
  have hj := congrFun hall j
  simp only [Pi.zero_apply] at hj
  linarith

private lemma thresholdLatentCompletion_selected_margins
    {P₀ : POSystem} {Pobs : Measure (ObservedDatum 𝒳 K)}
    {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (x : 𝒳) (gamma : Coupling K)
    (hgamma : gamma ∈ branchFreePolytope c hValid x) :
    (∀ i, rowMass gamma i +
        (thresholdLatentCompletion baseline hValid x gamma).selectedOnlyUnderZero i =
          c.lower x i) ∧
      (∀ j, columnMass gamma j +
        (thresholdLatentCompletion baseline hValid x gamma).selectedOnlyUnderOne j =
          c.upper x j) := by
  constructor
  · intro i
    by_cases hgap : c.gap x < 0
    · simp [thresholdLatentCompletion, hgap]
    · have hrow := branchFree_row_eq_of_gap_nonnegative c hValid x gamma hgamma
        (le_of_not_gt hgap) i
      simp [thresholdLatentCompletion, hgap, hrow]
  · intro j
    by_cases hgap : 0 < c.gap x
    · simp [thresholdLatentCompletion, hgap]
    · have hcolumn := branchFree_column_eq_of_gap_nonpositive c hValid x gamma hgamma
        (le_of_not_gt hgap) j
      simp [thresholdLatentCompletion, hgap, hcolumn]

/-- Replace an irrelevant zero-probability cell by a point mass, so the
conditional table is normalized in every cell. -/
noncomputable def normalizedCompletionCellTable {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c) :
    ThresholdCellTable 𝒳 K :=
  fun x d0 d1 s0 s1 y0 y1 =>
    if 0 < S.p x then
      thresholdCompletionCellTable reference completion x d0 d1 s0 s1 y0 y1
    else if d0 = false ∧ d1 = false ∧ s0 = false ∧ s1 = false ∧
        y0 = reference ∧ y1 = reference then 1 else 0

/-- Given [the stated hypotheses](hyp:completion,hraw), [normalized completion cell table is nonnegative](goal). -/
theorem normalizedCompletionCellTable_nonnegative {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c)
    (hraw : (thresholdCompletionCellTable reference completion).Nonnegative) :
    (normalizedCompletionCellTable S reference completion).Nonnegative := by
  intro x d0 d1 s0 s1 y0 y1
  by_cases hx : 0 < S.p x
  · simpa [normalizedCompletionCellTable, hx] using hraw x d0 d1 s0 s1 y0 y1
  · by_cases htuple : d0 = false ∧ d1 = false ∧ s0 = false ∧ s1 = false ∧
        y0 = reference ∧ y1 = reference <;>
      simp [normalizedCompletionCellTable, hx, htuple]

/-- Given [the stated hypotheses](hyp:completion,hraw), [the normalized completion cell table normalized property holds](goal). -/
theorem normalizedCompletionCellTable_normalized {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c)
    (hraw : ∀ x, 0 < S.p x →
      (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
        thresholdCompletionCellTable reference completion x d0 d1 s0 s1 y0 y1) = 1) :
    (normalizedCompletionCellTable S reference completion).Normalized := by
  intro x
  by_cases hx : 0 < S.p x
  · simp only [normalizedCompletionCellTable, hx, if_pos]
    exact hraw x hx
  · have hfin : (∑ y0 : Fin K, ∑ y1 : Fin K,
        if y0 = reference ∧ y1 = reference then (1 : ℝ) else 0) = 1 := by
      calc
        _ = ∑ y0 : Fin K, if y0 = reference then (1 : ℝ) else 0 := by
          apply Fintype.sum_congr
          intro y0
          by_cases hy0 : y0 = reference <;> simp [hy0]
        _ = 1 := by simp
    simpa [normalizedCompletionCellTable, hx, Fintype.sum_bool] using hfin

/-- Given [the stated hypotheses](hyp:completion), [the normalized completion cell table no defiers property holds](goal). -/
theorem normalizedCompletionCellTable_noDefiers {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : ∀ x : 𝒳, ThresholdLatentCompletion P₀ Pobs c) :
    ∀ x s0 s1 y0 y1,
      normalizedCompletionCellTable S reference completion
        x true false s0 s1 y0 y1 = 0 := by
  intro x s0 s1 y0 y1
  by_cases hx : 0 < S.p x <;>
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable]

private theorem normalizedCompletion_selected_observedMargins
    {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (x : 𝒳) (hx : 0 < S.p x)
    (hmargins :
      (∀ i, rowMass (completion x).survivor i +
          (completion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass (completion x).survivor j +
          (completion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j)) :
    (∀ i, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x false false true (some i) =
      (∑ s1, ∑ y1, (completion x).neverTakerComponent true s1 i y1) +
        (observableCapacities S.observedLaw).lower x i) ∧
    (∀ j, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x false true true (some j) =
      ∑ s0, ∑ y0, (completion x).alwaysTakerComponent s0 true y0 j) ∧
    (∀ i, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x true false true (some i) =
      ∑ s1, ∑ y1, (completion x).neverTakerComponent true s1 i y1) ∧
    (∀ j, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x true true true (some j) =
      (∑ s0, ∑ y0, (completion x).alwaysTakerComponent s0 true y0 j) +
        (observableCapacities S.observedLaw).upper x j) := by
  constructor
  · intro i
    rw [thresholdObservedTableMargin_false_false_selected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool, rowMass]
    rw [← hmargins.1 i]
    unfold rowMass
    ring
  constructor
  · intro j
    rw [thresholdObservedTableMargin_false_true_selected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool]
  constructor
  · intro i
    rw [thresholdObservedTableMargin_true_false_selected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool]
  · intro j
    rw [thresholdObservedTableMargin_true_true_selected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool, columnMass]
    rw [← hmargins.2 j]
    unfold columnMass
    ring

private theorem normalizedCompletion_unselected_observedMargins
    {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (x : 𝒳) (hx : 0 < S.p x) :
    thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x false false false none =
      (∑ s1, ∑ y0, ∑ y1,
        (completion x).neverTakerComponent false s1 y0 y1) +
      (∑ j, (completion x).selectedOnlyUnderOne j) +
      (completion x).neverSelectedMass ∧
    thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x false true false none =
      ∑ s0, ∑ y0, ∑ y1,
        (completion x).alwaysTakerComponent s0 false y0 y1 ∧
    thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x true false false none =
      ∑ s1, ∑ y0, ∑ y1,
        (completion x).neverTakerComponent false s1 y0 y1 ∧
    thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x true true false none =
      (∑ s0, ∑ y0, ∑ y1,
        (completion x).alwaysTakerComponent s0 false y0 y1) +
      (∑ i, (completion x).selectedOnlyUnderZero i) +
      (completion x).neverSelectedMass := by
  have hsingle : (∑ y0 : Fin K, ∑ y1 : Fin K,
      if y0 = reference ∧ y1 = reference then
        (completion x).neverSelectedMass else 0) =
      (completion x).neverSelectedMass := by
    calc
      _ = ∑ y0 : Fin K, if y0 = reference then
          (completion x).neverSelectedMass else 0 := by
        apply Fintype.sum_congr
        intro y0
        by_cases hy0 : y0 = reference <;> simp [hy0]
      _ = (completion x).neverSelectedMass := by simp
  constructor
  · rw [thresholdObservedTableMargin_false_false_unselected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool]
    rw [hsingle]
    ring
  constructor
  · rw [thresholdObservedTableMargin_false_true_unselected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool]
  constructor
  · rw [thresholdObservedTableMargin_true_false_unselected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool]
  · rw [thresholdObservedTableMargin_true_true_unselected]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
      Fintype.sum_bool]
    rw [hsingle]
    ring

/-- Given [the stated hypotheses](hyp:hValid,hpartition), [the threshold flow completion cell tables total property holds](goal). -/
theorem thresholdFlow_completionCellTables_total {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (reference : Fin K) (x : 𝒳)
    (hpartition :
      (∑ s0, ∑ s1, ∑ y0, ∑ y1,
          baseline.neverTakerComponent x s0 s1 y0 y1) +
        baseline.complierMass x +
        (∑ s0, ∑ s1, ∑ y0, ∑ y1,
          baseline.alwaysTakerComponent x s0 s1 y0 y1) = 1) :
    let flows := thresholdFlow baseline hValid x
    (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
      thresholdCompletionCellTable reference (fun _ => flows.lower)
        x d0 d1 s0 s1 y0 y1) = 1 ∧
    (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
      thresholdCompletionCellTable reference (fun _ => flows.upper)
        x d0 d1 s0 s1 y0 y1) = 1 := by
  dsimp only
  constructor
  · rw [thresholdCompletionCellTable_total]
    have hc := thresholdLatentCompletion_complier_total baseline hValid x
      (thresholdFlowLower c hValid x) (thresholdFlow_spec baseline hValid x).1
    simp only [thresholdFlow, thresholdLatentCompletion] at hc ⊢
    linarith

  · rw [thresholdCompletionCellTable_total]
    have hc := thresholdLatentCompletion_complier_total baseline hValid x
      (thresholdFlowUpper c hValid x) (thresholdFlow_spec baseline hValid x).2.2.1
    simp only [thresholdFlow, thresholdLatentCompletion] at hc ⊢
    linarith

/-- Given [the stated hypotheses](hyp:hValid), [threshold flow completion cell tables is nonnegative](goal). -/
theorem thresholdFlow_completionCellTables_nonnegative {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (reference : Fin K) :
    let flows := fun x => thresholdFlow baseline hValid x
    (thresholdCompletionCellTable reference (fun x => (flows x).lower)).Nonnegative ∧
      (thresholdCompletionCellTable reference (fun x => (flows x).upper)).Nonnegative := by
  dsimp only
  constructor
  · apply thresholdCompletionCellTable_nonnegative
    · intro x i j
      exact (thresholdFlow_spec baseline hValid x).1.1 i j
    · intro x i
      change 0 ≤ if c.gap x < 0 then
        c.lower x i - rowMass (thresholdFlowLower c hValid x) i else 0
      split_ifs
      · exact sub_nonneg.mpr ((thresholdFlow_spec baseline hValid x).1.2.1 i)
      · positivity
    · intro x j
      change 0 ≤ if 0 < c.gap x then
        c.upper x j - columnMass (thresholdFlowLower c hValid x) j else 0
      split_ifs
      · exact sub_nonneg.mpr ((thresholdFlow_spec baseline hValid x).1.2.2.1 j)
      · positivity
    · intro x
      exact sub_nonneg.mpr (baseline.qMax_le_complierMass x)
    · intro x s0 s1 y0 y1
      change 0 ≤ baseline.neverTakerComponent x s0 s1 y0 y1
      rw [baseline.neverTaker_eq]
      unfold baselineNeverTakerComponent conditionalReal
      split_ifs <;> positivity
    · intro x s0 s1 y0 y1
      change 0 ≤ baseline.alwaysTakerComponent x s0 s1 y0 y1
      rw [baseline.alwaysTaker_eq]
      unfold baselineAlwaysTakerComponent conditionalReal
      split_ifs <;> positivity
  · apply thresholdCompletionCellTable_nonnegative
    · intro x i j
      exact (thresholdFlow_spec baseline hValid x).2.2.1.1 i j
    · intro x i
      change 0 ≤ if c.gap x < 0 then
        c.lower x i - rowMass (thresholdFlowUpper c hValid x) i else 0
      split_ifs
      · exact sub_nonneg.mpr ((thresholdFlow_spec baseline hValid x).2.2.1.2.1 i)
      · positivity
    · intro x j
      change 0 ≤ if 0 < c.gap x then
        c.upper x j - columnMass (thresholdFlowUpper c hValid x) j else 0
      split_ifs
      · exact sub_nonneg.mpr ((thresholdFlow_spec baseline hValid x).2.2.1.2.2.1 j)
      · positivity
    · intro x
      exact sub_nonneg.mpr (baseline.qMax_le_complierMass x)
    · intro x s0 s1 y0 y1
      change 0 ≤ baseline.neverTakerComponent x s0 s1 y0 y1
      rw [baseline.neverTaker_eq]
      unfold baselineNeverTakerComponent conditionalReal
      split_ifs <;> positivity
    · intro x s0 s1 y0 y1
      change 0 ≤ baseline.alwaysTakerComponent x s0 s1 y0 y1
      rw [baseline.alwaysTaker_eq]
      unfold baselineAlwaysTakerComponent conditionalReal
      split_ifs <;> positivity

/-- A whole family of arbitrary exact-mass couplings has a nonnegative latent completion table. This is the generic form used by the sharpness lift. Given [the stated hypotheses](hyp:hValid,gamma,hgamma), [the stated conclusion follows](goal). -/
theorem branchFree_completionCellTable_nonnegative {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (reference : Fin K) (gamma : ∀ x : 𝒳, Coupling K)
    (hgamma : ∀ x, gamma x ∈ branchFreePolytope c hValid x) :
    (thresholdCompletionCellTable reference
      (fun x => thresholdLatentCompletion baseline hValid x (gamma x))).Nonnegative := by
  apply thresholdCompletionCellTable_nonnegative
  · exact fun x i j => (hgamma x).1 i j
  · intro x i
    change 0 ≤ if c.gap x < 0 then c.lower x i - rowMass (gamma x) i else 0
    split_ifs
    · exact sub_nonneg.mpr ((hgamma x).2.1 i)
    · positivity
  · intro x j
    change 0 ≤ if 0 < c.gap x then c.upper x j - columnMass (gamma x) j else 0
    split_ifs
    · exact sub_nonneg.mpr ((hgamma x).2.2.1 j)
    · positivity
  · intro x
    exact sub_nonneg.mpr (baseline.qMax_le_complierMass x)
  · intro x s0 s1 y0 y1
    change 0 ≤ baseline.neverTakerComponent x s0 s1 y0 y1
    rw [baseline.neverTaker_eq]
    unfold baselineNeverTakerComponent conditionalReal
    split_ifs <;> positivity
  · intro x s0 s1 y0 y1
    change 0 ≤ baseline.alwaysTakerComponent x s0 s1 y0 y1
    rw [baseline.alwaysTaker_eq]
    unfold baselineAlwaysTakerComponent conditionalReal
    split_ifs <;> positivity

/-- The arbitrary exact-mass completion preserves the baseline cell total. Given [the stated hypotheses](hyp:hValid,gamma,hgamma,hpartition), [the stated conclusion follows](goal). -/
theorem branchFree_completionCellTable_total {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (reference : Fin K) (gamma : ∀ x : 𝒳, Coupling K)
    (hgamma : ∀ x, gamma x ∈ branchFreePolytope c hValid x)
    (x : 𝒳)
    (hpartition :
      (∑ s0, ∑ s1, ∑ y0, ∑ y1, baseline.neverTakerComponent x s0 s1 y0 y1) +
        baseline.complierMass x +
        (∑ s0, ∑ s1, ∑ y0, ∑ y1,
          baseline.alwaysTakerComponent x s0 s1 y0 y1) = 1) :
    (∑ d0, ∑ d1, ∑ s0, ∑ s1, ∑ y0, ∑ y1,
      thresholdCompletionCellTable reference
        (fun x => thresholdLatentCompletion baseline hValid x (gamma x))
        x d0 d1 s0 s1 y0 y1) = 1 := by
  rw [thresholdCompletionCellTable_total]
  have hc := thresholdLatentCompletion_complier_total baseline hValid x
    (gamma x) (hgamma x)
  simp only [thresholdLatentCompletion] at hc ⊢
  linarith

private theorem conditionalReal_iUnion_fintype
    {P : POSystem} {I : Type*} [Fintype I]
    (E : I → Set P.Ω) (C : Set P.Ω)
    (hE : ∀ i, MeasurableSet (E i)) (hC : MeasurableSet C)
    (hdisj : Pairwise (fun i j ↦ Disjoint (E i) (E j))) :
    conditionalReal P.μ (⋃ i, E i) C = ∑ i, conditionalReal P.μ (E i) C := by
  unfold conditionalReal
  split_ifs with hpos
  · rw [← Finset.sum_div]
    rw [show (⋃ i, E i) ∩ C = ⋃ i, E i ∩ C by ext; simp]
    apply congrArg (fun r : ℝ ↦ r / P.μ.real C)
    rw [measureReal_iUnion_fintype]
    · intro i j hij
      exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    · intro i
      exact (hE i).inter hC
  · simp

private theorem conditionalReal_treatment_eq_unselected_add_selected
    {P : POSystem} (D S₀ : P.Ω → Bool) (Y : P.Ω → Fin K)
    (hD : Measurable D) (hS : Measurable S₀) (hY : Measurable Y)
    (d : Bool) (C : Set P.Ω) (hC : MeasurableSet C) :
    conditionalReal P.μ {ω | D ω = d} C =
      conditionalReal P.μ {ω | D ω = d ∧ S₀ ω = false} C +
        ∑ i, conditionalReal P.μ
          {ω | D ω = d ∧ S₀ ω = true ∧ Y ω = i} C := by
  let E : Option (Fin K) → Set P.Ω
    | none => {ω | D ω = d ∧ S₀ ω = false}
    | some i => {ω | D ω = d ∧ S₀ ω = true ∧ Y ω = i}
  have hmeas : ∀ a, MeasurableSet (E a) := by
    intro a
    cases a with
    | none =>
        change MeasurableSet {ω | D ω = d ∧ S₀ ω = false}
        exact (hD (measurableSet_singleton d)).inter
          (hS (measurableSet_singleton false))
    | some i =>
        change MeasurableSet {ω | D ω = d ∧ S₀ ω = true ∧ Y ω = i}
        convert ((hD (measurableSet_singleton d)).inter
          (hS (measurableSet_singleton true))).inter
          (hY (measurableSet_singleton i)) using 1 <;>
          ext ω <;> simp [and_assoc]
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    cases a with
    | none =>
        cases b with
        | none => exact False.elim (hab rfl)
        | some j =>
            exact Bool.noConfusion (ha.2.symm.trans hb.2.1)
    | some i =>
        cases b with
        | none =>
            exact Bool.noConfusion (hb.2.symm.trans ha.2.1)
        | some j =>
            apply hab
            congr
            exact ha.2.2.symm.trans hb.2.2
  rw [show {ω | D ω = d} = ⋃ a, E a by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hd
      cases hs : S₀ ω
      · exact ⟨none, hd, hs⟩
      · exact ⟨some (Y ω), hd, hs, rfl⟩
    · rintro ⟨a, ha⟩
      cases a with
      | none => exact ha.1
      | some i => exact ha.1]
  rw [conditionalReal_iUnion_fintype E C hmeas hC hdisj,
    Fintype.sum_option]

private theorem conditionalReal_bool_partition_event
    {P : POSystem} (A C : Set P.Ω) (f : P.Ω → Bool)
    (hA : MeasurableSet A) (hC : MeasurableSet C) (hf : Measurable f) :
    conditionalReal P.μ A C =
      ∑ b : Bool, conditionalReal P.μ (A ∩ {ω | f ω = b}) C := by
  let E : Bool → Set P.Ω := fun b => A ∩ {ω | f ω = b}
  have hmeas : ∀ b, MeasurableSet (E b) := fun b =>
    hA.inter (hf (measurableSet_singleton b))
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    apply hab
    exact ha.2.symm.trans hb.2
  have hunion : A = ⋃ b, E b := by
    ext ω
    simp only [Set.mem_iUnion, E, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ha
      exact ⟨f ω, ha, rfl⟩
    · rintro ⟨b, ha, _⟩
      exact ha
  calc
    conditionalReal P.μ A C = conditionalReal P.μ (⋃ b, E b) C := by rw [hunion]
    _ = ∑ b, conditionalReal P.μ (E b) C :=
      conditionalReal_iUnion_fintype E C hmeas hC hdisj
    _ = _ := rfl

private theorem conditionalReal_bool_fin_partition_event
    {P : POSystem} (A C : Set P.Ω) (f : P.Ω → Bool) (g : P.Ω → Fin K)
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hf : Measurable f) (hg : Measurable g) :
    conditionalReal P.μ A C =
      ∑ b : Bool, ∑ i : Fin K,
        conditionalReal P.μ (A ∩ {ω | f ω = b ∧ g ω = i}) C := by
  let E : Bool × Fin K → Set P.Ω := fun a =>
    A ∩ {ω | f ω = a.1 ∧ g ω = a.2}
  have hmeas : ∀ a, MeasurableSet (E a) := by
    intro a
    exact hA.inter ((hf (measurableSet_singleton a.1)).inter
      (hg (measurableSet_singleton a.2)))
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    apply hab
    exact Prod.ext (ha.2.1.symm.trans hb.2.1) (ha.2.2.symm.trans hb.2.2)
  have hunion : A = ⋃ a, E a := by
    ext ω
    simp only [Set.mem_iUnion, E, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ha
      exact ⟨⟨f ω, g ω⟩, ha, rfl, rfl⟩
    · rintro ⟨a, ha, _, _⟩
      exact ha
  calc
    conditionalReal P.μ A C = conditionalReal P.μ (⋃ a, E a) C := by rw [hunion]
    _ = ∑ a, conditionalReal P.μ (E a) C :=
      conditionalReal_iUnion_fintype E C hmeas hC hdisj
    _ = _ := by simp [E, Fintype.sum_prod_type]

private theorem coupling_eq_zero_of_nonnegative_total_zero
    (g : Coupling K) (hnonnegative : matrixNonnegative g)
    (htotal : totalMass g = 0) : g = 0 := by
  funext i j
  apply le_antisymm
  · have hij : g i j ≤ ∑ j', g i j' :=
      Finset.single_le_sum (fun j' _ ↦ hnonnegative i j') (Finset.mem_univ j)
    have hi : (∑ j', g i j') ≤ ∑ i', ∑ j', g i' j' :=
      Finset.single_le_sum
        (fun i' _ ↦ Finset.sum_nonneg (fun j' _ ↦ hnonnegative i' j'))
        (Finset.mem_univ i)
    calc
      g i j ≤ totalMass g := by simpa [totalMass] using hij.trans hi
      _ = 0 := htotal
  · exact hnonnegative i j

private theorem canonicalThresholdCandidate_withoutY1_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (x : 𝒳) (hx : 0 < S.p x) (d0 d1 s0 s1 : Bool) (y0 : Fin K) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    conditionalReal W.system.μ
      {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
        W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧ W.slate.Y0 ω = y0}
      (W.slate.xEvent x) = ∑ y1, T x d0 d1 s0 s1 y0 y1 := by
  dsimp only
  let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
  let E : Fin K → Set W.system.Ω := fun y1 =>
    {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
      W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
      W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1} ∩ W.slate.xEvent x
  have hmeas : ∀ y1, MeasurableSet (E y1) := by
    intro y1
    dsimp [E, POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S0,
      POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1, POSlateSystem.xEvent,
      POSlateSystem.factualX]
    exact (((((W.slate.dVar.measurable_cfUnder W.slate.zVar false
      (measurableSet_singleton d0)).inter
      (W.slate.dVar.measurable_cfUnder W.slate.zVar true
        (measurableSet_singleton d1))).inter
      (W.slate.sVar.measurable_cfUnder W.slate.dVar false
        (measurableSet_singleton s0))).inter
      (W.slate.sVar.measurable_cfUnder W.slate.dVar true
        (measurableSet_singleton s1))).inter
      (W.slate.yVar.measurable_cfUnder W.slate.dVar false
        (measurableSet_singleton y0))).inter
      (W.slate.yVar.measurable_cfUnder W.slate.dVar true
        (measurableSet_singleton y1)) |>.inter
      (W.slate.xVar.measurable_factual (measurableSet_singleton x))
  have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro ω hi hj
    exact hij (hi.1.2.2.2.2.2.symm.trans hj.1.2.2.2.2.2)
  have hcell := canonicalThresholdCandidate_cellMass S T hp hprop
    hTnonnegative hTnormalized x
  have hden : 0 < W.system.μ.real (W.slate.xEvent x) := by
    simpa [W, hcell] using hx
  unfold conditionalReal
  rw [if_pos hden]
  rw [show (∑ y1, T x d0 d1 s0 s1 y0 y1) =
      ∑ y1, conditionalReal W.system.μ
        {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
          W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
          W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1}
        (W.slate.xEvent x) by
    apply Finset.sum_congr rfl
    intro y1 _
    symm
    simpa [W] using canonicalThresholdCandidate_conditionalTuple S T hp hprop
      hTnonnegative hTnormalized x hx d0 d1 s0 s1 y0 y1]
  simp_rw [conditionalReal, if_pos hden]
  rw [← Finset.sum_div, ← measureReal_iUnion_fintype hdisj hmeas]
  congr 2
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, E]
  constructor
  · rintro ⟨⟨hd0, hd1, hs0, hs1, hy0⟩, hxω⟩
    exact ⟨W.slate.Y1 ω, ⟨hd0, hd1, hs0, hs1, hy0, rfl⟩, hxω⟩
  · rintro ⟨y1, ⟨hd0, hd1, hs0, hs1, hy0, _⟩, hxω⟩
    exact ⟨⟨hd0, hd1, hs0, hs1, hy0⟩, hxω⟩

private theorem canonicalThresholdCandidate_withoutY0_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (x : 𝒳) (hx : 0 < S.p x) (d0 d1 s0 s1 : Bool) (y1 : Fin K) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    conditionalReal W.system.μ
      {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
        W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧ W.slate.Y1 ω = y1}
      (W.slate.xEvent x) = ∑ y0, T x d0 d1 s0 s1 y0 y1 := by
  dsimp only
  let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
  let E : Fin K → Set W.system.Ω := fun y0 =>
    {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
      W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
      W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1}
  have hE : ∀ y0, MeasurableSet (E y0) := by
    intro y0
    dsimp [E, POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S0,
      POSlateSystem.S1, POSlateSystem.Y0, POSlateSystem.Y1]
    exact (((((W.slate.dVar.measurable_cfUnder W.slate.zVar false
      (measurableSet_singleton d0)).inter
      (W.slate.dVar.measurable_cfUnder W.slate.zVar true
        (measurableSet_singleton d1))).inter
      (W.slate.sVar.measurable_cfUnder W.slate.dVar false
        (measurableSet_singleton s0))).inter
      (W.slate.sVar.measurable_cfUnder W.slate.dVar true
        (measurableSet_singleton s1))).inter
      (W.slate.yVar.measurable_cfUnder W.slate.dVar false
        (measurableSet_singleton y0))).inter
      (W.slate.yVar.measurable_cfUnder W.slate.dVar true
        (measurableSet_singleton y1))
  have hC : MeasurableSet (W.slate.xEvent x) :=
    W.slate.xVar.measurable_factual (measurableSet_singleton x)
  have hdisj : Pairwise (fun i j ↦ Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro ω hi hj
    exact hij (hi.2.2.2.2.1.symm.trans hj.2.2.2.2.1)
  rw [show {ω | W.slate.D0 ω = d0 ∧ W.slate.D1 ω = d1 ∧
        W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧ W.slate.Y1 ω = y1} =
      ⋃ y0, E y0 by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    constructor
    · rintro ⟨hd0, hd1, hs0, hs1, hy1⟩
      exact ⟨W.slate.Y0 ω, hd0, hd1, hs0, hs1, rfl, hy1⟩
    · rintro ⟨y0, hd0, hd1, hs0, hs1, _, hy1⟩
      exact ⟨hd0, hd1, hs0, hs1, hy1⟩]
  rw [conditionalReal_iUnion_fintype E (W.slate.xEvent x) hE hC hdisj]
  apply Finset.sum_congr rfl
  intro y0 _
  simpa [W, E] using canonicalThresholdCandidate_conditionalTuple S T hp hprop
    hTnonnegative hTnormalized x hx d0 d1 s0 s1 y0 y1

private theorem canonicalThresholdCandidate_survivor_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : 0 < S.p x) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    fullLawSurvivorCoupling W x = (completion x).survivor := by
  dsimp only
  funext i j
  rw [show (completion x).survivor i j =
      normalizedCompletionCellTable S reference completion x
        false true true true i j by
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable]]
  rw [← canonicalThresholdCandidate_conditionalTuple S
    (normalizedCompletionCellTable S reference completion)
    hp hprop hTnonnegative hTnormalized x hx false true true true i j]
  unfold fullLawSurvivorCoupling
  congr 1
  ext ω
  simp only [POSlateSystem.complierEvent, POSlateSystem.D0, POSlateSystem.D1,
    Set.mem_setOf_eq]
  tauto

private theorem canonicalThresholdCandidate_selectedZero_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : 0 < S.p x) (i : Fin K) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    fullLawSelectedOnlyUnderZero W x i = (completion x).selectedOnlyUnderZero i := by
  dsimp only
  let W := canonicalThresholdCandidate S
    (normalizedCompletionCellTable S reference completion)
    hp hprop hTnonnegative hTnormalized
  calc
    fullLawSelectedOnlyUnderZero W x i = conditionalReal W.system.μ
        {ω | W.slate.D0 ω = false ∧ W.slate.D1 ω = true ∧
          W.slate.S0 ω = true ∧ W.slate.S1 ω = false ∧
          W.slate.Y0 ω = i} (W.slate.xEvent x) := by
      unfold fullLawSelectedOnlyUnderZero
      congr 1
      ext ω
      simp only [POSlateSystem.complierEvent, POSlateSystem.D0, POSlateSystem.D1,
        Set.mem_setOf_eq]
      tauto
    _ = ∑ y1, normalizedCompletionCellTable S reference completion x
        false true true false i y1 := by
      simpa [W] using canonicalThresholdCandidate_withoutY1_of_pos S
        (normalizedCompletionCellTable S reference completion)
        hp hprop hTnonnegative hTnormalized x hx false true true false i
    _ = (completion x).selectedOnlyUnderZero i := by
      simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable]

private theorem canonicalThresholdCandidate_selectedOne_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : 0 < S.p x) (j : Fin K) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    fullLawSelectedOnlyUnderOne W x j = (completion x).selectedOnlyUnderOne j := by
  dsimp only
  let W := canonicalThresholdCandidate S
    (normalizedCompletionCellTable S reference completion)
    hp hprop hTnonnegative hTnormalized
  calc
    fullLawSelectedOnlyUnderOne W x j = conditionalReal W.system.μ
        {ω | W.slate.D0 ω = false ∧ W.slate.D1 ω = true ∧
          W.slate.S0 ω = false ∧ W.slate.S1 ω = true ∧
          W.slate.Y1 ω = j} (W.slate.xEvent x) := by
      unfold fullLawSelectedOnlyUnderOne
      congr 1
      ext ω
      simp only [POSlateSystem.complierEvent, POSlateSystem.D0, POSlateSystem.D1,
        Set.mem_setOf_eq]
      tauto
    _ = ∑ y0, normalizedCompletionCellTable S reference completion x
        false true false true y0 j := by
      simpa [W] using canonicalThresholdCandidate_withoutY0_of_pos S
        (normalizedCompletionCellTable S reference completion)
        hp hprop hTnonnegative hTnormalized x hx false true false true j
    _ = (completion x).selectedOnlyUnderOne j := by
      simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable]

private theorem canonicalThresholdCandidate_neverSelected_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : 0 < S.p x) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    fullLawNeverSelectedMass W x = (completion x).neverSelectedMass := by
  dsimp only
  let T := normalizedCompletionCellTable S reference completion
  let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
  let E : Fin K → Set W.system.Ω := fun y0 =>
    {ω | W.slate.D0 ω = false ∧ W.slate.D1 ω = true ∧
      W.slate.S0 ω = false ∧ W.slate.S1 ω = false ∧ W.slate.Y0 ω = y0}
  have hE : ∀ y0, MeasurableSet (E y0) := by
    intro y0
    dsimp [E, POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S0,
      POSlateSystem.S1, POSlateSystem.Y0]
    exact ((((W.slate.dVar.measurable_cfUnder W.slate.zVar false
      (measurableSet_singleton false)).inter
      (W.slate.dVar.measurable_cfUnder W.slate.zVar true
        (measurableSet_singleton true))).inter
      (W.slate.sVar.measurable_cfUnder W.slate.dVar false
        (measurableSet_singleton false))).inter
      (W.slate.sVar.measurable_cfUnder W.slate.dVar true
        (measurableSet_singleton false))).inter
      (W.slate.yVar.measurable_cfUnder W.slate.dVar false
        (measurableSet_singleton y0))
  have hC : MeasurableSet (W.slate.xEvent x) :=
    W.slate.xVar.measurable_factual (measurableSet_singleton x)
  have hdisj : Pairwise (fun i j ↦ Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro ω hi hj
    exact hij (hi.2.2.2.2.symm.trans hj.2.2.2.2)
  calc
    fullLawNeverSelectedMass W x = conditionalReal W.system.μ (⋃ y0, E y0)
        (W.slate.xEvent x) := by
      unfold fullLawNeverSelectedMass
      congr 1
      ext ω
      simp only [POSlateSystem.complierEvent, POSlateSystem.D0, POSlateSystem.D1,
        Set.mem_setOf_eq, Set.mem_iUnion, E]
      constructor
      · rintro ⟨hs0, hs1, hd0, hd1⟩
        exact ⟨W.slate.Y0 ω, hd0, hd1, hs0, hs1, rfl⟩
      · rintro ⟨y0, hd0, hd1, hs0, hs1, _⟩
        exact ⟨hs0, hs1, hd0, hd1⟩
    _ = ∑ y0, conditionalReal W.system.μ (E y0) (W.slate.xEvent x) :=
      conditionalReal_iUnion_fintype E (W.slate.xEvent x) hE hC hdisj
    _ = ∑ y0, ∑ y1, T x false true false false y0 y1 := by
      apply Finset.sum_congr rfl
      intro y0 _
      simpa [W, E, T] using canonicalThresholdCandidate_withoutY1_of_pos S T
        hp hprop hTnonnegative hTnormalized x hx false true false false y0
    _ = (completion x).neverSelectedMass := by
      simp only [T, normalizedCompletionCellTable, hx, if_pos,
        thresholdCompletionCellTable]
      calc
        (∑ y0, ∑ y1, if y0 = reference ∧ y1 = reference then
            (completion x).neverSelectedMass else 0) =
            ∑ y0, if y0 = reference then (completion x).neverSelectedMass else 0 := by
          apply Finset.sum_congr rfl
          intro y0 _
          by_cases hy0 : y0 = reference <;> simp [hy0]
        _ = (completion x).neverSelectedMass := by simp

private theorem canonicalThresholdCandidate_noncompliers_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : 0 < S.p x) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    baselineNeverTakerComponent W x = (completion x).neverTakerComponent ∧
      baselineAlwaysTakerComponent W x = (completion x).alwaysTakerComponent := by
  dsimp only
  constructor <;> funext s0 s1 y0 y1
  · unfold baselineNeverTakerComponent
    rw [canonicalThresholdCandidate_conditionalTuple S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized x hx false false s0 s1 y0 y1]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable]
  · unfold baselineAlwaysTakerComponent
    rw [canonicalThresholdCandidate_conditionalTuple S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized x hx true true s0 s1 y0 y1]
    simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable]

private theorem canonicalThresholdCandidate_realizes_of_pos
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : 0 < S.p x) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    RealizesThresholdLatentCompletion W x (completion x) := by
  dsimp only
  refine ⟨canonicalThresholdCandidate_survivor_of_pos S reference completion
    hp hprop hTnonnegative hTnormalized x hx, ?_⟩
  refine ⟨canonicalThresholdCandidate_selectedZero_of_pos S reference completion
    hp hprop hTnonnegative hTnormalized x hx, ?_⟩
  refine ⟨canonicalThresholdCandidate_selectedOne_of_pos S reference completion
    hp hprop hTnonnegative hTnormalized x hx, ?_⟩
  refine ⟨canonicalThresholdCandidate_neverSelected_of_pos S reference completion
    hp hprop hTnonnegative hTnormalized x hx, ?_⟩
  exact canonicalThresholdCandidate_noncompliers_of_pos S reference completion
    hp hprop hTnonnegative hTnormalized x hx

private def ThresholdLatentCompletion.IsZero {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (completion : ThresholdLatentCompletion P₀ Pobs c) : Prop :=
  completion.survivor = 0 ∧
    completion.selectedOnlyUnderZero = 0 ∧
    completion.selectedOnlyUnderOne = 0 ∧
    completion.neverSelectedMass = 0 ∧
    completion.neverTakerComponent = 0 ∧
    completion.alwaysTakerComponent = 0

private theorem canonicalThresholdCandidate_realizes_of_zero
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative :
      (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized :
      (normalizedCompletionCellTable S reference completion).Normalized)
    (x : 𝒳) (hx : S.p x = 0) (hzero : (completion x).IsZero) :
    let W := canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion)
      hp hprop hTnonnegative hTnormalized
    RealizesThresholdLatentCompletion W x (completion x) := by
  dsimp only
  let W := canonicalThresholdCandidate S
    (normalizedCompletionCellTable S reference completion)
    hp hprop hTnonnegative hTnormalized
  have hcell := canonicalThresholdCandidate_cellMass S
    (normalizedCompletionCellTable S reference completion) hp hprop
    hTnonnegative hTnormalized x
  have hcond (A : Set W.system.Ω) :
      conditionalReal W.system.μ A (W.slate.xEvent x) = 0 := by
    unfold conditionalReal
    rw [show W.system.μ.real (W.slate.xEvent x) = 0 by
      simpa [W] using hcell.trans hx]
    simp
  rcases hzero with ⟨hsurvivor, hselectedZero, hselectedOne, hnever, hNT, hAT⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsurvivor]
    funext i j
    exact hcond _
  · rw [hselectedZero]
    intro i
    exact hcond _
  · rw [hselectedOne]
    intro j
    exact hcond _
  · rw [hnever]
    exact hcond _
  · rw [hNT]
    funext s0 s1 y0 y1
    exact hcond _
  · rw [hAT]
    funext s0 s1 y0 y1
    exact hcond _

private theorem thresholdFlow_isZero_of_data_zero {P₀ : POSystem}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (x : 𝒳)
    (hlower : ∀ i, c.lower x i = 0) (hupper : ∀ j, c.upper x j = 0)
    (hcomplier : baseline.complierMass x = 0)
    (hNT : baseline.neverTakerComponent x = 0)
    (hAT : baseline.alwaysTakerComponent x = 0) :
    let out := thresholdFlow baseline hValid x
    out.lower.IsZero ∧ out.upper.IsZero := by
  dsimp only
  have hq0 : c.q0 x = 0 := by simp [Capacities.q0, hlower]
  have hq1 : c.q1 x = 0 := by simp [Capacities.q1, hupper]
  have hmass : c.mass x = 0 := by simp [Capacities.mass, hq0, hq1]
  have hgap : c.gap x = 0 := by simp [Capacities.gap, hq0, hq1]
  have hspec := thresholdFlow_spec baseline hValid x
  have hlowerPoly := hspec.1
  have hupperPoly := hspec.2.2.1
  change matrixNonnegative (thresholdFlowLower c hValid x) ∧
    (∀ i, rowMass (thresholdFlowLower c hValid x) i ≤ c.lower x i) ∧
    (∀ j, columnMass (thresholdFlowLower c hValid x) j ≤ c.upper x j) ∧
    totalMass (thresholdFlowLower c hValid x) = c.mass x at hlowerPoly
  change matrixNonnegative (thresholdFlowUpper c hValid x) ∧
    (∀ i, rowMass (thresholdFlowUpper c hValid x) i ≤ c.lower x i) ∧
    (∀ j, columnMass (thresholdFlowUpper c hValid x) j ≤ c.upper x j) ∧
    totalMass (thresholdFlowUpper c hValid x) = c.mass x at hupperPoly
  have hγlower : thresholdFlowLower c hValid x = 0 :=
    coupling_eq_zero_of_nonnegative_total_zero _ hlowerPoly.1
      (hlowerPoly.2.2.2.trans hmass)
  have hγupper : thresholdFlowUpper c hValid x = 0 :=
    coupling_eq_zero_of_nonnegative_total_zero _ hupperPoly.1
      (hupperPoly.2.2.2.trans hmass)
  constructor <;>
    simp [ThresholdLatentCompletion.IsZero, thresholdFlow,
      thresholdLatentCompletion, hγlower, hγupper, hgap, hcomplier,
      hNT, hAT, hq0, hq1] <;> funext i <;> rfl

private theorem originalCompatibleBaseline_data_zero
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (model : TieSafeSurvivorModel S εZ d) (x : 𝒳) (hx : S.p x = 0) :
    let c := observableCapacities S.observedLaw
    let baseline := originalCompatibleBaseline S εZ d model
    (∀ i, c.lower x i = 0) ∧ (∀ j, c.upper x j = 0) ∧
      baseline.complierMass x = 0 ∧
      baseline.neverTakerComponent x = 0 ∧
      baseline.alwaysTakerComponent x = 0 := by
  dsimp only
  rcases observableCapacity_eq_zero_of_p_eq_zero S x hx with ⟨hlower, hupper⟩
  have hxreal : P.μ.real (S.xEvent x) = 0 := by
    simpa [POSlateSystem.p] using hx
  have hcond (A : Set P.Ω) : conditionalReal P.μ A (S.xEvent x) = 0 := by
    unfold conditionalReal
    rw [hxreal]
    simp
  refine ⟨hlower, hupper, hcond _, ?_, ?_⟩
  · funext s0 s1 y0 y1
    exact hcond _
  · funext s0 s1 y0 y1
    exact hcond _

private theorem measurable_observedDatum_local {P : POSystem}
    (S : POSlateSystem P 𝒳 K) : Measurable S.observedDatum := by
  intro t _
  rw [show S.observedDatum ⁻¹' t = ⋃ o : t, S.observedDatum ⁻¹' {o.1} by ext; simp]
  apply MeasurableSet.iUnion
  rintro ⟨⟨x, z, d, s, y⟩, _⟩
  have hout : MeasurableSet {ω |
      (if S.factualS ω then some (S.factualY ω) else none) = y} := by
    cases y with
    | none =>
        convert S.sVar.measurable_factual (measurableSet_singleton false) using 1 <;>
          ext ω <;> cases h : S.sVar.factual ω <;> simp [POSlateSystem.factualS, h]
    | some k =>
        convert (S.sVar.measurable_factual (measurableSet_singleton true)).inter
          (S.yVar.measurable_factual (measurableSet_singleton k)) using 1 <;>
          ext ω <;> cases h : S.sVar.factual ω <;>
            simp [POSlateSystem.factualS, POSlateSystem.factualY, h]
  have hm : MeasurableSet {ω | S.factualX ω = x ∧ S.factualZ ω = z ∧
      S.factualD ω = d ∧ S.factualS ω = s ∧
      (if S.factualS ω then some (S.factualY ω) else none) = y} := by
    have h := ((((S.xVar.measurable_factual (measurableSet_singleton x)).inter
      (S.zVar.measurable_factual (measurableSet_singleton z))).inter
      (S.dVar.measurable_factual (measurableSet_singleton d))).inter
      (S.sVar.measurable_factual (measurableSet_singleton s))).inter hout
    convert h using 1 <;> ext ω <;>
      simp [POSlateSystem.factualX, POSlateSystem.factualZ,
        POSlateSystem.factualD, POSlateSystem.factualS, and_assoc]
  convert hm using 1 <;> ext ω <;>
    simp [POSlateSystem.observedDatum, ObservedDatum.mk.injEq, and_assoc]

private theorem observedLaw_cellProbability {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (x : 𝒳) :
    S.observedLaw.real {o | o.cell = x} = S.p x := by
  unfold POSlateSystem.observedLaw POSlateSystem.p
  simp only [Measure.real, Measure.map_apply (measurable_observedDatum_local S)
    MeasurableSet.of_discrete]
  rfl

private def factualObservedTailEvent {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (d s : Bool) (y : Option (Fin K)) : Set P.Ω :=
  {ω | S.factualD ω = d ∧ S.factualS ω = s ∧
    (if S.factualS ω then some (S.factualY ω) else none) = y}

private def latentObservedTailEvent {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (z d s : Bool) (y : Option (Fin K)) : Set P.Ω :=
  {ω | S.DofZ z ω = d ∧ S.SofD d ω = s ∧
    (if S.SofD d ω then some (S.YofD d ω) else none) = y}

private theorem latentObservedTail_unselected_complement
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (z d : Bool) :
    conditionalReal P.μ (latentObservedTailEvent S z d false none)
        (S.xEvent x) =
      conditionalReal P.μ {ω | S.DofZ z ω = d} (S.xEvent x) -
        ∑ i, conditionalReal P.μ
          (latentObservedTailEvent S z d true (some i)) (S.xEvent x) := by
  have h := conditionalReal_treatment_eq_unselected_add_selected
    (P := P) (S.DofZ z) (S.SofD d) (S.YofD d)
    (S.dVar.measurable_cfUnder S.zVar z)
    (S.sVar.measurable_cfUnder S.dVar d)
    (S.yVar.measurable_cfUnder S.dVar d) d (S.xEvent x)
    (S.xVar.measurable_factual (measurableSet_singleton x))
  have hunselected :
      {ω | S.DofZ z ω = d ∧ S.SofD d ω = false} =
        latentObservedTailEvent S z d false none := by
    ext ω
    simp [latentObservedTailEvent]
  have hselected (i : Fin K) :
      {ω | S.DofZ z ω = d ∧ S.SofD d ω = true ∧ S.YofD d ω = i} =
        latentObservedTailEvent S z d true (some i) := by
    ext ω
    simp [latentObservedTailEvent, and_assoc]
  simp_rw [hselected] at h
  rw [hunselected] at h
  linarith

private theorem latentObservedTail_invalid
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (z d : Bool) :
    (∀ i, conditionalReal P.μ
      (latentObservedTailEvent S z d false (some i)) (S.xEvent x) = 0) ∧
    conditionalReal P.μ
      (latentObservedTailEvent S z d true none) (S.xEvent x) = 0 := by
  constructor
  · intro i
    rw [show latentObservedTailEvent S z d false (some i) = ∅ by
      ext ω
      constructor
      · intro h
        rcases h with ⟨_, hs, hy⟩
        exact False.elim (by simpa [hs] using hy)
      · intro h
        exact False.elim (by simpa using h)]
    simp [conditionalReal]
  · rw [show latentObservedTailEvent S z d true none = ∅ by
      ext ω
      constructor
      · intro h
        rcases h with ⟨_, hs, hy⟩
        exact False.elim (by simpa [hs] using hy)
      · intro h
        exact False.elim (by simpa using h)]
    simp [conditionalReal]

private theorem conditionalReal_DofZ_principal_partition
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (z d : Bool) :
    conditionalReal P.μ {ω | S.DofZ z ω = d} (S.xEvent x) =
      ∑ b : Bool, conditionalReal P.μ
        {ω | if z then S.D0 ω = b ∧ S.D1 ω = d
          else S.D0 ω = d ∧ S.D1 ω = b} (S.xEvent x) := by
  let E : Bool → Set P.Ω := fun b =>
    {ω | if z then S.D0 ω = b ∧ S.D1 ω = d
      else S.D0 ω = d ∧ S.D1 ω = b}
  have hmeas : ∀ b, MeasurableSet (E b) := by
    intro b
    dsimp [E]
    cases z
    · exact (S.dVar.measurable_cfUnder S.zVar false
        (measurableSet_singleton d)).inter
        (S.dVar.measurable_cfUnder S.zVar true
          (measurableSet_singleton b))
    · exact (S.dVar.measurable_cfUnder S.zVar false
        (measurableSet_singleton b)).inter
        (S.dVar.measurable_cfUnder S.zVar true
          (measurableSet_singleton d))
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro ω ha hb
    apply hab
    dsimp [E] at ha hb
    cases z
    · exact ha.2.symm.trans hb.2
    · exact ha.1.symm.trans hb.1
  rw [show {ω | S.DofZ z ω = d} = ⋃ b, E b by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    cases z
    · constructor
      · intro hd
        exact ⟨S.D1 ω, hd, rfl⟩
      · rintro ⟨b, hd, _⟩
        exact hd
    · constructor
      · intro hd
        exact ⟨S.D0 ω, rfl, hd⟩
      · rintro ⟨b, _, hd⟩
        exact hd]
  exact conditionalReal_iUnion_fintype E (S.xEvent x) hmeas
    (S.xVar.measurable_factual (measurableSet_singleton x)) hdisj

private theorem conditionalReal_defier_stratum_zero
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (hNoDefiers : NoDefiers S)
    (x : 𝒳) :
    conditionalReal P.μ {ω | S.D0 ω = true ∧ S.D1 ω = false}
      (S.xEvent x) = 0 := by
  have hzero : P.μ
      ({ω | S.D0 ω = true ∧ S.D1 ω = false} ∩ S.xEvent x) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hNoDefiers] with ω hω
    intro hmem
    have hcontra : true = false := (hω hmem.1.1).symm.trans hmem.1.2
    cases hcontra
  unfold conditionalReal
  split_ifs <;> simp [Measure.real, hzero]

private theorem conditionalReal_DofZ_principal_cases
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (hNoDefiers : NoDefiers S)
    (x : 𝒳) :
    conditionalReal P.μ {ω | S.DofZ false ω = false} (S.xEvent x) =
        conditionalReal P.μ {ω | S.D0 ω = false ∧ S.D1 ω = false}
          (S.xEvent x) +
        conditionalReal P.μ S.complierEvent (S.xEvent x) ∧
    conditionalReal P.μ {ω | S.DofZ false ω = true} (S.xEvent x) =
        conditionalReal P.μ {ω | S.D0 ω = true ∧ S.D1 ω = true}
          (S.xEvent x) ∧
    conditionalReal P.μ {ω | S.DofZ true ω = false} (S.xEvent x) =
        conditionalReal P.μ {ω | S.D0 ω = false ∧ S.D1 ω = false}
          (S.xEvent x) ∧
    conditionalReal P.μ {ω | S.DofZ true ω = true} (S.xEvent x) =
        conditionalReal P.μ S.complierEvent (S.xEvent x) +
        conditionalReal P.μ {ω | S.D0 ω = true ∧ S.D1 ω = true}
          (S.xEvent x) := by
  have h00 := conditionalReal_DofZ_principal_partition S x false false
  have h01 := conditionalReal_DofZ_principal_partition S x false true
  have h10 := conditionalReal_DofZ_principal_partition S x true false
  have h11 := conditionalReal_DofZ_principal_partition S x true true
  have hdef := conditionalReal_defier_stratum_zero S hNoDefiers x
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true] at h00 h01 h10 h11
  constructor
  · simpa [POSlateSystem.complierEvent, POSlateSystem.D0, POSlateSystem.D1,
      add_comm] using h00
  constructor
  · simpa [hdef] using h01
  constructor
  · simpa [hdef] using h10
  · simpa [POSlateSystem.complierEvent, POSlateSystem.D0, POSlateSystem.D1,
      add_comm] using h11

private theorem baselineNeverTaker_selected_sum
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (x : 𝒳) (i : Fin K) :
    (∑ s1, ∑ y1, baselineNeverTakerComponent
      ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
        x true s1 i y1) =
      conditionalReal P.μ
        {ω | S.D0 ω = false ∧ S.D1 ω = false ∧
          S.S0 ω = true ∧ S.Y0 ω = i} (S.xEvent x) := by
  let A : Set P.Ω := {ω | S.D0 ω = false ∧ S.D1 ω = false ∧
    S.S0 ω = true ∧ S.Y0 ω = i}
  have hA : MeasurableSet A := by
    dsimp [A, POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S0,
      POSlateSystem.Y0]
    convert (((S.dVar.measurable_cfUnder S.zVar false
      (measurableSet_singleton false)).inter
      (S.dVar.measurable_cfUnder S.zVar true
        (measurableSet_singleton false))).inter
      (S.sVar.measurable_cfUnder S.dVar false
        (measurableSet_singleton true))).inter
      (S.yVar.measurable_cfUnder S.dVar false
        (measurableSet_singleton i)) using 1 <;>
      ext ω <;> simp [POSlateSystem.DofZ, POSlateSystem.SofD,
        POSlateSystem.YofD, and_assoc]
  have h := conditionalReal_bool_fin_partition_event (P := P) A (S.xEvent x)
    S.S1 S.Y1 hA (S.xVar.measurable_factual (measurableSet_singleton x))
    (S.sVar.measurable_cfUnder S.dVar true)
    (S.yVar.measurable_cfUnder S.dVar true)
  rw [h]
  apply Fintype.sum_congr
  intro s1
  apply Fintype.sum_congr
  intro y1
  unfold baselineNeverTakerComponent
  apply congrArg (fun E : Set P.Ω => conditionalReal P.μ E (S.xEvent x))
  ext ω
  simp [A, and_assoc, and_left_comm, and_comm]

private theorem baselineAlwaysTaker_selected_sum
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (x : 𝒳) (j : Fin K) :
    (∑ s0, ∑ y0, baselineAlwaysTakerComponent
      ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
        x s0 true y0 j) =
      conditionalReal P.μ
        {ω | S.D0 ω = true ∧ S.D1 ω = true ∧
          S.S1 ω = true ∧ S.Y1 ω = j} (S.xEvent x) := by
  let A : Set P.Ω := {ω | S.D0 ω = true ∧ S.D1 ω = true ∧
    S.S1 ω = true ∧ S.Y1 ω = j}
  have hA : MeasurableSet A := by
    dsimp [A, POSlateSystem.D0, POSlateSystem.D1, POSlateSystem.S1,
      POSlateSystem.Y1]
    convert (((S.dVar.measurable_cfUnder S.zVar false
      (measurableSet_singleton true)).inter
      (S.dVar.measurable_cfUnder S.zVar true
        (measurableSet_singleton true))).inter
      (S.sVar.measurable_cfUnder S.dVar true
        (measurableSet_singleton true))).inter
      (S.yVar.measurable_cfUnder S.dVar true
        (measurableSet_singleton j)) using 1 <;>
      ext ω <;> simp [POSlateSystem.DofZ, POSlateSystem.SofD,
        POSlateSystem.YofD, and_assoc]
  have h := conditionalReal_bool_fin_partition_event (P := P) A (S.xEvent x)
    S.S0 S.Y0 hA (S.xVar.measurable_factual (measurableSet_singleton x))
    (S.sVar.measurable_cfUnder S.dVar false)
    (S.yVar.measurable_cfUnder S.dVar false)
  rw [h]
  apply Fintype.sum_congr
  intro s0
  apply Fintype.sum_congr
  intro y0
  unfold baselineAlwaysTakerComponent
  apply congrArg (fun E : Set P.Ω => conditionalReal P.μ E (S.xEvent x))
  ext ω
  simp [A, and_assoc, and_left_comm, and_comm]

private theorem conditionalReal_defier_subset_zero
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (hNoDefiers : NoDefiers S)
    (x : 𝒳) (A : Set P.Ω)
    (hsub : A ⊆ {ω | S.D0 ω = true ∧ S.D1 ω = false}) :
    conditionalReal P.μ A (S.xEvent x) = 0 := by
  have hzero : P.μ (A ∩ S.xEvent x) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hNoDefiers] with ω hω
    intro hmem
    have hd := hsub hmem.1
    have hcontra : true = false := (hω hd.1).symm.trans hd.2
    cases hcontra
  unfold conditionalReal
  split_ifs <;> simp [Measure.real, hzero]

private theorem latentObservedTail_selected_event
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (z d : Bool) (i : Fin K) :
    latentObservedTailEvent S z d true (some i) =
      {ω | S.DofZ z ω = d ∧ S.SofD d ω = true ∧ S.YofD d ω = i} := by
  ext ω
  constructor
  · rintro ⟨hd, hs, hy⟩
    exact ⟨hd, hs, by simpa [hs] using hy⟩
  · rintro ⟨hd, hs, hy⟩
    exact ⟨hd, hs, by simpa [hs, hy]⟩

private theorem latentObservedTail_selected_cases
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (hNoDefiers : NoDefiers S)
    (x : 𝒳)
    (hlower : ∀ i, (observableCapacities S.observedLaw).lower x i =
      lowerLatentMass S x i)
    (hupper : ∀ j, (observableCapacities S.observedLaw).upper x j =
      upperLatentMass S x j) :
    (∀ i, conditionalReal P.μ
        (latentObservedTailEvent S false false true (some i)) (S.xEvent x) =
      (∑ s1, ∑ y1, baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x true s1 i y1) +
        (observableCapacities S.observedLaw).lower x i) ∧
    (∀ j, conditionalReal P.μ
        (latentObservedTailEvent S false true true (some j)) (S.xEvent x) =
      ∑ s0, ∑ y0, baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 true y0 j) ∧
    (∀ i, conditionalReal P.μ
        (latentObservedTailEvent S true false true (some i)) (S.xEvent x) =
      ∑ s1, ∑ y1, baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x true s1 i y1) ∧
    (∀ j, conditionalReal P.μ
        (latentObservedTailEvent S true true true (some j)) (S.xEvent x) =
      (∑ s0, ∑ y0, baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 true y0 j) +
        (observableCapacities S.observedLaw).upper x j) := by
  constructor
  · intro i
    let A : Set P.Ω := {ω | S.D0 ω = false ∧ S.S0 ω = true ∧ S.Y0 ω = i}
    have hA : MeasurableSet A := by
      convert ((S.dVar.measurable_cfUnder S.zVar false
        (measurableSet_singleton false)).inter
        (S.sVar.measurable_cfUnder S.dVar false
          (measurableSet_singleton true))).inter
        (S.yVar.measurable_cfUnder S.dVar false (measurableSet_singleton i)) using 1 <;>
        ext ω <;> simp [A, POSlateSystem.D0, POSlateSystem.S0,
          POSlateSystem.Y0, POSlateSystem.DofZ, POSlateSystem.SofD,
          POSlateSystem.YofD, and_assoc]
    have h := conditionalReal_bool_partition_event (P := P) A (S.xEvent x)
      S.D1 hA (S.xVar.measurable_factual (measurableSet_singleton x))
      (S.dVar.measurable_cfUnder S.zVar true)
    have htail : latentObservedTailEvent S false false true (some i) = A := by
      rw [latentObservedTail_selected_event]
      ext ω
      simp [A, POSlateSystem.D0, POSlateSystem.S0,
        POSlateSystem.Y0, POSlateSystem.DofZ, POSlateSystem.SofD,
        POSlateSystem.YofD, and_assoc, and_left_comm, and_comm]
    have hcomp : A ∩ {ω | S.D1 ω = true} =
        {ω | S.YofD false ω = i ∧ S.SofD false ω = true ∧
          ω ∈ S.complierEvent} := by
      ext ω
      simp [A, POSlateSystem.complierEvent, POSlateSystem.D0,
        POSlateSystem.D1, POSlateSystem.S0, POSlateSystem.Y0,
        POSlateSystem.SofD, POSlateSystem.YofD, and_assoc,
        and_left_comm, and_comm]
    have hnt : A ∩ {ω | S.D1 ω = false} =
        {ω | S.D0 ω = false ∧ S.D1 ω = false ∧
          S.S0 ω = true ∧ S.Y0 ω = i} := by
      ext ω
      simp [A, and_assoc, and_left_comm, and_comm]
    rw [Fintype.sum_bool, hcomp, hnt] at h
    rw [htail, baselineNeverTaker_selected_sum S x i, hlower i]
    unfold lowerLatentMass
    linarith
  constructor
  · intro j
    let A : Set P.Ω := {ω | S.D0 ω = true ∧ S.S1 ω = true ∧ S.Y1 ω = j}
    have hA : MeasurableSet A := by
      convert ((S.dVar.measurable_cfUnder S.zVar false
        (measurableSet_singleton true)).inter
        (S.sVar.measurable_cfUnder S.dVar true
          (measurableSet_singleton true))).inter
        (S.yVar.measurable_cfUnder S.dVar true (measurableSet_singleton j)) using 1 <;>
        ext ω <;> simp [A, POSlateSystem.D0, POSlateSystem.S1,
          POSlateSystem.Y1, POSlateSystem.DofZ, POSlateSystem.SofD,
          POSlateSystem.YofD, and_assoc]
    have h := conditionalReal_bool_partition_event (P := P) A (S.xEvent x)
      S.D1 hA (S.xVar.measurable_factual (measurableSet_singleton x))
      (S.dVar.measurable_cfUnder S.zVar true)
    have hdef : conditionalReal P.μ (A ∩ {ω | S.D1 ω = false})
        (S.xEvent x) = 0 := by
      apply conditionalReal_defier_subset_zero S hNoDefiers x
      intro ω hω
      exact ⟨hω.1.1, hω.2⟩
    have htail : latentObservedTailEvent S false true true (some j) = A := by
      rw [latentObservedTail_selected_event]
      ext ω
      simp [A, POSlateSystem.D0, POSlateSystem.S1,
        POSlateSystem.Y1, POSlateSystem.DofZ, POSlateSystem.SofD,
        POSlateSystem.YofD, and_assoc, and_left_comm, and_comm]
    have hat : A ∩ {ω | S.D1 ω = true} =
        {ω | S.D0 ω = true ∧ S.D1 ω = true ∧
          S.S1 ω = true ∧ S.Y1 ω = j} := by
      ext ω
      simp [A, and_assoc, and_left_comm, and_comm]
    rw [Fintype.sum_bool, hat, hdef] at h
    simp only [add_zero] at h
    rw [htail, baselineAlwaysTaker_selected_sum S x j]
    exact h
  constructor
  · intro i
    let A : Set P.Ω := {ω | S.D1 ω = false ∧ S.S0 ω = true ∧ S.Y0 ω = i}
    have hA : MeasurableSet A := by
      convert ((S.dVar.measurable_cfUnder S.zVar true
        (measurableSet_singleton false)).inter
        (S.sVar.measurable_cfUnder S.dVar false
          (measurableSet_singleton true))).inter
        (S.yVar.measurable_cfUnder S.dVar false (measurableSet_singleton i)) using 1 <;>
        ext ω <;> simp [A, POSlateSystem.D1, POSlateSystem.S0,
          POSlateSystem.Y0, POSlateSystem.DofZ, POSlateSystem.SofD,
          POSlateSystem.YofD, and_assoc]
    have h := conditionalReal_bool_partition_event (P := P) A (S.xEvent x)
      S.D0 hA (S.xVar.measurable_factual (measurableSet_singleton x))
      (S.dVar.measurable_cfUnder S.zVar false)
    have hdef : conditionalReal P.μ (A ∩ {ω | S.D0 ω = true})
        (S.xEvent x) = 0 := by
      apply conditionalReal_defier_subset_zero S hNoDefiers x
      intro ω hω
      exact ⟨hω.2, hω.1.1⟩
    have htail : latentObservedTailEvent S true false true (some i) = A := by
      rw [latentObservedTail_selected_event]
      ext ω
      simp [A, POSlateSystem.D1, POSlateSystem.S0,
        POSlateSystem.Y0, POSlateSystem.DofZ, POSlateSystem.SofD,
        POSlateSystem.YofD, and_assoc, and_left_comm, and_comm]
    have hnt : A ∩ {ω | S.D0 ω = false} =
        {ω | S.D0 ω = false ∧ S.D1 ω = false ∧
          S.S0 ω = true ∧ S.Y0 ω = i} := by
      ext ω
      simp [A, and_assoc, and_left_comm, and_comm]
    rw [Fintype.sum_bool, hdef, hnt] at h
    simp only [zero_add] at h
    rw [htail, baselineNeverTaker_selected_sum S x i]
    exact h
  · intro j
    let A : Set P.Ω := {ω | S.D1 ω = true ∧ S.S1 ω = true ∧ S.Y1 ω = j}
    have hA : MeasurableSet A := by
      convert ((S.dVar.measurable_cfUnder S.zVar true
        (measurableSet_singleton true)).inter
        (S.sVar.measurable_cfUnder S.dVar true
          (measurableSet_singleton true))).inter
        (S.yVar.measurable_cfUnder S.dVar true (measurableSet_singleton j)) using 1 <;>
        ext ω <;> simp [A, POSlateSystem.D1, POSlateSystem.S1,
          POSlateSystem.Y1, POSlateSystem.DofZ, POSlateSystem.SofD,
          POSlateSystem.YofD, and_assoc]
    have h := conditionalReal_bool_partition_event (P := P) A (S.xEvent x)
      S.D0 hA (S.xVar.measurable_factual (measurableSet_singleton x))
      (S.dVar.measurable_cfUnder S.zVar false)
    have htail : latentObservedTailEvent S true true true (some j) = A := by
      rw [latentObservedTail_selected_event]
      ext ω
      simp [A, POSlateSystem.D1, POSlateSystem.S1,
        POSlateSystem.Y1, POSlateSystem.DofZ, POSlateSystem.SofD,
        POSlateSystem.YofD, and_assoc, and_left_comm, and_comm]
    have hat : A ∩ {ω | S.D0 ω = true} =
        {ω | S.D0 ω = true ∧ S.D1 ω = true ∧
          S.S1 ω = true ∧ S.Y1 ω = j} := by
      ext ω
      simp [A, and_assoc, and_left_comm, and_comm]
    have hcomp : A ∩ {ω | S.D0 ω = false} =
        {ω | S.YofD true ω = j ∧ S.SofD true ω = true ∧
          ω ∈ S.complierEvent} := by
      ext ω
      simp [A, POSlateSystem.complierEvent, POSlateSystem.D0,
        POSlateSystem.D1, POSlateSystem.S1, POSlateSystem.Y1,
        POSlateSystem.SofD, POSlateSystem.YofD, and_assoc,
        and_left_comm, and_comm]
    rw [Fintype.sum_bool, hat, hcomp] at h
    rw [htail, baselineAlwaysTaker_selected_sum S x j, hupper j]
    unfold upperLatentMass
    exact h

private theorem normalizedCompletion_selected_margin_eq_latent
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (x : 𝒳) (hx : 0 < S.p x)
    (hmargins :
      (∀ i, rowMass (completion x).survivor i +
          (completion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass (completion x).survivor j +
          (completion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j))
    (hNT : ∀ s0 s1 y0 y1, (completion x).neverTakerComponent s0 s1 y0 y1 =
      baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1)
    (hAT : ∀ s0 s1 y0 y1, (completion x).alwaysTakerComponent s0 s1 y0 y1 =
      baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1)
    (hNoDefiers : NoDefiers S)
    (hlower : ∀ i, (observableCapacities S.observedLaw).lower x i =
      lowerLatentMass S x i)
    (hupper : ∀ j, (observableCapacities S.observedLaw).upper x j =
      upperLatentMass S x j) :
    ∀ z d i, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x z d true (some i) =
      conditionalReal P.μ (latentObservedTailEvent S z d true (some i))
        (S.xEvent x) := by
  have hnew := normalizedCompletion_selected_observedMargins S reference completion
    x hx hmargins
  simp_rw [hNT, hAT] at hnew
  have hold := latentObservedTail_selected_cases S hNoDefiers x hlower hupper
  intro z d i
  cases z <;> cases d
  · exact (hnew.1 i).trans (hold.1 i).symm
  · exact (hnew.2.1 i).trans (hold.2.1 i).symm
  · exact (hnew.2.2.1 i).trans (hold.2.2.1 i).symm
  · exact (hnew.2.2.2 i).trans (hold.2.2.2 i).symm

private theorem component_selection_partition
    (C : Bool → Bool → Fin K → Fin K → ℝ) :
    (∑ s1, ∑ y0, ∑ y1, C false s1 y0 y1) +
        (∑ i, ∑ s1, ∑ y1, C true s1 i y1) =
      ∑ s0, ∑ s1, ∑ y0, ∑ y1, C s0 s1 y0 y1 := by
  rw [show (∑ i, ∑ s1, ∑ y1, C true s1 i y1) =
      ∑ s1, ∑ i, ∑ y1, C true s1 i y1 by
    rw [Finset.sum_comm]]
  simp only [Fintype.sum_bool]
  ring

private theorem component_selection_partition_one
    (C : Bool → Bool → Fin K → Fin K → ℝ) :
    (∑ s0, ∑ y0, ∑ y1, C s0 false y0 y1) +
        (∑ j, ∑ s0, ∑ y0, C s0 true y0 j) =
      ∑ s0, ∑ s1, ∑ y0, ∑ y1, C s0 s1 y0 y1 := by
  rw [show (∑ j, ∑ s0, ∑ y0, C s0 true y0 j) =
      ∑ s0, ∑ y0, ∑ j, C s0 true y0 j by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro s0
    rw [Finset.sum_comm]]
  simp only [Fintype.sum_bool]
  ring

private theorem completion_complier_unselected_plus_selected
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (completion : ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw)) (x : 𝒳)
    (hmargins :
      (∀ i, rowMass completion.survivor i + completion.selectedOnlyUnderZero i =
        (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass completion.survivor j + completion.selectedOnlyUnderOne j =
        (observableCapacities S.observedLaw).upper x j))
    (htotal : (∑ i, ∑ j, completion.survivor i j) +
        (∑ i, completion.selectedOnlyUnderZero i) +
        (∑ j, completion.selectedOnlyUnderOne j) + completion.neverSelectedMass =
      conditionalReal P.μ S.complierEvent (S.xEvent x)) :
    ((∑ j, completion.selectedOnlyUnderOne j) + completion.neverSelectedMass) +
        ∑ i, (observableCapacities S.observedLaw).lower x i =
      conditionalReal P.μ S.complierEvent (S.xEvent x) ∧
    ((∑ i, completion.selectedOnlyUnderZero i) + completion.neverSelectedMass) +
        ∑ j, (observableCapacities S.observedLaw).upper x j =
      conditionalReal P.μ S.complierEvent (S.xEvent x) := by
  have hlower : (∑ i, (observableCapacities S.observedLaw).lower x i) =
      (∑ i, ∑ j, completion.survivor i j) +
        ∑ i, completion.selectedOnlyUnderZero i := by
    rw [Finset.sum_congr rfl (fun i _ => (hmargins.1 i).symm),
      Finset.sum_add_distrib]
    simp [rowMass]
  have hupper : (∑ j, (observableCapacities S.observedLaw).upper x j) =
      (∑ i, ∑ j, completion.survivor i j) +
        ∑ j, completion.selectedOnlyUnderOne j := by
    rw [Finset.sum_congr rfl (fun j _ => (hmargins.2 j).symm),
      Finset.sum_add_distrib]
    simp [columnMass, Finset.sum_comm]
  constructor <;> linarith

private theorem normalizedCompletion_unselected_margin_eq_latent
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (x : 𝒳) (hx : 0 < S.p x)
    (hmargins :
      (∀ i, rowMass (completion x).survivor i +
          (completion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass (completion x).survivor j +
          (completion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j))
    (hNT : ∀ s0 s1 y0 y1, (completion x).neverTakerComponent s0 s1 y0 y1 =
      baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1)
    (hAT : ∀ s0 s1 y0 y1, (completion x).alwaysTakerComponent s0 s1 y0 y1 =
      baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1)
    (hcompletionTotal :
      (∑ i, ∑ j, (completion x).survivor i j) +
        (∑ i, (completion x).selectedOnlyUnderZero i) +
        (∑ j, (completion x).selectedOnlyUnderOne j) +
        (completion x).neverSelectedMass =
      conditionalReal P.μ S.complierEvent (S.xEvent x))
    (hNoDefiers : NoDefiers S)
    (hlower : ∀ i, (observableCapacities S.observedLaw).lower x i =
      lowerLatentMass S x i)
    (hupper : ∀ j, (observableCapacities S.observedLaw).upper x j =
      upperLatentMass S x j) :
    ∀ z d, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x z d false none =
      conditionalReal P.μ (latentObservedTailEvent S z d false none)
        (S.xEvent x) := by
  let T := normalizedCompletionCellTable S reference completion
  have hu := normalizedCompletion_unselected_observedMargins S reference completion x hx
  have hsFormula := normalizedCompletion_selected_observedMargins S reference completion
    x hx hmargins
  simp_rw [hNT, hAT] at hu hsFormula
  have hs := normalizedCompletion_selected_margin_eq_latent S reference completion x hx
    hmargins hNT hAT hNoDefiers hlower hupper
  have hc := completion_complier_unselected_plus_selected S (completion x) x
    hmargins hcompletionTotal
  have hp := conditionalReal_DofZ_principal_cases S hNoDefiers x
  have hnt := component_selection_partition
    (baselineNeverTakerComponent
      ({ system := P, slate := S } : FullLawCandidate P 𝒳 K) x)
  have hat := component_selection_partition_one
    (baselineAlwaysTakerComponent
      ({ system := P, slate := S } : FullLawCandidate P 𝒳 K) x)
  have hntTotal : (∑ s0, ∑ s1, ∑ y0, ∑ y1,
      baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1) =
      conditionalReal P.μ {ω | S.D0 ω = false ∧ S.D1 ω = false}
        (S.xEvent x) := by
    simpa [baselineNeverTakerComponent] using
      sum_principal_component S false false x
  have hatTotal : (∑ s0, ∑ s1, ∑ y0, ∑ y1,
      baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1) =
      conditionalReal P.μ {ω | S.D0 ω = true ∧ S.D1 ω = true}
        (S.xEvent x) := by
    simpa [baselineAlwaysTakerComponent] using
      sum_principal_component S true true x
  intro z d
  have hselectedSum : (∑ i, thresholdObservedTableMargin T x z d true (some i)) =
      ∑ i, conditionalReal P.μ
        (latentObservedTailEvent S z d true (some i)) (S.xEvent x) := by
    apply Fintype.sum_congr
    intro i
    exact hs z d i
  have hcomplement := latentObservedTail_unselected_complement S x z d
  have htotal : thresholdObservedTableMargin T x z d false none +
      (∑ i, thresholdObservedTableMargin T x z d true (some i)) =
      conditionalReal P.μ {ω | S.DofZ z ω = d} (S.xEvent x) := by
    dsimp only [T]
    cases z <;> cases d
    · rw [hu.1]
      simp_rw [hsFormula.1]
      rw [Finset.sum_add_distrib]
      linarith [hc.1, hnt, hntTotal, hp.1]
    · rw [hu.2.1]
      simp_rw [hsFormula.2.1]
      exact hat.trans (hatTotal.trans hp.2.1.symm)
    · rw [hu.2.2.1]
      simp_rw [hsFormula.2.2.1]
      exact hnt.trans (hntTotal.trans hp.2.2.1.symm)
    · rw [hu.2.2.2]
      simp_rw [hsFormula.2.2.2]
      rw [Finset.sum_add_distrib]
      linarith [hc.2, hat, hatTotal, hp.2.2.2]
  rw [hselectedSum] at htotal
  linarith

private theorem normalizedCompletion_observed_margin_eq_latent
    {P : POSystem} (S : POSlateSystem P 𝒳 K) (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (x : 𝒳) (hx : 0 < S.p x)
    (hmargins :
      (∀ i, rowMass (completion x).survivor i +
          (completion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass (completion x).survivor j +
          (completion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j))
    (hNT : ∀ s0 s1 y0 y1, (completion x).neverTakerComponent s0 s1 y0 y1 =
      baselineNeverTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1)
    (hAT : ∀ s0 s1 y0 y1, (completion x).alwaysTakerComponent s0 s1 y0 y1 =
      baselineAlwaysTakerComponent
        ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
          x s0 s1 y0 y1)
    (hcompletionTotal :
      (∑ i, ∑ j, (completion x).survivor i j) +
        (∑ i, (completion x).selectedOnlyUnderZero i) +
        (∑ j, (completion x).selectedOnlyUnderOne j) +
        (completion x).neverSelectedMass =
      conditionalReal P.μ S.complierEvent (S.xEvent x))
    (hNoDefiers : NoDefiers S)
    (hlower : ∀ i, (observableCapacities S.observedLaw).lower x i =
      lowerLatentMass S x i)
    (hupper : ∀ j, (observableCapacities S.observedLaw).upper x j =
      upperLatentMass S x j) :
    ∀ z d s y, thresholdObservedTableMargin
        (normalizedCompletionCellTable S reference completion)
        x z d s y =
      conditionalReal P.μ (latentObservedTailEvent S z d s y)
        (S.xEvent x) := by
  have hselected := normalizedCompletion_selected_margin_eq_latent S reference
    completion x hx hmargins hNT hAT hNoDefiers hlower hupper
  have hunselected := normalizedCompletion_unselected_margin_eq_latent S reference
    completion x hx hmargins hNT hAT hcompletionTotal hNoDefiers hlower hupper
  intro z d s y
  cases s
  · cases y with
    | none => exact hunselected z d
    | some i =>
        rw [(thresholdObservedTableMargin_invalid
          (normalizedCompletionCellTable S reference completion) x z d).2 i,
          (latentObservedTail_invalid S x z d).1 i]
  · cases y with
    | none =>
        rw [(thresholdObservedTableMargin_invalid
          (normalizedCompletionCellTable S reference completion) x z d).1,
          (latentObservedTail_invalid S x z d).2]
    | some i => exact hselected z d i

private theorem observedLaw_singleton_of_tail_factorization
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (z d s : Bool) (y : Option (Fin K))
    (harm : 0 < P.μ.real (S.xEvent x ∩ S.zVar.event z))
    (harmMass : P.μ.real (S.xEvent x ∩ S.zVar.event z) =
      S.p x * atomInstrumentMass S x z)
    (hfactor : conditionalReal P.μ (factualObservedTailEvent S d s y)
        (S.xEvent x ∩ S.zVar.event z) =
      conditionalReal P.μ (latentObservedTailEvent S z d s y) (S.xEvent x)) :
    S.observedLaw.real {⟨x, z, d, s, y⟩} =
      S.p x * atomInstrumentMass S x z *
        conditionalReal P.μ (latentObservedTailEvent S z d s y) (S.xEvent x) := by
  unfold POSlateSystem.observedLaw
  rw [Measure.real, Measure.map_apply (measurable_observedDatum_local S)
    MeasurableSet.of_discrete]
  change P.μ.real (S.observedDatum ⁻¹' {⟨x, z, d, s, y⟩}) = _
  rw [show S.observedDatum ⁻¹' {⟨x, z, d, s, y⟩} =
      factualObservedTailEvent S d s y ∩
        (S.xEvent x ∩ S.zVar.event z) by
    ext ω
    simp [factualObservedTailEvent, POSlateSystem.observedDatum,
      POSlateSystem.xEvent, POVar.event, POSlateSystem.factualX,
      POSlateSystem.factualZ, and_assoc, and_left_comm, and_comm]]
  unfold conditionalReal at hfactor
  rw [if_pos harm] at hfactor
  calc
    P.μ.real (factualObservedTailEvent S d s y ∩
        (S.xEvent x ∩ S.zVar.event z)) =
        P.μ.real (S.xEvent x ∩ S.zVar.event z) *
          (P.μ.real (factualObservedTailEvent S d s y ∩
            (S.xEvent x ∩ S.zVar.event z)) /
              P.μ.real (S.xEvent x ∩ S.zVar.event z)) := by
          field_simp [ne_of_gt harm]
    _ = P.μ.real (S.xEvent x ∩ S.zVar.event z) *
        conditionalReal P.μ (latentObservedTailEvent S z d s y)
          (S.xEvent x) := by
      simpa [conditionalReal] using congrArg
        (fun r : ℝ ↦ P.μ.real (S.xEvent x ∩ S.zVar.event z) * r) hfactor
    _ = _ := by rw [harmMass]

private theorem observedTail_conditional_factorization
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K)
    (hIV : IVIndependence S) (hTreatment : TreatmentConsistency S)
    (hSelection : SelectionExclusion S) (hOutcome : OutcomeExclusion S)
    (x : 𝒳) (z d s : Bool) (y : Option (Fin K))
    (hx : 0 < P.μ.real (S.xEvent x))
    (harm : 0 < P.μ.real (S.xEvent x ∩ S.zVar.event z)) :
    conditionalReal P.μ (factualObservedTailEvent S d s y)
        (S.xEvent x ∩ S.zVar.event z) =
      conditionalReal P.μ (latentObservedTailEvent S z d s y) (S.xEvent x) := by
  have hCI := condIndepCFBundle_of_condIndepCF S
    (RegimedVar.ofFactual S.zVar) S.cfBundle hIV
  apply conditionalReal_eq_of_condIndepCFBundle S S.cfBundle hCI z
  · have hD := S.dVar.measurable_factual (measurableSet_singleton d)
    have hS0 := S.sVar.measurable_factual (measurableSet_singleton false)
    have hS1 := S.sVar.measurable_factual (measurableSet_singleton true)
    cases s
    · cases y with
      | none =>
          convert hD.inter hS0 using 1 <;> ext ω <;>
            simp_all [factualObservedTailEvent, POSlateSystem.factualD,
              POSlateSystem.factualS]
      | some k =>
          convert MeasurableSet.empty using 1 <;>
            ext ω <;> simp_all [factualObservedTailEvent, POSlateSystem.factualD,
              POSlateSystem.factualS, POSlateSystem.factualY, and_assoc]
    · cases y with
      | none =>
          convert MeasurableSet.empty using 1 <;> ext ω <;>
            simp_all [factualObservedTailEvent, POSlateSystem.factualD,
              POSlateSystem.factualS]
      | some k =>
          convert (hD.inter hS1).inter
            (S.yVar.measurable_factual (measurableSet_singleton k)) using 1 <;>
            ext ω <;> simp_all [factualObservedTailEvent, POSlateSystem.factualD,
              POSlateSystem.factualS, POSlateSystem.factualY, and_assoc]
  · have hD := measurable_DofZ_cfBundle S z (measurableSet_singleton d)
    have hS0 := measurable_SofD_cfBundle S d (measurableSet_singleton false)
    have hS1 := measurable_SofD_cfBundle S d (measurableSet_singleton true)
    cases s
    · cases y with
      | none =>
          convert hD.inter hS0 using 1
          · rfl
          · ext ω
            simp [latentObservedTailEvent]
      | some k =>
          convert MeasurableSet.empty using 1 <;>
            ext ω <;> simp_all [latentObservedTailEvent, and_assoc]
    · cases y with
      | none =>
          convert MeasurableSet.empty using 1 <;> ext ω <;>
            simp_all [latentObservedTailEvent]
      | some k =>
          convert (hD.inter hS1).inter
            (measurable_YofD_cfBundle S d (measurableSet_singleton k)) using 1
          · rfl
          · ext ω
            simp [latentObservedTailEvent, and_assoc]
  · filter_upwards [hTreatment, hSelection, hOutcome] with ω ht hs hy
    unfold factualObservedTailEvent latentObservedTailEvent
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hD, hS, hY⟩, hz⟩
      have hd : S.factualD ω = S.DofZ z ω := by simpa [hz] using ht
      have hs' : S.factualS ω = S.SofD d ω := by simpa [hD] using hs
      have hout : (if S.factualS ω then some (S.factualY ω) else none) =
          if S.SofD d ω then some (S.YofD d ω) else none := by
        cases hfs : S.factualS ω
        · have hsd : S.SofD d ω = false := by simpa [hfs] using hs'
          simp [hfs, hsd]
        · have hsd : S.SofD d ω = true := by simpa [hfs] using hs'
          have hyv := hy (by simpa using hfs)
          simp [hfs, hsd, hD, hyv]
      exact ⟨⟨hd.symm.trans hD, hs'.symm.trans hS, hout.symm.trans hY⟩, hz⟩
    · rintro ⟨⟨hD, hS, hY⟩, hz⟩
      have hd : S.factualD ω = S.DofZ z ω := by simpa [hz] using ht
      have hfd : S.factualD ω = d := hd.trans hD
      have hs' : S.factualS ω = S.SofD d ω := by simpa [hfd] using hs
      have hout : (if S.factualS ω then some (S.factualY ω) else none) =
          if S.SofD d ω then some (S.YofD d ω) else none := by
        cases hfs : S.factualS ω
        · have hsd : S.SofD d ω = false := by simpa [hfs] using hs'
          simp [hfs, hsd]
        · have hsd : S.SofD d ω = true := by simpa [hfs] using hs'
          have hyv := hy (by simpa using hfs)
          simp [hfs, hsd, hfd, hyv]
      exact ⟨⟨hfd, hs'.trans hS, hout.trans hY⟩, hz⟩
  · exact hx
  · exact harm

private theorem measureReal_bool_partition_observedLaw
    {P : POSystem} (f : P.Ω → Bool) (hf : Measurable f)
    (X : Set P.Ω) (hX : MeasurableSet X) :
    P.μ.real X = P.μ.real (X ∩ {ω | f ω = false}) +
      P.μ.real (X ∩ {ω | f ω = true}) := by
  have hfalse : MeasurableSet {ω | f ω = false} :=
    hf (measurableSet_singleton false)
  have htrue : MeasurableSet {ω | f ω = true} :=
    hf (measurableSet_singleton true)
  have hunion : (X ∩ {ω | f ω = false}) ∪
      (X ∩ {ω | f ω = true}) = X := by
    ext ω
    cases h : f ω <;> simp [h]
  have hdisjoint : Disjoint (X ∩ {ω | f ω = false})
      (X ∩ {ω | f ω = true}) := by
    apply Set.disjoint_left.2
    intro ω h0 h1
    simp_all
  calc
    P.μ.real X = P.μ.real ((X ∩ {ω | f ω = false}) ∪
        (X ∩ {ω | f ω = true})) := congrArg P.μ.real hunion.symm
    _ = _ := measureReal_union hdisjoint (hX.inter htrue)

private theorem observedArm_mass_factorization
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (z : Bool) (hx : 0 < S.p x) :
    P.μ.real (S.xEvent x ∩ S.zVar.event z) =
      S.p x * atomInstrumentMass S x z := by
  have hxreal : 0 < P.μ.real (S.xEvent x) := by
    simpa [POSlateSystem.p] using hx
  have hpart := measureReal_bool_partition_observedLaw S.factualZ
    S.zVar.measurable_factual (S.xEvent x)
    (S.xVar.measurable_factual (measurableSet_singleton x))
  have hprop : S.propensity x =
      P.μ.real (S.xEvent x ∩ S.zVar.event true) /
        P.μ.real (S.xEvent x) := by
    unfold POSlateSystem.propensity conditionalReal
    rw [if_pos hxreal]
    congr 2
    ext ω
    simp [POSlateSystem.xEvent, POVar.event, POSlateSystem.factualZ,
      and_comm]
  have hprop' : S.propensity x =
      P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = true}) /
        P.μ.real (S.xEvent x) := by
    rw [show {ω | S.factualZ ω = true} = S.zVar.factual ⁻¹' {true} by
      ext ω
      simp [POSlateSystem.factualZ]]
    exact hprop
  cases z
  · unfold atomInstrumentMass
    simp only [Bool.false_eq_true, ↓reduceIte]
    change P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = false}) = _
    change P.μ.real (S.xEvent x) =
      P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = false}) +
        P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = true}) at hpart
    rw [hprop']
    change P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = false}) =
      P.μ.real (S.xEvent x) *
        (1 - P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = true}) /
          P.μ.real (S.xEvent x))
    field_simp [ne_of_gt hxreal]
    linarith
  · unfold atomInstrumentMass
    simp only [↓reduceIte]
    change P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = true}) = _
    rw [hprop']
    change P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = true}) =
      P.μ.real (S.xEvent x) *
        (P.μ.real (S.xEvent x ∩ {ω | S.factualZ ω = true}) /
          P.μ.real (S.xEvent x))
    field_simp [ne_of_gt hxreal]

private theorem observedArm_positive
    {P : POSystem} (S : POSlateSystem P 𝒳 K) {εZ : ℝ}
    (hOverlap : InstrumentOverlap S εZ)
    (x : 𝒳) (hx : 0 < S.p x) (z : Bool) :
    0 < P.μ.real (S.xEvent x ∩ S.zVar.event z) := by
  rw [observedArm_mass_factorization S x z hx]
  have hπ := hOverlap.2.2 x hx
  have hε : 0 < εZ := hOverlap.1
  have hpz : 0 < atomInstrumentMass S x z := by
    unfold atomInstrumentMass
    cases z
    · simp only [Bool.false_eq_true, ↓reduceIte]
      linarith [hπ.2]
    · simp only [↓reduceIte]
      linarith [hπ.1]
  positivity

private theorem observedLaw_singleton_latent_factorization
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) {εZ : ℝ}
    (hIV : IVIndependence S) (hTreatment : TreatmentConsistency S)
    (hSelection : SelectionExclusion S) (hOutcome : OutcomeExclusion S)
    (hOverlap : InstrumentOverlap S εZ)
    (x : 𝒳) (z d s : Bool) (y : Option (Fin K))
    (hx : 0 < S.p x) :
    S.observedLaw.real {⟨x, z, d, s, y⟩} =
      S.p x * atomInstrumentMass S x z *
        conditionalReal P.μ (latentObservedTailEvent S z d s y)
          (S.xEvent x) := by
  apply observedLaw_singleton_of_tail_factorization S x z d s y
  · exact observedArm_positive S hOverlap x hx z
  · exact observedArm_mass_factorization S x z hx
  · apply observedTail_conditional_factorization S hIV hTreatment hSelection hOutcome
    · simpa [POSlateSystem.p] using hx
    · exact observedArm_positive S hOverlap x hx z

private theorem canonicalThresholdCandidate_observedLaw_eq_of_positive_singletons
    {P : POSystem} (S : POSlateSystem P 𝒳 K)
    (T : ThresholdCellTable 𝒳 K)
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : T.Nonnegative) (hTnormalized : T.Normalized)
    (hmatch : ∀ o : ObservedDatum 𝒳 K, 0 < S.p o.cell →
      S.observedLaw.real {o} =
        S.p o.cell * atomInstrumentMass S o.cell o.instrument *
          thresholdObservedTableMargin T o.cell o.instrument o.treatment
            o.selected o.outcome) :
    let W := canonicalThresholdCandidate S T hp hprop hTnonnegative hTnormalized
    W.slate.observedLaw = S.observedLaw := by
  letI : IsProbabilityMeasure S.observedLaw :=
    Measure.isProbabilityMeasure_map (measurable_observedDatum_local S).aemeasurable
  apply canonicalThresholdCandidate_observedLaw_eq_of_singletons
  intro o
  by_cases ho : 0 < S.p o.cell
  · rw [thresholdPastedWeight_observedSum]
    exact hmatch o ho
  · have hp0 : S.p o.cell = 0 := le_antisymm (not_lt.mp ho) (hp o.cell)
    have hlaw0 : S.observedLaw.real {o} = 0 := by
      apply le_antisymm
      · calc
          S.observedLaw.real {o} ≤ S.observedLaw.real {q | q.cell = o.cell} := by
            apply measureReal_mono
            intro q hq
            simpa using congrArg ObservedDatum.cell hq
            finiteness
          _ = 0 := (observedLaw_cellProbability S o.cell).trans hp0
      · exact measureReal_nonneg
    rw [hlaw0, thresholdPastedWeight_observedSum, hp0]
    ring

private theorem canonicalThresholdCandidate_completion_observedLaw_eq
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) {εZ : ℝ}
    (hIV : IVIndependence S) (hTreatment : TreatmentConsistency S)
    (hSelection : SelectionExclusion S) (hOutcome : OutcomeExclusion S)
    (hOverlap : InstrumentOverlap S εZ) (hNoDefiers : NoDefiers S)
    (reference : Fin K)
    (completion : 𝒳 → ThresholdLatentCompletion P S.observedLaw
      (observableCapacities S.observedLaw))
    (hp : ∀ x, 0 ≤ S.p x)
    (hprop : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1)
    (hTnonnegative : (normalizedCompletionCellTable S reference completion).Nonnegative)
    (hTnormalized : (normalizedCompletionCellTable S reference completion).Normalized)
    (hmargins : ∀ x,
      (∀ i, rowMass (completion x).survivor i +
          (completion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass (completion x).survivor j +
          (completion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j))
    (hNT : ∀ x s0 s1 y0 y1,
      (completion x).neverTakerComponent s0 s1 y0 y1 =
        baselineNeverTakerComponent
          ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
            x s0 s1 y0 y1)
    (hAT : ∀ x s0 s1 y0 y1,
      (completion x).alwaysTakerComponent s0 s1 y0 y1 =
        baselineAlwaysTakerComponent
          ({ system := P, slate := S } : FullLawCandidate P 𝒳 K)
            x s0 s1 y0 y1)
    (hcompletionTotal : ∀ x, 0 < S.p x →
      (∑ i, ∑ j, (completion x).survivor i j) +
        (∑ i, (completion x).selectedOnlyUnderZero i) +
        (∑ j, (completion x).selectedOnlyUnderOne j) +
        (completion x).neverSelectedMass =
      conditionalReal P.μ S.complierEvent (S.xEvent x))
    (hlower : ∀ x, 0 < S.p x → ∀ i,
      (observableCapacities S.observedLaw).lower x i = lowerLatentMass S x i)
    (hupper : ∀ x, 0 < S.p x → ∀ j,
      (observableCapacities S.observedLaw).upper x j = upperLatentMass S x j) :
    (canonicalThresholdCandidate S
      (normalizedCompletionCellTable S reference completion) hp hprop
      hTnonnegative hTnormalized).slate.observedLaw = S.observedLaw := by
  apply canonicalThresholdCandidate_observedLaw_eq_of_positive_singletons S
    (normalizedCompletionCellTable S reference completion) hp hprop
    hTnonnegative hTnormalized
  intro o ho
  rw [observedLaw_singleton_latent_factorization S hIV hTreatment hSelection
    hOutcome hOverlap o.cell o.instrument o.treatment o.selected o.outcome ho]
  rw [normalizedCompletion_observed_margin_eq_latent S reference completion
    o.cell ho (hmargins o.cell) (hNT o.cell) (hAT o.cell)
    (hcompletionTotal o.cell ho) hNoDefiers (hlower o.cell ho) (hupper o.cell ho)]


private theorem observedLaw_propensity {P : POSystem}
    (S : POSlateSystem P 𝒳 K) (x : 𝒳) :
    conditionalReal S.observedLaw {o | o.instrument = true} {o | o.cell = x} =
      S.propensity x := by
  unfold POSlateSystem.observedLaw
  rw [conditionalReal_map P.μ S.observedDatum (measurable_observedDatum_local S)
    _ _ MeasurableSet.of_discrete MeasurableSet.of_discrete]
  unfold POSlateSystem.propensity
  congr 2 <;> ext ω <;> rfl

/-- Given [the stated hypotheses](hyp:hlaw), [the observed law equals transfers p propensity property holds](goal). -/
theorem observedLaw_eq_transfers_p_propensity
    {P Q : POSystem} (S : POSlateSystem P 𝒳 K) (R : POSlateSystem Q 𝒳 K)
    (hlaw : R.observedLaw = S.observedLaw) :
    (∀ x, R.p x = S.p x) ∧ (∀ x, R.propensity x = S.propensity x) := by
  constructor
  · intro x
    rw [← observedLaw_cellProbability R x, hlaw, observedLaw_cellProbability S x]
  · intro x
    rw [← observedLaw_propensity R x, hlaw, observedLaw_propensity S x]

private theorem instrumentOverlap_of_observedLaw_eq
    {P Q : POSystem} (S : POSlateSystem P 𝒳 K) (R : POSlateSystem Q 𝒳 K)
    (εZ : ℝ) (hS : InstrumentOverlap S εZ)
    (hlaw : R.observedLaw = S.observedLaw) : InstrumentOverlap R εZ := by
  rcases observedLaw_eq_transfers_p_propensity S R hlaw with ⟨hp, hprop⟩
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro x hx
  rw [hp x] at hx
  simpa [hprop x] using hS.2.2 x hx

private theorem positiveAggregateSurvivors_of_observedLaw_eq
    {P Q : POSystem} (S : POSlateSystem P 𝒳 K) (R : POSlateSystem Q 𝒳 K)
    (hS : PositiveAggregateSurvivors (observableCapacities S.observedLaw) S.p)
    (hlaw : R.observedLaw = S.observedLaw) :
    PositiveAggregateSurvivors (observableCapacities R.observedLaw) R.p := by
  have hp := (observedLaw_eq_transfers_p_propensity S R hlaw).1
  have hp' : R.p = S.p := funext hp
  unfold PositiveAggregateSurvivors at hS ⊢
  rw [hlaw, hp']
  exact hS

/-- Every compatible observed law has lower- and upper-attaining full latent laws in the maintained model class, including tie and zero-survivor cells. [the stated conclusion follows](goal). -/
-- @node: thm:full-law-endpoint-attainment
theorem full_law_endpoint_attainment
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (_hIV : IVIndependence S) (_hNoDefiers : NoDefiers S)
    (_hMonotone : WeakSelectionMonotonicity S d)
    (compatible : TieSafeSurvivorModel S εZ d) :
    let c := observableCapacities S.observedLaw
    let hIdentification := capacity_identification S εZ d compatible.ivIndependence
      compatible.treatmentConsistency compatible.selectionExclusion compatible.outcomeExclusion
      compatible.instrumentOverlap compatible.noDefiers compatible.weakSelectionMonotonicity
    let hValid : ValidCapacities c := hIdentification.1.2
    let hp : ∀ x, 0 ≤ S.p x := hIdentification.2.1
    let hMass : 0 < c.aggregateMass S.p := compatible.positiveAggregateSurvivors
    ∃ baseline : CompatibleBaseline P S.observedLaw c,
      let flows := fun x => thresholdFlow baseline hValid x
      ∃ (PL : POSystem) (SL : POSlateSystem PL 𝒳 K)
        (PU : POSystem) (SU : POSlateSystem PU 𝒳 K),
        IsEndpointWitness S.observedLaw εZ d
          (c.endpointMap S.p S.observedLaw rfl (p_eq_observedCellWeights S)
            hValid hp hMass (observedLawDomain S)).endpoints.1 PL SL ∧
        IsEndpointWitness S.observedLaw εZ d
          (c.endpointMap S.p S.observedLaw rfl (p_eq_observedCellWeights S)
            hValid hp hMass (observedLawDomain S)).endpoints.2 PU SU ∧
        (∀ x, RealizesThresholdLatentCompletion
          ({ system := PL, slate := SL } : FullLawCandidate P 𝒳 K) x
            (flows x).lower) ∧
        (∀ x, RealizesThresholdLatentCompletion
          ({ system := PU, slate := SU } : FullLawCandidate P 𝒳 K) x
        (flows x).upper) := by
  dsimp only
  have hIdentification := capacity_identification S εZ d compatible.ivIndependence
    compatible.treatmentConsistency compatible.selectionExclusion compatible.outcomeExclusion
    compatible.instrumentOverlap compatible.noDefiers compatible.weakSelectionMonotonicity
  let baseline := originalCompatibleBaseline S εZ d compatible
  refine ⟨baseline, ?_⟩
  let reference : Fin K := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) S.hK⟩
  let lowerCompletion :=
    (fun x => (thresholdFlow baseline hIdentification.1.2 x).lower)
  let upperCompletion :=
    (fun x => (thresholdFlow baseline hIdentification.1.2 x).upper)
  have hselectedMarginsLower : ∀ x,
      (∀ i, rowMass (lowerCompletion x).survivor i +
          (lowerCompletion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
        (∀ j, columnMass (lowerCompletion x).survivor j +
          (lowerCompletion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j) := by
    intro x
    simpa [lowerCompletion, thresholdFlow, thresholdLatentCompletion] using
      thresholdLatentCompletion_selected_margins baseline hIdentification.1.2 x
        (thresholdFlowLower (observableCapacities S.observedLaw)
          hIdentification.1.2 x)
        (thresholdFlow_spec baseline hIdentification.1.2 x).1
  have hselectedMarginsUpper : ∀ x,
      (∀ i, rowMass (upperCompletion x).survivor i +
          (upperCompletion x).selectedOnlyUnderZero i =
            (observableCapacities S.observedLaw).lower x i) ∧
        (∀ j, columnMass (upperCompletion x).survivor j +
          (upperCompletion x).selectedOnlyUnderOne j =
            (observableCapacities S.observedLaw).upper x j) := by
    intro x
    simpa [upperCompletion, thresholdFlow, thresholdLatentCompletion] using
      thresholdLatentCompletion_selected_margins baseline hIdentification.1.2 x
        (thresholdFlowUpper (observableCapacities S.observedLaw)
          hIdentification.1.2 x)
        (thresholdFlow_spec baseline hIdentification.1.2 x).2.2.1
  let lowerTable := normalizedCompletionCellTable S reference lowerCompletion
  let upperTable := normalizedCompletionCellTable S reference upperCompletion
  have hrawNonnegative :
      (thresholdCompletionCellTable reference lowerCompletion).Nonnegative ∧
      (thresholdCompletionCellTable reference upperCompletion).Nonnegative := by
    exact thresholdFlow_completionCellTables_nonnegative baseline hIdentification.1.2 reference
  have htablesNonnegative : lowerTable.Nonnegative ∧ upperTable.Nonnegative := by
    exact ⟨normalizedCompletionCellTable_nonnegative S reference lowerCompletion
        hrawNonnegative.1,
      normalizedCompletionCellTable_nonnegative S reference upperCompletion
        hrawNonnegative.2⟩
  have htablesNormalized : lowerTable.Normalized ∧ upperTable.Normalized := by
    constructor
    · apply normalizedCompletionCellTable_normalized
      intro x hx
      apply (thresholdFlow_completionCellTables_total baseline hIdentification.1.2
        reference x ?_).1
      simpa [baseline, originalCompatibleBaseline] using
        baseline_principal_partition S x compatible.noDefiers hx
    · apply normalizedCompletionCellTable_normalized
      intro x hx
      apply (thresholdFlow_completionCellTables_total baseline hIdentification.1.2
        reference x ?_).2
      simpa [baseline, originalCompatibleBaseline] using
        baseline_principal_partition S x compatible.noDefiers hx
  have hpropensity : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1 :=
    propensity_mem_unitInterval S
  let WL := canonicalThresholdCandidate S lowerTable hIdentification.2.1 hpropensity
    htablesNonnegative.1 htablesNormalized.1
  let WU := canonicalThresholdCandidate S upperTable hIdentification.2.1 hpropensity
    htablesNonnegative.2 htablesNormalized.2
  have hObservedLawLower : WL.slate.observedLaw = S.observedLaw := by
    apply canonicalThresholdCandidate_completion_observedLaw_eq S
      compatible.ivIndependence compatible.treatmentConsistency
      compatible.selectionExclusion compatible.outcomeExclusion
      compatible.instrumentOverlap compatible.noDefiers reference lowerCompletion
      hIdentification.2.1 hpropensity
    · exact hselectedMarginsLower
    · intro x s0 s1 y0 y1
      simp [lowerCompletion, thresholdFlow, thresholdLatentCompletion,
        baseline, originalCompatibleBaseline]
    · intro x s0 s1 y0 y1
      simp [lowerCompletion, thresholdFlow, thresholdLatentCompletion,
        baseline, originalCompatibleBaseline]
    · intro x hx
      have hc := thresholdLatentCompletion_complier_total baseline
        hIdentification.1.2 x
        (thresholdFlowLower (observableCapacities S.observedLaw)
          hIdentification.1.2 x)
        (thresholdFlow_spec baseline hIdentification.1.2 x).1
      simpa [lowerCompletion, thresholdFlow, thresholdLatentCompletion,
        baseline, originalCompatibleBaseline] using hc
    · exact hIdentification.2.2.1
    · exact hIdentification.2.2.2.1
  have hObservedLawUpper : WU.slate.observedLaw = S.observedLaw := by
    apply canonicalThresholdCandidate_completion_observedLaw_eq S
      compatible.ivIndependence compatible.treatmentConsistency
      compatible.selectionExclusion compatible.outcomeExclusion
      compatible.instrumentOverlap compatible.noDefiers reference upperCompletion
      hIdentification.2.1 hpropensity
    · exact hselectedMarginsUpper
    · intro x s0 s1 y0 y1
      simp [upperCompletion, thresholdFlow, thresholdLatentCompletion,
        baseline, originalCompatibleBaseline]
    · intro x s0 s1 y0 y1
      simp [upperCompletion, thresholdFlow, thresholdLatentCompletion,
        baseline, originalCompatibleBaseline]
    · intro x hx
      have hc := thresholdLatentCompletion_complier_total baseline
        hIdentification.1.2 x
        (thresholdFlowUpper (observableCapacities S.observedLaw)
          hIdentification.1.2 x)
        (thresholdFlow_spec baseline hIdentification.1.2 x).2.2.1
      simpa [upperCompletion, thresholdFlow, thresholdLatentCompletion,
        baseline, originalCompatibleBaseline] using hc
    · exact hIdentification.2.2.1
    · exact hIdentification.2.2.2.1
  have hOverlapLower : InstrumentOverlap WL.slate εZ :=
    instrumentOverlap_of_observedLaw_eq S WL.slate εZ
      compatible.instrumentOverlap hObservedLawLower
  have hOverlapUpper : InstrumentOverlap WU.slate εZ :=
    instrumentOverlap_of_observedLaw_eq S WU.slate εZ
      compatible.instrumentOverlap hObservedLawUpper
  have hPositiveLower : PositiveAggregateSurvivors
      (observableCapacities WL.slate.observedLaw) WL.slate.p :=
    positiveAggregateSurvivors_of_observedLaw_eq S WL.slate
      compatible.positiveAggregateSurvivors hObservedLawLower
  have hPositiveUpper : PositiveAggregateSurvivors
      (observableCapacities WU.slate.observedLaw) WU.slate.p :=
    positiveAggregateSurvivors_of_observedLaw_eq S WU.slate
      compatible.positiveAggregateSurvivors hObservedLawUpper
  have hconsistencyLower : TreatmentConsistency WL.slate ∧
      SelectionExclusion WL.slate ∧ OutcomeExclusion WL.slate := by
    simpa [WL, lowerTable] using canonicalThresholdCandidate_consistency S lowerTable
      hIdentification.2.1 hpropensity htablesNonnegative.1 htablesNormalized.1
  have hconsistencyUpper : TreatmentConsistency WU.slate ∧
      SelectionExclusion WU.slate ∧ OutcomeExclusion WU.slate := by
    simpa [WU, upperTable] using canonicalThresholdCandidate_consistency S upperTable
      hIdentification.2.1 hpropensity htablesNonnegative.2 htablesNormalized.2
  have hnoDefiersLower : NoDefiers WL.slate := by
    apply canonicalThresholdCandidate_noDefiers S lowerTable hIdentification.2.1
      hpropensity htablesNonnegative.1 htablesNormalized.1
    simpa [lowerTable] using
      normalizedCompletionCellTable_noDefiers S reference lowerCompletion
  have hnoDefiersUpper : NoDefiers WU.slate := by
    apply canonicalThresholdCandidate_noDefiers S upperTable hIdentification.2.1
      hpropensity htablesNonnegative.2 htablesNormalized.2
    simpa [upperTable] using
      normalizedCompletionCellTable_noDefiers S reference upperCompletion
  have htableDirections (completion : ∀ x, ThresholdLatentCompletion P
      S.observedLaw (observableCapacities S.observedLaw))
      (hzero : ∀ x, 0 < S.p x → ∀ i, d x = true →
        (completion x).selectedOnlyUnderZero i = 0)
      (hone : ∀ x, 0 < S.p x → ∀ j, d x = false →
        (completion x).selectedOnlyUnderOne j = 0) :
      (∀ x y0 y1, d x = true →
        normalizedCompletionCellTable S reference completion x false true true false y0 y1 = 0) ∧
      (∀ x y0 y1, d x = false →
        normalizedCompletionCellTable S reference completion x false true false true y0 y1 = 0) := by
    constructor
    · intro x y0 y1 hd
      by_cases hx : 0 < S.p x
      · simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
          hzero x hx y0 hd]
      · simp [normalizedCompletionCellTable, hx]
    · intro x y0 y1 hd
      by_cases hx : 0 < S.p x
      · simp [normalizedCompletionCellTable, hx, thresholdCompletionCellTable,
          hone x hx y1 hd]
      · simp [normalizedCompletionCellTable, hx]
  have hmonotoneLower : WeakSelectionMonotonicity WL.slate d := by
    apply canonicalThresholdCandidate_weakSelectionMonotonicity S lowerTable
      hIdentification.2.1 hpropensity htablesNonnegative.1 htablesNormalized.1 d
    · simpa [lowerTable] using (htableDirections lowerCompletion
        (by
          intro x hx i hd
          have hn : ¬ (observableCapacities S.observedLaw).gap x < 0 := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [lowerCompletion, thresholdFlow, thresholdLatentCompletion, hn])
        (by
          intro x hx j hd
          have hn : ¬ 0 < (observableCapacities S.observedLaw).gap x := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [lowerCompletion, thresholdFlow, thresholdLatentCompletion, hn])).1
    · simpa [lowerTable] using (htableDirections lowerCompletion
        (by
          intro x hx i hd
          have hn : ¬ (observableCapacities S.observedLaw).gap x < 0 := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [lowerCompletion, thresholdFlow, thresholdLatentCompletion, hn]
        ) (by
          intro x hx j hd
          have hn : ¬ 0 < (observableCapacities S.observedLaw).gap x := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [lowerCompletion, thresholdFlow, thresholdLatentCompletion, hn]
        )).2
  have hmonotoneUpper : WeakSelectionMonotonicity WU.slate d := by
    apply canonicalThresholdCandidate_weakSelectionMonotonicity S upperTable
      hIdentification.2.1 hpropensity htablesNonnegative.2 htablesNormalized.2 d
    · simpa [upperTable] using (htableDirections upperCompletion
        (by
          intro x hx i hd
          have hn : ¬ (observableCapacities S.observedLaw).gap x < 0 := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [upperCompletion, thresholdFlow, thresholdLatentCompletion, hn])
        (by
          intro x hx j hd
          have hn : ¬ 0 < (observableCapacities S.observedLaw).gap x := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [upperCompletion, thresholdFlow, thresholdLatentCompletion, hn])).1
    · simpa [upperTable] using (htableDirections upperCompletion
        (by
          intro x hx i hd
          have hn : ¬ (observableCapacities S.observedLaw).gap x < 0 := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [upperCompletion, thresholdFlow, thresholdLatentCompletion, hn])
        (by
          intro x hx j hd
          have hn : ¬ 0 < (observableCapacities S.observedLaw).gap x := by
            intro hg
            have := hIdentification.2.2.2.2.2.2.1 x hx hg
            simp [hd] at this
          simp [upperCompletion, thresholdFlow, thresholdLatentCompletion, hn])).2
  have hrealizesLower : ∀ x, RealizesThresholdLatentCompletion WL x
      (thresholdFlow baseline hIdentification.1.2 x).lower := by
    intro x
    by_cases hx : 0 < S.p x
    · simpa [WL, lowerTable, lowerCompletion] using
        canonicalThresholdCandidate_realizes_of_pos S reference lowerCompletion
          hIdentification.2.1 hpropensity htablesNonnegative.1
          htablesNormalized.1 x hx
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      have hdata := originalCompatibleBaseline_data_zero S εZ d compatible x hx0
      have hflow := thresholdFlow_isZero_of_data_zero baseline hIdentification.1.2 x
        hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2
      simpa [WL, lowerTable, lowerCompletion] using
        canonicalThresholdCandidate_realizes_of_zero S reference lowerCompletion
          hIdentification.2.1 hpropensity htablesNonnegative.1
          htablesNormalized.1 x hx0 hflow.1
  have hrealizesUpper : ∀ x, RealizesThresholdLatentCompletion WU x
      (thresholdFlow baseline hIdentification.1.2 x).upper := by
    intro x
    by_cases hx : 0 < S.p x
    · simpa [WU, upperTable, upperCompletion] using
        canonicalThresholdCandidate_realizes_of_pos S reference upperCompletion
          hIdentification.2.1 hpropensity htablesNonnegative.2
          htablesNormalized.2 x hx
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      have hdata := originalCompatibleBaseline_data_zero S εZ d compatible x hx0
      have hflow := thresholdFlow_isZero_of_data_zero baseline hIdentification.1.2 x
        hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2
      simpa [WU, upperTable, upperCompletion] using
        canonicalThresholdCandidate_realizes_of_zero S reference upperCompletion
          hIdentification.2.1 hpropensity htablesNonnegative.2
          htablesNormalized.2 x hx0 hflow.2
  have htableSurvivorLower : ∀ x, 0 < S.p x →
      tableSurvivorCoupling (lowerTable x) = (lowerCompletion x).survivor := by
    intro x hx
    funext i j
    simp [lowerTable, normalizedCompletionCellTable, hx,
      tableSurvivorCoupling, thresholdCompletionCellTable]
  have htableSurvivorUpper : ∀ x, 0 < S.p x →
      tableSurvivorCoupling (upperTable x) = (upperCompletion x).survivor := by
    intro x hx
    funext i j
    simp [upperTable, normalizedCompletionCellTable, hx,
      tableSurvivorCoupling, thresholdCompletionCellTable]
  have hmassTableLower :
      (∑ x, S.p x * totalMass (tableSurvivorCoupling (lowerTable x))) =
        (observableCapacities S.observedLaw).aggregateMass S.p := by
    unfold Capacities.aggregateMass
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < S.p x
    · rw [htableSurvivorLower x hx]
      rw [(thresholdFlow_spec baseline hIdentification.1.2 x).1.2.2.2]
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      simp [hx0]
  have hmassTableUpper :
      (∑ x, S.p x * totalMass (tableSurvivorCoupling (upperTable x))) =
        (observableCapacities S.observedLaw).aggregateMass S.p := by
    unfold Capacities.aggregateMass
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < S.p x
    · rw [htableSurvivorUpper x hx]
      rw [(thresholdFlow_spec baseline hIdentification.1.2 x).2.2.1.2.2.2]
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      simp [hx0]
  have hbenefitTableLower :
      (∑ x, S.p x * benefitMass (tableSurvivorCoupling (lowerTable x))) =
        ∑ x, S.p x * (observableCapacities S.observedLaw).benefitLower x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < S.p x
    · rw [htableSurvivorLower x hx]
      rw [(thresholdFlow_spec baseline hIdentification.1.2 x).2.1]
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      simp [hx0]
  have hbenefitTableUpper :
      (∑ x, S.p x * benefitMass (tableSurvivorCoupling (upperTable x))) =
        ∑ x, S.p x * (observableCapacities S.observedLaw).benefitUpper x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < S.p x
    · rw [htableSurvivorUpper x hx]
      rw [(thresholdFlow_spec baseline hIdentification.1.2 x).2.2.2.1]
    · have hx0 : S.p x = 0 :=
        le_antisymm (not_lt.mp hx) (hIdentification.2.1 x)
      simp [hx0]
  have hbenefitLower : benefitProbability WL.slate =
      ((observableCapacities S.observedLaw).endpointMap S.p S.observedLaw rfl
        (p_eq_observedCellWeights S) hIdentification.1.2 hIdentification.2.1
        compatible.positiveAggregateSurvivors (observedLawDomain S)).endpoints.1 := by
    unfold benefitProbability
    change benefitProbabilityOf WL = _
    have h := canonicalThresholdCandidate_benefitProbabilityOf S lowerTable
      hIdentification.2.1 hpropensity htablesNonnegative.1 htablesNormalized.1
      (hmassTableLower.symm ▸ compatible.positiveAggregateSurvivors)
    rw [show WL = canonicalThresholdCandidate S lowerTable hIdentification.2.1
      hpropensity htablesNonnegative.1 htablesNormalized.1 from rfl]
    simpa [Capacities.endpointMap, hmassTableLower, hbenefitTableLower] using h
  have hbenefitUpper : benefitProbability WU.slate =
      ((observableCapacities S.observedLaw).endpointMap S.p S.observedLaw rfl
        (p_eq_observedCellWeights S) hIdentification.1.2 hIdentification.2.1
        compatible.positiveAggregateSurvivors (observedLawDomain S)).endpoints.2 := by
    unfold benefitProbability
    change benefitProbabilityOf WU = _
    have h := canonicalThresholdCandidate_benefitProbabilityOf S upperTable
      hIdentification.2.1 hpropensity htablesNonnegative.2 htablesNormalized.2
      (hmassTableUpper.symm ▸ compatible.positiveAggregateSurvivors)
    rw [show WU = canonicalThresholdCandidate S upperTable hIdentification.2.1
      hpropensity htablesNonnegative.2 htablesNormalized.2 from rfl]
    simpa [Capacities.endpointMap, hmassTableUpper, hbenefitTableUpper] using h
  refine ⟨WL.system, WL.slate, WU.system, WU.slate, ?_⟩
  have hendpoints :
      IsEndpointWitness S.observedLaw εZ d
          ((observableCapacities S.observedLaw).endpointMap S.p S.observedLaw rfl
            (p_eq_observedCellWeights S) hIdentification.1.2 hIdentification.2.1
            compatible.positiveAggregateSurvivors (observedLawDomain S)).endpoints.1
          WL.system WL.slate ∧
        IsEndpointWitness S.observedLaw εZ d
          ((observableCapacities S.observedLaw).endpointMap S.p S.observedLaw rfl
            (p_eq_observedCellWeights S) hIdentification.1.2 hIdentification.2.1
            compatible.positiveAggregateSurvivors (observedLawDomain S)).endpoints.2
          WU.system WU.slate := by
    constructor
    · letI : StandardBorelSpace WL.system.Ω := WL.slate.borel
      dsimp [IsEndpointWitness]
      refine ⟨?_, hObservedLawLower, hbenefitLower⟩
      refine
        { ivIndependence := ?_
          treatmentConsistency := hconsistencyLower.1
          selectionExclusion := hconsistencyLower.2.1
          outcomeExclusion := hconsistencyLower.2.2
          instrumentOverlap := hOverlapLower
          noDefiers := hnoDefiersLower
          weakSelectionMonotonicity := hmonotoneLower
          positiveAggregateSurvivors := hPositiveLower }
      simpa [WL, lowerTable] using
        canonicalThresholdCandidate_ivIndependence S lowerTable
          hIdentification.2.1 hpropensity htablesNonnegative.1 htablesNormalized.1
    · letI : StandardBorelSpace WU.system.Ω := WU.slate.borel
      dsimp [IsEndpointWitness]
      refine ⟨?_, hObservedLawUpper, hbenefitUpper⟩
      refine
        { ivIndependence := ?_
          treatmentConsistency := hconsistencyUpper.1
          selectionExclusion := hconsistencyUpper.2.1
          outcomeExclusion := hconsistencyUpper.2.2
          instrumentOverlap := hOverlapUpper
          noDefiers := hnoDefiersUpper
          weakSelectionMonotonicity := hmonotoneUpper
          positiveAggregateSurvivors := hPositiveUpper }
      simpa [WU, upperTable] using
        canonicalThresholdCandidate_ivIndependence S upperTable
          hIdentification.2.1 hpropensity htablesNonnegative.2 htablesNormalized.2
  exact ⟨hendpoints.1, hendpoints.2, hrealizesLower, hrealizesUpper⟩
  -- @realizes P^L(lower endpoint-attaining full law)
  -- @realizes P^U(upper endpoint-attaining full law)

/-- Every product family of branch-free exact-mass couplings is realized by a
single compatible canonical full law.  The last equality records its aggregate
strict-benefit probability and is the affine bridge used for interpolation. -/
private theorem conditionalReal_mono_left_local {Q : POSystem}
    {A B C : Set Q.Ω} (hAB : A ⊆ B) :
    conditionalReal Q.μ A C ≤ conditionalReal Q.μ B C := by
  unfold conditionalReal
  split_ifs
  · exact div_le_div_of_nonneg_right
      (measureReal_mono (Set.inter_subset_inter_left C hAB) (measure_ne_top _ _))
      measureReal_nonneg
  · exact le_rfl

private theorem measurableSet_complierEvent_local {P₀ : POSystem}
    (W : FullLawCandidate P₀ 𝒳 K) : MeasurableSet W.slate.complierEvent := by
  unfold POSlateSystem.complierEvent
  exact ((W.slate.dVar.measurable_cfUnder W.slate.zVar false)
    (measurableSet_singleton false)).inter
    ((W.slate.dVar.measurable_cfUnder W.slate.zVar true)
      (measurableSet_singleton true))

private theorem fullLawSurvivorCoupling_row_sum
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) (i : Fin K) :
    rowMass (fullLawSurvivorCoupling W x) i =
      conditionalReal W.system.μ
        {ω | W.slate.Y0 ω = i ∧ W.slate.S0 ω = true ∧
          W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
        (W.slate.xEvent x) := by
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  unfold rowMass fullLawSurvivorCoupling
  rw [← conditionalReal_iUnion_fintype]
  · congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, h0, h1, hs0, hs1, hc⟩
      exact ⟨h0, hs0, hs1, hc⟩
    · rintro ⟨h0, hs0, hs1, hc⟩
      exact ⟨W.slate.Y1 ω, h0, rfl, hs0, hs1, hc⟩
  · intro j
    convert ((((W.slate.yVar.measurable_cfUnder W.slate.dVar false)
      (measurableSet_singleton i)).inter
      ((W.slate.yVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton j))).inter
      ((W.slate.sVar.measurable_cfUnder W.slate.dVar false)
        (measurableSet_singleton true))).inter
      (((W.slate.sVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton true)).inter
        (measurableSet_complierEvent_local W)) using 1 <;>
      ext ω <;> simp [POSlateSystem.Y0, POSlateSystem.Y1,
        POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.YofD,
        POSlateSystem.SofD, and_assoc]
  · exact W.slate.xVar.measurable_factual (measurableSet_singleton x)
  · intro j k hjk
    apply Set.disjoint_left.2
    intro ω hj hk
    simp only [Set.mem_setOf_eq] at hj hk
    exact hjk (hj.2.1.symm.trans hk.2.1)

private theorem fullLawSurvivorCoupling_column_sum
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) (j : Fin K) :
    columnMass (fullLawSurvivorCoupling W x) j =
      conditionalReal W.system.μ
        {ω | W.slate.Y1 ω = j ∧ W.slate.S0 ω = true ∧
          W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
        (W.slate.xEvent x) := by
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  unfold columnMass fullLawSurvivorCoupling
  rw [← conditionalReal_iUnion_fintype]
  · congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, h0, h1, hs0, hs1, hc⟩
      exact ⟨h1, hs0, hs1, hc⟩
    · rintro ⟨h1, hs0, hs1, hc⟩
      exact ⟨W.slate.Y0 ω, rfl, h1, hs0, hs1, hc⟩
  · intro i
    convert ((((W.slate.yVar.measurable_cfUnder W.slate.dVar false)
      (measurableSet_singleton i)).inter
      ((W.slate.yVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton j))).inter
      ((W.slate.sVar.measurable_cfUnder W.slate.dVar false)
        (measurableSet_singleton true))).inter
      (((W.slate.sVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton true)).inter
        (measurableSet_complierEvent_local W)) using 1 <;>
      ext ω <;> simp [POSlateSystem.Y0, POSlateSystem.Y1,
        POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.YofD,
        POSlateSystem.SofD, and_assoc]
  · exact W.slate.xVar.measurable_factual (measurableSet_singleton x)
  · intro i k hik
    apply Set.disjoint_left.2
    intro ω hi hk
    simp only [Set.mem_setOf_eq] at hi hk
    exact hik (hi.1.symm.trans hk.1)

private theorem fullLawSurvivorCoupling_total
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) :
    totalMass (fullLawSurvivorCoupling W x) = survivorComplierMass W.slate x := by
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  rw [← sum_rowMass_eq_totalMass]
  simp_rw [fullLawSurvivorCoupling_row_sum]
  rw [← conditionalReal_iUnion_fintype]
  · unfold survivorComplierMass
    congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hs0, hs1, hc⟩
      exact ⟨hs0, hs1, hc⟩
    · rintro ⟨hs0, hs1, hc⟩
      exact ⟨W.slate.Y0 ω, rfl, hs0, hs1, hc⟩
  · intro i
    convert (((W.slate.yVar.measurable_cfUnder W.slate.dVar false)
      (measurableSet_singleton i)).inter
      ((W.slate.sVar.measurable_cfUnder W.slate.dVar false)
        (measurableSet_singleton true))).inter
      (((W.slate.sVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton true)).inter
        (measurableSet_complierEvent_local W)) using 1 <;>
      ext ω <;> simp [POSlateSystem.Y0, POSlateSystem.S0,
        POSlateSystem.S1, POSlateSystem.YofD, POSlateSystem.SofD, and_assoc]
  · exact W.slate.xVar.measurable_factual (measurableSet_singleton x)
  · intro i j hij
    apply Set.disjoint_left.2
    intro ω hi hj
    simp only [Set.mem_setOf_eq] at hi hj
    exact hij (hi.1.symm.trans hj.1)

private theorem fullLawSurvivorCoupling_benefit
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) :
    benefitMass (fullLawSurvivorCoupling W x) =
      conditionalReal W.system.μ
        {ω | W.slate.Y0 ω < W.slate.Y1 ω ∧ W.slate.S0 ω = true ∧
          W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
        (W.slate.xEvent x) := by
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  let E : Fin K × Fin K → Set W.system.Ω := fun a =>
    if a.1 < a.2 then
      {ω | W.slate.Y0 ω = a.1 ∧ W.slate.Y1 ω = a.2 ∧
        W.slate.S0 ω = true ∧ W.slate.S1 ω = true ∧
        ω ∈ W.slate.complierEvent}
    else ∅
  calc
    benefitMass (fullLawSurvivorCoupling W x) =
        ∑ i, ∑ j, if i < j then fullLawSurvivorCoupling W x i j else 0 := by
      unfold benefitMass
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
    _ = ∑ a : Fin K × Fin K, conditionalReal W.system.μ (E a)
        (W.slate.xEvent x) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j
      · simp [E, hij, fullLawSurvivorCoupling]
      · simp [E, hij, conditionalReal]
    _ = conditionalReal W.system.μ (⋃ a, E a) (W.slate.xEvent x) := by
      symm
      apply conditionalReal_iUnion_fintype
      · intro a
        by_cases ha : a.1 < a.2
        · simp only [E, ha, if_pos]
          convert ((((W.slate.yVar.measurable_cfUnder W.slate.dVar false)
            (measurableSet_singleton a.1)).inter
            ((W.slate.yVar.measurable_cfUnder W.slate.dVar true)
              (measurableSet_singleton a.2))).inter
            ((W.slate.sVar.measurable_cfUnder W.slate.dVar false)
              (measurableSet_singleton true))).inter
            (((W.slate.sVar.measurable_cfUnder W.slate.dVar true)
              (measurableSet_singleton true)).inter
              (measurableSet_complierEvent_local W)) using 1 <;>
            ext ω <;> simp [POSlateSystem.Y0, POSlateSystem.Y1,
              POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.YofD,
              POSlateSystem.SofD, and_assoc]
        · simp [E, ha]
      · exact W.slate.xVar.measurable_factual (measurableSet_singleton x)
      · intro a b hab
        apply Set.disjoint_left.2
        intro ω ha hb
        by_cases hai : a.1 < a.2 <;> by_cases hbi : b.1 < b.2
        · simp only [E, hai, hbi, if_pos, Set.mem_setOf_eq] at ha hb
          have hpair : a = b := by
            apply Prod.ext
            · exact ha.1.symm.trans hb.1
            · exact ha.2.1.symm.trans hb.2.1
          exact hab hpair
        · simp [E, hbi] at hb
        · simp [E, hai] at ha
        · simp [E, hai] at ha
    _ = _ := by
      congr 1
      ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ha⟩
        by_cases hai : a.1 < a.2
        · simp only [E, hai, if_pos, Set.mem_setOf_eq] at ha
          exact ⟨by simpa [ha.1, ha.2.1] using hai, ha.2.2⟩
        · simp [E, hai] at ha
      · rintro ⟨hy, hs0, hs1, hc⟩
        refine ⟨(W.slate.Y0 ω, W.slate.Y1 ω), ?_⟩
        simp [E, hy, hs0, hs1, hc]

private theorem cellMass_mul_conditionalReal
    {Q : POSystem} (A C : Set Q.Ω) :
    Q.μ.real C * conditionalReal Q.μ A C = Q.μ.real (A ∩ C) := by
  unfold conditionalReal
  by_cases hC : 0 < Q.μ.real C
  · rw [if_pos hC]
    field_simp
  · rw [if_neg hC]
    have hC0 : Q.μ.real C = 0 := le_antisymm (not_lt.mp hC) measureReal_nonneg
    have hAC : Q.μ.real (A ∩ C) = 0 := le_antisymm
      ((measureReal_mono Set.inter_subset_right).trans_eq hC0) measureReal_nonneg
    simp [hC0, hAC]

private theorem sum_cellMass_mul_conditionalReal
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K)
    (A : Set W.system.Ω) (hA : MeasurableSet A) :
    (∑ x, W.slate.p x * conditionalReal W.system.μ A (W.slate.xEvent x)) =
      W.system.μ.real A := by
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  calc
    _ = ∑ x, W.system.μ.real (A ∩ W.slate.xEvent x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [POSlateSystem.p]
      exact cellMass_mul_conditionalReal A (W.slate.xEvent x)
    _ = W.system.μ.real (⋃ x, A ∩ W.slate.xEvent x) := by
      symm
      apply measureReal_iUnion_fintype
      · intro i j hij
        apply Set.disjoint_left.2
        intro ω hi hj
        exact hij (by
          have hxi := hi.2
          have hxj := hj.2
          simpa [POSlateSystem.xEvent, POVar.event] using hxi.symm.trans hxj)
      · intro x
        exact hA.inter (W.slate.xVar.measurable_factual (measurableSet_singleton x))
      · exact fun _ => measure_ne_top _ _
    _ = _ := by
      congr 1
      ext ω
      simp [POSlateSystem.xEvent, POVar.event]

/-- The full-law objective is the cell-probability-weighted benefit mass of its projected survivor couplings, divided by their aggregate survivor mass. Given [the stated hypotheses](hyp:hpositive), [the stated conclusion follows](goal). -/
theorem benefitProbabilityOf_eq_aggregate
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K)
    (hpositive : 0 < ∑ x, W.slate.p x *
      totalMass (fullLawSurvivorCoupling W x)) :
    benefitProbabilityOf W =
      (∑ x, W.slate.p x * benefitMass (fullLawSurvivorCoupling W x)) /
        (∑ x, W.slate.p x * totalMass (fullLawSurvivorCoupling W x)) := by
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  let A : Set W.system.Ω := {ω | W.slate.Y0 ω < W.slate.Y1 ω ∧
    W.slate.S0 ω = true ∧ W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
  let B : Set W.system.Ω := {ω | W.slate.S0 ω = true ∧
    W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
  have hA : MeasurableSet A := by
    dsimp [A]
    convert (((((W.slate.yVar.measurable_cfUnder W.slate.dVar false).prodMk
      (W.slate.yVar.measurable_cfUnder W.slate.dVar true))
        (MeasurableSet.of_discrete : MeasurableSet
          {p : Fin K × Fin K | p.1 < p.2})).inter
      ((W.slate.sVar.measurable_cfUnder W.slate.dVar false)
        (measurableSet_singleton true))).inter
      ((W.slate.sVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton true))).inter
      (measurableSet_complierEvent_local W) using 1 <;>
      ext ω <;> simp [POSlateSystem.Y0, POSlateSystem.Y1,
        POSlateSystem.S0, POSlateSystem.S1, POSlateSystem.YofD,
        POSlateSystem.SofD, and_assoc]
  have hB : MeasurableSet B := by
    dsimp [B]
    convert (((W.slate.sVar.measurable_cfUnder W.slate.dVar false)
      (measurableSet_singleton true)).inter
      ((W.slate.sVar.measurable_cfUnder W.slate.dVar true)
        (measurableSet_singleton true))).inter
      (measurableSet_complierEvent_local W) using 1 <;>
      ext ω <;> simp [POSlateSystem.S0, POSlateSystem.S1,
        POSlateSystem.SofD, and_assoc]
  have hnum : (∑ x, W.slate.p x * benefitMass
      (fullLawSurvivorCoupling W x)) = W.system.μ.real A := by
    simp_rw [fullLawSurvivorCoupling_benefit]
    exact sum_cellMass_mul_conditionalReal W A hA
  have hden : (∑ x, W.slate.p x * totalMass
      (fullLawSurvivorCoupling W x)) = W.system.μ.real B := by
    simp_rw [fullLawSurvivorCoupling_total]
    unfold survivorComplierMass
    exact sum_cellMass_mul_conditionalReal W B hB
  unfold benefitProbabilityOf conditionalReal
  change (if 0 < W.system.μ.real B then W.system.μ.real (A ∩ B) /
    W.system.μ.real B else 0) = _
  rw [if_pos (hden ▸ hpositive)]
  have hAB : A ∩ B = A := by
    ext ω
    simp [A, B, and_assoc]
  rw [hAB, hnum, hden]

/-- Any compatible full law projects into the branch-free exact-mass polytope determined by its observed distribution. Given [the stated hypotheses](hyp:hx), [the stated conclusion follows](goal). -/
theorem fullLawSurvivorCoupling_mem_branchFree
    {P₀ : POSystem} (W : FullLawCandidate P₀ 𝒳 K)
    [StandardBorelSpace W.system.Ω]
    (εZ : ℝ) (d : 𝒳 → Bool) (model : TieSafeSurvivorModel W.slate εZ d)
    (x : 𝒳) (hx : 0 < W.slate.p x) :
    fullLawSurvivorCoupling W x ∈ branchFreePolytope
      (observableCapacities W.slate.observedLaw)
      (capacity_identification W.slate εZ d model.ivIndependence
        model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
        model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity).1.2 x := by
  let ident := capacity_identification W.slate εZ d model.ivIndependence
    model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
    model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
  change matrixNonnegative (fullLawSurvivorCoupling W x) ∧
    (∀ i, rowMass (fullLawSurvivorCoupling W x) i ≤
      (observableCapacities W.slate.observedLaw).lower x i) ∧
    (∀ j, columnMass (fullLawSurvivorCoupling W x) j ≤
      (observableCapacities W.slate.observedLaw).upper x j) ∧
    totalMass (fullLawSurvivorCoupling W x) =
      (observableCapacities W.slate.observedLaw).mass x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    unfold fullLawSurvivorCoupling conditionalReal
    split_ifs <;> positivity
  · intro i
    rw [fullLawSurvivorCoupling_row_sum, ident.2.2.1 x hx i]
    unfold lowerLatentMass
    apply conditionalReal_mono_left_local
    intro ω hω
    exact ⟨hω.1, hω.2.1, hω.2.2.2⟩
  · intro j
    rw [fullLawSurvivorCoupling_column_sum, ident.2.2.2.1 x hx j]
    unfold upperLatentMass
    apply conditionalReal_mono_left_local
    intro ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.2.2⟩
  · rw [fullLawSurvivorCoupling_total, ident.2.2.2.2.2.1 x hx]

/-- Given [the stated hypotheses](hyp:hlaw,hValid,hx), [the full law survivor coupling belongs to branch free whenever observed law eq property holds](goal). -/
theorem fullLawSurvivorCoupling_mem_branchFree_of_observedLaw_eq
    {P Q : POSystem} (S : POSlateSystem P 𝒳 K)
    (W : FullLawCandidate Q 𝒳 K) [StandardBorelSpace W.system.Ω]
    (εZ : ℝ) (d : 𝒳 → Bool) (model : TieSafeSurvivorModel W.slate εZ d)
    (hlaw : W.slate.observedLaw = S.observedLaw)
    (hValid : ValidCapacities (observableCapacities S.observedLaw))
    (x : 𝒳) (hx : 0 < S.p x) :
    fullLawSurvivorCoupling W x ∈ branchFreePolytope
      (observableCapacities S.observedLaw)
      hValid x := by
  have hp := (observedLaw_eq_transfers_p_propensity S W.slate hlaw).1
  have hmem := fullLawSurvivorCoupling_mem_branchFree W εZ d model x (by
    rw [hp x]
    exact hx)
  change matrixNonnegative (fullLawSurvivorCoupling W x) ∧
    (∀ i, rowMass (fullLawSurvivorCoupling W x) i ≤
      (observableCapacities W.slate.observedLaw).lower x i) ∧
    (∀ j, columnMass (fullLawSurvivorCoupling W x) j ≤
      (observableCapacities W.slate.observedLaw).upper x j) ∧
    totalMass (fullLawSurvivorCoupling W x) =
      (observableCapacities W.slate.observedLaw).mass x at hmem
  change matrixNonnegative (fullLawSurvivorCoupling W x) ∧
    (∀ i, rowMass (fullLawSurvivorCoupling W x) i ≤
      (observableCapacities S.observedLaw).lower x i) ∧
    (∀ j, columnMass (fullLawSurvivorCoupling W x) j ≤
      (observableCapacities S.observedLaw).upper x j) ∧
    totalMass (fullLawSurvivorCoupling W x) =
      (observableCapacities S.observedLaw).mass x
  rw [hlaw] at hmem
  exact hmem

/-- Given [the stated hypotheses](hyp:gamma,hgamma), [the full law branch free family attainment property holds](goal). -/
theorem full_law_branchFree_family_attainment
    {P : POSystem} [StandardBorelSpace P.Ω]
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (compatible : TieSafeSurvivorModel S εZ d)
    (gamma : ∀ x : 𝒳, Coupling K)
    (hgamma : ∀ x, gamma x ∈ branchFreePolytope
      (observableCapacities S.observedLaw)
      (capacity_identification S εZ d compatible.ivIndependence
        compatible.treatmentConsistency compatible.selectionExclusion
        compatible.outcomeExclusion compatible.instrumentOverlap
        compatible.noDefiers compatible.weakSelectionMonotonicity).1.2 x) :
    ∃ W : FullLawCandidate P 𝒳 K,
      FullLawFeasible S.observedLaw W ∧
      (∀ x, 0 < S.p x → fullLawSurvivorCoupling W x = gamma x) ∧
      benefitProbabilityOf W =
        (∑ x, S.p x * benefitMass (gamma x)) /
          (observableCapacities S.observedLaw).aggregateMass S.p := by
  let ident := capacity_identification S εZ d compatible.ivIndependence
    compatible.treatmentConsistency compatible.selectionExclusion
    compatible.outcomeExclusion compatible.instrumentOverlap
    compatible.noDefiers compatible.weakSelectionMonotonicity
  let c := observableCapacities S.observedLaw
  let baseline := originalCompatibleBaseline S εZ d compatible
  let reference : Fin K := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) S.hK⟩
  let completion := fun x => thresholdLatentCompletion baseline ident.1.2 x (gamma x)
  have hmargins : ∀ x,
      (∀ i, rowMass (completion x).survivor i +
          (completion x).selectedOnlyUnderZero i = c.lower x i) ∧
      (∀ j, columnMass (completion x).survivor j +
          (completion x).selectedOnlyUnderOne j = c.upper x j) := by
    intro x
    change (∀ i, rowMass (gamma x) i +
        (thresholdLatentCompletion baseline ident.1.2 x (gamma x)).selectedOnlyUnderZero i =
          (observableCapacities S.observedLaw).lower x i) ∧
      (∀ j, columnMass (gamma x) j +
        (thresholdLatentCompletion baseline ident.1.2 x (gamma x)).selectedOnlyUnderOne j =
          (observableCapacities S.observedLaw).upper x j)
    exact thresholdLatentCompletion_selected_margins
      baseline ident.1.2 x (gamma x) (hgamma x)
  have hraw : (thresholdCompletionCellTable reference completion).Nonnegative := by
    simpa [completion] using branchFree_completionCellTable_nonnegative
      baseline ident.1.2 reference gamma hgamma
  let table := normalizedCompletionCellTable S reference completion
  have htableNonnegative : table.Nonnegative :=
    normalizedCompletionCellTable_nonnegative S reference completion hraw
  have htableNormalized : table.Normalized := by
    apply normalizedCompletionCellTable_normalized
    intro x hx
    apply branchFree_completionCellTable_total baseline ident.1.2 reference gamma hgamma
    simpa [baseline, originalCompatibleBaseline] using
      baseline_principal_partition S x compatible.noDefiers hx
  have hpropensity : ∀ x, 0 ≤ S.propensity x ∧ S.propensity x ≤ 1 :=
    propensity_mem_unitInterval S
  let W := canonicalThresholdCandidate S table ident.2.1 hpropensity
    htableNonnegative htableNormalized
  have hobserved : W.slate.observedLaw = S.observedLaw := by
    apply canonicalThresholdCandidate_completion_observedLaw_eq S
      compatible.ivIndependence compatible.treatmentConsistency
      compatible.selectionExclusion compatible.outcomeExclusion
      compatible.instrumentOverlap compatible.noDefiers reference completion
      ident.2.1 hpropensity
    · exact hmargins
    · intro x s0 s1 y0 y1
      simp [completion, baseline, originalCompatibleBaseline,
        thresholdLatentCompletion]
    · intro x s0 s1 y0 y1
      simp [completion, baseline, originalCompatibleBaseline,
        thresholdLatentCompletion]
    · intro x hx
      have hc := thresholdLatentCompletion_complier_total baseline ident.1.2 x
        (gamma x) (hgamma x)
      change (∑ i, ∑ j, (completion x).survivor i j) +
          (∑ i, (completion x).selectedOnlyUnderZero i) +
          (∑ j, (completion x).selectedOnlyUnderOne j) +
          (completion x).neverSelectedMass = baseline.complierMass x
      simpa only [completion] using hc
    · exact ident.2.2.1
    · exact ident.2.2.2.1
  have hconsistency : TreatmentConsistency W.slate ∧
      SelectionExclusion W.slate ∧ OutcomeExclusion W.slate := by
    simpa [W, table] using canonicalThresholdCandidate_consistency S table
      ident.2.1 hpropensity htableNonnegative htableNormalized
  have hnoDefiers : NoDefiers W.slate := by
    apply canonicalThresholdCandidate_noDefiers S table ident.2.1
      hpropensity htableNonnegative htableNormalized
    simpa [table] using
      normalizedCompletionCellTable_noDefiers S reference completion
  have hdirections :
      (∀ x y0 y1, d x = true → table x false true true false y0 y1 = 0) ∧
      (∀ x y0 y1, d x = false → table x false true false true y0 y1 = 0) := by
    constructor
    · intro x y0 y1 hd
      by_cases hx : 0 < S.p x
      · have hn : ¬ (observableCapacities S.observedLaw).gap x < 0 := by
          intro hg
          have := ident.2.2.2.2.2.2.2.1 x hx hg
          simp [hd] at this
        simp [table, normalizedCompletionCellTable, hx, completion,
          thresholdCompletionCellTable, thresholdLatentCompletion, hn]
      · simp [table, normalizedCompletionCellTable, hx]
    · intro x y0 y1 hd
      by_cases hx : 0 < S.p x
      · have hn : ¬ 0 < (observableCapacities S.observedLaw).gap x := by
          intro hg
          have := ident.2.2.2.2.2.2.1 x hx hg
          simp [hd] at this
        simp [table, normalizedCompletionCellTable, hx, completion,
          thresholdCompletionCellTable, thresholdLatentCompletion, hn]
      · simp [table, normalizedCompletionCellTable, hx]
  have hmonotone : WeakSelectionMonotonicity W.slate d := by
    apply canonicalThresholdCandidate_weakSelectionMonotonicity S table
      ident.2.1 hpropensity htableNonnegative htableNormalized d
    · exact hdirections.1
    · exact hdirections.2
  have hoverlap : InstrumentOverlap W.slate εZ :=
    instrumentOverlap_of_observedLaw_eq S W.slate εZ
      compatible.instrumentOverlap hobserved
  have hpositive : PositiveAggregateSurvivors
      (observableCapacities W.slate.observedLaw) W.slate.p :=
    positiveAggregateSurvivors_of_observedLaw_eq S W.slate
      compatible.positiveAggregateSurvivors hobserved
  letI : StandardBorelSpace W.system.Ω := W.slate.borel
  have hmodel : TieSafeSurvivorModel W.slate εZ d := by
    refine
      { ivIndependence := ?_
        treatmentConsistency := hconsistency.1
        selectionExclusion := hconsistency.2.1
        outcomeExclusion := hconsistency.2.2
        instrumentOverlap := hoverlap
        noDefiers := hnoDefiers
        weakSelectionMonotonicity := hmonotone
        positiveAggregateSurvivors := hpositive }
    simpa [W, table] using canonicalThresholdCandidate_ivIndependence S table
      ident.2.1 hpropensity htableNonnegative htableNormalized
  have hrealizes : ∀ x, 0 < S.p x → fullLawSurvivorCoupling W x = gamma x := by
    intro x hx
    have hr := canonicalThresholdCandidate_realizes_of_pos S reference completion
      ident.2.1 hpropensity htableNonnegative htableNormalized x hx
    change fullLawSurvivorCoupling W x = gamma x
    exact hr.1.trans (by rfl)
  have htableSurvivor : ∀ x, 0 < S.p x →
      tableSurvivorCoupling (table x) = gamma x := by
    intro x hx
    funext i j
    simp [table, normalizedCompletionCellTable, hx, completion,
      tableSurvivorCoupling, thresholdCompletionCellTable,
      thresholdLatentCompletion]
  have hmassTable : (∑ x, S.p x * totalMass
      (tableSurvivorCoupling (table x))) = c.aggregateMass S.p := by
    unfold Capacities.aggregateMass
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < S.p x
    · rw [htableSurvivor x hx, (hgamma x).2.2.2]
    · have hx0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (ident.2.1 x)
      simp [hx0]
  have hbenefitTable : (∑ x, S.p x * benefitMass
      (tableSurvivorCoupling (table x))) = ∑ x, S.p x * benefitMass (gamma x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < S.p x
    · rw [htableSurvivor x hx]
    · have hx0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (ident.2.1 x)
      simp [hx0]
  have hbenefit := canonicalThresholdCandidate_benefitProbabilityOf S table
    ident.2.1 hpropensity htableNonnegative htableNormalized
    (hmassTable.symm ▸ compatible.positiveAggregateSurvivors)
  refine ⟨W, ?_, hrealizes, ?_⟩
  · exact ⟨εZ, d, hmodel, hobserved⟩
  · simpa [W, c, hmassTable, hbenefitTable] using hbenefit

end CausalSmith.PartialID.SlateBenefitPartialTransport
