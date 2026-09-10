import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.CondIndepBridge

/-!
# Identification of observable capacities

The observable IV contrasts identify the two selected-complier marginal
subdistributions and hence the survivor mass and observable selection gap.
-/

open MeasureTheory Set
open Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ} {P : POSystem} [StandardBorelSpace P.Ω]

private def factualSelectedOutcomeEvent (S : POSlateSystem P 𝒳 K)
    (d : Bool) (i : Fin K) : Set P.Ω :=
  {ω | S.factualD ω = d ∧ S.factualS ω = true ∧ S.factualY ω = i}

private def latentSelectedOutcomeArmEvent (S : POSlateSystem P 𝒳 K)
    (d z : Bool) (i : Fin K) : Set P.Ω :=
  {ω | S.DofZ z ω = d ∧ S.SofD d ω = true ∧ S.YofD d ω = i}

private lemma selectedOutcome_arm_identified
    (S : POSlateSystem P 𝒳 K) (hIV : IVIndependence S)
    (hTreatment : TreatmentConsistency S) (hSelection : SelectionExclusion S)
    (hOutcome : OutcomeExclusion S) (d z : Bool) (i : Fin K) (x : 𝒳)
    (hx : 0 < P.μ.real (S.xEvent x))
    (harm : 0 < P.μ.real (S.xEvent x ∩ S.zVar.event z)) :
    conditionalReal P.μ (factualSelectedOutcomeEvent S d i)
        (S.xEvent x ∩ S.zVar.event z) =
      conditionalReal P.μ (latentSelectedOutcomeArmEvent S d z i) (S.xEvent x) := by
  have hCI := condIndepCFBundle_of_condIndepCF S (RegimedVar.ofFactual S.zVar)
    S.cfBundle hIV
  apply conditionalReal_eq_of_condIndepCFBundle S S.cfBundle hCI z
  · unfold factualSelectedOutcomeEvent
    convert ((S.dVar.measurable_factual (measurableSet_singleton d)).inter
      (S.sVar.measurable_factual (measurableSet_singleton true))).inter
      (S.yVar.measurable_factual (measurableSet_singleton i)) using 1 <;>
      ext ω <;> simp [POSlateSystem.factualD, POSlateSystem.factualS,
        POSlateSystem.factualY, and_assoc]
  · unfold latentSelectedOutcomeArmEvent
    convert (((measurable_DofZ_cfBundle S z) (measurableSet_singleton d)).inter
      ((measurable_SofD_cfBundle S d) (measurableSet_singleton true))).inter
      ((measurable_YofD_cfBundle S d) (measurableSet_singleton i)) using 1
    · rfl
    · ext ω
      simp [and_assoc]
  · filter_upwards [hTreatment, hSelection, hOutcome] with ω ht hs hy
    unfold factualSelectedOutcomeEvent latentSelectedOutcomeArmEvent
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hfd, hfs, hfy⟩, hfz⟩
      have hd : S.factualD ω = S.DofZ z ω := by simpa [hfz] using ht
      have hs' : S.SofD d ω = true := by simpa [hfd, hfs] using hs.symm
      have hy' : S.YofD d ω = i := by simpa [hfd, hfs, hfy] using (hy hfs).symm
      exact ⟨⟨hd ▸ hfd, hs', hy'⟩, hfz⟩
    · rintro ⟨⟨hd, hsd, hyd⟩, hfz⟩
      have hfd : S.factualD ω = d := by simpa [hfz, hd] using ht
      have hfs : S.factualS ω = true := by simpa [hfd, hsd] using hs
      have hfy : S.factualY ω = i := by simpa [hfd, hfs, hyd] using hy hfs
      exact ⟨⟨hfd, hfs, hfy⟩, hfz⟩
  · exact hx
  · exact harm

private lemma measurable_observedDatum (S : POSlateSystem P 𝒳 K) :
    Measurable S.observedDatum := by
  intro t _
  rw [show S.observedDatum ⁻¹' t = ⋃ o : t, S.observedDatum ⁻¹' {o.1} by ext; simp]
  apply MeasurableSet.iUnion
  rintro ⟨⟨x, z, d, s, y⟩, ho⟩
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
  have hm : MeasurableSet { ω | S.factualX ω = x ∧ S.factualZ ω = z ∧
      S.factualD ω = d ∧ S.factualS ω = s ∧
      (if S.factualS ω then some (S.factualY ω) else none) = y } := by
    have h := ((((S.xVar.measurable_factual (measurableSet_singleton x)).inter
      (S.zVar.measurable_factual (measurableSet_singleton z))).inter
      (S.dVar.measurable_factual (measurableSet_singleton d))).inter
      (S.sVar.measurable_factual (measurableSet_singleton s))).inter hout
    convert h using 1 <;> ext ω <;>
      simp [POSlateSystem.factualX, POSlateSystem.factualZ,
        POSlateSystem.factualD, POSlateSystem.factualS, and_assoc]
  convert hm using 1 <;> ext ω <;>
    simp [POSlateSystem.observedDatum, ObservedDatum.mk.injEq, and_assoc]

/-- Public measurability bridge used by downstream estimator limit proofs. [the stated conclusion follows](goal). -/
theorem observedDatum_measurable_for_identification (S : POSlateSystem P 𝒳 K) :
    Measurable S.observedDatum :=
  measurable_observedDatum S

omit [StandardBorelSpace P.Ω] in
/-- Every slate-system pushforward is a probability law on the paper's valid observed-data domain, with an outcome present exactly on selected records. [the stated conclusion follows](goal). -/
theorem observedLawDomain (S : POSlateSystem P 𝒳 K) :
    ObservedLawDomain S.observedLaw := by
  letI : StandardBorelSpace P.Ω := S.borel
  refine ⟨S.hK, Measure.isProbabilityMeasure_map
    (measurable_observedDatum S).aemeasurable, ?_⟩
  unfold POSlateSystem.observedLaw
  apply (ae_map_iff (measurable_observedDatum S).aemeasurable
    MeasurableSet.of_discrete).2
  filter_upwards with ω
  cases h : S.factualS ω <;> simp [POSlateSystem.observedDatum, h]

/-- The system cell-mass function is exactly the cell-probability vector of its observed pushforward law. [the stated conclusion follows](goal). -/
theorem p_eq_observedCellWeights (S : POSlateSystem P 𝒳 K) :
    S.p = Capacities.observedCellWeights S.observedLaw := by
  funext x
  symm
  unfold POSlateSystem.observedLaw POSlateSystem.p Capacities.observedCellWeights
  rw [Measure.real, Measure.map_apply
    (observedDatum_measurable_for_identification S)
    ((Set.toFinite _).measurableSet)]
  rfl

private lemma conditionalReal_congr_left {A A' B : Set P.Ω}
    (h : A ∩ B = A' ∩ B) :
    conditionalReal P.μ A B = conditionalReal P.μ A' B := by
  unfold conditionalReal
  rw [h]

private lemma observable_lower_pullback (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (i : Fin K) :
    (observableCapacities S.observedLaw).lower x i =
      conditionalReal P.μ (factualSelectedOutcomeEvent S false i)
          (S.xEvent x ∩ S.zVar.event false) -
        conditionalReal P.μ (factualSelectedOutcomeEvent S false i)
          (S.xEvent x ∩ S.zVar.event true) := by
  unfold observableCapacities observableCapacityContrasts POSlateSystem.observedLaw
  change conditionalReal (P.μ.map S.observedDatum)
      {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some i}
        {o | o.cell = x ∧ o.instrument = false} -
      conditionalReal (P.μ.map S.observedDatum)
      {o | o.cell = x ∧ o.treatment = false ∧ o.selected = true ∧ o.outcome = some i}
        {o | o.cell = x ∧ o.instrument = true} = _
  rw [conditionalReal_map, conditionalReal_map]
  all_goals try exact measurable_observedDatum S
  all_goals try exact MeasurableSet.of_discrete
  apply congrArg₂ (fun a b : ℝ => a - b)
  · apply conditionalReal_congr_left
    ext ω
    simp [factualSelectedOutcomeEvent, POSlateSystem.observedDatum,
      POSlateSystem.xEvent, POVar.event, POSlateSystem.factualX,
      POSlateSystem.factualZ, and_assoc, and_left_comm, and_comm]
  · apply conditionalReal_congr_left
    ext ω
    simp [factualSelectedOutcomeEvent, POSlateSystem.observedDatum,
      POSlateSystem.xEvent, POVar.event, POSlateSystem.factualX,
      POSlateSystem.factualZ, and_assoc, and_left_comm, and_comm]

private lemma observable_upper_pullback (S : POSlateSystem P 𝒳 K)
    (x : 𝒳) (j : Fin K) :
    (observableCapacities S.observedLaw).upper x j =
      conditionalReal P.μ (factualSelectedOutcomeEvent S true j)
          (S.xEvent x ∩ S.zVar.event true) -
        conditionalReal P.μ (factualSelectedOutcomeEvent S true j)
          (S.xEvent x ∩ S.zVar.event false) := by
  unfold observableCapacities observableCapacityContrasts POSlateSystem.observedLaw
  change conditionalReal (P.μ.map S.observedDatum)
      {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some j}
        {o | o.cell = x ∧ o.instrument = true} -
      conditionalReal (P.μ.map S.observedDatum)
      {o | o.cell = x ∧ o.treatment = true ∧ o.selected = true ∧ o.outcome = some j}
        {o | o.cell = x ∧ o.instrument = false} = _
  rw [conditionalReal_map, conditionalReal_map]
  all_goals try exact measurable_observedDatum S
  all_goals try exact MeasurableSet.of_discrete
  apply congrArg₂ (fun a b : ℝ => a - b)
  · apply conditionalReal_congr_left
    ext ω
    simp [factualSelectedOutcomeEvent, POSlateSystem.observedDatum,
      POSlateSystem.xEvent, POVar.event, POSlateSystem.factualX,
      POSlateSystem.factualZ, and_assoc, and_left_comm, and_comm]
  · apply conditionalReal_congr_left
    ext ω
    simp [factualSelectedOutcomeEvent, POSlateSystem.observedDatum,
      POSlateSystem.xEvent, POVar.event, POSlateSystem.factualX,
      POSlateSystem.factualZ, and_assoc, and_left_comm, and_comm]

/-- The lower latent mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def lowerLatentMass (S : POSlateSystem P 𝒳 K) (x : 𝒳) (i : Fin K) : ℝ :=
  conditionalReal P.μ
    {ω | S.YofD false ω = i ∧ S.SofD false ω = true ∧ ω ∈ S.complierEvent}
    (S.xEvent x)

/-- The upper latent mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def upperLatentMass (S : POSlateSystem P 𝒳 K) (x : 𝒳) (j : Fin K) : ℝ :=
  conditionalReal P.μ
    {ω | S.YofD true ω = j ∧ S.SofD true ω = true ∧ ω ∈ S.complierEvent}
    (S.xEvent x)

/-- The selected complier mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def selectedComplierMass (S : POSlateSystem P 𝒳 K)
    (d : Bool) (x : 𝒳) : ℝ :=
  conditionalReal P.μ {ω | S.SofD d ω = true ∧ ω ∈ S.complierEvent} (S.xEvent x)

/-- The survivor complier mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def survivorComplierMass (S : POSlateSystem P 𝒳 K) (x : 𝒳) : ℝ :=
  conditionalReal P.μ
    {ω | S.SofD false ω = true ∧ S.SofD true ω = true ∧ ω ∈ S.complierEvent}
    (S.xEvent x)

/-- The equal selection complier mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def equalSelectionComplierMass (S : POSlateSystem P 𝒳 K) (x : 𝒳) : ℝ :=
  conditionalReal P.μ
    {ω | S.SofD false ω = S.SofD true ω ∧ ω ∈ S.complierEvent}
    (S.xEvent x)

private lemma measurable_DofZ (S : POSlateSystem P 𝒳 K) (z : Bool) :
    Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

private lemma measurable_SofD (S : POSlateSystem P 𝒳 K) (d : Bool) :
    Measurable (S.SofD d) :=
  S.sVar.measurable_cfUnder S.dVar d

private lemma measurable_YofD (S : POSlateSystem P 𝒳 K) (d : Bool) :
    Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

private lemma measureReal_bool_partition (f : P.Ω → Bool) (hf : Measurable f)
    (X : Set P.Ω) (hX : MeasurableSet X) :
    P.μ.real X = P.μ.real (X ∩ {w | f w = false}) +
      P.μ.real (X ∩ {w | f w = true}) := by
  have hfalse : MeasurableSet {w | f w = false} :=
    hf (measurableSet_singleton false)
  have htrue : MeasurableSet {w | f w = true} :=
    hf (measurableSet_singleton true)
  have hu : (X ∩ {w | f w = false}) ∪ (X ∩ {w | f w = true}) = X := by
    ext w
    cases h : f w <;> simp [h]
  have hd : Disjoint (X ∩ {w | f w = false}) (X ∩ {w | f w = true}) := by
    apply Set.disjoint_left.2
    intro w hw0 hw1
    simp_all
  calc
    P.μ.real X = P.μ.real ((X ∩ {w | f w = false}) ∪
        (X ∩ {w | f w = true})) := congrArg P.μ.real hu.symm
    _ = _ := measureReal_union hd (hX.inter htrue)

private lemma arm_cell_positive {εZ : ℝ} (S : POSlateSystem P 𝒳 K)
    (hOverlap : InstrumentOverlap S εZ)
    (x : 𝒳) (hx : 0 < S.p x) (z : Bool) :
    0 < P.μ.real (S.xEvent x ∩ S.zVar.event z) := by
  have hp : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
  have hov := hOverlap.2.2 x hx
  have hzmeas : Measurable (S.factualZ) := S.zVar.measurable_factual
  have hxmeas : MeasurableSet (S.xEvent x) :=
    S.xVar.measurable_factual (measurableSet_singleton x)
  have hpart := measureReal_bool_partition S.factualZ hzmeas (S.xEvent x) hxmeas
  have hprop : S.propensity x =
      P.μ.real (S.xEvent x ∩ S.zVar.event true) / P.μ.real (S.xEvent x) := by
    unfold POSlateSystem.propensity conditionalReal
    rw [if_pos hp]
    congr 2
    ext w
    simp [POSlateSystem.xEvent, POVar.event, POSlateSystem.factualZ,
      and_comm]
  cases z
  · have hplt : S.propensity x < 1 := lt_of_le_of_lt hov.2 (by linarith [hOverlap.1])
    have hnumlt : P.μ.real (S.xEvent x ∩ S.zVar.event true) <
        P.μ.real (S.xEvent x) := by
      rw [hprop] at hplt
      exact (div_lt_one (by positivity)).mp hplt
    have hfalse : P.μ.real (S.xEvent x ∩ S.zVar.event false) =
        P.μ.real (S.xEvent x) -
          P.μ.real (S.xEvent x ∩ S.zVar.event true) := by
      change P.μ.real (S.xEvent x ∩ {w | S.factualZ w = false}) =
        P.μ.real (S.xEvent x) -
          P.μ.real (S.xEvent x ∩ {w | S.factualZ w = true})
      linarith [hpart]
    rw [hfalse]
    linarith
  · have hppos : 0 < S.propensity x := lt_of_lt_of_le hOverlap.1 hov.1
    rw [hprop] at hppos
    rcases (div_pos_iff.mp hppos) with h | h
    · exact h.1
    · linarith

/-- Public overlap bridge for positive cell-by-instrument probabilities. Given [the stated hypotheses](hyp:hOverlap,hx), [the stated conclusion follows](goal). -/
theorem arm_cell_positive_of_overlap {εZ : ℝ} (S : POSlateSystem P 𝒳 K)
    (hOverlap : InstrumentOverlap S εZ)
    (x : 𝒳) (hx : 0 < S.p x) (z : Bool) :
    0 < P.μ.real (S.xEvent x ∩ S.zVar.event z) :=
  arm_cell_positive S hOverlap x hx z

private lemma lower_noDefier_contrast (S : POSlateSystem P 𝒳 K)
    (hNoDefiers : NoDefiers S) (x : 𝒳) (i : Fin K)
    (hx : 0 < P.μ.real (S.xEvent x)) :
    conditionalReal P.μ (latentSelectedOutcomeArmEvent S false false i) (S.xEvent x) -
      conditionalReal P.μ (latentSelectedOutcomeArmEvent S false true i) (S.xEvent x) =
      lowerLatentMass S x i := by
  let A0 : Set P.Ω := latentSelectedOutcomeArmEvent S false false i
  let A1 : Set P.Ω := latentSelectedOutcomeArmEvent S false true i
  let C : Set P.Ω :=
    {w | S.YofD false w = i ∧ S.SofD false w = true ∧ w ∈ S.complierEvent}
  have hA1 : MeasurableSet A1 := by
    dsimp [A1, latentSelectedOutcomeArmEvent]
    exact ((measurable_DofZ S true) (measurableSet_singleton false)).inter
      (((measurable_SofD S false) (measurableSet_singleton true)).inter
        ((measurable_YofD S false) (measurableSet_singleton i)))
  have hC : MeasurableSet C := by
    dsimp [C, POSlateSystem.complierEvent]
    exact ((measurable_YofD S false) (measurableSet_singleton i)).inter
      (((measurable_SofD S false) (measurableSet_singleton true)).inter
        (((measurable_DofZ S false) (measurableSet_singleton false)).inter
          ((measurable_DofZ S true) (measurableSet_singleton true))))
  have hEq : P.μ.real (A0 ∩ S.xEvent x) =
      P.μ.real ((A1 ∩ S.xEvent x) ∪ (C ∩ S.xEvent x)) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hNoDefiers] with w hnd
    apply propext
    dsimp [A0, A1, C, latentSelectedOutcomeArmEvent, POSlateSystem.complierEvent]
    constructor
    · rintro ⟨⟨hd0, hs, hy⟩, hX⟩
      cases h1 : S.DofZ true w
      · left; exact ⟨⟨h1, hs, hy⟩, hX⟩
      · right; exact ⟨⟨hy, hs, hd0, h1⟩, hX⟩
    · rintro (⟨⟨hd1, hs, hy⟩, hX⟩ | ⟨⟨hy, hs, hd0, hd1⟩, hX⟩)
      · exact ⟨⟨Bool.eq_false_of_not_eq_true (fun hd0 => by simpa [hd0, hd1] using hnd hd0), hs, hy⟩, hX⟩
      · exact ⟨⟨hd0, hs, hy⟩, hX⟩
  have hdisj : Disjoint (A1 ∩ S.xEvent x) (C ∩ S.xEvent x) := by
    apply Set.disjoint_left.2
    intro w hw1 hwc
    dsimp [A1, C, latentSelectedOutcomeArmEvent, POSlateSystem.complierEvent] at hw1 hwc
    simp_all
  rw [measureReal_union hdisj (hC.inter
    (S.xVar.measurable_factual (measurableSet_singleton x)))] at hEq
  unfold lowerLatentMass
  simp only [conditionalReal, if_pos hx]
  change P.μ.real (A0 ∩ S.xEvent x) / _ - P.μ.real (A1 ∩ S.xEvent x) / _ =
    P.μ.real (C ∩ S.xEvent x) / _
  rw [hEq]
  ring

private lemma upper_noDefier_contrast (S : POSlateSystem P 𝒳 K)
    (hNoDefiers : NoDefiers S) (x : 𝒳) (j : Fin K)
    (hx : 0 < P.μ.real (S.xEvent x)) :
    conditionalReal P.μ (latentSelectedOutcomeArmEvent S true true j) (S.xEvent x) -
      conditionalReal P.μ (latentSelectedOutcomeArmEvent S true false j) (S.xEvent x) =
      upperLatentMass S x j := by
  let A1 : Set P.Ω := latentSelectedOutcomeArmEvent S true true j
  let A0 : Set P.Ω := latentSelectedOutcomeArmEvent S true false j
  let C : Set P.Ω :=
    {w | S.YofD true w = j ∧ S.SofD true w = true ∧ w ∈ S.complierEvent}
  have hA0 : MeasurableSet A0 := by
    dsimp [A0, latentSelectedOutcomeArmEvent]
    exact ((measurable_DofZ S false) (measurableSet_singleton true)).inter
      (((measurable_SofD S true) (measurableSet_singleton true)).inter
        ((measurable_YofD S true) (measurableSet_singleton j)))
  have hC : MeasurableSet C := by
    dsimp [C, POSlateSystem.complierEvent]
    exact ((measurable_YofD S true) (measurableSet_singleton j)).inter
      (((measurable_SofD S true) (measurableSet_singleton true)).inter
        (((measurable_DofZ S false) (measurableSet_singleton false)).inter
          ((measurable_DofZ S true) (measurableSet_singleton true))))
  have hEq : P.μ.real (A1 ∩ S.xEvent x) =
      P.μ.real ((A0 ∩ S.xEvent x) ∪ (C ∩ S.xEvent x)) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hNoDefiers] with w hnd
    apply propext
    dsimp [A1, A0, C, latentSelectedOutcomeArmEvent, POSlateSystem.complierEvent]
    constructor
    · rintro ⟨⟨hd1, hs, hy⟩, hX⟩
      cases h0 : S.DofZ false w
      · right; exact ⟨⟨hy, hs, h0, hd1⟩, hX⟩
      · left; exact ⟨⟨h0, hs, hy⟩, hX⟩
    · rintro (⟨⟨hd0, hs, hy⟩, hX⟩ | ⟨⟨hy, hs, hd0, hd1⟩, hX⟩)
      · exact ⟨⟨hnd hd0, hs, hy⟩, hX⟩
      · exact ⟨⟨hd1, hs, hy⟩, hX⟩
  have hdisj : Disjoint (A0 ∩ S.xEvent x) (C ∩ S.xEvent x) := by
    apply Set.disjoint_left.2
    intro w hw0 hwc
    dsimp [A0, C, latentSelectedOutcomeArmEvent, POSlateSystem.complierEvent] at hw0 hwc
    simp_all
  rw [measureReal_union hdisj (hC.inter
    (S.xVar.measurable_factual (measurableSet_singleton x)))] at hEq
  unfold upperLatentMass
  simp only [conditionalReal, if_pos hx]
  change P.μ.real (A1 ∩ S.xEvent x) / _ - P.μ.real (A0 ∩ S.xEvent x) / _ =
    P.μ.real (C ∩ S.xEvent x) / _
  rw [hEq]
  ring

private lemma sum_outcome_partition (S : POSlateSystem P 𝒳 K) (d : Bool)
    (x : 𝒳) :
    (∑ i : Fin K, P.μ.real
      ({w | S.YofD d w = i ∧ S.SofD d w = true ∧ w ∈ S.complierEvent} ∩
        S.xEvent x)) =
      P.μ.real ({w | S.SofD d w = true ∧ w ∈ S.complierEvent} ∩
        S.xEvent x) := by
  let E : Fin K → Set P.Ω := fun i =>
    {w | S.YofD d w = i ∧ S.SofD d w = true ∧ w ∈ S.complierEvent} ∩
      S.xEvent x
  have hmeas : ∀ i, MeasurableSet (E i) := by
    intro i
    dsimp [E, POSlateSystem.complierEvent]
    exact (((measurable_YofD S d) (measurableSet_singleton i)).inter
      (((measurable_SofD S d) (measurableSet_singleton true)).inter
        (((measurable_DofZ S false) (measurableSet_singleton false)).inter
          ((measurable_DofZ S true) (measurableSet_singleton true))))).inter
      (S.xVar.measurable_factual (measurableSet_singleton x))
  have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro w hwi hwj
    dsimp [E] at hwi hwj
    exact hij (hwi.1.1.symm.trans hwj.1.1)
  rw [← measureReal_iUnion_fintype hdisj hmeas]
  congr 1
  ext w
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨_, hs, hc⟩, hx⟩
    exact ⟨⟨hs, hc⟩, hx⟩
  · rintro ⟨⟨hs, hc⟩, hx⟩
    exact ⟨S.YofD d w, ⟨rfl, hs, hc⟩, hx⟩

private lemma sum_lowerLatentMass (S : POSlateSystem P 𝒳 K) (x : 𝒳)
    (hx : 0 < P.μ.real (S.xEvent x)) :
    (∑ i, lowerLatentMass S x i) = selectedComplierMass S false x := by
  simp only [lowerLatentMass, selectedComplierMass, conditionalReal, if_pos hx,
    ← Finset.sum_div]
  rw [sum_outcome_partition S false x]

private lemma sum_upperLatentMass (S : POSlateSystem P 𝒳 K) (x : 𝒳)
    (hx : 0 < P.μ.real (S.xEvent x)) :
    (∑ j, upperLatentMass S x j) = selectedComplierMass S true x := by
  simp only [upperLatentMass, selectedComplierMass, conditionalReal, if_pos hx,
    ← Finset.sum_div]
  rw [sum_outcome_partition S true x]

private lemma selection_monotone_cell (S : POSlateSystem P 𝒳 K)
    (d : 𝒳 → Bool) (hMonotone : WeakSelectionMonotonicity S d)
    (x : 𝒳) (hx : 0 < P.μ.real (S.xEvent x)) :
    (d x = true ∧ survivorComplierMass S x = selectedComplierMass S false x ∧
        selectedComplierMass S false x ≤ selectedComplierMass S true x) ∨
    (d x = false ∧ survivorComplierMass S x = selectedComplierMass S true x ∧
        selectedComplierMass S true x ≤ selectedComplierMass S false x) := by
  let CB : Set P.Ω := S.complierEvent ∩ S.xEvent x
  let A0 : Set P.Ω := {w | S.SofD false w = true}
  let A1 : Set P.Ω := {w | S.SofD true w = true}
  let AS : Set P.Ω := {w | S.SofD false w = true ∧ S.SofD true w = true}
  let ν : Measure P.Ω := P.μ.restrict CB
  have hCB : MeasurableSet CB := by
    dsimp [CB, POSlateSystem.complierEvent]
    exact (((measurable_DofZ S false) (measurableSet_singleton false)).inter
      ((measurable_DofZ S true) (measurableSet_singleton true))).inter
      (S.xVar.measurable_factual (measurableSet_singleton x))
  have hA0 : MeasurableSet A0 := (measurable_SofD S false) (measurableSet_singleton true)
  have hA1 : MeasurableSet A1 := (measurable_SofD S true) (measurableSet_singleton true)
  have hAS : MeasurableSet AS := hA0.inter hA1
  have hm : ∀ᵐ w ∂ν,
      (d x = true → S.SofD false w ≤ S.SofD true w) ∧
      (d x = false → S.SofD true w ≤ S.SofD false w) := by
    by_cases hp : 0 < P.μ CB
    · exact hMonotone x hp
    · have hz : P.μ CB = 0 := bot_unique (not_lt.mp hp)
      rw [show ν = 0 by exact Measure.restrict_eq_zero.mpr hz, MeasureTheory.ae_zero]
      trivial
  have real_restrict (A : Set P.Ω) (hA : MeasurableSet A) :
      ν.real A = P.μ.real (A ∩ CB) := by
    exact congrArg ENNReal.toReal (Measure.restrict_apply hA)
  have translate0 : ν.real A0 =
      P.μ.real ({w | S.SofD false w = true ∧ w ∈ S.complierEvent} ∩
        S.xEvent x) := by
    calc
      ν.real A0 = P.μ.real (A0 ∩ CB) := real_restrict A0 hA0
      _ = _ := by
        apply congrArg P.μ.real
        ext w
        simp [A0, CB, and_assoc, and_left_comm, and_comm]
  have translate1 : ν.real A1 =
      P.μ.real ({w | S.SofD true w = true ∧ w ∈ S.complierEvent} ∩
        S.xEvent x) := by
    calc
      ν.real A1 = P.μ.real (A1 ∩ CB) := real_restrict A1 hA1
      _ = _ := by
        apply congrArg P.μ.real
        ext w
        simp [A1, CB, and_assoc, and_left_comm, and_comm]
  have translateS : ν.real AS =
      P.μ.real ({w | S.SofD false w = true ∧ S.SofD true w = true ∧
        w ∈ S.complierEvent} ∩ S.xEvent x) := by
    calc
      ν.real AS = P.μ.real (AS ∩ CB) := real_restrict AS hAS
      _ = _ := by
        apply congrArg P.μ.real
        ext w
        simp [AS, CB, and_assoc, and_left_comm, and_comm]
  have hcond0 : selectedComplierMass S false x = ν.real A0 / P.μ.real (S.xEvent x) := by
    simp only [selectedComplierMass, conditionalReal, if_pos hx, translate0]
  have hcond1 : selectedComplierMass S true x = ν.real A1 / P.μ.real (S.xEvent x) := by
    simp only [selectedComplierMass, conditionalReal, if_pos hx, translate1]
  have hcondS : survivorComplierMass S x = ν.real AS / P.μ.real (S.xEvent x) := by
    simp only [survivorComplierMass, conditionalReal, if_pos hx, translateS]
  cases hd : d x
  · right
    have hae : A1 =ᵐ[ν] AS := by
      filter_upwards [hm] with w hw
      apply propext
      change (S.SofD true w = true) ↔
        (S.SofD false w = true ∧ S.SofD true w = true)
      have hle := hw.2 hd
      constructor
      · intro h1
        exact ⟨(Bool.le_iff_imp.mp hle) h1, h1⟩
      · exact fun h => h.2
    have heq : ν.real A1 = ν.real AS :=
      congrArg ENNReal.toReal (measure_congr hae)
    have hleENN : ν A1 ≤ ν A0 := by
      apply measure_mono_ae
      filter_upwards [hm] with w hw
      intro h1
      have hle := hw.2 hd
      change S.SofD true w = true at h1
      change S.SofD false w = true
      exact (Bool.le_iff_imp.mp hle) h1
    have hle : ν.real A1 ≤ ν.real A0 := by
      exact ENNReal.toReal_mono (measure_ne_top ν A0) hleENN
    refine ⟨rfl, ?_, ?_⟩
    · rw [hcondS, hcond1, heq]
    · rw [hcond1, hcond0]
      exact div_le_div_of_nonneg_right hle hx.le
  · left
    have hae : A0 =ᵐ[ν] AS := by
      filter_upwards [hm] with w hw
      apply propext
      change (S.SofD false w = true) ↔
        (S.SofD false w = true ∧ S.SofD true w = true)
      have hle := hw.1 hd
      constructor
      · intro h0
        exact ⟨h0, (Bool.le_iff_imp.mp hle) h0⟩
      · exact fun h => h.1
    have heq : ν.real A0 = ν.real AS :=
      congrArg ENNReal.toReal (measure_congr hae)
    have hleENN : ν A0 ≤ ν A1 := by
      apply measure_mono_ae
      filter_upwards [hm] with w hw
      intro h0
      have hle := hw.1 hd
      change S.SofD false w = true at h0
      change S.SofD true w = true
      exact (Bool.le_iff_imp.mp hle) h0
    have hle : ν.real A0 ≤ ν.real A1 := by
      exact ENNReal.toReal_mono (measure_ne_top ν A1) hleENN
    refine ⟨rfl, ?_, ?_⟩
    · rw [hcondS, hcond0, heq]
    · rw [hcond0, hcond1]
      exact div_le_div_of_nonneg_right hle hx.le

private lemma weakMonotone_update_of_equal (S : POSlateSystem P 𝒳 K)
    (d : 𝒳 → Bool) (hMonotone : WeakSelectionMonotonicity S d)
    (x : 𝒳) (hx : 0 < P.μ.real (S.xEvent x))
    (heq : selectedComplierMass S true x = selectedComplierMass S false x)
    (b : Bool) : WeakSelectionMonotonicity S (Function.update d x b) := by
  intro y hy
  by_cases hyx : y = x
  · subst y
    let CB : Set P.Ω := S.complierEvent ∩ S.xEvent x
    let A0 : Set P.Ω := {w | S.SofD false w = true}
    let A1 : Set P.Ω := {w | S.SofD true w = true}
    let ν : Measure P.Ω := P.μ.restrict CB
    have hA0 : MeasurableSet A0 :=
      (measurable_SofD S false) (measurableSet_singleton true)
    have hA1 : MeasurableSet A1 :=
      (measurable_SofD S true) (measurableSet_singleton true)
    have hreal : ν.real A1 = ν.real A0 := by
      have hnum :
          P.μ.real ({w | S.SofD true w = true ∧ w ∈ S.complierEvent} ∩
              S.xEvent x) =
            P.μ.real ({w | S.SofD false w = true ∧ w ∈ S.complierEvent} ∩
              S.xEvent x) := by
        apply (div_left_inj' (ne_of_gt hx)).mp
        simpa [selectedComplierMass, conditionalReal, hx] using heq
      calc
        ν.real A1 = P.μ.real (A1 ∩ CB) :=
          congrArg ENNReal.toReal (Measure.restrict_apply hA1)
        _ = P.μ.real
            ({w | S.SofD true w = true ∧ w ∈ S.complierEvent} ∩ S.xEvent x) := by
          apply congrArg P.μ.real
          ext w
          simp [A1, CB, and_assoc, and_left_comm, and_comm]
        _ = P.μ.real
            ({w | S.SofD false w = true ∧ w ∈ S.complierEvent} ∩ S.xEvent x) := hnum
        _ = P.μ.real (A0 ∩ CB) := by
          apply congrArg P.μ.real
          ext w
          simp [A0, CB, and_assoc, and_left_comm, and_comm]
        _ = ν.real A0 :=
          (congrArg ENNReal.toReal (Measure.restrict_apply hA0)).symm
    have hmeasure : ν A1 = ν A0 :=
      (MeasureTheory.measureReal_eq_measureReal_iff).mp hreal
    have hm := hMonotone x hy
    have hsets : A0 =ᵐ[ν] A1 := by
      cases hd : d x
      · have hsub : A1 ≤ᵐ[ν] A0 := by
          filter_upwards [hm] with w hw
          intro h1
          change S.SofD true w = true at h1
          change S.SofD false w = true
          exact (Bool.le_iff_imp.mp (hw.2 hd)) h1
        exact (ae_eq_of_ae_subset_of_measure_ge hsub hmeasure.ge
          hA1.nullMeasurableSet (measure_ne_top ν A0)).symm
      · have hsub : A0 ≤ᵐ[ν] A1 := by
          filter_upwards [hm] with w hw
          intro h0
          change S.SofD false w = true at h0
          change S.SofD true w = true
          exact (Bool.le_iff_imp.mp (hw.1 hd)) h0
        exact ae_eq_of_ae_subset_of_measure_ge hsub hmeasure.le
          hA0.nullMeasurableSet (measure_ne_top ν A1)
    filter_upwards [hsets] with w hw
    have hbool : S.SofD false w = S.SofD true w := by
      have hw' : (S.SofD false w = true) ↔ (S.SofD true w = true) := by
        exact iff_of_eq hw
      cases h0 : S.SofD false w <;> cases h1 : S.SofD true w <;> simp_all
    simp only [Function.update_self]
    constructor <;> intro <;> simp [hbool]
  · have hm := hMonotone y hy
    rw [Function.update_of_ne hyx]
    exact hm

/-- A direction label is observationally admissible in a cell when some full
law satisfying the seven identification assumptions induces the same observed
law and carries that label in the cell.  Aggregate survivor positivity is not
part of cellwise direction admissibility. -/
def DirectionObservationallyAdmissible
    (P₀ : POSystem) (Pobs : Measure (ObservedDatum 𝒳 K)) (x : 𝒳) (dir : Bool) : Prop :=
  ∃ W : FullLawCandidate P₀ 𝒳 K,
    let _ : StandardBorelSpace W.system.Ω := W.slate.borel
    ∃ (εZ : ℝ) (d : 𝒳 → Bool),
      IVIndependence W.slate ∧
      TreatmentConsistency W.slate ∧
      SelectionExclusion W.slate ∧
      OutcomeExclusion W.slate ∧
      InstrumentOverlap W.slate εZ ∧
      NoDefiers W.slate ∧
      WeakSelectionMonotonicity W.slate d ∧
      W.slate.observedLaw = Pobs ∧ d x = dir

/-- The conditional IV contrasts equal the two selected-complier marginals; their totals identify the selection gap and, under cellwise weak monotonicity, the survivor-complier mass and every strictly identified direction. [the stated conclusion follows](goal). -/
-- @node: prop:capacity-identification
theorem capacity_identification (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (_hIV : IVIndependence S)
    (_hTreatment : TreatmentConsistency S)
    (_hSelection : SelectionExclusion S)
    (_hOutcome : OutcomeExclusion S)
    (_hOverlap : InstrumentOverlap S εZ)
    (_hNoDefiers : NoDefiers S)
    (_hMonotone : WeakSelectionMonotonicity S d) :
    let c := observableCapacities S.observedLaw
    CompatibleObservedLaw S.observedLaw ∧
    (∀ x, 0 ≤ S.p x) ∧
    (∀ x, 0 < S.p x → ∀ i, c.lower x i = lowerLatentMass S x i) ∧
    (∀ x, 0 < S.p x → ∀ j, c.upper x j = upperLatentMass S x j) ∧
    (∀ x, 0 < S.p x →
      c.gap x = selectedComplierMass S true x - selectedComplierMass S false x) ∧
    (∀ x, 0 < S.p x → c.mass x = survivorComplierMass S x) ∧
    (∀ x, 0 < S.p x → 0 < c.gap x → d x = true) ∧
    (∀ x, 0 < S.p x → c.gap x < 0 → d x = false) ∧
    (∀ x, 0 < S.p x → c.gap x = 0 →
      DirectionObservationallyAdmissible P S.observedLaw x true ∧
      DirectionObservationallyAdmissible P S.observedLaw x false) := by
  dsimp
  have hpnonneg : ∀ x, 0 ≤ S.p x := by
    intro x
    exact measureReal_nonneg
  have hlower : ∀ x, 0 < S.p x → ∀ i,
      (observableCapacities S.observedLaw).lower x i = lowerLatentMass S x i := by
    intro x hx i
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rw [observable_lower_pullback]
    rw [selectedOutcome_arm_identified S _hIV _hTreatment _hSelection _hOutcome
      false false i x hx' (arm_cell_positive S _hOverlap x hx false)]
    rw [selectedOutcome_arm_identified S _hIV _hTreatment _hSelection _hOutcome
      false true i x hx' (arm_cell_positive S _hOverlap x hx true)]
    exact lower_noDefier_contrast S _hNoDefiers x i hx'
  have hupper : ∀ x, 0 < S.p x → ∀ j,
      (observableCapacities S.observedLaw).upper x j = upperLatentMass S x j := by
    intro x hx j
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rw [observable_upper_pullback]
    rw [selectedOutcome_arm_identified S _hIV _hTreatment _hSelection _hOutcome
      true true j x hx' (arm_cell_positive S _hOverlap x hx true)]
    rw [selectedOutcome_arm_identified S _hIV _hTreatment _hSelection _hOutcome
      true false j x hx' (arm_cell_positive S _hOverlap x hx false)]
    exact upper_noDefier_contrast S _hNoDefiers x j hx'
  have hvalid : ValidCapacities (observableCapacities S.observedLaw) := by
    constructor
    · intro x i
      by_cases hx : 0 < S.p x
      · rw [hlower x hx i]
        unfold lowerLatentMass conditionalReal
        split_ifs <;> positivity
      · have hp0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (hpnonneg x)
        have hxzero : P.μ.real (S.xEvent x) = 0 := by
          simpa [POSlateSystem.p] using hp0
        have harm (z : Bool) : P.μ.real (S.xEvent x ∩ S.zVar.event z) = 0 := by
          apply le_antisymm
          · exact (measureReal_mono inter_subset_left).trans_eq hxzero
          · exact measureReal_nonneg
        rw [observable_lower_pullback]
        simp [conditionalReal, harm]
    · intro x j
      by_cases hx : 0 < S.p x
      · rw [hupper x hx j]
        unfold upperLatentMass conditionalReal
        split_ifs <;> positivity
      · have hp0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (hpnonneg x)
        have hxzero : P.μ.real (S.xEvent x) = 0 := by
          simpa [POSlateSystem.p] using hp0
        have harm (z : Bool) : P.μ.real (S.xEvent x ∩ S.zVar.event z) = 0 := by
          apply le_antisymm
          · exact (measureReal_mono inter_subset_left).trans_eq hxzero
          · exact measureReal_nonneg
        rw [observable_upper_pullback]
        simp [conditionalReal, harm]
  have hcompat : CompatibleObservedLaw S.observedLaw := by
    refine ⟨?_, hvalid⟩
    exact Measure.isProbabilityMeasure_map (measurable_observedDatum S).aemeasurable
  have hq0 : ∀ x, 0 < S.p x →
      (observableCapacities S.observedLaw).q0 x = selectedComplierMass S false x := by
    intro x hx
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rw [Capacities.q0, Finset.sum_congr rfl (fun i _ => hlower x hx i)]
    exact sum_lowerLatentMass S x hx'
  have hq1 : ∀ x, 0 < S.p x →
      (observableCapacities S.observedLaw).q1 x = selectedComplierMass S true x := by
    intro x hx
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rw [Capacities.q1, Finset.sum_congr rfl (fun j _ => hupper x hx j)]
    exact sum_upperLatentMass S x hx'
  have hgap : ∀ x, 0 < S.p x →
      (observableCapacities S.observedLaw).gap x =
        selectedComplierMass S true x - selectedComplierMass S false x := by
    intro x hx
    simp [Capacities.gap, hq0 x hx, hq1 x hx]
  have hmass : ∀ x, 0 < S.p x →
      (observableCapacities S.observedLaw).mass x = survivorComplierMass S x := by
    intro x hx
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rcases selection_monotone_cell S d _hMonotone x hx' with h | h
    · rw [Capacities.mass, hq0 x hx, hq1 x hx, min_eq_left h.2.2, h.2.1]
    · rw [Capacities.mass, hq0 x hx, hq1 x hx, min_eq_right h.2.2, h.2.1]
  have hposdir : ∀ x, 0 < S.p x →
      0 < (observableCapacities S.observedLaw).gap x → d x = true := by
    intro x hx hpos
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rcases selection_monotone_cell S d _hMonotone x hx' with h | h
    · exact h.1
    · exfalso
      rw [hgap x hx] at hpos
      linarith [h.2.2]
  have hnegdir : ∀ x, 0 < S.p x →
      (observableCapacities S.observedLaw).gap x < 0 → d x = false := by
    intro x hx hneg
    have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
    rcases selection_monotone_cell S d _hMonotone x hx' with h | h
    · exfalso
      rw [hgap x hx] at hneg
      linarith [h.2.2]
    · exact h.1
  refine ⟨hcompat, hpnonneg, hlower, hupper, hgap, hmass, hposdir, hnegdir, ?_⟩
  intro x hx hzero
  have hx' : 0 < P.μ.real (S.xEvent x) := by simpa [POSlateSystem.p] using hx
  have hselEq : selectedComplierMass S true x = selectedComplierMass S false x := by
    have := hgap x hx
    rw [hzero] at this
    linarith
  let W : FullLawCandidate P 𝒳 K := ⟨P, S⟩
  constructor
  · refine ⟨W, εZ, Function.update d x true, _hIV, _hTreatment, _hSelection,
      _hOutcome, _hOverlap, _hNoDefiers, ?_, rfl, ?_⟩
    · exact weakMonotone_update_of_equal S d _hMonotone x hx' hselEq true
    · exact Function.update_self x true d
  · refine ⟨W, εZ, Function.update d x false, _hIV, _hTreatment, _hSelection,
      _hOutcome, _hOverlap, _hNoDefiers, ?_, rfl, ?_⟩
    · exact weakMonotone_update_of_equal S d _hMonotone x hx' hselEq false
    · exact Function.update_self x false d

end CausalSmith.PartialID.SlateBenefitPartialTransport
