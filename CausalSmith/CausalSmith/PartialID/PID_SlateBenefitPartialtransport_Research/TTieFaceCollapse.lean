import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TCapacityIdentification
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Transport

/-!
# Observable tie-face collapse

At zero selected-complier selection gap, the exact-row, exact-column, and
fixed-marginal transport faces coincide, together with all cut formulas.
-/

open Causalean PO MeasureTheory Set

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ} {P : POSystem} [StandardBorelSpace P.Ω]

-- @node: measurable_POSlate_SofD
/-- [the po slate sof d map is measurable](goal). -/
theorem measurable_POSlate_SofD (S : POSlateSystem P 𝒳 K) (d : Bool) :
    Measurable (S.SofD d) := S.sVar.measurable_cfUnder S.dVar d

-- @node: sum_rowMass_eq_totalMass
/-- [the sum row mass equals total mass property holds](goal). -/
theorem sum_rowMass_eq_totalMass (γ : Coupling K) :
    (∑ i, rowMass γ i) = totalMass γ := by
  rfl

-- @node: sum_columnMass_eq_totalMass
/-- [the sum column mass equals total mass property holds](goal). -/
theorem sum_columnMass_eq_totalMass (γ : Coupling K) :
    (∑ j, columnMass γ j) = totalMass γ := by
  simp only [columnMass, totalMass, Finset.sum_comm]

-- @node: pointwise_eq_of_le_of_sum_eq
/-- Given [the stated hypotheses](hyp:hab,hsum), [the pointwise equals of is at most of sum eq property holds](goal). -/
theorem pointwise_eq_of_le_of_sum_eq {a b : Fin K → ℝ}
    (hab : ∀ i, a i ≤ b i) (hsum : (∑ i, a i) = ∑ i, b i) :
    ∀ i, a i = b i := by
  intro i
  by_contra hne
  have hlt : a i < b i := lt_of_le_of_ne (hab i) hne
  have : (∑ j, a j) < ∑ j, b j :=
    Finset.sum_lt_sum (fun j _ => hab j) ⟨i, Finset.mem_univ i, hlt⟩
  linarith

-- @node: branchFree_exact_rows_of_q0_le_q1
/-- Given [the stated hypotheses](hyp:hValid,hq,hγ), [the branch free exact rows whenever q0 is at most q1 property holds](goal). -/
theorem branchFree_exact_rows_of_q0_le_q1 (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) (hq : c.q0 x ≤ c.q1 x)
    {γ : Coupling K} (hγ : γ ∈ branchFreePolytope c hValid x) :
    ∀ i, rowMass γ i = c.lower x i := by
  apply pointwise_eq_of_le_of_sum_eq hγ.2.1
  rw [sum_rowMass_eq_totalMass, hγ.2.2.2, Capacities.mass, min_eq_left hq]
  rfl

-- @node: branchFree_exact_columns_of_q1_le_q0
/-- Given [the stated hypotheses](hyp:hValid,hq,hγ), [the branch free exact columns whenever q1 is at most q0 property holds](goal). -/
theorem branchFree_exact_columns_of_q1_le_q0 (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) (hq : c.q1 x ≤ c.q0 x)
    {γ : Coupling K} (hγ : γ ∈ branchFreePolytope c hValid x) :
    ∀ j, columnMass γ j = c.upper x j := by
  apply pointwise_eq_of_le_of_sum_eq hγ.2.2.1
  rw [sum_columnMass_eq_totalMass, hγ.2.2.2, Capacities.mass, min_eq_right hq]
  rfl

-- @node: polytope_tie_iff_gap_zero
/-- Given [the stated hypotheses](hyp:hValid), [the polytope tie exactly when gap zero property holds](goal). -/
theorem polytope_tie_iff_gap_zero (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) :
    ((incPolytope c hValid x = decPolytope c hValid x ∧
        decPolytope c hValid x = tiePolytope c hValid x) ↔ c.gap x = 0) := by
  have hflow := (thresholdFlow_endpoint_spec c hValid x).1
  constructor
  · rintro ⟨hincdec, hdectie⟩
    rcases le_total (c.q0 x) (c.q1 x) with hq | hq
    · have hinc : thresholdFlowLower c hValid x ∈ incPolytope c hValid x :=
        ⟨hflow.1, branchFree_exact_rows_of_q0_le_q1 c hValid x hq hflow,
          hflow.2.2.1⟩
      have htie : thresholdFlowLower c hValid x ∈ tiePolytope c hValid x := by
        rw [← hdectie, ← hincdec]
        exact hinc
      have htot0 : c.q0 x = totalMass (thresholdFlowLower c hValid x) := by
        rw [← sum_rowMass_eq_totalMass]
        exact Finset.sum_congr rfl (fun i _ => (hinc.2.1 i).symm)
      have htot1 : c.q1 x = totalMass (thresholdFlowLower c hValid x) := by
        rw [← sum_columnMass_eq_totalMass]
        exact Finset.sum_congr rfl (fun j _ => (htie.2.2 j).symm)
      simp only [Capacities.gap]
      linarith
    · have hdec : thresholdFlowLower c hValid x ∈ decPolytope c hValid x :=
        ⟨hflow.1, hflow.2.1,
          branchFree_exact_columns_of_q1_le_q0 c hValid x hq hflow⟩
      have htie : thresholdFlowLower c hValid x ∈ tiePolytope c hValid x := by
        rw [← hdectie]
        exact hdec
      have htot0 : c.q0 x = totalMass (thresholdFlowLower c hValid x) := by
        rw [← sum_rowMass_eq_totalMass]
        exact Finset.sum_congr rfl (fun i _ => (htie.2.1 i).symm)
      have htot1 : c.q1 x = totalMass (thresholdFlowLower c hValid x) := by
        rw [← sum_columnMass_eq_totalMass]
        exact Finset.sum_congr rfl (fun j _ => (hdec.2.2 j).symm)
      simp only [Capacities.gap]
      linarith
  · intro hgap
    have hq : c.q0 x = c.q1 x := by
      exact (sub_eq_zero.mp (by simpa [Capacities.gap] using hgap)).symm
    have hle01 : c.q0 x ≤ c.q1 x := hq.le
    have hle10 : c.q1 x ≤ c.q0 x := hq.ge
    apply And.intro <;> ext γ
    · constructor
      · intro hγ
        have hstar : γ ∈ branchFreePolytope c hValid x := by
          exact ⟨hγ.1, fun i => (hγ.2.1 i).le, hγ.2.2,
            by rw [← sum_rowMass_eq_totalMass, Finset.sum_congr rfl
              (fun i _ => hγ.2.1 i), Capacities.mass, min_eq_left hle01,
              Capacities.q0]⟩
        exact ⟨hγ.1, hstar.2.1,
          branchFree_exact_columns_of_q1_le_q0 c hValid x hle10 hstar⟩
      · intro hγ
        have hstar : γ ∈ branchFreePolytope c hValid x := by
          exact ⟨hγ.1, hγ.2.1, fun j => (hγ.2.2 j).le,
            by rw [← sum_columnMass_eq_totalMass, Finset.sum_congr rfl
              (fun j _ => hγ.2.2 j), Capacities.mass, min_eq_right hle10,
              Capacities.q1]⟩
        exact ⟨hγ.1,
          branchFree_exact_rows_of_q0_le_q1 c hValid x hle01 hstar,
          fun j => (hγ.2.2 j).le⟩
    · constructor
      · exact fun hγ => ⟨hγ.1,
          branchFree_exact_rows_of_q0_le_q1 c hValid x hle01
            ⟨hγ.1, hγ.2.1, fun j => (hγ.2.2 j).le,
              by rw [← sum_columnMass_eq_totalMass, Finset.sum_congr rfl
                (fun j _ => hγ.2.2 j), Capacities.mass, min_eq_right hle10,
                Capacities.q1]⟩,
          hγ.2.2⟩
      · exact fun hγ => ⟨hγ.1, fun i => (hγ.2.1 i).le, hγ.2.2⟩

-- @node: branchFree_eq_tie_of_gap_zero
/-- Given [the stated hypotheses](hyp:hValid,hgap), [the branch free equals tie whenever gap zero property holds](goal). -/
theorem branchFree_eq_tie_of_gap_zero (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) (hgap : c.gap x = 0) :
    branchFreePolytope c hValid x = tiePolytope c hValid x := by
  have hq : c.q0 x = c.q1 x :=
    (sub_eq_zero.mp (by simpa [Capacities.gap] using hgap)).symm
  have hle01 : c.q0 x ≤ c.q1 x := hq.le
  have hle10 : c.q1 x ≤ c.q0 x := hq.ge
  ext γ
  constructor
  · intro hγ
    exact ⟨hγ.1, branchFree_exact_rows_of_q0_le_q1 c hValid x hle01 hγ,
      branchFree_exact_columns_of_q1_le_q0 c hValid x hle10 hγ⟩
  · intro hγ
    refine ⟨hγ.1, fun i => (hγ.2.1 i).le, fun j => (hγ.2.2 j).le, ?_⟩
    rw [← sum_rowMass_eq_totalMass, Finset.sum_congr rfl
      (fun i _ => hγ.2.1 i), Capacities.mass, min_eq_left hle01,
      Capacities.q0]

-- @node: prefix_difference_eq_tail_difference_of_gap_zero
/-- Given [the stated hypotheses](hyp:hgap), [the prefix difference equals tail difference whenever gap zero property holds](goal). -/
theorem prefix_difference_eq_tail_difference_of_gap_zero
    (c : Capacities 𝒳 K) (x : 𝒳) (hgap : c.gap x = 0) (t : Fin K) :
    c.lowerLe x t - c.upperLe x t = c.upperGt x t - c.lowerGt x t := by
  have hq : c.q0 x = c.q1 x :=
    (sub_eq_zero.mp (by simpa [Capacities.gap] using hgap)).symm
  have hlower : c.lowerLe x t + c.lowerGt x t = c.q0 x := by
    simpa [Capacities.lowerLe, Capacities.lowerGt, Capacities.q0, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin K => i ≤ t) (c.lower x))
  have hupper : c.upperLe x t + c.upperGt x t = c.q1 x := by
    simpa [Capacities.upperLe, Capacities.upperGt, Capacities.q1, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin K => j ≤ t) (c.upper x))
  linarith

-- @node: equalSelectionComplierMass_of_zero_gap
/-- Given [the stated hypotheses](hyp:hMonotone,hgapIdent,hgap), [the equal selection complier mass whenever zero gap property holds](goal). -/
theorem equalSelectionComplierMass_of_zero_gap
    (S : POSlateSystem P 𝒳 K) (d : 𝒳 → Bool)
    (hMonotone : WeakSelectionMonotonicity S d) (x : 𝒳)
    (hgapIdent : (observableCapacities S.observedLaw).gap x =
      selectedComplierMass S true x - selectedComplierMass S false x)
    (hgap : (observableCapacities S.observedLaw).gap x = 0) :
    equalSelectionComplierMass S x =
      conditionalReal P.μ S.complierEvent (S.xEvent x) := by
  have hselected : selectedComplierMass S true x = selectedComplierMass S false x := by
    rw [hgap] at hgapIdent
    linarith
  by_cases hB : 0 < P.μ.real (S.xEvent x)
  · have hBne : P.μ.real (S.xEvent x) ≠ 0 := ne_of_gt hB
    have hnumReal :
        P.μ.real ({ω | S.SofD true ω = true ∧ ω ∈ S.complierEvent} ∩ S.xEvent x) =
        P.μ.real ({ω | S.SofD false ω = true ∧ ω ∈ S.complierEvent} ∩ S.xEvent x) := by
      apply (div_left_inj' hBne).mp
      simpa [selectedComplierMass, conditionalReal, hB] using hselected
    let CB : Set P.Ω := S.complierEvent ∩ S.xEvent x
    let A0 : Set P.Ω := {ω | S.SofD false ω = true}
    let A1 : Set P.Ω := {ω | S.SofD true ω = true}
    let ν : Measure P.Ω := P.μ.restrict CB
    have hA0 : MeasurableSet A0 := by
      dsimp [A0]
      exact (measurable_POSlate_SofD S false) (measurableSet_singleton true)
    have hA1 : MeasurableSet A1 := by
      dsimp [A1]
      exact (measurable_POSlate_SofD S true) (measurableSet_singleton true)
    have hνmass : ν A0 = ν A1 := by
      apply (measureReal_eq_measureReal_iff).mp
      have hset0 : A0 ∩ CB =
          {ω | S.SofD false ω = true ∧ ω ∈ S.complierEvent} ∩ S.xEvent x := by
        ext ω
        simp [A0, CB, and_assoc, and_left_comm, and_comm]
      have hset1 : A1 ∩ CB =
          {ω | S.SofD true ω = true ∧ ω ∈ S.complierEvent} ∩ S.xEvent x := by
        ext ω
        simp [A1, CB, and_assoc, and_left_comm, and_comm]
      simpa [ν, Measure.restrict_apply, hA0, hA1, hset0, hset1] using hnumReal.symm
    have hmono :
        (fun ω => A0.indicator (fun _ => (1 : ENNReal)) ω) =ᵐ[ν]
          (fun ω => A1.indicator (fun _ => (1 : ENNReal)) ω) := by
      have horder :
          (fun ω => A0.indicator (fun _ => (1 : ENNReal)) ω) ≤ᵐ[ν]
            (fun ω => A1.indicator (fun _ => (1 : ENNReal)) ω) ∨
          (fun ω => A1.indicator (fun _ => (1 : ENNReal)) ω) ≤ᵐ[ν]
            (fun ω => A0.indicator (fun _ => (1 : ENNReal)) ω) := by
        by_cases hpos : 0 < P.μ CB
        · have hm := hMonotone x hpos
          by_cases hd : d x = true
          · left
            filter_upwards [hm] with ω hω
            simp only [A0, A1, Set.indicator]
            split_ifs <;> simp_all <;> first | contradiction | decide
          · right
            have hd' : d x = false := Bool.eq_false_of_not_eq_true hd
            filter_upwards [hm] with ω hω
            simp only [A0, A1, Set.indicator]
            split_ifs <;> simp_all <;> first | contradiction | decide
        · have hzero : P.μ CB = 0 := bot_unique (not_lt.mp hpos)
          have hνzero : ν = 0 := Measure.restrict_eq_zero.mpr hzero
          rw [hνzero]
          left
          rw [MeasureTheory.ae_zero]
          trivial
      rcases horder with hle | hle
      · exact ae_eq_of_ae_le_of_lintegral_le hle
          (by simp [MeasureTheory.lintegral_indicator, hA0])
          (Measurable.indicator measurable_const hA1).aemeasurable
          (by simpa [MeasureTheory.lintegral_indicator, hA0, hA1] using hνmass.ge)
      · exact (ae_eq_of_ae_le_of_lintegral_le hle
          (by simp [MeasureTheory.lintegral_indicator, hA1])
          (Measurable.indicator measurable_const hA0).aemeasurable
          (by simpa [MeasureTheory.lintegral_indicator, hA0, hA1] using hνmass.le)).symm
    have heq : ∀ᵐ ω ∂ν, S.SofD false ω = S.SofD true ω := by
      filter_upwards [hmono] with ω hω
      simp only [A0, A1, Set.indicator] at hω
      split_ifs at hω <;> simp_all
    have hmeasure :
        P.μ ({ω | S.SofD false ω = S.SofD true ω ∧ ω ∈ S.complierEvent} ∩
            S.xEvent x) = P.μ (S.complierEvent ∩ S.xEvent x) := by
      let E : Set P.Ω := {ω | S.SofD false ω = S.SofD true ω}
      have hE : MeasurableSet E := by
        dsimp [E]
        exact measurableSet_eq_fun (measurable_POSlate_SofD S false)
          (measurable_POSlate_SofD S true)
      have hν : ν E = ν Set.univ := by
        apply measure_congr
        filter_upwards [heq] with ω hω
        change (ω ∈ E) = (ω ∈ Set.univ)
        simp [E, hω]
      rw [show ν E = P.μ (E ∩ CB) from Measure.restrict_apply hE,
        show ν Set.univ = P.μ (Set.univ ∩ CB) from
          Measure.restrict_apply MeasurableSet.univ] at hν
      have hset : E ∩ CB =
          {ω | S.SofD false ω = S.SofD true ω ∧ ω ∈ S.complierEvent} ∩
            S.xEvent x := by
        ext ω
        simp [E, CB, and_assoc, and_left_comm, and_comm]
      simpa [hset] using hν
    unfold equalSelectionComplierMass conditionalReal
    rw [if_pos hB, if_pos hB]
    congr 1
    exact (measureReal_eq_measureReal_iff).2 hmeasure
  · simp [equalSelectionComplierMass, conditionalReal, hB]

/-- On every supported observable tie cell, weak selection monotonicity collapses selection strata and all three partial-transport faces and cut expressions agree. [the stated conclusion follows](goal). -/
-- @node: prop:tie-face-collapse
theorem tie_face_collapse (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (model : TieSafeSurvivorModel S εZ d) :
    let c := observableCapacities S.observedLaw
    let hIdentification := capacity_identification S εZ d model.ivIndependence
      model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
      model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
    let hValid : ValidCapacities c := hIdentification.1.2
    ∀ x, 0 < S.p x →
      ((incPolytope c hValid x = decPolytope c hValid x ∧
          decPolytope c hValid x = tiePolytope c hValid x) ↔
        c.gap x = 0) ∧
      (c.gap x = 0 →
        equalSelectionComplierMass S x =
          conditionalReal P.μ S.complierEvent (S.xEvent x)) ∧
      (c.gap x = 0 →
        branchFreePolytope c hValid x = incPolytope c hValid x ∧
        branchFreePolytope c hValid x = decPolytope c hValid x ∧
        branchFreePolytope c hValid x = tiePolytope c hValid x) ∧
      (c.gap x = 0 → ∀ t,
        c.lowerLe x t - c.upperLe x t = c.upperGt x t - c.lowerGt x t) := by
  dsimp
  let ident := capacity_identification S εZ d model.ivIndependence
    model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
    model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
  intro x hp
  have hValid : ValidCapacities (observableCapacities S.observedLaw) := ident.1.2
  refine ⟨polytope_tie_iff_gap_zero _ hValid x, ?_, ?_, ?_⟩
  · exact fun hgap => equalSelectionComplierMass_of_zero_gap S d
      model.weakSelectionMonotonicity x (ident.2.2.2.2.1 x hp) hgap
  · intro hgap
    have hstar := branchFree_eq_tie_of_gap_zero _ hValid x hgap
    have hfaces := (polytope_tie_iff_gap_zero _ hValid x).2 hgap
    exact ⟨hstar.trans (hfaces.1.trans hfaces.2).symm,
      hstar.trans hfaces.2.symm, hstar⟩
  · exact fun hgap t => prefix_difference_eq_tail_difference_of_gap_zero _ x hgap t

end CausalSmith.PartialID.SlateBenefitPartialTransport
