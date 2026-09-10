import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.CitedGates
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TTieFaceCollapse

/-!
# Reduction to fixed-marginal ordinal benefit bounds

On the no-selection submodel, survivor-complier capacities are complete
marginals and the threshold formulas reduce to the cited ordinal formulas.
-/

open MeasureTheory Set Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ} {P : POSystem} [StandardBorelSpace P.Ω]

/-- The no selection submodel condition is the stated property of the slate-benefit partial-transport model. -/
def NoSelectionSubmodel (S : POSlateSystem P 𝒳 K) : Prop :=
  ∀ x, 0 < conditionalReal P.μ S.complierEvent (S.xEvent x) →
    conditionalReal P.μ
      {ω | S.SofD false ω = true ∧ S.SofD true ω = true ∧ ω ∈ S.complierEvent}
      (S.complierEvent ∩ S.xEvent x) = 1

-- @node: selectedComplierMass_eq_complierMass_of_noSelection
/-- Given [the stated hypotheses](hyp:hNoSelection), [the selected complier mass equals complier mass whenever no selection property holds](goal). -/
theorem selectedComplierMass_eq_complierMass_of_noSelection
    (S : POSlateSystem P 𝒳 K) (hNoSelection : NoSelectionSubmodel S) (x : 𝒳) :
    selectedComplierMass S false x =
        conditionalReal P.μ S.complierEvent (S.xEvent x) ∧
      selectedComplierMass S true x =
        conditionalReal P.μ S.complierEvent (S.xEvent x) := by
  let B : Set P.Ω := S.xEvent x
  let C : Set P.Ω := S.complierEvent
  let A0 : Set P.Ω := {w | S.SofD false w = true}
  let A1 : Set P.Ω := {w | S.SofD true w = true}
  change conditionalReal P.μ (A0 ∩ C) B = conditionalReal P.μ C B ∧
    conditionalReal P.μ (A1 ∩ C) B = conditionalReal P.μ C B
  by_cases hB : 0 < P.μ.real B
  · have hcond : conditionalReal P.μ C B = P.μ.real (C ∩ B) / P.μ.real B := by
      simp [conditionalReal, hB]
    by_cases hC : 0 < conditionalReal P.μ C B
    · have hCB : 0 < P.μ.real (C ∩ B) := by
        rw [hcond] at hC
        rcases div_pos_iff.mp hC with hpos | hneg
        · exact hpos.1
        · linarith [hneg.2, hB]
      have hsurv := hNoSelection x hC
      have hsurv' :
          P.μ.real ((A0 ∩ A1 ∩ C) ∩ (C ∩ B)) = P.μ.real (C ∩ B) := by
        unfold conditionalReal at hsurv
        rw [if_pos hCB] at hsurv
        apply (div_eq_one_iff_eq (ne_of_gt hCB)).mp
        have hset :
            {w | S.SofD false w = true ∧ S.SofD true w = true ∧
              w ∈ S.complierEvent} ∩ (S.complierEvent ∩ S.xEvent x) =
              (A0 ∩ A1 ∩ C) ∩ (C ∩ B) := by
          ext w
          simp [A0, A1, C, B, and_assoc, and_left_comm, and_comm]
        rw [hset] at hsurv
        exact hsurv
      have hsurv0 : (A0 ∩ A1 ∩ C) ∩ (C ∩ B) ⊆ (A0 ∩ C) ∩ B := by
        intro w hw
        exact ⟨⟨hw.1.1.1, hw.1.2⟩, hw.2.2⟩
      have hsurv1 : (A0 ∩ A1 ∩ C) ∩ (C ∩ B) ⊆ (A1 ∩ C) ∩ B := by
        intro w hw
        exact ⟨⟨hw.1.1.2, hw.1.2⟩, hw.2.2⟩
      have hsel0 : P.μ.real ((A0 ∩ C) ∩ B) = P.μ.real (C ∩ B) :=
        le_antisymm (measureReal_mono (by intro w hw; exact ⟨hw.1.2, hw.2⟩))
          (hsurv' ▸ measureReal_mono hsurv0)
      have hsel1 : P.μ.real ((A1 ∩ C) ∩ B) = P.μ.real (C ∩ B) :=
        le_antisymm (measureReal_mono (by intro w hw; exact ⟨hw.1.2, hw.2⟩))
          (hsurv' ▸ measureReal_mono hsurv1)
      unfold conditionalReal
      simp only [hB, if_pos]
      exact ⟨congrArg (fun z => z / P.μ.real B) hsel0,
        congrArg (fun z => z / P.μ.real B) hsel1⟩
    · have hC0 : conditionalReal P.μ C B = 0 :=
        le_antisymm (not_lt.mp hC) (by rw [hcond]; positivity)
      have hCB0 : P.μ.real (C ∩ B) = 0 := by
        rw [hcond] at hC0
        exact (div_eq_zero_iff.mp hC0).resolve_right (ne_of_gt hB)
      have hsel0 : P.μ.real ((A0 ∩ C) ∩ B) = 0 :=
        le_antisymm (hCB0 ▸ measureReal_mono (by intro w hw; exact ⟨hw.1.2, hw.2⟩))
          (by positivity)
      have hsel1 : P.μ.real ((A1 ∩ C) ∩ B) = 0 :=
        le_antisymm (hCB0 ▸ measureReal_mono (by intro w hw; exact ⟨hw.1.2, hw.2⟩))
          (by positivity)
      rw [hC0]
      unfold conditionalReal
      rw [if_pos hB, if_pos hB]
      exact ⟨by rw [hsel0, zero_div], by rw [hsel1, zero_div]⟩
  · simp [conditionalReal, hB]

-- @node: finset_sup'_div_pos
/-- Given [the stated hypotheses](hyp:hs,hm), [the finset sup' div pos property holds](goal). -/
theorem finset_sup'_div_pos {I : Type*} [DecidableEq I] (s : Finset I)
    (hs : s.Nonempty) (f : I → ℝ) {m : ℝ} (hm : 0 < m) :
    s.sup' hs f / m = s.sup' hs (fun i => f i / m) := by
  apply le_antisymm
  · apply (div_le_iff₀ hm).2
    apply Finset.sup'_le hs
    intro i hi
    have h := Finset.le_sup' (fun i => f i / m) hi
    have hi' : f i ≤ s.sup' hs (fun i => f i / m) * m := (div_le_iff₀ hm).1 h
    simpa [mul_comm] using hi'
  · apply Finset.sup'_le hs
    intro i hi
    exact (div_le_div_iff_of_pos_right hm).2 (Finset.le_sup' f hi)

-- @node: finset_inf'_div_pos
/-- Given [the stated hypotheses](hyp:hs,hm), [the finset inf' div pos property holds](goal). -/
theorem finset_inf'_div_pos {I : Type*} [DecidableEq I] (s : Finset I)
    (hs : s.Nonempty) (f : I → ℝ) {m : ℝ} (hm : 0 < m) :
    s.inf' hs f / m = s.inf' hs (fun i => f i / m) := by
  apply le_antisymm
  · apply Finset.le_inf' hs
    intro i hi
    exact (div_le_div_iff_of_pos_right hm).2 (Finset.inf'_le f hi)
  · apply (le_div_iff₀ hm).2
    apply Finset.le_inf' hs
    intro i hi
    have h := Finset.inf'_le (fun i => f i / m) hi
    exact (le_div_iff₀ hm).1 h

/-- Conditional on the cited fixed-marginal theorem, the no-selection submodel has zero capacity gap and the full coupling polytope in every supported cell, including zero-complier-mass cells. The normalized strict-benefit formulas are asserted when the cell mass is positive. [the stated conclusion follows](goal). -/
-- @node: thm:no-selection-reduction
theorem no_selection_reduction
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (_hIV : IVIndependence S) (_hNoDefiers : NoDefiers S)
    (model : TieSafeSurvivorModel S εZ d)
    (_hNoSelection : NoSelectionSubmodel S)
    (_hOrdinalFixedMarginalStrictBenefit_of_gate : OrdinalFixedMarginalStrictBenefit) :
    let c := observableCapacities S.observedLaw
    let hIdentification := capacity_identification S εZ d model.ivIndependence
      model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
      model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
    let hValid : ValidCapacities c := hIdentification.1.2
    ∀ x, 0 < S.p x →
      c.gap x = 0 ∧ branchFreePolytope c hValid x = tiePolytope c hValid x ∧
      (0 < c.mass x →
        c.benefitLower x / c.mass x =
          max 0 (Finset.univ.sup' Finset.univ_nonempty
            (fun t : Option (Fin K) => match t with
              | none => 0
              | some k => (c.lowerLe x k - c.upperLe x k) / c.mass x)) ∧
      c.benefitUpper x / c.mass x =
          Finset.univ.inf' Finset.univ_nonempty
            (fun t : Option (Fin K) => match t with
              | none => 1
              | some k => (c.lowerLt x k + c.upperGt x k) / c.mass x)) := by
  dsimp
  let ident := capacity_identification S εZ d model.ivIndependence
    model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
    model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
  intro x hp
  have hmasses := selectedComplierMass_eq_complierMass_of_noSelection S _hNoSelection x
  have hgapIdent := ident.2.2.2.2.1 x hp
  have hgap : (observableCapacities S.observedLaw).gap x = 0 := by
    rw [hmasses.2, hmasses.1] at hgapIdent
    linarith
  have hValid : ValidCapacities (observableCapacities S.observedLaw) := ident.1.2
  refine ⟨hgap, branchFree_eq_tie_of_gap_zero _ hValid x hgap, ?_⟩
  intro hm
  constructor
  · rw [Capacities.benefitLower, finset_sup'_div_pos _ _ _ hm]
    change Finset.univ.sup' Finset.univ_nonempty
        (fun t : Option (Fin K) => (match t with
          | none => 0
          | some k => (observableCapacities S.observedLaw).lowerLe x k -
            (observableCapacities S.observedLaw).upperLe x k +
              min ((observableCapacities S.observedLaw).gap x) 0) /
                (observableCapacities S.observedLaw).mass x) = _
    simp only [hgap, min_eq_left (le_refl 0), add_zero]
    have hzero : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun t : Option (Fin K) => match t with
          | none => 0
          | some k => ((observableCapacities S.observedLaw).lowerLe x k -
            (observableCapacities S.observedLaw).upperLe x k) /
              (observableCapacities S.observedLaw).mass x) := by
      exact Finset.le_sup'
        (fun t : Option (Fin K) => match t with
          | none => 0
          | some k => ((observableCapacities S.observedLaw).lowerLe x k -
            (observableCapacities S.observedLaw).upperLe x k) /
              (observableCapacities S.observedLaw).mass x)
        (Finset.mem_univ (none : Option (Fin K)))
    rw [max_eq_right hzero]
    apply congrArg (Finset.univ.sup' Finset.univ_nonempty)
    funext t
    cases t <;> simp [add_zero, zero_div]
  · rw [Capacities.benefitUpper, finset_inf'_div_pos _ _ _ hm]
    apply congrArg (Finset.univ.inf' Finset.univ_nonempty)
    funext t
    cases t with
    | none =>
        change (observableCapacities S.observedLaw).mass x /
          (observableCapacities S.observedLaw).mass x = 1
        exact div_self (ne_of_gt hm)
    | some k => rfl

end CausalSmith.PartialID.SlateBenefitPartialTransport
