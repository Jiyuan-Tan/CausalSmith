import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TFullLawEndpointAttainment

/-!
# Sharp exact-mass threshold interval

The cellwise exact-mass projection, sharp threshold cut values, and aggregate
identified interval are stated together.
-/

open scoped BigOperators
open MeasureTheory Set Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

universe uV uVal uOmega uCell

variable {𝒳 : Type uCell} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ} {P : POSystem.{uV, uVal, uOmega}} [StandardBorelSpace P.Ω]

/-- Every compatible law projects exactly onto the exact-mass capacity polytope; the sharp cellwise extrema are the threshold cuts, and aggregation gives the closed endpoint interval with zero contribution from zero-survivor cells. [the stated conclusion follows](goal). -/
-- @node: thm:sharp-exact-mass-threshold-interval
theorem sharp_exact_mass_threshold_interval
    (S : POSlateSystem P 𝒳 K) (εZ : ℝ) (d : 𝒳 → Bool)
    (model : TieSafeSurvivorModel S εZ d) :
    let c := observableCapacities S.observedLaw
    let hIdentification := capacity_identification S εZ d model.ivIndependence
      model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
      model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
    let hValid : ValidCapacities c := hIdentification.1.2
    let hp : ∀ x, 0 ≤ S.p x := hIdentification.2.1
    let hMass : 0 < c.aggregateMass S.p := model.positiveAggregateSurvivors
    (∀ x, 0 < S.p x →
      {γ | ∃ W : FullLawCandidate P 𝒳 K, FullLawFeasible S.observedLaw W ∧
          γ = fullLawSurvivorCoupling W x} = branchFreePolytope c hValid x) ∧
    (∀ x, 0 < S.p x →
      (0 < c.gap x → branchFreePolytope c hValid x = incPolytope c hValid x) ∧
      (c.gap x < 0 → branchFreePolytope c hValid x = decPolytope c hValid x) ∧
      (c.gap x = 0 → branchFreePolytope c hValid x = tiePolytope c hValid x)) ∧
    (∀ x, 0 < S.p x →
      sInf (benefitMass '' branchFreePolytope c hValid x) = c.benefitLower x ∧
      sSup (benefitMass '' branchFreePolytope c hValid x) = c.benefitUpper x) ∧
    (∀ x, c.mass x = 0 → branchFreePolytope c hValid x = {0}) ∧
    Causalean.PartialID.IdentifiedInterval
      (fun W : FullLawCandidate P 𝒳 K => benefitProbabilityOf W)
      (fun W : FullLawCandidate P 𝒳 K => FullLawFeasible S.observedLaw W) =
        c.identifiedIcc S.p S.observedLaw rfl (p_eq_observedCellWeights S)
          hValid hp hMass (observedLawDomain S) ∧
    (∀ x, 0 < S.p x →
      thresholdFlowLower c hValid x ∈ branchFreePolytope c hValid x ∧
      benefitMass (thresholdFlowLower c hValid x) = c.benefitLower x ∧
      thresholdFlowUpper c hValid x ∈ branchFreePolytope c hValid x ∧
      benefitMass (thresholdFlowUpper c hValid x) = c.benefitUpper x) := by
  dsimp only
  let ident := capacity_identification S εZ d model.ivIndependence
    model.treatmentConsistency model.selectionExclusion model.outcomeExclusion
    model.instrumentOverlap model.noDefiers model.weakSelectionMonotonicity
  let c := observableCapacities S.observedLaw
  have hValid : ValidCapacities c := ident.1.2
  have hp : ∀ x, 0 ≤ S.p x := ident.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    ext γ
    constructor
    · rintro ⟨W, hW, rfl⟩
      rcases hW with ⟨εW, dW, modelW, hlaw⟩
      letI : StandardBorelSpace W.system.Ω := W.slate.borel
      exact fullLawSurvivorCoupling_mem_branchFree_of_observedLaw_eq
        S W εW dW modelW hlaw hValid x hx
    · intro hγ
      let gammaFamily : ∀ y : 𝒳, Coupling K := fun y =>
        if y = x then γ else thresholdFlowLower c hValid y
      have hgammaFamily : ∀ y, gammaFamily y ∈ branchFreePolytope c hValid y := by
        intro y
        by_cases hy : y = x
        · subst y
          simpa [gammaFamily] using hγ
        · simpa [gammaFamily, hy] using
            (thresholdFlow_endpoint_spec c hValid y).1
      obtain ⟨W, hfeas, hrealizes, _hbenefit⟩ :=
        full_law_branchFree_family_attainment S εZ d model gammaFamily hgammaFamily
      refine ⟨W, hfeas, ?_⟩
      have hr := hrealizes x hx
      simpa [gammaFamily] using hr.symm
  · intro x _hx
    constructor
    · intro hgap
      have hq : c.q0 x ≤ c.q1 x := by
        unfold Capacities.gap at hgap
        linarith
      ext γ
      constructor
      · intro hγ
        exact ⟨hγ.1, branchFree_exact_rows_of_q0_le_q1 c hValid x hq hγ,
          hγ.2.2.1⟩
      · intro hγ
        change matrixNonnegative γ ∧ (∀ i, rowMass γ i ≤ c.lower x i) ∧
          (∀ j, columnMass γ j ≤ c.upper x j) ∧ totalMass γ = c.mass x
        refine ⟨hγ.1, fun i => (hγ.2.1 i).le, hγ.2.2, ?_⟩
        rw [← sum_rowMass_eq_totalMass]
        calc
          (∑ i, rowMass γ i) = c.q0 x := by
            exact Finset.sum_congr rfl fun i _ => hγ.2.1 i
          _ = c.mass x := by simp [Capacities.mass, min_eq_left hq]
    constructor
    · intro hgap
      have hq : c.q1 x ≤ c.q0 x := by
        unfold Capacities.gap at hgap
        linarith
      ext γ
      constructor
      · intro hγ
        exact ⟨hγ.1, hγ.2.1,
          branchFree_exact_columns_of_q1_le_q0 c hValid x hq hγ⟩
      · intro hγ
        change matrixNonnegative γ ∧ (∀ i, rowMass γ i ≤ c.lower x i) ∧
          (∀ j, columnMass γ j ≤ c.upper x j) ∧ totalMass γ = c.mass x
        refine ⟨hγ.1, hγ.2.1, fun j => (hγ.2.2 j).le, ?_⟩
        rw [← sum_columnMass_eq_totalMass]
        calc
          (∑ j, columnMass γ j) = c.q1 x := by
            exact Finset.sum_congr rfl fun j _ => hγ.2.2 j
          _ = c.mass x := by simp [Capacities.mass, min_eq_right hq]
    · exact branchFree_eq_tie_of_gap_zero c hValid x
  · intro x _hx
    have hflow := thresholdFlow_endpoint_spec c hValid x
    constructor
    · apply le_antisymm
      · apply csInf_le
        · refine ⟨c.benefitLower x, ?_⟩
          intro y hy
          rcases hy with ⟨γ, hγ, rfl⟩
          exact branchFree_lower_le_benefitMass c hValid x hγ
        · exact ⟨thresholdFlowLower c hValid x, hflow.1, hflow.2.1⟩
      · apply le_csInf
        · exact ⟨c.benefitLower x,
            thresholdFlowLower c hValid x, hflow.1, hflow.2.1⟩
        · intro y hy
          rcases hy with ⟨γ, hγ, rfl⟩
          exact branchFree_lower_le_benefitMass c hValid x hγ
    · apply le_antisymm
      · apply csSup_le
        · exact ⟨c.benefitUpper x,
            thresholdFlowUpper c hValid x, hflow.2.2.1, hflow.2.2.2⟩
        · intro y hy
          rcases hy with ⟨γ, hγ, rfl⟩
          exact branchFree_benefitMass_le_upper c hValid x hγ
      · apply le_csSup
        · refine ⟨c.benefitUpper x, ?_⟩
          intro y hy
          rcases hy with ⟨γ, hγ, rfl⟩
          exact branchFree_benefitMass_le_upper c hValid x hγ
        · exact ⟨thresholdFlowUpper c hValid x, hflow.2.2.1, hflow.2.2.2⟩
  · intro x hmass
    exact branchFreePolytope_eq_singleton_zero_of_mass_eq_zero c hValid x hmass
  · let L := (c.endpointMap S.p S.observedLaw rfl (p_eq_observedCellWeights S)
      hValid hp model.positiveAggregateSurvivors (observedLawDomain S)).endpoints.1
    let U := (c.endpointMap S.p S.observedLaw rfl (p_eq_observedCellWeights S)
      hValid hp model.positiveAggregateSurvivors (observedLawDomain S)).endpoints.2
    have hcellLU : ∀ x, c.benefitLower x ≤ c.benefitUpper x := by
      intro x
      have hflow := thresholdFlow_endpoint_spec c hValid x
      rw [← hflow.2.1]
      exact branchFree_benefitMass_le_upper c hValid x hflow.1
    have hsumLU : (∑ x, S.p x * c.benefitLower x) ≤
        ∑ x, S.p x * c.benefitUpper x := by
      exact Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hcellLU x) (hp x)
    have hLU : L ≤ U := by
      dsimp [L, U, Capacities.endpointMap]
      exact (div_le_div_iff_of_pos_right model.positiveAggregateSurvivors).2 hsumLU
    have houter : Causalean.PartialID.IdentifiedInterval
        (fun W : FullLawCandidate P 𝒳 K => benefitProbabilityOf W)
        (fun W : FullLawCandidate P 𝒳 K => FullLawFeasible S.observedLaw W) ⊆
        Set.Icc L U := by
      rintro _ ⟨Wsub, rfl⟩
      let W := Wsub.1
      have hW : FullLawFeasible S.observedLaw W := Wsub.2
      rcases hW with ⟨εW, dW, modelW, hlaw⟩
      letI : StandardBorelSpace W.system.Ω := W.slate.borel
      have hpW : ∀ x, W.slate.p x = S.p x :=
        (observedLaw_eq_transfers_p_propensity S W.slate hlaw).1
      have hproj : ∀ x, 0 < S.p x →
          fullLawSurvivorCoupling W x ∈ branchFreePolytope c hValid x := by
        intro x hx
        exact fullLawSurvivorCoupling_mem_branchFree_of_observedLaw_eq
          S W εW dW modelW hlaw hValid x hx
      have hden : (∑ x, W.slate.p x * totalMass
          (fullLawSurvivorCoupling W x)) = c.aggregateMass S.p := by
        unfold Capacities.aggregateMass
        apply Finset.sum_congr rfl
        intro x _
        rw [hpW x]
        by_cases hx : 0 < S.p x
        · rw [(hproj x hx).2.2.2]
        · have hx0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (hp x)
          simp [hx0]
      have hobj := benefitProbabilityOf_eq_aggregate W
        (hden.symm ▸ model.positiveAggregateSurvivors)
      rw [hden] at hobj
      have hnumLower : (∑ x, S.p x * c.benefitLower x) ≤
          ∑ x, W.slate.p x * benefitMass (fullLawSurvivorCoupling W x) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hpW x]
        by_cases hx : 0 < S.p x
        · exact mul_le_mul_of_nonneg_left
            (branchFree_lower_le_benefitMass c hValid x (hproj x hx)) (hp x)
        · have hx0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (hp x)
          simp [hx0]
      have hnumUpper : (∑ x, W.slate.p x * benefitMass
          (fullLawSurvivorCoupling W x)) ≤
          ∑ x, S.p x * c.benefitUpper x := by
        apply Finset.sum_le_sum
        intro x _
        rw [hpW x]
        by_cases hx : 0 < S.p x
        · exact mul_le_mul_of_nonneg_left
            (branchFree_benefitMass_le_upper c hValid x (hproj x hx)) (hp x)
        · have hx0 : S.p x = 0 := le_antisymm (not_lt.mp hx) (hp x)
          simp [hx0]
      change benefitProbabilityOf W ∈ Set.Icc L U
      rw [hobj]
      constructor
      · dsimp [L, Capacities.endpointMap]
        exact (div_le_div_iff_of_pos_right model.positiveAggregateSurvivors).2 hnumLower
      · dsimp [U, Capacities.endpointMap]
        exact (div_le_div_iff_of_pos_right model.positiveAggregateSurvivors).2 hnumUpper
    apply Set.Subset.antisymm
    · simpa [L, U, Capacities.identifiedIcc, Capacities.endpointMap] using houter
    · intro y hy
      change L ≤ y ∧ y ≤ U at hy
      by_cases hEq : L = U
      · have hyL : y = L := by linarith
        let gamma : ∀ x : 𝒳, Coupling K := fun x => thresholdFlowLower c hValid x
        have hgamma : ∀ x, gamma x ∈ branchFreePolytope c hValid x := by
          intro x
          exact (thresholdFlow_endpoint_spec c hValid x).1
        obtain ⟨W, hfeas, _hrealizes, hbenefit⟩ :=
          full_law_branchFree_family_attainment S εZ d model gamma hgamma
        refine ⟨⟨W, hfeas⟩, ?_⟩
        rw [hyL]
        change benefitProbabilityOf W = L
        rw [hbenefit]
        dsimp [L, Capacities.endpointMap]
        apply congrArg (fun z => z / c.aggregateMass S.p)
        apply Finset.sum_congr rfl
        intro x _
        rw [(thresholdFlow_endpoint_spec c hValid x).2.1]
      · have hlt : L < U := lt_of_le_of_ne hLU hEq
        let t : ℝ := (y - L) / (U - L)
        have ht0 : 0 ≤ t := by
          dsimp [t]
          exact div_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hLU)
        have ht1 : t ≤ 1 := by
          dsimp [t]
          apply (div_le_one (sub_pos.mpr hlt)).2
          linarith
        let gamma : ∀ x : 𝒳, Coupling K := fun x => couplingSegment t
          (thresholdFlowLower c hValid x) (thresholdFlowUpper c hValid x)
        have hgamma : ∀ x, gamma x ∈ branchFreePolytope c hValid x := by
          intro x
          exact couplingSegment_mem_branchFree c hValid x
            (thresholdFlow_endpoint_spec c hValid x).1
            (thresholdFlow_endpoint_spec c hValid x).2.2.1 ht0 ht1
        obtain ⟨W, hfeas, _hrealizes, hbenefit⟩ :=
          full_law_branchFree_family_attainment S εZ d model gamma hgamma
        refine ⟨⟨W, hfeas⟩, ?_⟩
        change benefitProbabilityOf W = y
        rw [hbenefit]
        have hnum : (∑ x, S.p x * benefitMass (gamma x)) =
            (1 - t) * (∑ x, S.p x * c.benefitLower x) +
              t * (∑ x, S.p x * c.benefitUpper x) := by
          simp_rw [gamma, benefitMass_couplingSegment,
            (thresholdFlow_endpoint_spec c hValid _).2.1,
            (thresholdFlow_endpoint_spec c hValid _).2.2.2]
          simp only [mul_add, Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
        rw [hnum]
        have hmassne : c.aggregateMass S.p ≠ 0 :=
          ne_of_gt model.positiveAggregateSurvivors
        have haffine : ((1 - t) * (∑ x, S.p x * c.benefitLower x) +
              t * (∑ x, S.p x * c.benefitUpper x)) /
              c.aggregateMass S.p = (1 - t) * L + t * U := by
          dsimp [L, U, Capacities.endpointMap]
          field_simp
        rw [haffine]
        dsimp [t]
        field_simp [sub_ne_zero.mpr hEq]
        ring
  · intro x _hx
    exact thresholdFlow_endpoint_spec c hValid x

end CausalSmith.PartialID.SlateBenefitPartialTransport
