import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Transport

/-!
# Linear sparse threshold-flow complexity

The implicit sparse endpoint couplings use linearly many arithmetic/comparison
steps and positive entries; dense materialization is quadratic.
-/

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

/-- The costed implementation evaluates the threshold formulas and constructs sparse endpoint flows in linear time. Materializing both dense matrices is quadratic. The absolute bounds are uniform over all capacity magnitudes. [the stated conclusion follows](goal). -/
-- @node: thm:linear-sparse-threshold-flow
theorem linear_sparse_threshold_flow :
    ∃ sparseConstant denseConstant : ℕ,
      0 < sparseConstant ∧ 0 < denseConstant ∧
      ∀ {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] {K : ℕ},
      3 ≤ K → ∀ c : Capacities 𝒳 K, ∀ hValid : ValidCapacities c,
      thresholdFlowActualCostFor c ≤
          sparseConstant * Fintype.card 𝒳 * K ∧
      thresholdFlowCostFor c hValid ≤
          sparseConstant * Fintype.card 𝒳 * K ∧
      denseThresholdFlowActualCostFor c ≤
          denseConstant * Fintype.card 𝒳 * K ^ 2 ∧
      denseThresholdFlowCostFor c hValid ≤
          denseConstant * Fintype.card 𝒳 * K ^ 2 ∧
      (∀ (c' : Capacities 𝒳 K) (hValid' : ValidCapacities c'),
        thresholdFlowCostFor c hValid = thresholdFlowCostFor c' hValid' ∧
        denseThresholdFlowCostFor c hValid = denseThresholdFlowCostFor c' hValid') ∧
      (∀ x,
        let run := costedSparseThresholdFlow c hValid x
        run.value.1 = (c.benefitLower x, c.benefitUpper x) ∧
        run.value.2.1 = thresholdFlowLowerSparse c hValid x ∧
        run.value.2.2 = thresholdFlowUpperSparse c hValid x ∧
        positiveSupportCard (thresholdFlowLower c hValid x) ≤ 2 * K - 1 ∧
        positiveSupportCard (thresholdFlowUpper c hValid x) ≤ 2 * K - 1 ∧
        thresholdFlowLower c hValid x ∈ branchFreePolytope c hValid x ∧
        benefitMass (thresholdFlowLower c hValid x) = c.benefitLower x ∧
        thresholdFlowUpper c hValid x ∈ branchFreePolytope c hValid x ∧
        benefitMass (thresholdFlowUpper c hValid x) = c.benefitUpper x) := by
  refine ⟨75, 77, by omega, by omega, ?_⟩
  intro 𝒳 _ _ K hK c hValid
  letI : MeasurableSpace 𝒳 := ⊤
  have hCell : sparseCellOperationBudget K ≤ 75 * K := by
    simp [sparseCellOperationBudget]
    omega
  have hActual :
      thresholdFlowActualCostFor c ≤ 75 * Fintype.card 𝒳 * K := by
    rw [thresholdFlowActualCostFor]
    calc
      (∑ x, sparseCellActualOperations c x) ≤
          ∑ _x : 𝒳, sparseCellOperationBudget K :=
        Finset.sum_le_sum fun x _ => sparseCellActualOperations_le_budget hK c x
      _ ≤ ∑ _x : 𝒳, 75 * K := Finset.sum_le_sum fun _ _ => hCell
      _ = 75 * Fintype.card 𝒳 * K := by
        simp [mul_assoc, mul_left_comm, mul_comm]
  have hFixed :
      thresholdFlowCostFor c hValid ≤ 75 * Fintype.card 𝒳 * K := by
    rw [thresholdFlowCostFor]
    calc
      (∑ x, (costedSparseThresholdFlow c hValid x).operations) =
          ∑ _x : 𝒳, sparseCellOperationBudget K := by
        apply Finset.sum_congr rfl
        intro x hx
        rfl
      _ ≤ ∑ _x : 𝒳, 75 * K := Finset.sum_le_sum fun _ _ => hCell
      _ = 75 * Fintype.card 𝒳 * K := by
        simp [mul_assoc, mul_left_comm, mul_comm]
  have hKsq : K ≤ K ^ 2 := by
    rw [pow_two]
    have hOne : 1 ≤ K := by omega
    simpa using Nat.mul_le_mul_left K hOne
  have hActualQuad :
      thresholdFlowActualCostFor c ≤ 75 * Fintype.card 𝒳 * K ^ 2 :=
    hActual.trans (Nat.mul_le_mul_left (75 * Fintype.card 𝒳) hKsq)
  have hFixedQuad :
      thresholdFlowCostFor c hValid ≤ 75 * Fintype.card 𝒳 * K ^ 2 :=
    hFixed.trans (Nat.mul_le_mul_left (75 * Fintype.card 𝒳) hKsq)
  refine ⟨hActual, hFixed, ?_, ?_, ?_, ?_⟩
  · unfold denseThresholdFlowActualCostFor
    calc
      thresholdFlowActualCostFor c + 2 * Fintype.card 𝒳 * K ^ 2 ≤
          75 * Fintype.card 𝒳 * K ^ 2 + 2 * Fintype.card 𝒳 * K ^ 2 :=
        Nat.add_le_add_right hActualQuad _
      _ = 77 * Fintype.card 𝒳 * K ^ 2 := by ring
  · unfold denseThresholdFlowCostFor costedDenseThresholdFlow
    dsimp only [Costed.operations]
    calc
      thresholdFlowCostFor c hValid + 2 * Fintype.card 𝒳 * K ^ 2 ≤
          75 * Fintype.card 𝒳 * K ^ 2 + 2 * Fintype.card 𝒳 * K ^ 2 :=
        Nat.add_le_add_right hFixedQuad _
      _ = 77 * Fintype.card 𝒳 * K ^ 2 := by ring
  · intro c' hValid'
    constructor <;>
      simp [thresholdFlowCostFor, costedSparseThresholdFlow,
        denseThresholdFlowCostFor, costedDenseThresholdFlow]
  · intro x
    have hendpoint := thresholdFlow_endpoint_spec c hValid x
    dsimp only [costedSparseThresholdFlow, Costed.value]
    exact ⟨costedThresholdCuts_value c x, rfl, rfl,
      thresholdFlowLower_positiveSupportCard_le hK c hValid x,
      thresholdFlowUpper_positiveSupportCard_le hK c hValid x,
      hendpoint.1, hendpoint.2.1, hendpoint.2.2.1, hendpoint.2.2.2⟩

end CausalSmith.PartialID.SlateBenefitPartialTransport
