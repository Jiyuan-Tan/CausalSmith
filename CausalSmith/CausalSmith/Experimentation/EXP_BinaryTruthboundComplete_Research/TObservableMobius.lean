import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BooleanMobius

/-! Observable-rule characterization by Boolean Mobius support. -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- Universal randomization conservativeness of an assignment rule. -/
def UniversallyConservative (E : Setup) (g : AssignmentRule E) : Prop :=
  ∀ θ, E.design.Var (fun z => score E z θ) ≤ expectedRule E g θ

/-- For [an experiment](hyp:E), [assignment-rule expectations are exactly the functions in the unrestricted observable span, equivalently those whose Möbius coefficients vanish off the observable complex; supported coefficients have the displayed implementation, and universal conservativeness is exactly pointwise domination of true variance](goal). -/
-- @node: thm:observable-mobius
theorem expectedRule_mem_observableSpan_iff (E : Setup) :
    (∀ b : Theta E → ℝ,
      ((∃ g : AssignmentRule E, expectedRule E g = b) ↔ b ∈ observableSpan E ⊤) ∧
      (b ∈ observableSpan E ⊤ ↔
        ∀ S, S ∉ observableComplex E →
          (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * b (vertex E T)) = 0)) ∧
    (∀ a : Finset (Fin E.K) → ℝ,
      (∀ S, S ∉ observableComplex E → a S = 0) →
      expectedRule E (mobiusImplementation E a) =
        fun θ => ∑ S, a S * monomial E S θ) ∧
    (∀ g : AssignmentRule E,
      UniversallyConservative E g ↔
        ∀ θ, trueVarianceFn E θ ≤ expectedRule E g θ) := by
  refine ⟨?_, expectedRule_mobiusImplementation E, ?_⟩
  · intro b
    constructor
    · constructor
      · rintro ⟨g, rfl⟩
        exact expectedRule_mem_observableSpan E g
      · intro hb
        refine ⟨mobiusImplementation E (beta E b), ?_⟩
        rw [expectedRule_mobiusImplementation E (beta E b)
          ((observableSpan_iff_beta_vanishes E b).mp hb)]
        funext θ
        exact (boolean_mobius_expansion E b θ).symm
    · simpa only [beta] using observableSpan_iff_beta_vanishes E b
  · intro g
    unfold UniversallyConservative
    constructor <;> intro h θ
    · rw [designVarianceFn_eq_Var]
      exact h θ
    · have hθ := h θ
      rwa [designVarianceFn_eq_Var] at hθ

end CausalSmith.Experimentation.BinaryTruthbound
