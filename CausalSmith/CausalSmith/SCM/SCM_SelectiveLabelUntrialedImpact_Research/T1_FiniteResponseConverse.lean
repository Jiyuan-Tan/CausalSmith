import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Basic
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.openClassical false

/-!
# Finite-response representation and converse

The model-to-mixture direction and the canonical finite product-space
realization of every legal response-type mixture.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators ENNReal Classical
open MeasureTheory Set

/-- The design incidence matrix is nonnegative and column-stochastic. -/
lemma incidence_stochastic (d : SLCCDesign) :
    (∀ o t, 0 ≤ incidence d o t) ∧ (∀ t, ∑ o, incidence d o t = 1) := by
  sorry

/-- The design-specific label-blind incidence geometry. -/
noncomputable def designGeometry (d : SLCCDesign) :
    SLCCIncidence (ObservableCell d) (LegalResponseType d) (BlindCell d) where
  B := incidence d
  B_nonnegative := (incidence_stochastic d).1
  B_column_sum := (incidence_stochastic d).2
  h := targetVector d
  h_binary := by
    intro t
    simp only [targetVector]
    split <;> simp
  K := fun b o =>
    if b.arm = o.arm ∧ b.stratum = o.stratum ∧
        b.action = o.action ∧ b.outcome = o.outcome then 1 else 0

/-- A model with its ambient probability space bundled existentially. -/
structure SLCCRealization (d : SLCCDesign) where
  Omega : Type
  measurableOmega : MeasurableSpace Omega
  mu : Measure Omega
  probability : IsProbabilityMeasure mu
  model : @SLCCModel d Omega measurableOmega mu probability

instance (d : SLCCDesign) (R : SLCCRealization d) : MeasurableSpace R.Omega :=
  R.measurableOmega

instance (d : SLCCDesign) (R : SLCCRealization d) : IsProbabilityMeasure R.mu :=
  R.probability

/-- The observable cell probabilities induced by a realization. -/
noncomputable def modelObservableLaw (d : SLCCDesign) (R : SLCCRealization d) :
    ObservableCell d → ℝ := fun o =>
  ENNReal.toReal (R.mu {ω |
    R.model.D ω = o.arm ∧ R.model.S ω = o.stratum ∧
    R.model.A ω = o.action ∧ R.model.Y ω = o.outcome ∧
    R.model.Zobs ω = o.label})

/-- The untrialed mean outcome induced by a realization. -/
noncomputable def modelUntrialedMean (d : SLCCDesign) (R : SLCCRealization d) : ℝ :=
  ∫ ω, if R.model.Yc ω (d.config d.untrialed (R.model.S ω)) then 1 else 0 ∂R.mu

/-- The observable-target image of finite selective-label models. -/
noncomputable def modelObservableTargetImage (d : SLCCDesign) :
    Set ((ObservableCell d → ℝ) × ℝ) :=
  Set.range fun R : SLCCRealization d => (modelObservableLaw d R, modelUntrialedMean d R)

/-- Every model induces legal response-type weights, and every legal simplex
weight has a canonical product-space attaining model. -/
-- @node: thm:finite-response-converse
theorem finite_response_converse (d : SLCCDesign) (R : SLCCRealization d) :
    (∃ w ∈ responseSimplex d,
      (incidence d).mulVec w = modelObservableLaw d R ∧
      targetFunctional (designGeometry d) w = modelUntrialedMean d R) ∧
    (∀ w ∈ responseSimplex d,
      ∃ Rw : SLCCRealization d,
        modelObservableLaw d Rw = (incidence d).mulVec w ∧
        modelUntrialedMean d Rw = targetFunctional (designGeometry d) w) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
