import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.BernsteinSpan
import Causalean.Mathlib.IndepIntegral
import Causalean.Mathlib.CondIndep
import Causalean.Mathlib.Probability.BernoulliMeasure

/-! # Reduction from the hierarchical model to Bernstein moments -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The cluster-equally-weighted mean potential-outcome contrast of a model. -/
noncomputable def modelAte {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ} {ε : ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : HierarchicalPlateModel m n ε P) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (m : ℝ)⁻¹ * ∑ j,
    ((∫ ω, (if M.Y1 i j ω then (1 : ℝ) else 0) ∂P) -
      ∫ ω, (if M.Y0 i j ω then (1 : ℝ) else 0) ∂P)

/-- Forward observable and causal implications of a hierarchical plate model. -/
def MomentReductionForward {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ} {ε : ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : HierarchicalPlateModel m n ε P) : Prop :=
  (∀ i, Measure.map (M.Q i) P = M.mu) ∧
  (∀ i c, ∀ᵐ q ∂Measure.map (M.Q i) P,
    condDistrib (M.C i) (M.Q i) P q {c} =
      ENNReal.ofReal (bernsteinCoordinate m c q)) ∧
  (∀ i c, Measure.map (M.C i) P {c} =
    ENNReal.ofReal (∫ q, bernsteinCoordinate m c q ∂M.mu)) ∧
  modelAte P M = ateFunctional M.mu

/-- Existence of an explicit hierarchical model for a supplied mixing law. -/
def MomentReductionConverse (m n : ℕ) (ε : ℝ) (μ : Measure CellLaw) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω)
      (P : @Measure Ω mΩ) (hP : @IsProbabilityMeasure Ω mΩ P),
    ∃ M : @HierarchicalPlateModel m n ε Ω mΩ P hP,
      M.mu = μ ∧ MomentReductionForward P M

/-- The plate assumptions yield the multinomial Bernstein moment law and the
ATE formula for every supplied hierarchical model. -/
-- @node: lem:scm-moment-reduction
lemma scm_moment_reduction {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ} {ε : ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (M : HierarchicalPlateModel m n ε P) :
    MomentReductionForward P M := by
  sorry

/-- Every overlap-supported mixing law has the explicit Bernoulli-kernel
hierarchical construction, independently of whether a model was supplied. -/
lemma scm_moment_converse (m n : ℕ) (ε : ℝ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hε0 : 0 < ε)
    (hεhalf : ε < (1 / 2 : ℝ)) :
    ∀ μ, IsMixingLaw ε μ → MomentReductionConverse m n ε μ := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
