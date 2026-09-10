import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Divergence
import Mathlib.Probability.Kernel.CondDistrib

/-! # Conditional bow, mixture, and adaptive-hinge classes -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Common-conull reverse-support kernel class. -/
def reverseSupportSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (muX : Measure X) (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | (∀ a, IsMarkovKernel (P a)) ∧ (∀ a, IsMarkovKernel (Q a)) ∧
    CondReverseSupport muX P Q}

/-- One-sided conditional bow witness bundle. -/
-- @node: def:conditional-bow-compatible-one-sided
structure CondBowCompatibleOneSided {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P Q : Bool → Kernel X Y) : Prop where
  realization : ∃ w : CondBowWitness X Y,
    CondBowArchitecture w ∧ CondConsistency w ∧ w.covariateLaw = muX ∧
      ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧
        ∀ x ∈ S, ∀ a, w.condProp a x = e a x ∧
          w.condArmLaw a x = P a x ∧ w.condIntervLaw a x = Q a x
  architecture : ∃ w : CondBowWitness X Y, CondBowArchitecture w
  overlap : CondOverlap kappa e
  consistency : ∃ w : CondBowWitness X Y, CondConsistency w
  observed_markov : ∀ a, IsMarkovKernel (P a)
  candidate_markov : ∀ a, IsMarkovKernel (Q a)

/-- Globally realized one-sided conditional class, on one common conull set. -/
def condBowCompatibleOneSidedSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | IsProbabilityMeasure muX ∧ CondOverlap kappa e ∧
    CondBowCompatibleOneSided kappa muX e P Q}
  -- @realizes \mathfrak M^{\to}_{\mu_X,\boldsymbol e}(\boldsymbol P)(global one-sided class)

/-- One-sided conditional mixture witness bundle. -/
-- @node: def:conditional-mixture-class-one-sided
structure CondMixtureClassOneSided {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P Q : Bool → Kernel X Y) : Prop where
  overlap : CondOverlap kappa e
  covariate_probability : IsProbabilityMeasure muX
  observed_markov : ∀ a, IsMarkovKernel (P a)
  candidate_markov : ∀ a, IsMarkovKernel (Q a)
  representation : ∃ R : Bool → Kernel X Y, (∀ a, IsMarkovKernel (R a)) ∧
    ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧ ∀ x ∈ S, ∀ a,
      Q a x = ENNReal.ofReal (e a x) • P a x +
        ENNReal.ofReal (1 - e a x) • R a x

/-- Kernel mixtures with arbitrary residual Markov kernels. -/
def condMixtureClassOneSidedSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | CondMixtureClassOneSided kappa muX e P Q}
  -- @realizes \mathfrak L^{\to}_{\mu_X,\boldsymbol e}(\boldsymbol P)(kernel-mixture class)
  -- @realizes \boldsymbol R(residual Markov-kernel pair)

/-- Mutual-support conditional bow witness bundle. -/
-- @node: def:conditional-bow-compatible
structure CondBowCompatible {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P Q : Bool → Kernel X Y) : Prop where
  realization : ∃ w : CondBowWitness X Y,
    CondBowArchitecture w ∧ CondConsistency w ∧ w.covariateLaw = muX ∧
      ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧
        ∀ x ∈ S, ∀ a, w.condProp a x = e a x ∧
          w.condArmLaw a x = P a x ∧ w.condIntervLaw a x = Q a x ∧
            (Q a x).AbsolutelyContinuous (P a x)
  architecture : ∃ w : CondBowWitness X Y, CondBowArchitecture w
  overlap : CondOverlap kappa e
  consistency : ∃ w : CondBowWitness X Y, CondConsistency w
  reverse_support : CondReverseSupport muX P Q
  observed_markov : ∀ a, IsMarkovKernel (P a)
  candidate_markov : ∀ a, IsMarkovKernel (Q a)

/-- Globally realized conditional class with reverse support on the same set. -/
def condBowCompatibleSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | IsProbabilityMeasure muX ∧ CondOverlap kappa e ∧
    CondBowCompatible kappa muX e P Q}
  -- @realizes \mathfrak M_{\mu_X,\boldsymbol e}(\boldsymbol P)(global mutual-support class)

/-- Mutual-support conditional mixture witness bundle. -/
-- @node: def:conditional-mixture-class
structure CondMixtureClass {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P Q : Bool → Kernel X Y) : Prop where
  overlap : CondOverlap kappa e
  covariate_probability : IsProbabilityMeasure muX
  observed_markov : ∀ a, IsMarkovKernel (P a)
  candidate_markov : ∀ a, IsMarkovKernel (Q a)
  representation : ∃ R : Bool → Kernel X Y, (∀ a, IsMarkovKernel (R a)) ∧
    ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧ ∀ x ∈ S, ∀ a,
      Q a x = ENNReal.ofReal (e a x) • P a x +
        ENNReal.ofReal (1 - e a x) • R a x ∧
      (R a x).AbsolutelyContinuous (P a x)

/-- Kernel mixtures whose residual kernels are dominated by observed kernels. -/
def condMixtureClassSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | CondMixtureClass kappa muX e P Q}
  -- @realizes \mathfrak L_{\mu_X,\boldsymbol e}(\boldsymbol P)(dominated residual kernel class)

/-- One-sided fiberwise adaptive-hinge membership bundle. -/
-- @node: def:conditional-adaptive-hinge-ball-one-sided
structure CondAdaptiveHingeBallOneSided {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P Q : Bool → Kernel X Y) : Prop where
  overlap : CondOverlap kappa e
  covariate_probability : IsProbabilityMeasure muX
  observed_markov : ∀ a, IsMarkovKernel (P a)
  candidate_markov : ∀ a, IsMarkovKernel (Q a)
  fiberwise : ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧ ∀ x ∈ S, ∀ a,
    (P a x).AbsolutelyContinuous (Q a x) ∧
      fDiv (adaptiveHinge (e a x)) (P a x) (Q a x) ≤
        (divRadius (adaptiveHinge (e a x)) (e a x) : EReal)

/-- Fiberwise, nonintegrated one-sided adaptive-hinge class. -/
noncomputable def condAdaptiveHingeBallOneSidedSet {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | CondAdaptiveHingeBallOneSided kappa muX e P Q}
  -- @realizes \mathfrak B^{\mathrm{ad},\to}_{\mu_X,\boldsymbol e}(\boldsymbol P)(adaptive ball)

/-- Mutual-support fiberwise adaptive-hinge membership bundle. -/
-- @node: def:conditional-adaptive-hinge-ball
structure CondAdaptiveHingeBall {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
  (P Q : Bool → Kernel X Y) : Prop where
  overlap : CondOverlap kappa e
  reverse_support : CondReverseSupport muX P Q
  covariate_probability : IsProbabilityMeasure muX
  observed_markov : ∀ a, IsMarkovKernel (P a)
  candidate_markov : ∀ a, IsMarkovKernel (Q a)
  fiberwise : ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧ ∀ x ∈ S, ∀ a,
    MutuallyAC (P a x) (Q a x) ∧
      fDiv (adaptiveHinge (e a x)) (P a x) (Q a x) ≤
        (divRadius (adaptiveHinge (e a x)) (e a x) : EReal)

/-- Fiberwise adaptive-hinge class with mutual support. -/
noncomputable def condAdaptiveHingeBallSet {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    (P : Bool → Kernel X Y) : Set (Bool → Kernel X Y) :=
  {Q | CondAdaptiveHingeBall kappa muX e P Q}
  -- @realizes \mathfrak B^{\mathrm{ad}}_{\mu_X,\boldsymbol e}(\boldsymbol P)(adaptive ball)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
