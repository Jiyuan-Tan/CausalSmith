import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CondClasses
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Sampling
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CitedGates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.CDF

/-! # Shared statement-level predicates -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

/-- A concrete Bernoulli law on `Bool`. -/
noncomputable def binaryLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false + ENNReal.ofReal p • Measure.dirac true

/-- Exactness of the mutual-support divergence relaxation for every law. -/
def MutualExactAt {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ P : Measure Y, IsProbabilityMeasure P → jkBallSet f e P = mixtureClassSet e P

/-- Exactness of the one-sided divergence relaxation for every law. -/
def OneSidedExactAt {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ P : Measure Y, IsProbabilityMeasure P →
    jkBallOneSidedSet f e P = mixtureClassOneSidedSet e P

/-- Exactness over every standard Borel carrier. -/
def UniversalMutualExact (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ (Z : Type) (mZ : MeasurableSpace Z), @StandardBorelSpace Z mZ →
    @MutualExactAt Z mZ f e

/-- One-sided exactness over every standard Borel carrier. -/
def UniversalOneSidedExact (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ (Z : Type) (mZ : MeasurableSpace Z), @StandardBorelSpace Z mZ →
    @OneSidedExactAt Z mZ f e

/-- Full-support binary exactness in the mutual regime. -/
def BinaryMutualExact (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Set.Ioo 0 1 →
    jkBallSet f e (binaryLaw p) = mixtureClassSet e (binaryLaw p)

/-- Full-support binary exactness in the one-sided regime. -/
def BinaryOneSidedExact (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Set.Ioo 0 1 →
    jkBallOneSidedSet f e (binaryLaw p) = mixtureClassOneSidedSet e (binaryLaw p)

/-- A generic probability coordinate. -/
def ProbabilityCoordinate (q : ℝ) : Prop :=
  q ∈ Set.Icc 0 1
  -- @realizes q(candidate binary probability in [0,1])

/-- A probability coordinate pinned to a measurable event under a probability law. -/
def EventProbabilityCoordinate {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) (B : Set Y) (p : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ MeasurableSet B ∧ p = (P B).toReal ∧ p ∈ Set.Icc 0 1
  -- @realizes p(p=P(B) in [0,1])

/-- The cap-boundary coordinate and its permitted outward perturbation. -/
def BoundaryPerturbation (e p q₀ epsilon q : ℝ) : Prop :=
  StrictPositivity e ∧ p ∈ Set.Ioo 0 1 ∧
    q₀ = e * p ∧ q₀ ∈ Set.Ioo 0 1 ∧ -- @realizes q_0(q_0=e*p in (0,1))
    epsilon ∈ Set.Ioo 0 (e * p) ∧ -- @realizes \varepsilon(0<epsilon<e*p)
    q = q₀ - epsilon ∧ q ∈ Set.Icc 0 1

/-- A valid familywise miscoverage level. -/
def MiscoverageLevel (alpha : ℝ) : Prop :=
  alpha ∈ Set.Ioo 0 1
  -- @realizes \alpha(alpha in (0,1))

/-- A stable open region of binary ball-feasible but mixture-illegal pairs. -/
def OpenIllegalRegion (f : ℝ → ℝ) (e : ℝ) (oneSided : Bool) : Prop :=
  ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O.Nonempty ∧ O ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ∧
    ∀ z ∈ O,
      if oneSided then
        binaryLaw z.2 ∈ jkBallOneSidedSet f e (binaryLaw z.1) \
          mixtureClassOneSidedSet e (binaryLaw z.1)
      else
        binaryLaw z.2 ∈ jkBallSet f e (binaryLaw z.1) \
          mixtureClassSet e (binaryLaw z.1)
  -- @realizes \mathcal O_f(nonempty Euclidean-open illegal region)
  -- @realizes q(region-local coordinate in (0,1), separate from the general q domain)

/-- The mutual-support affine/nonaffine illegal-region dichotomy. -/
def MutualOpenIllegalDichotomy (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O.Nonempty ∧
    O ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ∧
    (∀ z ∈ O, z.2 < e * z.1) ∧
    (( (¬ ∃ b : ℝ, ∀ t ∈ Set.Icc 0 (1 / e), f t = b * (t - 1)) ∧
        ∀ z ∈ O, binaryLaw z.2 ∈ jkBallSet f e (binaryLaw z.1) \
          mixtureClassSet e (binaryLaw z.1) ∧
          fDiv f (binaryLaw z.1) (binaryLaw z.2) < (divRadius f e : EReal)) ∨
      (∃ b d : ℝ, 1 / e < d ∧
        (∀ t ∈ Set.Icc 0 d, f t - b * (t - 1) = 0) ∧
        ∀ z ∈ O, binaryLaw z.2 ∈ jkBallSet f e (binaryLaw z.1) \
          mixtureClassSet e (binaryLaw z.1) ∧
          fDiv f (binaryLaw z.1) (binaryLaw z.2) = 0))

/-- One common illegal region carrying the affine/nonaffine dichotomy in both
support regimes. -/
def SupportRegimeOpenIllegalDichotomy (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O.Nonempty ∧
    O ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ∧
    (∀ z ∈ O, z.2 < e * z.1) ∧
    (( (¬ ∃ b : ℝ, ∀ t ∈ Set.Icc 0 (1 / e), f t = b * (t - 1)) ∧
        ∀ z ∈ O,
          binaryLaw z.2 ∈ jkBallOneSidedSet f e (binaryLaw z.1) \
            mixtureClassOneSidedSet e (binaryLaw z.1) ∧
          binaryLaw z.2 ∈ jkBallSet f e (binaryLaw z.1) \
            mixtureClassSet e (binaryLaw z.1) ∧
          fDiv f (binaryLaw z.1) (binaryLaw z.2) < (divRadius f e : EReal)) ∨
      (∃ b d : ℝ, 1 / e < d ∧
        (∀ t ∈ Set.Icc 0 d, f t - b * (t - 1) = 0) ∧
        ∀ z ∈ O,
          binaryLaw z.2 ∈ jkBallOneSidedSet f e (binaryLaw z.1) \
            mixtureClassOneSidedSet e (binaryLaw z.1) ∧
          binaryLaw z.2 ∈ jkBallSet f e (binaryLaw z.1) \
            mixtureClassSet e (binaryLaw z.1) ∧
          fDiv f (binaryLaw z.1) (binaryLaw z.2) = 0))

/-- Lower lawful expectation endpoint. -/
noncomputable def lowerQueryEndpoint {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P : Measure Y) (h : Y → ℝ) : ℝ :=
  e * ∫ x, h x ∂P + (1 - e) * sSup {r : ℝ | ∀ᵐ x ∂P, r ≤ h x}
  -- @realizes \underline\theta_h(e E_P[h] plus residual essential infimum)

/-- Upper lawful expectation endpoint. -/
noncomputable def upperQueryEndpoint {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P : Measure Y) (h : Y → ℝ) : ℝ :=
  e * ∫ x, h x ∂P + (1 - e) * sInf {r : ℝ | ∀ᵐ x ∂P, h x ≤ r}
  -- @realizes \overline\theta_h(e E_P[h] plus residual essential supremum)

/-- The `n`-fold product law of an observed-data distribution. -/
noncomputable def iidProductLaw (n : ℕ) (nu : Measure (Bool × ℝ)) :
    Measure (ObservedSample n) :=
  Measure.pi fun _ : Fin n => nu

/-- Total variation between the corresponding `n`-sample product laws tends to zero. -/
def ProductTVLocal (nu0 : Measure (Bool × ℝ))
    (nun : ℕ → Measure (Bool × ℝ)) : Prop :=
  Tendsto (fun n => sSup {d : ℝ | ∃ C : Set (ObservedSample n),
    d = |(iidProductLaw n (nun n) C).toReal -
      (iidProductLaw n nu0 C).toReal|}) atTop (nhds 0)

/-- A real sequence is eventually bounded below by a target up to `o(1)`. -/
def AsymptoticAtLeast (target : ℝ) (u : ℕ → ℝ) : Prop :=
  ∃ r : ℕ → ℝ, Tendsto r atTop (nhds 0) ∧ ∀ᶠ n in atTop, target - r n ≤ u n

/-- A probability law occurs as the observed arm law of a consistent bow SCM
with the specified propensity. -/
def BowObservedLawAt (a : Bool) (e : ℝ) (P : Measure ℝ)
    (nu : Measure (Bool × ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure nu ∧ ∃ w : BowWitness ℝ,
    BowStructure w ∧ POConsistency w ∧ armPropensity w a = e ∧ armLaw w a = P
      ∧ observedLaw w = nu

/-- A boundary CDF and a total-variation-local sequence of bow-SCM
alternatives with the same propensity and eventual displayed CDF identity. -/
def TieContactScenario (atOne : Bool) (a : Bool) (e y₀ : ℝ)
    (P₀ : Measure ℝ) (Pn : ℕ → Measure ℝ) (delta : ℕ → ℝ)
    (nu₀ : Measure (Bool × ℝ)) (nun : ℕ → Measure (Bool × ℝ)) : Prop :=
  BowObservedLawAt a e P₀ nu₀ ∧
    (∀ᶠ n in atTop, BowObservedLawAt a e (Pn n) (nun n)) ∧
    cdf P₀ y₀ = (if atOne then 1 else 0) ∧
    (∀ᶠ n in atTop,
      cdf (Pn n) y₀ = if atOne then 1 - delta n else delta n) ∧
    (∀ n, 0 < delta n) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * delta n) atTop (nhds 0) ∧
    ProductTVLocal nu₀ nun

/-- Uniform asymptotic simultaneous coverage over a local class pairing each
observed-data law with its arm CDF law. -/
def UniformAsymptoticLocalCoverage
    (alpha e : ℝ) (he : StrictPositivity e)
    (band : FiniteSampleBand)
    (localClass : Set (Measure (Bool × ℝ) × Measure ℝ)) : Prop :=
  AsymptoticAtLeast (1 - alpha) (fun n =>
    sInf {r : ℝ | ∃ nu P, ∃ _hnu : IsProbabilityMeasure nu,
      ∃ hP : IsProbabilityMeasure P,
      (nu, P) ∈ localClass ∧ r = (iidProductLaw n nu {S | ∀ y : ℝ,
        cdfEndpoints (endpointPropensity e (Or.inl he)) (@cdfProbability P hP y) ∈
          band n S y}).toReal})

/-- Diameter of one endpoint projection of a rectangular band at a fixed
threshold, measured under a specified law. -/
noncomputable def ProjectionDiameterProbability
    (firstCoordinate : Bool) (nu : Measure (Bool × ℝ))
    (band : FiniteSampleBand)
    (n : ℕ) (y₀ width : ℝ) : ℝ :=
  (iidProductLaw n nu {S | ∃ z₁ z₂, z₁ ∈ band n S y₀ ∧ z₂ ∈ band n S y₀ ∧
    width ≤ if firstCoordinate then |z₁.1 - z₂.1| else |z₁.2 - z₂.2|}).toReal

/-- Uniform shrinking at both CDF contacts, the property ruled out by the tie
theorem. -/
def UniformlyShrinkingAtContacts (band : FiniteSampleBand)
    (localClass : Set (Measure (Bool × ℝ) × Measure ℝ)) : Prop :=
  ∀ (nu : Measure (Bool × ℝ)) (P : Measure ℝ),
    (nu, P) ∈ localClass → IsProbabilityMeasure nu → IsProbabilityMeasure P →
    ∀ (y₀ : ℝ) (atOne : Bool), cdf P y₀ = (if atOne then 1 else 0) →
      ∀ width : ℝ, 0 < width →
        Tendsto (fun n => ProjectionDiameterProbability atOne nu band n y₀ width)
          atTop (nhds 0)

/-- The finite-sample construction remains available as a rectangular fallback
at every sample, arm, level, and threshold. -/
def HonestBandFallback : Prop :=
  (∀ (n : ℕ) (a : Bool) (alpha : ℝ) (S : ObservedSample n) (y : ℝ),
    ∃ lL uL lU uU : ℝ,
      honestFiniteSampleBand a n alpha S y = Set.Icc lL uL ×ˢ Set.Icc lU uU) ∧
  (HoeffdingBoundedMean.{0} → DkwMassartCdfBand →
    ∀ (n : ℕ) (a : Bool) (alpha e : ℝ)
      (nu : Measure (Bool × ℝ)) (P : Measure ℝ)
      (hP : IsProbabilityMeasure P) (hPos : StrictPositivity e),
      IidObservationalSampling n (sampleCoordinate n) (iidProductLaw n nu) nu →
      (∀ B : Set ℝ, MeasurableSet B →
        nu {z | z.1 = a ∧ z.2 ∈ B} = ENNReal.ofReal e * P B) →
      MiscoverageLevel alpha →
      iidProductLaw n nu {S | ∀ y : ℝ,
        cdfEndpoints (endpointPropensity e (Or.inl hPos))
          (@cdfProbability P hP y) ∈ honestFiniteSampleBand a n alpha S y} ≥
        ENNReal.ofReal (1 - alpha))

/-- The common-conull kernel cap class. -/
def condCapSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (muX : Measure X) (e : Bool → X → ℝ) (P : Bool → Kernel X Y) :
    Set (Bool → Kernel X Y) :=
  {Q | (∀ a, IsMarkovKernel (Q a)) ∧
    ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧ ∀ x ∈ S, ∀ a,
      ENNReal.ofReal (e a x) • P a x ≤ Q a x ∧
      (P a x).AbsolutelyContinuous (Q a x) ∧
      ∀ᵐ y ∂Q a x, ((P a x).rnDeriv (Q a x) y).toReal ≤ 1 / e a x}

/-- A probability vector on a finite alphabet. -/
def FiniteProbabilityVector {J : Type} [Fintype J] (p : J → ℝ) : Prop :=
  (∀ j, p j ∈ Set.Icc 0 1) ∧ ∑ j, p j = 1

/-- The discrete `f`-divergence objective. -/
noncomputable def finiteFDiv {J : Type} [Fintype J]
    (f : ℝ → ℝ) (p q : J → ℝ) : ℝ :=
  ∑ j, q j * f (p j / q j)

/-- The finite-alphabet legality, optimization monotonicity, and strictness
conclusions used by both query theorems. -/
def FiniteAlphabetLegality (f : ℝ → ℝ) (e : ℝ) (oneSided : Bool) : Prop :=
  ∀ (J : Type) [Fintype J] (p : J → ℝ),
    FiniteProbabilityVector p →
    (oneSided = false → ∀ j, 0 < p j) →
    let relaxed : Set (J → ℝ) :=
      {q | FiniteProbabilityVector q ∧ (∀ j, 0 < p j → 0 < q j) ∧
        finiteFDiv f p q ≤ divRadius f e}
    let lawful : Set (J → ℝ) := {q | q ∈ relaxed ∧ ∀ j, e * p j ≤ q j}
    let mixtures : Set (J → ℝ) :=
      {q | FiniteProbabilityVector q ∧ ∃ r : J → ℝ,
        FiniteProbabilityVector r ∧ ∀ j, q j = e * p j + (1 - e) * r j}
    lawful = mixtures ∧
      ∀ h : J → ℝ,
        sSup ((fun q => ∑ j, h j * q j) '' lawful) ≤
          sSup ((fun q => ∑ j, h j * q j) '' relaxed) ∧
        ∀ qStar ∈ relaxed,
          (∀ q ∈ relaxed, ∑ j, h j * q j ≤ ∑ j, h j * qStar j) →
          (∀ q ∈ relaxed, (∑ j, h j * q j = ∑ j, h j * qStar j) → q = qStar) →
          (∃ j, qStar j < e * p j) →
          sSup ((fun q => ∑ j, h j * q j) '' lawful) < ∑ j, h j * qStar j
  -- @realizes p_j,q_j(cellwise probability and cap coordinates)

/-- A strict success-indicator optimization gap on an open set of binary
observational laws. -/
def SuccessIndicatorLegalityGap (f : ℝ → ℝ) (e : ℝ)
    (oneSided : Bool) : Prop :=
  ∃ O : Set ℝ, IsOpen O ∧ O.Nonempty ∧ O ⊆ Set.Ioo 0 1 ∧ ∀ p ∈ O,
    sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
      binaryLaw q ∈ (if oneSided then jkBallOneSidedSet f e (binaryLaw p)
        else jkBallSet f e (binaryLaw p))} <
    sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
      binaryLaw q ∈ (if oneSided then mixtureClassOneSidedSet e (binaryLaw p)
        else mixtureClassSet e (binaryLaw p))}

end CausalSmith.SCM.PropensityLvSharpnessFrontier
