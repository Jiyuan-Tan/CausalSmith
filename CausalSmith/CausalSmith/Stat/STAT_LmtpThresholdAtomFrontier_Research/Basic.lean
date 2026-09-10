/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Moments.SubGaussian
import Causalean.Stat.Sample

/-!
# Threshold-clamp minimax frontier: shared formal world

This cold Stage-2 scaffold defines the observed and full-data experiments, the
modeling assumptions, model classes, rate objects, and minimax criteria used by
the threshold-clamp frontier. Proof obligations are split into the theorem and
helper modules named in the formalization plan.

The Causalean survey found reusable i.i.d.-sample and minimax infrastructure,
but no continuous-treatment clamp world. `Causalean.PO` is intentionally
bypassed because its finite-regime potential-outcome carrier is at a different
abstraction from the continuum-indexed standard-Borel response process here.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

noncomputable section

/-! ## Disclosed substrate gates -/

/-- Kallenberg (2002), *Foundations of Modern Probability*, second edition,
Theorem 6.3 (conditional distribution), doi:10.1007/978-1-4757-4015-8.

Every probability law of a pair of standard-Borel-valued random elements has
a Borel regular conditional probability kernel in the rectangle-integral
form used by the observed-margin lifting arguments. -/
-- @node: lem:standard-borel-regular-conditional-law
def StandardBorelRegularConditionalLaw : Sort 0 :=
  ∀ (S T : Type*) [MeasurableSpace S] [StandardBorelSpace S]
      [MeasurableSpace T] [StandardBorelSpace T]
      (μ : Measure (S × T)), IsProbabilityMeasure μ →
    ∃ K : ProbabilityTheory.Kernel S T,
      (∀ s, IsProbabilityMeasure (K s)) ∧
      ∀ (B : Set S) (C : Set T), MeasurableSet B → MeasurableSet C →
        μ (B ×ˢ C) = ∫⁻ s in B, K s C ∂μ.map Prod.fst

/-- Hoeffding (1963), “Probability inequalities for sums of bounded random
variables”, Theorem 2 specialized to unit ranges and two tails,
doi:10.1080/01621459.1963.10500830.

The centered average of independent, not necessarily identically
distributed, measurable `[0,1]`-valued variables obeys the stated two-sided
Hoeffding bound. -/
-- @node: lem:hoeffding-bounded-average
def HoeffdingBoundedAverage : Sort 0 :=
  ∀ (m : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ Z : Fin m → Ω → ℝ,
      (∀ i, Measurable (Z i)) → ProbabilityTheory.iIndepFun Z μ →
      (∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1) →
      ∀ t : ℝ, 0 < t →
        μ.real {ω | |(m : ℝ)⁻¹ * ∑ i, Z i ω -
          (m : ℝ)⁻¹ * ∑ i, ∫ ω, Z i ω ∂μ| > t} ≤
          2 * Real.exp (-2 * (m : ℝ) * t ^ 2)

/-! ## S1: observed-data experiment -/

-- @env: S1
variable {J : ℕ} -- @realizes J(number of strata; positive in RegimeConstants)
variable {n : ℕ} -- @realizes n(sample size)

/-- One observed unit `O = (X,A,Y)` in a finite-stratum continuous-treatment model. -/
structure ClampObs (J : ℕ) where -- @realizes O(carrier mathcal_X × ℝ × ℝ)
  X : Fin J -- @realizes X(carrier mathcal_X) @realizes mathcal_X(Fin J)
  A : ℝ -- @realizes A(carrier ℝ; range [0,1] pinned by IidSampling)
  Y : ℝ -- @realizes Y(carrier ℝ; range [0,1] pinned by IidSampling)

/-- The observation carrier inherits the product Borel structure. -/
instance instMeasurableSpaceClampObs {J : ℕ} : MeasurableSpace (ClampObs J) :=
  MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A, o.Y)) inferInstance

/-- A law and its law-pinned finite-stratum nuisance functions. -/
structure ClampLaw (J : ℕ) where
  dataMeasure : Measure (ClampObs J) -- @realizes P(law on O; probability via IidSampling)
  px : Fin J → ℝ -- @realizes p_x(carrier mathcal_X→ℝ; tied to P by StratumMass)
  pi : Fin J → ℝ → ℝ -- @realizes pi_x(density carrier; tied by CondDensityLaw)
  mu : Fin J → ℝ → ℝ -- @realizes mu_x_P(regression carrier; tied by HolderRegression)

/-- The lower-threshold modified-treatment policy `d_delta(a) = max a delta`. -/
-- @node: def:clamp-policy
def clampPolicy (delta a : ℝ) : ℝ := -- @realizes d_delta(d_delta(a)=max a delta)
  max a delta

/-- Conditional mass collapsed to the threshold by the clamp. -/
def atomMass (P : ClampLaw J) (x : Fin J) (delta : ℝ) : ℝ :=
  ∫ a in Set.Icc (0 : ℝ) delta, P.pi x a -- @realizes q_x(q_x(delta)=integral_0^delta pi_x)

/-- The retained natural-course contribution above the threshold. -/
def retainedMean (P : ClampLaw J) (delta : ℝ) : ℝ :=
  ∫ o, o.Y * Set.indicator {o : ClampObs J | delta < o.A} (fun _ => (1 : ℝ)) o
    ∂P.dataMeasure -- @realizes nu_delta(E_P[Y 1{A>delta}])

/-- The observed-data clamp target. -/
def clampFunctional (P : ClampLaw J) (delta : ℝ) : ℝ :=
  retainedMean P delta +
    ∑ x : Fin J, P.px x * atomMass P x delta * P.mu x delta
    -- @realizes theta_delta(nu_delta + sum_x p_x q_x(delta) mu_x_P(delta))

/-- The designated `i`-th observation in the canonical finite sample. -/
def observedSampleCoordinate (n : ℕ) (i : Fin n) :
    (Fin n → ClampObs J) → ClampObs J :=
  fun z => z i -- @realizes O_i(designated i-th observation among the first n)

/-- The designated observations are the canonical first `n` coordinate maps
under the `n`-fold product law; they are independent and each has law `P`. -/
-- @node: ass:iid-sampling
def IidSampling (P : ClampLaw J) (n : ℕ) : Prop :=
  IsProbabilityMeasure P.dataMeasure ∧
    (∀ᵐ o ∂P.dataMeasure, o.A ∈ Set.Icc (0 : ℝ) 1) ∧
      -- @realizes A(a.s. range [0,1])
    (∀ᵐ o ∂P.dataMeasure, o.Y ∈ Set.Icc (0 : ℝ) 1) ∧
      -- @realizes Y(a.s. range [0,1])
    ProbabilityTheory.iIndepFun
      (observedSampleCoordinate (J := J) n)
      (Measure.pi (fun _ : Fin n => P.dataMeasure)) ∧
    ∀ i : Fin n,
      (Measure.pi (fun _ : Fin n => P.dataMeasure)).map
        (observedSampleCoordinate (J := J) n i) = P.dataMeasure
      -- @realizes O_i(designated first n coordinate maps, independent with law P)

/-- The declared conditional density is nonnegative and gives every
finite-stratum conditional treatment probability. -/
-- @node: ass:conditional-density-law
def CondDensityLaw (P : ClampLaw J) : Prop :=
  (∀ x, Measurable (fun a : Set.Icc (0 : ℝ) 1 => P.pi x a)) ∧
    -- @realizes pi_x(Borel measurable on [0,1])
  (∀ x, ∀ᵐ a ∂volume.restrict (Set.Icc (0 : ℝ) 1), 0 ≤ P.pi x a) ∧
    -- @realizes pi_x(nonnegative on [0,1])
  ∀ x : Fin J,
    P.px x = (P.dataMeasure.map (fun o => o.X)).real {x} ∧
      -- @realizes p_x(P.px is tied to P(X=x) inside the density law)
    ∀ (B : Set ℝ), MeasurableSet B → B ⊆ Set.Icc (0 : ℝ) 1 →
      P.dataMeasure.real {o | o.X = x ∧ o.A ∈ B} =
        P.px x * ∫ a in B, P.pi x a
        -- @realizes pi_x(P(A in B,X=x)=P(X=x) integral_B pi_x)

/-- Every stratum mass is the corresponding atom of the `X` marginal and is
bounded below by `pmin`. -/
-- @node: ass:stratum-mass
def StratumMass (P : ClampLaw J) (pmin : ℝ) : Prop :=
  ∀ x : Fin J,
    P.px x = (P.dataMeasure.map (fun o => o.X)).real {x} ∧
      -- @realizes p_x(p_x=P(X=x))
    pmin ≤ P.px x -- @realizes p_min(lower bound on every p_x)

/-- The two-sided polynomial density envelope, with no smoothness imposed on
the treatment density. -/
-- @node: ass:polynomial-thinning
def PolynomialThinning (P : ClampLaw J) (kappa cminus cplus : ℝ) : Prop :=
  ∀ x : Fin J, ∀ᵐ a ∂volume.restrict (Set.Icc (0 : ℝ) 1),
    cminus * a ^ kappa ≤ P.pi x a ∧ P.pi x a ≤ cplus * a ^ kappa
    -- @realizes pi_x(two-sided c_minus*a^kappa and c_plus*a^kappa envelope)

/-- The local-polynomial order: the greatest natural number strictly below
`beta`, including the integer-order correction. -/
def ellOf (beta : ℝ) : ℕ :=
  ⌈beta⌉₊ - 1 -- @realizes ell(floor beta, with beta-1 at integer beta)

/-- Continuous bounded regression, its conditional-expectation law tie, and
the stated Taylor-remainder Hölder condition. -/
-- @node: ass:holder-regression
def HolderRegression (P : ClampLaw J) (beta L : ℝ) : Prop :=
  ∀ x : Fin J,
    ContinuousOn (P.mu x) (Set.Icc (0 : ℝ) 1) ∧
    (∀ a ∈ Set.Icc (0 : ℝ) 1, P.mu x a ∈ Set.Icc (0 : ℝ) 1) ∧
      -- @realizes mu_x_P(continuous extension with range [0,1])
    (P.dataMeasure[(fun o : ClampObs J => o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
      =ᵐ[P.dataMeasure] fun o => P.mu o.X o.A) ∧
      -- @realizes mu_x_P(condExp version given the complete (X,A) design)
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |P.mu x t - ∑ j ∈ Finset.range (ellOf beta + 1),
          iteratedDerivWithin j (P.mu x) (Set.Icc (0 : ℝ) 1) s *
            (t - s) ^ j / (Nat.factorial j : ℝ)|
        ≤ L * |t - s| ^ beta
      -- @realizes mu_x_P(intrinsic [0,1] Taylor coefficients)
      -- @realizes beta(Taylor-remainder exponent) @realizes L(Taylor-remainder radius)

/-- The finite-stratum clamp model, with exactly the four core member atoms. -/
-- @node: def:model-class
structure ClampModel (P : ClampLaw J) (beta kappa L cminus cplus pmin : ℝ) : Prop where
  probability : IsProbabilityMeasure P.dataMeasure
    -- @realizes P(probability law on O)
  treatmentSupport : ∀ᵐ o ∂P.dataMeasure, o.A ∈ Set.Icc (0 : ℝ) 1
    -- @realizes A(a.s. range [0,1]) @realizes O(treatment coordinate supported on [0,1])
  outcomeSupport : ∀ᵐ o ∂P.dataMeasure, o.Y ∈ Set.Icc (0 : ℝ) 1
    -- @realizes Y(a.s. range [0,1]) @realizes O(outcome coordinate supported on [0,1])
  condDensity : CondDensityLaw P
  stratumMass : StratumMass P pmin
  thinning : PolynomialThinning P kappa cminus cplus
  holder : HolderRegression P beta L
  -- @realizes mathcal_M(laws satisfying density, stratum mass, thinning, and Holder members)

/-! ## S2: regime constants and rates -/

-- @env: S2
variable (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
  -- @realizes beta(smoothness exponent) @realizes kappa(thinning exponent)
  -- @realizes L(Holder radius) @realizes c_minus(lower density constant)
  -- @realizes c_plus(upper density constant) @realizes p_min(stratum mass floor)
  -- @realizes delta_bar(threshold envelope) @realizes alpha(noncoverage level)

/-- Standing declared-space constraints for the frontier constants. -/
def RegimeConstants (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ) : Prop :=
  0 < J ∧ -- @realizes J(J is positive)
  0 < beta ∧ -- @realizes beta(beta > 0)
  0 ≤ kappa ∧ -- @realizes kappa(kappa >= 0)
  0 < L ∧ -- @realizes L(L > 0)
  0 < cminus ∧ -- @realizes c_minus(c_minus > 0)
  cminus ≤ kappa + 1 ∧ -- @realizes c_minus(c_minus <= kappa+1)
  kappa + 1 ≤ cplus ∧
  0 < pmin ∧ -- @realizes p_min(p_min > 0)
  pmin ≤ 1 / (J : ℝ) ∧ -- @realizes p_min(p_min <= 1/J)
  0 < deltaBar ∧ deltaBar < 1 ∧ -- @realizes delta_bar(delta_bar in (0,1))
  0 < alpha ∧ alpha < 1 / 2 -- @realizes alpha(alpha in (0,1/2))

/-- [Admissibility of the regime constants](hyp:h) [forces the number of strata to be at least one](goal). -/
lemma RegimeConstants.one_le_J
    (h : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) : 1 ≤ J := by
  exact Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt h.1)

/-- [Admissibility of the regime constants](hyp:h) [forces the error level to be positive](goal). -/
lemma RegimeConstants.alpha_pos
    (h : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) : 0 < alpha := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, halpha, _⟩
  exact halpha

/-- [Admissibility of the regime constants](hyp:h) [forces the error level to be less than one half](goal). -/
lemma RegimeConstants.alpha_lt_half
    (h : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) : alpha < 1 / 2 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, halpha⟩
  exact halpha

/-- The conditional test multiplier on its declared core domain. -/
-- keep: canonical computed realization of the frozen core symbol sym:t_alpha
def testMultiplier (J : ℕ) (alpha : ℝ)
    (_hJ : 1 ≤ J) (_halpha_pos : 0 < alpha) (_halpha_lt : alpha < 1 / 2) : ℝ :=
  Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
  -- @realizes t_alpha(sqrt(log(12 J / alpha)/2), for J≥1 and alpha∈(0,1/2))

/-- A deterministic threshold sequence stays in `[0,deltaBar]`. -/
def ThresholdSequence (deltaBar : ℝ) (delta : ℕ → ℝ) : Prop :=
  ∀ n, delta n ∈ Set.Icc (0 : ℝ) deltaBar
  -- @realizes delta_n(deterministic sequence in [0,delta_bar])

/-- The information-balance crossing set. -/
def bandwidthCrossingSet (n : ℕ) (delta beta kappa deltaBar : ℝ) : Set ℝ :=
  {h | 0 < h ∧ h ≤ 1 - deltaBar ∧
    1 ≤ (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa}

/-- First information-balance crossing, with the prescribed empty-set fallback. -/
-- @node: def:bandwidth
def infoBandwidth (n : ℕ) (delta beta kappa deltaBar : ℝ) : ℝ :=
  by
    classical
    exact if (bandwidthCrossingSet n delta beta kappa deltaBar).Nonempty then
      sInf (bandwidthCrossingSet n delta beta kappa deltaBar)
    else 1 - deltaBar
  -- @realizes h_n(infimum information-balance crossing with fallback 1-delta_bar)

/-- Candidate regular-plus-atom estimation frontier. -/
-- @node: def:frontier
def clampFrontier (n : ℕ) (delta kappa h beta : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 2) + delta ^ (kappa + 1) * h ^ beta
  -- @realizes r_n(n^(-1/2)+delta_n^(kappa+1)*h_n^beta)

/-- Critical threshold scale. -/
def deltaCrit (n : ℕ) (beta kappa : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) /
    (2 * (beta * kappa + 2 * beta + kappa + 1)))
  -- @realizes delta_crit(n^(-1/[2(beta*kappa+2beta+kappa+1)]))

/-- Boundary-design scale. -/
def deltaEdge (n : ℕ) (beta kappa : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / (2 * beta + kappa + 1))
  -- @realizes delta_edge(n^(-1/(2beta+kappa+1)))

/-- The canonical product law of the observed sample. -/
def iidProduct (P : ClampLaw J) (n : ℕ) : Measure (Fin n → ClampObs J) :=
  Measure.pi (fun _ : Fin n => P.dataMeasure)
  -- @realizes O_i(product law of the observed iid sample)

/-- Observed-sample point estimators. -/
abbrev Estimator (n J : ℕ) := (Fin n → ClampObs J) → ℝ

/-- Observed-sample confidence-set procedures. -/
abbrev ConfidenceProcedure (n J : ℕ) := (Fin n → ClampObs J) → Set ℝ

/-- An estimator is measurable with respect to the observed sample. -/
def ObservedMeasurableEstimator {n J : ℕ} (est : Estimator n J) : Prop :=
  Measurable est

/-- A confidence procedure has measurable ordered endpoints and returns exactly
the corresponding closed interval. -/
def ObservedMeasurableInterval {n J : ℕ} (C : ConfidenceProcedure n J) : Prop :=
  ∃ lo hi : (Fin n → ClampObs J) → ℝ,
    Measurable lo ∧ Measurable hi ∧ (∀ z, lo z ≤ hi z) ∧
    ∀ z, C z = Set.Icc (lo z) (hi z)

/-- Length of the convex hull of a real confidence set. -/
def intervalLength (C : Set ℝ) : ℝ := max 0 (sSup C - sInf C)

/-- Extended-real interval length, used so non-integrable expected lengths are
represented by `∞` rather than the junk value of the real Bochner integral. -/
def intervalLengthENNReal (C : Set ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (intervalLength C)

/-- Absolute-error risk of an observed-sample estimator under one law. -/
def estimatorRisk (P : ClampLaw J) (n : ℕ) (delta : ℝ)
    (est : Estimator n J) : ℝ :=
  ∫ z, |est z - clampFunctional P delta| ∂iidProduct P n

/-- Minimax absolute-error risk over the clamp model. -/
def observedMinimaxRisk (J n : ℕ) (beta kappa L cminus cplus pmin delta : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ est : Estimator n J,
    ObservedMeasurableEstimator est ∧ (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
    r = sSup {v : ℝ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧
      v = estimatorRisk P n delta est}}
  -- @realizes R_n_star(infimum estimator worst-case absolute risk over mathcal_M)

/-- Uniform coverage of a confidence procedure over the clamp model. -/
def UniformCoverage (J n : ℕ) (beta kappa L cminus cplus pmin delta alpha : ℝ)
    (C : ConfidenceProcedure n J) : Prop :=
  ObservedMeasurableInterval C ∧
  ∀ P : ClampLaw J, ClampModel P beta kappa L cminus cplus pmin →
    1 - alpha ≤ (iidProduct P n).real {z | clampFunctional P delta ∈ C z}

/-- Minimax worst-case expected length among uniformly honest intervals. -/
def observedMinimaxLength (J n : ℕ)
    (beta kappa L cminus cplus pmin delta alpha : ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ C : ConfidenceProcedure n J,
    UniformCoverage J n beta kappa L cminus cplus pmin delta alpha C ∧
    r = sSup {v : ℝ≥0∞ | ∃ P : ClampLaw J,
      ClampModel P beta kappa L cminus cplus pmin ∧
      v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P n}}
  -- @realizes L_n_star(infimum honest worst-case expected confidence length)

/-! ## S4: full-data standard-Borel latent-response overlay -/

-- @env: S4
/-- A full-data law packages its own standard-Borel latent carrier, so different
members of a full-data model class need not share a carrier. The observed-model
restriction is deliberately imposed by the class predicates below, rather than
by this carrier. -/
structure FullDataLaw (J : ℕ) where
  latentCarrier : Type -- @realizes mathcal_U(member-specific standard Borel latent carrier)
  [latentMeasurable : MeasurableSpace latentCarrier]
  [latentStandardBorel : StandardBorelSpace latentCarrier]
  [latentNonempty : Nonempty latentCarrier]
  observedMargin : ClampLaw J
  fullMeasure : Measure (ClampObs J × latentCarrier)
    -- @realizes P_full(full-data probability law on the member-specific carrier)
  probability : IsProbabilityMeasure fullMeasure
  margin_eq : fullMeasure.map Prod.fst = observedMargin.dataMeasure
  g : Fin J → ℝ → latentCarrier → ℝ
    -- @realizes g_x(structural response map on [0,1]×mathcal_U)
  pot : ℝ → (ClampObs J × latentCarrier) → ℝ
    -- @realizes Y_a(potential-outcome process a↦Y(a))
  pot_jointlyMeasurable : Measurable (Function.uncurry pot)
    -- @realizes Y_a(jointly Borel measurable in dose and full-data state)

/-- [the canonical inst measurable space latent carrier instance is defined](goal) for [the specified `J` input](hyp:J), [the specified `PF` input](hyp:PF). -/
instance (PF : FullDataLaw J) : MeasurableSpace PF.latentCarrier :=
  PF.latentMeasurable

/-- [the canonical inst standard borel space latent carrier instance is defined](goal) for [the specified `J` input](hyp:J), [the specified `PF` input](hyp:PF). -/
instance (PF : FullDataLaw J) : StandardBorelSpace PF.latentCarrier :=
  PF.latentStandardBorel

/-- [the canonical inst nonempty latent carrier instance is defined](goal) for [the specified `J` input](hyp:J), [the specified `PF` input](hyp:PF). -/
instance (PF : FullDataLaw J) : Nonempty PF.latentCarrier :=
  PF.latentNonempty

/-- Simultaneous latent-response consistency outside one common null set. -/
-- @node: ass:consistency
def LatentResponseConsistency
    (PF : FullDataLaw J) : Prop :=
  (∀ x, Measurable (fun z : Set.Icc (0 : ℝ) 1 × PF.latentCarrier =>
      PF.g x z.1 z.2)) ∧
  (∀ x a u, a ∈ Set.Icc (0 : ℝ) 1 → PF.g x a u ∈ Set.Icc (0 : ℝ) 1) ∧
    -- @realizes g_x(jointly Borel and [0,1]-valued)
  ∀ᵐ z ∂PF.fullMeasure,
    (∀ a ∈ Set.Icc (0 : ℝ) 1, PF.pot a z = PF.g z.1.X a z.2) ∧
      -- @realizes Y_a(one null set, simultaneous Y(a)=g_X(a,U))
    z.1.Y = PF.g z.1.X z.1.A z.2

/-- The actual `X=x` marginal mass under a full-data law.  This is computed
from the observed marginal measure, which `FullDataLaw.margin_eq` pins to the
`(X,A,Y)` projection of the full-data measure; it deliberately does not use
the auxiliary `ClampLaw.px` field. -/
def fullDataStratumMass (PF : FullDataLaw J) (x : Fin J) : ℝ :=
  (PF.observedMargin.dataMeasure.map (fun o => o.X)).real {x}

/-- Finite-stratum conditional independence of treatment and latent response,
written as the exact stratumwise product-moment factorization using the actual
`X`-marginal mass. -/
-- @node: ass:exchangeability
def LatentExchangeability
    (PF : FullDataLaw J) : Prop :=
  ∀ (x : Fin J) (f : ℝ → ℝ) (g : PF.latentCarrier → ℝ),
    Measurable f → Measurable g →
    (∃ M, ∀ a, |f a| ≤ M) → (∃ M, ∀ u, |g u| ≤ M) →
    fullDataStratumMass PF x *
        (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
          f z.1.A * g z.2 ∂PF.fullMeasure) =
      (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
        f z.1.A ∂PF.fullMeasure) *
      (∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
        g z.2 ∂PF.fullMeasure)
    -- @realizes A(conditionally independent of U given X)
    -- @realizes U(conditionally independent of A given X)

/-- Full-data conditional response mean in a finite stratum. -/
def fullDataResponseMean
    (PF : FullDataLaw J)
    (x : Fin J) (a : ℝ) : ℝ :=
  (fullDataStratumMass PF x)⁻¹ *
    ∫ z in {z : ClampObs J × PF.latentCarrier | z.1.X = x},
      PF.g x a z.2 ∂PF.fullMeasure
  -- @realizes m_x_F(E_Pfull[g_x(a,U)|X=x])

/-- Continuity of the fiberwise structural response mean on the declared
threshold range. -/
-- @node: ass:full-data-response-continuity
def FullDataResponseContinuity
    (PF : FullDataLaw J) (deltaBar : ℝ) : Prop :=
  ∀ x : Fin J,
    ContinuousOn (fullDataResponseMean PF x) (Set.Icc (0 : ℝ) deltaBar)
    -- @realizes m_x_F(fiberwise structural-mean continuity on [0,delta_bar])

/-- The full-data clamp-policy mean. -/
def causalClampMean
    (PF : FullDataLaw J) (delta : ℝ) : ℝ :=
  ∫ z, PF.pot (clampPolicy delta z.1.A) z ∂PF.fullMeasure
  -- @realizes psi_delta(E_Pfull[Y(d_delta(A))])

/-- The structural full-data class. Each member carries its own latent carrier;
the observed margin belongs to the fixed-Hölder model, and the three causal
member conditions hold on that same package. -/
-- @node: def:full-data-model-class
structure FullDataClampModel
    (PF : FullDataLaw J)
    (beta kappa L cminus cplus pmin deltaBar : ℝ) : Prop where
  observedModel : ClampModel PF.observedMargin beta kappa L cminus cplus pmin
  consistency : LatentResponseConsistency (PF := PF)
  exchangeability : LatentExchangeability (PF := PF)
  responseContinuity : FullDataResponseContinuity PF deltaBar
  -- @realizes mathcal_M_F(carrier-heterogeneous laws with margin in mathcal_M and causal members)

/-- Absolute risk of an observed-sample estimator for one full-data law. -/
def causalEstimatorRisk
    (PF : FullDataLaw J)
    (n : ℕ) (delta : ℝ) (est : Estimator n J) : ℝ :=
  ∫ z, |est z - causalClampMean (PF := PF) (delta := delta)|
    ∂iidProduct PF.observedMargin n

/-- The pair `(R_{n,F}^star, L_{n,F}^star)` of full-data criteria, with
expected length valued in `ℝ≥0∞` so infinite expectations are preserved. -/
-- @node: def:causal-frontier-criteria
def causalFrontierCriteria (J n : ℕ)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ × ℝ≥0∞ :=
  (sInf {r : ℝ | ∃ est : Estimator n J,
      ObservedMeasurableEstimator est ∧
      (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
      r = sSup {v : ℝ | ∃ PF : FullDataLaw J,
        FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
          v = causalEstimatorRisk (PF := PF) (n := n) (delta := delta) (est := est)}},
   sInf {r : ℝ≥0∞ | ∃ C : ConfidenceProcedure n J,
      ObservedMeasurableInterval C ∧
      (∀ PF : FullDataLaw J,
        FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar →
        1 - alpha ≤ (iidProduct PF.observedMargin n).real
          {z | causalClampMean (PF := PF) (delta := delta) ∈ C z}) ∧
      r = sSup {v : ℝ≥0∞ | ∃ PF : FullDataLaw J,
        FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar ∧
        v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct PF.observedMargin n}})
  -- @realizes R_n_F_star(first component: causal minimax absolute risk)
  -- @realizes L_n_F_star(second component: causal minimax honest expected length)

/-! ## S5: continuity-only experiment -/

-- @env: S5
variable {deltaBar : ℝ}

/-- Declared design spaces for the continuity-only model, with no Hölder
exponent or radius among its parameters. -/
def ContDesignConstants (J : ℕ)
    (kappa cminus cplus pmin deltaBar : ℝ) : Prop :=
  0 < J ∧ -- @realizes J(J is positive)
  0 ≤ kappa ∧ -- @realizes kappa(kappa >= 0)
  0 < cminus ∧ -- @realizes c_minus(c_minus > 0)
  cminus ≤ kappa + 1 ∧ -- @realizes c_minus(c_minus <= kappa+1)
  kappa + 1 ≤ cplus ∧ -- @realizes c_plus(c_plus >= kappa+1)
  0 < pmin ∧ pmin ≤ 1 / (J : ℝ) ∧ -- @realizes p_min(p_min in (0,1/J])
  0 < deltaBar ∧ deltaBar < 1 -- @realizes delta_bar(delta_bar in (0,1))

/-- Declared spaces for the continuity-only inference regime. -/
def ContRegimeConstants (J : ℕ)
    (kappa cminus cplus pmin deltaBar alpha : ℝ) : Prop :=
  ContDesignConstants J kappa cminus cplus pmin deltaBar ∧
  0 < alpha ∧ alpha < 1 / 2 -- @realizes alpha(alpha in (0,1/2))

/-- The continuity-only observed model: the three shared law conditions and
existence of a continuous conditional-regression version on the threshold
range, with no common modulus or Hölder radius. -/
-- @node: def:continuity-model-class
structure ContClampModel (P : ClampLaw J)
    (kappa cminus cplus pmin deltaBar : ℝ) : Prop where
  probability : IsProbabilityMeasure P.dataMeasure
  treatmentSupport : ∀ᵐ o ∂P.dataMeasure, o.A ∈ Set.Icc (0 : ℝ) 1
  outcomeSupport : ∀ᵐ o ∂P.dataMeasure, o.Y ∈ Set.Icc (0 : ℝ) 1
  condDensity : CondDensityLaw P
  stratumMass : StratumMass P pmin
  thinning : PolynomialThinning P kappa cminus cplus
  continuousVersion : ∃ mu : Fin J → ℝ → ℝ,
    (∀ x, ContinuousOn (mu x) (Set.Icc (0 : ℝ) deltaBar)) ∧
      (P.dataMeasure[(fun o : ClampObs J => o.Y) |
          MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
        =ᵐ[P.dataMeasure] fun o => mu o.X o.A)
  -- @realizes mathcal_M_cont(density, stratum-mass, thinning, qualitative continuity)

/-- The selected continuous conditional-regression version. Its uniqueness is
proved separately from positivity of the treatment density. -/
noncomputable def contRegression (P : ClampLaw J)
    (kappa cminus cplus pmin deltaBar : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar) : Fin J → ℝ → ℝ :=
  Classical.choose hP.continuousVersion
  -- @realizes mu_x_cont_P(selected continuous conditional-regression version)

/-- The continuity-only observed clamp functional. -/
-- @node: def:continuity-clamp-functional
def contClampFunctional (P : ClampLaw J)
    (kappa cminus cplus pmin deltaBar : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar) (delta : ℝ) : ℝ :=
  retainedMean P delta + ∑ x : Fin J,
    P.px x * atomMass P x delta *
      contRegression P kappa cminus cplus pmin deltaBar hP x delta
  -- @realizes theta_delta_cont(retained mean plus atom mass times continuous version)

/-- The continuity-only regular-plus-atom frontier. -/
-- @node: def:continuity-frontier
def contFrontier (n : ℕ) (delta kappa : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 2) + delta ^ (kappa + 1)
  -- @realizes s_n(n^(-1/2)+delta_n^(kappa+1))

/-- Continuity-only full-data membership over the same law-specific latent
carrier, differing from the fixed-Hölder class only in its observed margin. -/
-- @node: def:continuity-full-data-model-class
structure ContFullDataClampModel
    (PF : FullDataLaw J)
    (kappa cminus cplus pmin deltaBar : ℝ) : Prop where
  observedModel : ContClampModel PF.observedMargin kappa cminus cplus pmin deltaBar
  consistency : LatentResponseConsistency (PF := PF)
  exchangeability : LatentExchangeability (PF := PF)
  responseContinuity : FullDataResponseContinuity PF deltaBar
  -- @realizes mathcal_M_cont_F(full-data members with continuity-only observed margin)

/-- The common observed-law fields used by the full-data identification bridge. -/
-- @node: BridgeClampModel
structure BridgeClampModel (P : ClampLaw J)
    (kappa cminus cplus pmin : ℝ) : Prop where
  probability : IsProbabilityMeasure P.dataMeasure
  treatmentSupport : ∀ᵐ o ∂P.dataMeasure, o.A ∈ Set.Icc (0 : ℝ) 1
  outcomeSupport : ∀ᵐ o ∂P.dataMeasure, o.Y ∈ Set.Icc (0 : ℝ) 1
  condDensity : CondDensityLaw P
  stratumMass : StratumMass P pmin
  thinning : PolynomialThinning P kappa cminus cplus

/-- Forget the fixed-Hölder regression field when proving the causal bridge. The result uses [the `hP` condition](hyp:hP). [This is the stated conclusion](goal).
-/
-- @node: ClampModel.toBridge
theorem ClampModel.toBridge
    (hP : ClampModel P beta kappa L cminus cplus pmin) :
    BridgeClampModel P kappa cminus cplus pmin :=
  ⟨hP.probability, hP.treatmentSupport, hP.outcomeSupport, hP.condDensity,
    hP.stratumMass, hP.thinning⟩

/-- Forget the qualitative regression field when proving the causal bridge. The result uses [the `hP` condition](hyp:hP). [This is the stated conclusion](goal).
-/
-- @node: ContClampModel.toBridge
theorem ContClampModel.toBridge
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar) :
    BridgeClampModel P kappa cminus cplus pmin :=
  ⟨hP.probability, hP.treatmentSupport, hP.outcomeSupport, hP.condDensity,
    hP.stratumMass, hP.thinning⟩

/-- The causal assumptions together with precisely the common observed-law
fields needed by the measure-factorization argument. -/
-- @node: BridgeFullDataClampModel
structure BridgeFullDataClampModel (PF : FullDataLaw J)
    (kappa cminus cplus pmin deltaBar : ℝ) : Prop where
  observedModel : BridgeClampModel PF.observedMargin kappa cminus cplus pmin
  consistency : LatentResponseConsistency (PF := PF)
  exchangeability : LatentExchangeability (PF := PF)
  responseContinuity : FullDataResponseContinuity PF deltaBar

/-- The common bridge view of a fixed-Hölder full-data member. The result uses [the `hPF` condition](hyp:hPF). [This is the stated conclusion](goal).
-/
-- @node: FullDataClampModel.toBridge
theorem FullDataClampModel.toBridge {PF : FullDataLaw J}
    (hPF : FullDataClampModel PF beta kappa L cminus cplus pmin deltaBar) :
    BridgeFullDataClampModel PF kappa cminus cplus pmin deltaBar :=
  ⟨hPF.observedModel.toBridge, hPF.consistency, hPF.exchangeability,
    hPF.responseContinuity⟩

/-- The common bridge view of a continuity-only full-data member. The result uses [the `hPF` condition](hyp:hPF). [This is the stated conclusion](goal).
-/
-- @node: ContFullDataClampModel.toBridge
theorem ContFullDataClampModel.toBridge {PF : FullDataLaw J}
    (hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar) :
    BridgeFullDataClampModel PF kappa cminus cplus pmin deltaBar :=
  ⟨hPF.observedModel.toBridge, hPF.consistency, hPF.exchangeability,
    hPF.responseContinuity⟩

/-- Absolute risk for the continuity-only observed functional. -/
def contEstimatorRisk (P : ClampLaw J) (n : ℕ)
    (kappa cminus cplus pmin deltaBar delta : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (est : Estimator n J) : ℝ :=
  ∫ z, |est z - contClampFunctional P kappa cminus cplus pmin deltaBar hP delta|
    ∂iidProduct P n

/-- The four continuity-only observed and causal decision criteria, ordered as
observed risk, observed length, causal risk, and causal length. -/
-- @node: def:continuity-frontier-criteria
def contFrontierCriteria (J n : ℕ)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ) :
    ℝ × ℝ≥0∞ × ℝ × ℝ≥0∞ :=
  (sInf {r : ℝ | ∃ est : Estimator n J,
      ObservedMeasurableEstimator est ∧ (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
      r = sSup {v : ℝ | ∃ (P : ClampLaw J)
          (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
        v = contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP est}},
   sInf {r : ℝ≥0∞ | ∃ C : ConfidenceProcedure n J,
      ObservedMeasurableInterval C ∧
      (∀ (P : ClampLaw J)
          (hP : ContClampModel P kappa cminus cplus pmin deltaBar),
        1 - alpha ≤ (iidProduct P n).real
          {z | contClampFunctional P kappa cminus cplus pmin deltaBar hP delta ∈ C z}) ∧
      r = sSup {v : ℝ≥0∞ | ∃ (P : ClampLaw J)
          (_hP : ContClampModel P kappa cminus cplus pmin deltaBar),
        v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct P n}},
   sInf {r : ℝ | ∃ est : Estimator n J,
      ObservedMeasurableEstimator est ∧ (∀ z, est z ∈ Set.Icc (0 : ℝ) 1) ∧
      r = sSup {v : ℝ | ∃ (PF : FullDataLaw J)
          (_hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
        v = causalEstimatorRisk (PF := PF) (n := n) (delta := delta) (est := est)}},
   sInf {r : ℝ≥0∞ | ∃ C : ConfidenceProcedure n J,
      ObservedMeasurableInterval C ∧
      (∀ (PF : FullDataLaw J),
        ContFullDataClampModel PF kappa cminus cplus pmin deltaBar →
        1 - alpha ≤ (iidProduct PF.observedMargin n).real
          {z | causalClampMean (PF := PF) (delta := delta) ∈ C z}) ∧
      r = sSup {v : ℝ≥0∞ | ∃ (PF : FullDataLaw J)
          (_hPF : ContFullDataClampModel PF kappa cminus cplus pmin deltaBar),
        v = ∫⁻ z, intervalLengthENNReal (C z) ∂iidProduct PF.observedMargin n}})
  -- @realizes R_n_cont_star(first component)
  -- @realizes L_n_cont_star(second component)
  -- @realizes R_n_cont_F_star(third component)
  -- @realizes L_n_cont_F_star(fourth component)

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
