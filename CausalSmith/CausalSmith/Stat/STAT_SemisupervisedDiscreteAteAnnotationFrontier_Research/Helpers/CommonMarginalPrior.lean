module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.AlternationDuality
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalFiniteLaw
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalProductBounds
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPoissonTransport
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPoissonReindex
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricLabelFloor
public import Causalean.Stat.Minimax.Mixture
public import Causalean.Stat.Minimax.Mixture.MomentMatched.SupportLocalized
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Main
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Probability.Distributions.Poisson.Basic

/-! Auxiliary-invariant fuzzy priors and their uniform-intensity certificate. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
/-- This declaration defines [the specified object](goal). -/

noncomputable instance {d : Nat} : MeasurableSpace (DiscreteLaw d) := ⊤

/-- Raw cell counts: independent labeled `Y=1` and `Y=0` counts, followed by
the auxiliary `(X,A)` count.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev RawPoissonCounts (d : Nat) := Fin d → Bool → (Nat × Nat) × Nat

/-- The explicit raw marked-Poisson law of one normalized finite law.  [the stated conditions](hyp:P,scale,u,v) [the stated conclusion](goal). -/
noncomputable def rawPoissonLaw {d : Nat} (P : DiscreteLaw d)
    (scale u v : Real) :
    Measure (RawPoissonCounts d) :=
  Measure.pi fun x => Measure.pi fun arm =>
    ((ProbabilityTheory.poissonMeasure
      (Real.toNNReal (u * scale * markedMass P x arm))).prod
      (ProbabilityTheory.poissonMeasure
        (Real.toNNReal
          (u * scale * (armMass P x arm - markedMass P x arm))))).prod
      (ProbabilityTheory.poissonMeasure
        (Real.toNNReal (v * scale * armMass P x arm)))

/-- The load-bearing constants chosen once for a fixed overlap level.  The
handle bandwidth is the paper's `b₀`, while `uniformBandwidthConstant` is the
larger `bε` allowance used by the uniform-intensity construction. -/
structure CommonMarginalCalibration (eps : Real) where
  regimeConstant : Real
  regimeConstant_pos : 0 < regimeConstant
  degreeConstant : Real
  degreeConstant_pos : 0 < degreeConstant
  bandwidthConstant : Real
  bandwidthConstant_pos : 0 < bandwidthConstant
  uniformBandwidthConstant : Real
  uniformBandwidthConstant_pos : 0 < uniformBandwidthConstant
  gamma : Real
  gamma_pos : 0 < gamma
  rareCountConstant : Real
  rareCountConstant_pos : 0 < rareCountConstant
  dualGap : Real
  dualGap_pos : 0 < dualGap
  dualGap_le_quarter : dualGap ≤ 1 / 4
  dimensionConstant : Real
  dimensionConstant_pos : 0 < dimensionConstant

/-- A pair of priors at one realized finite-atom scale.  The epsilon-only
calibration is fixed before the instance indices; `L`, `B`, `a`, and `k` are
indices of the recipe rather than consequences of a canonical `n + m` scale. -/
structure CommonMarginalRecipe {eps : Real} (calibration : CommonMarginalCalibration eps)
    (n m d L : Nat) (B a : Real) (k : Nat) where
  finiteAtomConstruction : Prop
  kappa : Real
  degree_ge_two : finiteAtomConstruction → 2 ≤ L
  bandwidth_pos : finiteAtomConstruction → 0 < B
  shift_eq : finiteAtomConstruction →
    a = calibration.gamma * B / (L : Real) ^ 2
  kappa_eq : kappa = (1 - 2 * eps) / eps
  rareCount_le : k ≤ d - 1
  reservoir : Fin d
  reservoir_is_first : reservoir.val = 0
  rareCell : Fin k → Fin d
  rareCell_injective : Function.Injective rareCell
  reservoir_ne_rare : ∀ i, reservoir ≠ rareCell i
  outcomeSign : Real → Real
  outcomeSign_mem : ∀ p, outcomeSign p ∈ Set.Icc (-1 : Real) 1
  generator : Measure (Fin k → Real)
  generatorProbability : IsProbabilityMeasure generator
  sigma : SignedMeasure Real
  sigmaVariationProbability : IsProbabilityMeasure sigma.variation
  sigma_support : finiteAtomConstruction →
    ∀ᵐ p ∂sigma.variation, p ∈ Set.Icc (a / kappa) B
  outcomeSign_integrable : Integrable outcomeSign sigma.variation
  sigma_density : sigma = sigma.variation.withDensityᵥ outcomeSign
  nu : Measure Real
  nuProbability : IsProbabilityMeasure nu
  nu_eq : finiteAtomConstruction →
    nu = sigma.variation.withDensity
        (fun p ↦ ENNReal.ofReal (a / (p + a))) +
      ENNReal.ofReal
          (1 - ∫ p, a / (p + a) ∂sigma.variation) • Measure.dirac 0
  generator_eq_iid : generator = Measure.pi (fun _ : Fin k => nu)
  generator_support : finiteAtomConstruction →
    ∀ᵐ w ∂generator, ∀ i, w i = 0 ∨ w i ∈ Set.Icc (a / kappa) B
  dual0 : Measure Real
  dual1 : Measure Real
  dualProbability0 : IsProbabilityMeasure dual0
  dualProbability1 : IsProbabilityMeasure dual1
  dualSupport0 : finiteAtomConstruction →
    ∀ᵐ p ∂dual0, p ∈ Set.Icc (a / kappa) B
  dualSupport1 : finiteAtomConstruction →
    ∀ᵐ p ∂dual1, p ∈ Set.Icc (a / kappa) B
  dualMomentMatch : finiteAtomConstruction → ∀ j : Nat, j ≤ L →
    ∫ p, p ^ j ∂dual0 = ∫ p, p ^ j ∂dual1
  dualSeparation : finiteAtomConstruction →
    calibration.dualGap ≤ ∫ p, p / (p + a) ∂dual1 -
      ∫ p, p / (p + a) ∂dual0
  sigmaMomentZero : finiteAtomConstruction → ∀ j : Nat, j ≤ L →
    ∫ᵛ p, p ^ j ∂<•sigma = 0
  sigmaSeparation : finiteAtomConstruction →
    calibration.dualGap ≤ ∫ᵛ p, p / (p + a) ∂<•sigma
  lawOf : Bool → (Fin k → Real) → DiscreteLaw d
  lawOf_measurable : ∀ branch, Measurable (lawOf branch)
  rawMass : (Fin k → Real) → Fin d → Real
  rawTotalMass : (Fin k → Real) → Real
  rawTarget : Bool → (Fin k → Real) → Real
  rawMass_sum : ∀ᵐ w ∂generator, rawTotalMass w = ∑ x, rawMass w x
  rawMass_pos : ∀ᵐ w ∂generator, 0 < rawTotalMass w
  rareRawMass : finiteAtomConstruction → ∀ᵐ w ∂generator, ∀ i,
    rawMass w (rareCell i) = w i
  reservoirRawMass : finiteAtomConstruction → ∀ᵐ w ∂generator,
    rawMass w reservoir = 1 - ∑ i, ∫ z, z i ∂generator
  unusedRawMass : ∀ᵐ w ∂generator, ∀ x, x ≠ reservoir →
    (∀ i, x ≠ rareCell i) → rawMass w x = 0
  normalization : ∀ branch, ∀ᵐ w ∂generator, ∀ x,
    cellMass (lawOf branch w) x = rawMass w x / rawTotalMass w
  rawTarget_formula : ∀ branch, ∀ᵐ w ∂generator,
    rawTarget branch w =
      rawTotalMass w * ateFunctional (lawOf branch w)
  rawScale : DiscreteLaw d → Real
  rawScale_measurable : Measurable rawScale
  rawScale_lawOf : ∀ branch, ∀ᵐ w ∂generator,
    rawScale (lawOf branch w) = rawTotalMass w
  commonTable_pointwise : ∀ᵐ w ∂generator,
    auxTableOf (lawOf false w) = auxTableOf (lawOf true w)
  rareTreatmentMass : finiteAtomConstruction → ∀ branch, ∀ᵐ w ∂generator, ∀ i,
    w i ≠ 0 →
    armMass (lawOf branch w) (rareCell i) true =
      eps * (w i + a) / rawTotalMass w
  reservoirPropensity : ∀ branch, ∀ᵐ w ∂generator,
    propensity (lawOf branch w) reservoir = 1 / 2
  controlOutcomeZero : ∀ branch, ∀ᵐ w ∂generator, ∀ x,
    outcomeMean (lawOf branch w) false x = 0
  reservoirTreatedOutcomeZero : finiteAtomConstruction → ∀ branch, ∀ᵐ w ∂generator,
    outcomeMean (lawOf branch w) true reservoir = 0
  rareOutcomeMeans : finiteAtomConstruction → ∀ᵐ w ∂generator, ∀ i, w i ≠ 0 →
    outcomeMean (lawOf false w) true (rareCell i) =
        (1 - outcomeSign (w i)) / 2 ∧
      outcomeMean (lawOf true w) true (rareCell i) =
        (1 + outcomeSign (w i)) / 2
  parametricShape : ¬finiteAtomConstruction → ∀ᵐ w ∂generator,
    calibration.dualGap / Real.sqrt n ≤ 1 / 4 ∧
    cellMass (lawOf false w) reservoir = 1 ∧
    cellMass (lawOf true w) reservoir = 1 ∧
    outcomeMean (lawOf false w) true reservoir =
      1 / 2 - calibration.dualGap / Real.sqrt n ∧
    outcomeMean (lawOf true w) true reservoir =
      1 / 2 + calibration.dualGap / Real.sqrt n
  model0 : ∀ᵐ w ∂generator, ModelClass d eps (lawOf false w)
  model1 : ∀ᵐ w ∂generator, ModelClass d eps (lawOf true w)
  prior0 : Measure (DiscreteLaw d)
  prior1 : Measure (DiscreteLaw d)
  prior0_eq : prior0 = generator.map (lawOf false)
  prior1_eq : prior1 = generator.map (lawOf true)
  probability0 : IsProbabilityMeasure prior0
  probability1 : IsProbabilityMeasure prior1
  priorModel0 : ∀ᵐ P ∂prior0, ModelClass d eps P
  priorModel1 : ∀ᵐ P ∂prior1, ModelClass d eps P
  labeledIntensity : Real
  auxiliaryIntensity : Real
  experimentKernel : ProbabilityTheory.Kernel (DiscreteLaw d) (RawPoissonCounts d)
  experimentKernel_eq : ∀ P,
    experimentKernel P =
      rawPoissonLaw P (rawScale P) labeledIntensity auxiliaryIntensity
  rawExperiment0 : Measure (RawPoissonCounts d)
  rawExperiment1 : Measure (RawPoissonCounts d)
  rawExperiment0_eq : rawExperiment0 =
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive prior0 experimentKernel
  rawExperiment1_eq : rawExperiment1 =
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive prior1 experimentKernel

/-- The law of the random full treatment-covariate table under a prior.  [the stated conditions](hyp:Pi) [the stated conclusion](goal). -/
noncomputable def randomAuxTableLaw {d : Nat} (Pi : Measure (DiscreteLaw d)) :
    Measure (AuxTable d) := Pi.map auxTableOf

/-- Center of the unnormalized target induced directly from the atom generator.  [the stated conditions](hyp:R,branch) [the stated conclusion](goal). -/
noncomputable def rawPriorCenter {eps : Real} {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k) (branch : Bool) : Real :=
  ∫ w, R.rawTarget branch w ∂R.generator

/-- Variance of the unnormalized mass or target over the atom generator.  [the stated conditions](hyp:R,f) [the stated conclusion](goal). -/
noncomputable def generatorVariance {eps : Real} {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (f : (Fin k → Real) → Real) : Real :=
  ∫ w, (f w - ∫ z, f z ∂R.generator) ^ 2 ∂R.generator

/-- A quantitative certificate for one common-marginal rare-cell recipe. -/
structure CommonMarginalBounds {eps : Real} {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (u v c C rho : Real) : Prop where
  finiteAtomConstruction : R.finiteAtomConstruction
  class0 : ∀ᵐ P ∂R.prior0, ModelClass d eps P
  class1 : ∀ᵐ P ∂R.prior1, ModelClass d eps P
  sameTable : randomAuxTableLaw R.prior0 = randomAuxTableLaw R.prior1
  separation : c * k * a ≤ |rawPriorCenter R true - rawPriorCenter R false|
  massMean : ∫ w, R.rawTotalMass w ∂R.generator = 1
  mass_memLp_two : MemLp R.rawTotalMass 2 R.generator
  target_memLp_two : ∀ branch, MemLp (R.rawTarget branch) 2 R.generator
  massVariance : generatorVariance R R.rawTotalMass ≤ C * k * B * a
  targetVariance : max (generatorVariance R (R.rawTarget false))
      (generatorVariance R (R.rawTarget true)) ≤ C * k * B * a
  mixtureTV : Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤
    C * u * k * a * rho ^ L

/-- Provenance certificate for a realized finite-atom scale produced by the
common-marginal Poisson-prior construction. -/
structure CommonMarginalPoissonPriorWitness {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v C rho : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k) : Prop where
  bandwidth_bound : (u + v) * B ≤ calibration.uniformBandwidthConstant * L
  bandwidth_pos : 0 < B
  shift_eq : a = calibration.gamma * B / (L : Real) ^ 2
  rareShiftSmall : k * a ≤ calibration.dualGap
  labeledIntensity_eq : R.labeledIntensity = u
  auxiliaryIntensity_eq : R.auxiliaryIntensity = v
  bounds : CommonMarginalBounds R u v calibration.dualGap C rho

/-- The null or alternative prior belonging to an arbitrary calibrated recipe.
This projection is used by the scale-robust Poisson lemmas; the paper-facing
`commonMarginalPriorOf` below additionally enforces the regime and C55 scales.  [the stated conditions](hyp:R,branch) [the stated conclusion](goal). -/
noncomputable def commonMarginalRecipePriorOf {eps : Real}
    {calibration : CommonMarginalCalibration eps} {n m d L k : Nat} {B a : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k) (branch : Bool) :
    Measure (DiscreteLaw d) :=
  if branch then R.prior1 else R.prior0

/-- The low-dimensional branch in the paper's regime-dependent prior handle.  [the stated conditions](hyp:calibration,n,m,d) [the stated conclusion](goal). -/
def commonMarginalParametricRegime {eps : Real}
    (calibration : CommonMarginalCalibration eps) (n m d : Nat) : Prop :=
  min 1 ((d : Real) ^ 2 /
      (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2)) ≤
    calibration.regimeConstant / (n : Real)

/-- A paper-facing prior handle.  It stores one recipe, chosen only after the
/-- This declaration defines [the specified object](goal). -/
instance indices, and pins its branch and all four approximation-dual scales to
the formulas in the note.  In particular, C55 uses the treatment--covariate
information size `n + m`; the fixed-sample multiplier does not enter this
bandwidth. -/
structure CommonMarginalPriorHandle {eps : Real}
    (calibration : CommonMarginalCalibration eps) (n m d : Nat) where
  L : Nat
  B : Real
  a : Real
  k : Nat
  recipe : CommonMarginalRecipe calibration n m d L B a k
  branchCondition : recipe.finiteAtomConstruction ↔
    ¬commonMarginalParametricRegime calibration n m d
  degree_eq : L = Nat.ceil (calibration.degreeConstant * logEN n)
  bandwidth_eq : B = calibration.bandwidthConstant * L / (n + m : Nat)
  shift_eq : a = calibration.gamma * B / (L : Real) ^ 2
  rareCount_eq : k = min (d - 1)
    ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊

-- @node: def:common-marginal-prior-handle
/-- The null or alternative prior from the uniquely supplied regime-dependent
handle.  Both branches project from the identical calibrated recipe.  [the stated conditions](hyp:H,branch) [the stated conclusion](goal). -/
noncomputable def commonMarginalPriorOf {eps : Real}
    {calibration : CommonMarginalCalibration eps} {n m d : Nat}
    (H : CommonMarginalPriorHandle calibration n m d) (branch : Bool) :
    Measure (DiscreteLaw d) :=
  commonMarginalRecipePriorOf H.recipe branch
  -- @realizes \Pi_0(null prior, branch=false)
  -- @realizes \Pi_1(alternative prior, branch=true)
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma commonMarginalPriorOf_isProbabilityMeasure {eps : Real}
    {calibration : CommonMarginalCalibration eps} {n m d : Nat}
    (H : CommonMarginalPriorHandle calibration n m d) (branch : Bool) :
    IsProbabilityMeasure (commonMarginalPriorOf H branch) := by
  cases branch
  · change IsProbabilityMeasure H.recipe.prior0
    exact H.recipe.probability0
  · change IsProbabilityMeasure H.recipe.prior1
    exact H.recipe.probability1
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma map_auxMarginal_commonMarginalPriorOf_eq {eps : Real}
    {calibration : CommonMarginalCalibration eps} {n m d : Nat}
    (H : CommonMarginalPriorHandle calibration n m d) :
    randomAuxTableLaw (commonMarginalPriorOf H false) =
      randomAuxTableLaw (commonMarginalPriorOf H true) := by
  change randomAuxTableLaw H.recipe.prior0 = randomAuxTableLaw H.recipe.prior1
  unfold randomAuxTableLaw
  rw [H.recipe.prior0_eq, H.recipe.prior1_eq]
  rw [Measure.map_map (by fun_prop) (H.recipe.lawOf_measurable false),
    Measure.map_map (by fun_prop) (H.recipe.lawOf_measurable true)]
  exact Measure.map_congr H.recipe.commonTable_pointwise

/-- The exact labeled intensity used by the fixed-sample coupling.  [the stated conditions](hyp:Cfixed,n) [the stated conclusion](goal). -/
def commonMarginalLabeledIntensity (Cfixed : Real) (n : Nat) : Real :=
  Cfixed * n

/-- The exact auxiliary intensity used by the fixed-sample coupling.  [the stated conditions](hyp:Cfixed,n,m) [the stated conclusion](goal). -/
def commonMarginalAuxiliaryIntensity (Cfixed : Real) (n m : Nat) : Real :=
  Cfixed * (n + m)

/-- The C55 lower-bound separation attached to the recipe stored in `H`.  [the stated conditions](hyp:H) [the stated conclusion](goal). -/
def commonMarginalDelta {eps : Real} {calibration : CommonMarginalCalibration eps}
    {n m d : Nat}
    (H : CommonMarginalPriorHandle calibration n m d) : Real :=
  calibration.dualGap * H.k * H.a

/-- The dimension-dependent part of the annotation-frontier rate.  [the stated conditions](hyp:n,m,d) [the stated conclusion](goal). -/
noncomputable def commonMarginalDimensionTerm (n m d : Nat) : Real :=
  min 1 ((d : Real) ^ 2 /
    (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2))

private noncomputable def normalizedCertificateOfFiniteMomentDual
    {L : Nat} {lo hi a c : Real} (D : FiniteMomentDual L lo hi a c) :
    Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate
      (Fin (L + 2)) L where
  node := D.node
  weight := D.weight
  node_injective := D.node_injective
  normalized := D.totalVariation
  moments_zero := D.moments

private noncomputable def commonMarginalDegreeConstant
    (C gap rho : Real) : Real :=
  max 2 (max 1 (Real.log (8 * (C * 65536 * gap)) + 2) / (-Real.log rho))

/-- Quantitative facts retained from the explicit epsilon-only calibration. -/
structure CommonMarginalCalibrationClosure {eps : Real}
    (calibration : CommonMarginalCalibration eps) (C rho : Real) : Prop where
  bandwidthSlack :
    131072 * calibration.bandwidthConstant ≤
      calibration.uniformBandwidthConstant
  degreeFloor : 2 ≤ calibration.degreeConstant
  rareScale :
    calibration.rareCountConstant * calibration.gamma *
      calibration.bandwidthConstant ≤ calibration.dualGap
  rareCountIdentity : calibration.rareCountConstant =
    calibration.dualGap /
      (2 * calibration.gamma * calibration.bandwidthConstant)
  rareCountFloor : 4 ≤ calibration.rareCountConstant
  dimensionFloor :
    calibration.dimensionConstant * calibration.regimeConstant ≤ 1 / 65536
  varianceBandwidth :
    8 * (calibration.degreeConstant + 1) * calibration.bandwidthConstant ≤
      calibration.dualGap ^ 3 / (65536 * C)
  rareCountLower :
    4 * (calibration.degreeConstant + 1) /
        ((1 / (65536 * C)) * calibration.dualGap ^ 2 * calibration.gamma) ≤
      calibration.rareCountConstant
  regimeScale :
    (4 * (calibration.degreeConstant + 1) ^ 2 /
        ((1 / (65536 * C)) * calibration.dualGap ^ 2 * calibration.gamma)) ^ 2 ≤
      calibration.regimeConstant
  dimensionRare :
    calibration.dimensionConstant ≤ calibration.dualGap ^ 4 / 16
  dimensionBranch :
    calibration.dimensionConstant ≤
      (calibration.dualGap * calibration.gamma * calibration.bandwidthConstant /
        (2 * (calibration.degreeConstant + 1))) ^ 2
  mixtureDecay : ∀ n : Nat, 1 ≤ n →
    C * (65536 * (n : Real)) * calibration.dualGap *
        rho ^ Nat.ceil (calibration.degreeConstant * logEN n) ≤ 1 / 8

set_option maxHeartbeats 4000000 in
-- The explicit finite-product transport has substantial reducible kernel terms.
-- @node: lem:common-marginal-uniform-intensity
/-- Uniform-intensity rare-cell priors have overlap, identical random `(X,A)` tables,
separated target centers, controlled variance, and label-gated mixture distance.
The returned calibration also exports the degree floor and the C55 bandwidth
slack already used by its construction.  [the stated conclusion](goal). -/
lemma common_marginal_uniform_intensity :
    ∀ (eps : Real), 0 < eps → eps < 1 / 2 →
    ∃ calibration : CommonMarginalCalibration eps, ∃ C rho : Real,
      0 < C ∧ rho ∈ Set.Ioo (0 : Real) 1 ∧
      CommonMarginalCalibrationClosure calibration C rho ∧
      ∀ (n m L : Nat), 1 ≤ n → 2 ≤ L → ∀ (u v B a : Real) (k d : Nat),
        2 ≤ d →
        0 ≤ u → 0 ≤ v → 0 < u + v →
        (u + v) * B ≤ calibration.uniformBandwidthConstant * L →
        0 < B →
        a = calibration.gamma * B / (L : Real) ^ 2 →
        k * a ≤ calibration.dualGap → k + 1 ≤ d →
        ∃ R : CommonMarginalRecipe calibration n m d L B a k,
          R.labeledIntensity = u ∧ R.auxiliaryIntensity = v ∧
          R.prior0 = commonMarginalRecipePriorOf R false ∧
          R.prior1 = commonMarginalRecipePriorOf R true ∧
          CommonMarginalBounds R u v calibration.dualGap C rho := by
  intro eps heps hepsHalf
  rcases finite_alternation_duality heps hepsHalf with
    ⟨gamma, gap, hgamma, hgap, hdual⟩
  let kappa := (1 - 2 * eps) / eps
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact div_pos (by linarith) heps
  rcases Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.exists_geometric_markedPoisson_tv_bound.{0}
      eps kappa heps hepsHalf rfl with
    ⟨bandwidth, C0, rho, hbandwidth, hC0, hrho, htv⟩
  let C := max C0 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right C0 1)
  have hC0_le : C0 ≤ C := le_max_left C0 1
  let dualGap : Real := min gap (1 / 4)
  have hdualGap : 0 < dualGap := lt_min hgap (by norm_num)
  let degreeConstant := commonMarginalDegreeConstant C dualGap rho
  have hdegreeConstant : 0 < degreeConstant :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let s : Real := 1 / (65536 * C)
  have hs : 0 < s := by dsimp [s]; positivity
  let K : Real := s * dualGap ^ 2 * gamma
  have hK : 0 < K := by dsimp [K]; positivity
  let b0 : Real := min (bandwidth / 131072)
    (min (dualGap / (8 * gamma))
      (s * dualGap ^ 3 / (8 * (degreeConstant + 1))))
  have hb0 : 0 < b0 := by
    apply lt_min (div_pos hbandwidth (by norm_num))
    apply lt_min (div_pos hdualGap (mul_pos (by norm_num) hgamma))
    exact div_pos (mul_pos hs (pow_pos hdualGap 3))
      (mul_pos (by norm_num) (by linarith))
  let rareConstant : Real := dualGap / (2 * gamma * b0)
  have hrareConstant : 0 < rareConstant := by
    exact div_pos hdualGap (mul_pos (mul_pos (by norm_num) hgamma) hb0)
  let regimeConstant : Real :=
    max 1 (4 * (degreeConstant + 1) ^ 2 / K) ^ 2
  have hregimeConstant : 0 < regimeConstant := by
    dsimp [regimeConstant]
    positivity
  let dimensionConstant : Real := min (dualGap ^ 4 / 16)
    (min ((dualGap * gamma * b0 / (2 * (degreeConstant + 1))) ^ 2)
      ((1 / 65536) / regimeConstant))
  have hdimensionConstant : 0 < dimensionConstant := by
    dsimp [dimensionConstant]
    positivity
  let calibration : CommonMarginalCalibration eps :=
    { regimeConstant := regimeConstant
      regimeConstant_pos := hregimeConstant
      degreeConstant := degreeConstant
      degreeConstant_pos := hdegreeConstant
      bandwidthConstant := b0
      bandwidthConstant_pos := hb0
      uniformBandwidthConstant := bandwidth
      uniformBandwidthConstant_pos := hbandwidth
      gamma := gamma
      gamma_pos := hgamma
      rareCountConstant := rareConstant
      rareCountConstant_pos := hrareConstant
      dualGap := dualGap
      dualGap_pos := hdualGap
      dualGap_le_quarter := min_le_right _ _
      dimensionConstant := dimensionConstant
      dimensionConstant_pos := hdimensionConstant }
  have hbandwidthSlack :
      131072 * calibration.bandwidthConstant ≤
        calibration.uniformBandwidthConstant := by
    dsimp [calibration]
    have hb0_le : b0 ≤ bandwidth / 131072 := min_le_left _ _
    nlinarith
  have hdegreeFloor : (2 : Real) ≤ calibration.degreeConstant := by
    exact le_max_left _ _
  have hrareScale : calibration.rareCountConstant * calibration.gamma *
      calibration.bandwidthConstant ≤ calibration.dualGap := by
    dsimp [calibration, rareConstant]
    field_simp
    nlinarith [hdualGap]
  have hrareCountIdentity : calibration.rareCountConstant =
      calibration.dualGap /
        (2 * calibration.gamma * calibration.bandwidthConstant) := by
    rfl
  have hrareCountFloor : (4 : Real) ≤ calibration.rareCountConstant := by
    dsimp [calibration, rareConstant]
    have hb0_le : b0 ≤ dualGap / (8 * gamma) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hgne : gamma ≠ 0 := ne_of_gt hgamma
    have hbne : b0 ≠ 0 := ne_of_gt hb0
    field_simp [hgne, hbne] at hb0_le ⊢
    nlinarith
  have hdimensionFloor : calibration.dimensionConstant *
      calibration.regimeConstant ≤ 1 / 65536 := by
    dsimp [calibration, dimensionConstant]
    have hdim : dimensionConstant ≤ (1 / 65536) / regimeConstant :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc
      dimensionConstant * regimeConstant ≤
          ((1 / 65536) / regimeConstant) * regimeConstant :=
        mul_le_mul_of_nonneg_right hdim hregimeConstant.le
      _ = 1 / 65536 := by field_simp [ne_of_gt hregimeConstant]
  have hvarianceBandwidth :
      8 * (calibration.degreeConstant + 1) * calibration.bandwidthConstant ≤
        calibration.dualGap ^ 3 / (65536 * C) := by
    dsimp [calibration]
    have hb0_le : b0 ≤ s * dualGap ^ 3 / (8 * (degreeConstant + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp [s] at hb0_le
    have hD1 : 0 < degreeConstant + 1 := by linarith
    have hCne : C ≠ 0 := ne_of_gt hC
    have hDne : degreeConstant + 1 ≠ 0 := ne_of_gt hD1
    field_simp [hCne, hDne] at hb0_le ⊢
    nlinarith
  have hrareCountLower :
      4 * (calibration.degreeConstant + 1) /
          ((1 / (65536 * C)) * calibration.dualGap ^ 2 * calibration.gamma) ≤
        calibration.rareCountConstant := by
    dsimp [calibration, rareConstant]
    have hb0_le : b0 ≤ s * dualGap ^ 3 / (8 * (degreeConstant + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hCne : C ≠ 0 := ne_of_gt hC
    have hDne : degreeConstant + 1 ≠ 0 := by linarith
    have hgne : gamma ≠ 0 := ne_of_gt hgamma
    have hbne : b0 ≠ 0 := ne_of_gt hb0
    have hgapne : dualGap ≠ 0 := ne_of_gt hdualGap
    dsimp [s] at hb0_le ⊢
    field_simp [hCne, hDne, hgne, hbne, hgapne] at hb0_le ⊢
    nlinarith
  have hregimeScale :
      (4 * (calibration.degreeConstant + 1) ^ 2 /
          ((1 / (65536 * C)) * calibration.dualGap ^ 2 * calibration.gamma)) ^ 2 ≤
        calibration.regimeConstant := by
    dsimp [calibration, regimeConstant, K, s]
    have hq : 0 ≤ 4 * (degreeConstant + 1) ^ 2 /
        (1 / (65536 * C) * dualGap ^ 2 * gamma) := by positivity
    have hqmax := le_max_right (1 : Real)
      (4 * (degreeConstant + 1) ^ 2 /
        (1 / (65536 * C) * dualGap ^ 2 * gamma))
    nlinarith [sq_nonneg
      (max 1 (4 * (degreeConstant + 1) ^ 2 /
        (1 / (65536 * C) * dualGap ^ 2 * gamma)) -
          4 * (degreeConstant + 1) ^ 2 /
            (1 / (65536 * C) * dualGap ^ 2 * gamma))]
  have hdimensionRare :
      calibration.dimensionConstant ≤ calibration.dualGap ^ 4 / 16 := by
    exact min_le_left _ _
  have hdimensionBranch :
      calibration.dimensionConstant ≤
        (calibration.dualGap * calibration.gamma * calibration.bandwidthConstant /
          (2 * (calibration.degreeConstant + 1))) ^ 2 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmixtureDecay : ∀ n : Nat, 1 ≤ n →
      C * (65536 * (n : Real)) * calibration.dualGap *
          rho ^ Nat.ceil (calibration.degreeConstant * logEN n) ≤ 1 / 8 := by
    intro n hn
    let q : Real := -Real.log rho
    let M : Real := 8 * (C * 65536 * dualGap)
    have hq : 0 < q := by
      dsimp [q]
      exact neg_pos.mpr (Real.log_neg hrho.1 hrho.2)
    have hM : 0 < M := by dsimp [M]; positivity
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log (n : Real) :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hdegree : max 1 (Real.log M + 2) / q ≤
        commonMarginalDegreeConstant C dualGap rho := by
      exact le_max_right _ _
    have hqdegree : max 1 (Real.log M + 2) ≤
        q * commonMarginalDegreeConstant C dualGap rho := by
      rw [mul_comm]
      exact (div_le_iff₀ hq).mp hdegree
    have hqdegree_one : 1 ≤
        q * commonMarginalDegreeConstant C dualGap rho :=
      (le_max_left _ _).trans hqdegree
    have hqdegree_log : Real.log M + 2 ≤
        q * commonMarginalDegreeConstant C dualGap rho :=
      (le_max_right _ _).trans hqdegree
    have hlogEN : logEN n = 1 + Real.log (n : Real) := by
      rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    have hceil : commonMarginalDegreeConstant C dualGap rho * logEN n ≤
        (Nat.ceil (commonMarginalDegreeConstant C dualGap rho * logEN n) : Real) :=
      Nat.le_ceil _
    have hlogpow :
        (Nat.ceil (commonMarginalDegreeConstant C dualGap rho * logEN n) : Real) *
            Real.log rho ≤ -Real.log M - Real.log (n : Real) := by
      have hqrho : Real.log rho = -q := by simp [q]
      rw [hlogEN] at hceil
      rw [hlogEN, hqrho]
      nlinarith [mul_le_mul_of_nonneg_left hqdegree_one hlogn]
    have htarget : 0 < 1 / (M * (n : Real)) := by positivity
    have htargetLog : Real.log (1 / (M * (n : Real))) =
        -Real.log M - Real.log (n : Real) := by
      rw [one_div, Real.log_inv, Real.log_mul hM.ne' hnR.ne']
      ring
    have hpow : rho ^ Nat.ceil
          (commonMarginalDegreeConstant C dualGap rho * logEN n) ≤
        1 / (M * (n : Real)) := by
      apply (Real.pow_le_iff_le_log hrho.1 htarget).2
      rw [htargetLog]
      exact hlogpow
    dsimp [calibration]
    have hfactor : 0 ≤ C * (65536 * (n : Real)) * dualGap := by positivity
    calc
      C * (65536 * (n : Real)) * dualGap *
          rho ^ Nat.ceil (commonMarginalDegreeConstant C dualGap rho * logEN n)
          ≤ C * (65536 * (n : Real)) * dualGap *
              (1 / (M * (n : Real))) := mul_le_mul_of_nonneg_left hpow hfactor
      _ = 1 / 8 := by dsimp [M]; field_simp
  have hclosure : CommonMarginalCalibrationClosure calibration C rho :=
    ⟨hbandwidthSlack, hdegreeFloor, hrareScale, hrareCountIdentity,
      hrareCountFloor,
      hdimensionFloor,
      hvarianceBandwidth, hrareCountLower, hregimeScale, hdimensionRare,
      hdimensionBranch,
      hmixtureDecay⟩
  refine ⟨calibration, C, rho, hC, hrho, hclosure, ?_⟩
  intro n m L hn hL u v B a k d hd hu hv huv hband hB ha hka hkd
  have ha' : a = gamma * B / (L : Real) ^ 2 := by
    simpa [calibration] using ha
  have ha_pos : 0 < a := by rw [ha']; positivity
  have hdualScale := hdual L hL B hB
  dsimp only at hdualScale
  rw [← ha'] at hdualScale
  rcases hdualScale with ⟨hlo, ⟨D⟩⟩
  let cert := normalizedCertificateOfFiniteMomentDual D
  have hcertSupport : ∀ᵐ p ∂cert.signedMeasure.variation,
      p ∈ Set.Icc (a / kappa) B := by
    rw [cert.variation_eq_absoluteMeasure]
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.absoluteMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by
      simpa [cert, normalizedCertificateOfFiniteMomentDual, kappa] using D.support i)
  let nu := cert.zeroInflatedPrior a
  have hnu : IsProbabilityMeasure nu := by
    exact cert.zeroInflatedPrior_isProbabilityMeasure a kappa B ha_pos hkappa hcertSupport
  let generator := cert.zeroInflatedProductPrior a k
  have hgenerator : IsProbabilityMeasure generator := by
    exact cert.zeroInflatedProductPrior_isProbabilityMeasure
      a kappa B k ha_pos hkappa hcertSupport
  have hgeneratorSupport : ∀ᵐ w ∂generator,
      ∀ i, w i = 0 ∨ w i ∈ Set.Icc (a / kappa) B := by
    exact cert.zeroInflatedProductPrior_support a kappa B k ha_pos hkappa hcertSupport
  let mean : Real := ∫ p, p ∂nu
  have hratioInt : Integrable (fun p : Real => p / (p + a))
      cert.signedMeasure.variation := by
    apply Integrable.of_bound
      (measurable_id.div (measurable_id.add measurable_const)).aestronglyMeasurable 1
    filter_upwards [hcertSupport] with p hp
    have hp0 : 0 < p := (div_pos ha_pos hkappa).trans_le hp.1
    change |p / (p + a)| ≤ 1
    rw [abs_of_nonneg (div_nonneg hp0.le (add_nonneg hp0.le ha_pos.le))]
    exact (div_le_one (add_pos hp0 ha_pos)).2 (le_add_of_nonneg_right ha_pos.le)
  have hratio_nonneg : 0 ≤ ∫ p, p / (p + a) ∂cert.signedMeasure.variation := by
    apply integral_nonneg_of_ae
    filter_upwards [hcertSupport] with p hp
    have hp0 : 0 < p := (div_pos ha_pos hkappa).trans_le hp.1
    positivity
  have hratio_le : ∫ p, p / (p + a) ∂cert.signedMeasure.variation ≤ 1 := by
    have hone : Integrable (fun _p : Real => (1 : Real)) cert.signedMeasure.variation :=
      integrable_const 1
    calc
      ∫ p, p / (p + a) ∂cert.signedMeasure.variation ≤
          ∫ _p, (1 : Real) ∂cert.signedMeasure.variation := by
        apply integral_mono_ae hratioInt hone
        filter_upwards [hcertSupport] with p hp
        have hp0 : 0 < p := (div_pos ha_pos hkappa).trans_le hp.1
        exact (div_le_one (add_pos hp0 ha_pos)).2 (le_add_of_nonneg_right ha_pos.le)
      _ = 1 := by simp
  have hmean_eq : mean =
      a * ∫ p, p / (p + a) ∂cert.signedMeasure.variation := by
    simpa [mean, nu] using
      cert.integral_id_zeroInflatedPrior a kappa B ha_pos hkappa hcertSupport
  have hmean_nonneg : 0 ≤ mean := by rw [hmean_eq]; positivity
  have hmean_le : mean ≤ a := by
    rw [hmean_eq]
    nlinarith
  let reservoirMass : Real := 1 - (k : Real) * mean
  have hreservoirMass_pos : 0 < reservoirMass := by
    have hkmean : (k : Real) * mean ≤ (k : Real) * a := by gcongr
    have hkale : (k : Real) * a ≤ 1 / 4 :=
      hka.trans (calibration.dualGap_le_quarter)
    dsimp [reservoirMass]
    linarith
  have hd1 : 1 ≤ d := by omega
  have hvariationNodes : ∀ᵐ p ∂cert.signedMeasure.variation,
      p ∈ Set.range cert.node := by
    rw [cert.variation_eq_absoluteMeasure]
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.absoluteMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff (Set.finite_range cert.node).measurableSet).2 ⟨i, rfl⟩
  have hnuNodes : ∀ᵐ p ∂nu, p = 0 ∨ p ∈ Set.range cert.node := by
    rw [show nu = cert.zeroInflatedPrior a from rfl]
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedPrior
    rw [ae_add_measure_iff]
    constructor
    · apply (ae_withDensity_iff (by fun_prop)).2
      filter_upwards [hvariationNodes] with p hp
      exact fun _ => Or.inr hp
    · apply Measure.ae_smul_measure
      exact (ae_dirac_iff ((measurableSet_singleton (0 : Real)).union
        (Set.finite_range cert.node).measurableSet)).2 (Or.inl rfl)
  have hgeneratorNodes : ∀ᵐ w ∂generator, ∀ i,
      w i = 0 ∨ w i ∈ Set.range cert.node := by
    rw [show generator = cert.zeroInflatedProductPrior a k from rfl]
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedProductPrior
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin k => cert.zeroInflatedPrior a)).eventually hnuNodes
  let q : (Fin k → Real) → Fin k → Real := fun w i =>
    if w i ∈ Set.range cert.node then w i else 0
  have hq_good (w : Fin k → Real) (i : Fin k) :
      q w i = 0 ∨ q w i ∈ Set.Icc (a / kappa) B := by
    by_cases hi : w i ∈ Set.range cert.node
    · right
      rw [show q w i = w i by dsimp [q]; rw [if_pos hi]]
      obtain ⟨j, hj⟩ := hi
      rw [← hj]
      simpa [cert, normalizedCertificateOfFiniteMomentDual, kappa] using D.support j
    · left
      dsimp [q]
      rw [if_neg hi]
  have hq_nonneg (w : Fin k → Real) (i : Fin k) : 0 ≤ q w i := by
    rcases hq_good w i with hi | hi
    · simp [hi]
    · exact hi.1.trans' (div_nonneg ha_pos.le hkappa.le)
  have hq_eq : ∀ᵐ w ∂generator, q w = w := by
    filter_upwards [hgeneratorNodes] with w hw
    funext i
    rcases hw i with hi | hi
    · dsimp [q]
      by_cases hnode : w i ∈ Set.range cert.node
      · rw [if_pos hnode]
      · rw [if_neg hnode]
        exact hi.symm
    · dsimp [q]
      rw [if_pos hi]
  have hq_measurable : Measurable q := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).piecewise
      ((Set.finite_range cert.node).measurableSet.preimage (measurable_pi_apply i))
      measurable_const
  have hq_finite : (Set.range q).Finite := by
    apply (Set.Finite.pi (fun _ : Fin k =>
      (Set.finite_range cert.node).insert (0 : Real))).subset
    intro z hz i _
    obtain ⟨w, rfl⟩ := hz
    change q w i = 0 ∨ q w i ∈ Set.range cert.node
    by_cases hi : w i ∈ Set.range cert.node
    · right; dsimp [q]; rw [if_pos hi]; exact hi
    · left; dsimp [q]; rw [if_neg hi]
  have hzero_not_node : (0 : Real) ∉ Set.range cert.node := by
    rintro ⟨i, hi⟩
    have hlo_pos : 0 < a / kappa := div_pos ha_pos hkappa
    have hnode_pos : 0 < cert.node i := hlo_pos.trans_le (by
      simpa [cert, normalizedCertificateOfFiniteMomentDual, kappa] using (D.support i).1)
    exact (ne_of_gt hnode_pos) hi
  have hq_idem (w : Fin k → Real) : q (q w) = q w := by
    funext i
    by_cases hi : w i ∈ Set.range cert.node
    · have hqi : q w i = w i := by dsimp [q]; exact if_pos hi
      change (if q w i ∈ Set.range cert.node then q w i else 0) = q w i
      simp [hqi, hi]
    · have hqi : q w i = 0 := by dsimp [q]; exact if_neg hi
      change (if q w i ∈ Set.range cert.node then q w i else 0) = q w i
      simp [hqi, hzero_not_node]
  let rawMass : (Fin k → Real) → Fin d → Real := fun w =>
    commonMarginalRawMass hd1 hkd reservoirMass (q w)
  let rawTotalMass : (Fin k → Real) → Real := fun w =>
    reservoirMass + ∑ i, q w i
  have hrawTotalMass_pos (w : Fin k → Real) : 0 < rawTotalMass w := by
    dsimp [rawTotalMass]
    exact add_pos_of_pos_of_nonneg hreservoirMass_pos
      (Finset.sum_nonneg fun i _ => hq_nonneg w i)
  have hrawMass_sum (w : Fin k → Real) :
      rawTotalMass w = ∑ x, rawMass w x := by
    dsimp [rawTotalMass, rawMass]
    exact (commonMarginalRawMass_sum hd1 hkd reservoirMass (q w)).symm
  have hrawMass_nonneg (w : Fin k → Real) (x : Fin d) : 0 ≤ rawMass w x := by
    exact commonMarginalRawMass_nonneg hd1 hkd hreservoirMass_pos.le
      (hq_nonneg w) x
  let cellProbability : (Fin k → Real) → Fin d → Real := fun w x =>
    rawMass w x / rawTotalMass w
  have hcellProbability (w : Fin k → Real) (x : Fin d) :
      cellProbability w x ∈ Set.Icc (0 : Real) 1 := by
    have hxsum : rawMass w x ≤ rawTotalMass w := by
      rw [hrawMass_sum]
      exact Finset.single_le_sum (fun y _ => hrawMass_nonneg w y) (Finset.mem_univ x)
    constructor
    · exact div_nonneg (hrawMass_nonneg w x) (hrawTotalMass_pos w).le
    · exact (div_le_one (hrawTotalMass_pos w)).2 hxsum
  have hcellProbability_sum (w : Fin k → Real) :
      ∑ x, cellProbability w x = 1 := by
    simp_rw [cellProbability, ← Finset.sum_div, ← hrawMass_sum]
    exact div_self (ne_of_gt (hrawTotalMass_pos w))
  let outcomeSign : Real → Real := commonMarginalClampSign cert.polarSign
  have hpolarSign_mem (p : Real) : cert.polarSign p ∈ Set.Icc (-1 : Real) 1 := by
    by_cases hp : ∃ i, p = cert.node i
    · obtain ⟨i, rfl⟩ := hp
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.polarSign
      rw [Finset.sum_eq_single i]
      · rcases lt_trichotomy (cert.weight i) 0 with hi | hi | hi
        · simp [Real.sign_of_neg hi]
        · simp [hi]
        · simp [Real.sign_of_pos hi]
      · intro j _ hji
        simp [(cert.node_injective.ne hji.symm)]
      · simp
    · unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.polarSign
      have hne : ∀ i, p ≠ cert.node i := fun i hi => hp ⟨i, hi⟩
      simp [hne]
  have houtcomeSign (p : Real) : outcomeSign p ∈ Set.Icc (-1 : Real) 1 :=
    commonMarginalClampSign_mem _ _
  have houtcomeSign_eq (p : Real) : outcomeSign p = cert.polarSign p :=
    commonMarginalClampSign_eq (hpolarSign_mem p)
  let propensityField : (Fin k → Real) → Fin d → Real := fun w =>
    commonMarginalPropensity hd1 hkd eps a (q w)
  have hoverlapField (w : Fin k → Real) (x : Fin d) :
      propensityField w x ∈ Set.Icc eps (1 - eps) := by
    by_cases hx0 : x = commonMarginalReservoir hd1
    · subst x
      constructor <;> dsimp [propensityField] <;>
        rw [commonMarginalPropensity_reservoir] <;> linarith
    · by_cases hx : commonMarginalRawMass hd1 hkd 0 (q w) x = 0
      · constructor <;> simp [propensityField, commonMarginalPropensity, hx0, hx] <;>
          linarith
      · have hp0 : 0 < commonMarginalRawMass hd1 hkd 0 (q w) x :=
          lt_of_le_of_ne
            (commonMarginalRawMass_nonneg hd1 hkd le_rfl (hq_nonneg w) x)
            (Ne.symm hx)
        have hlower : a / kappa ≤ commonMarginalRawMass hd1 hkd 0 (q w) x := by
          by_cases hrare : ∃ i, x = commonMarginalRareCell hkd i
          · obtain ⟨i, rfl⟩ := hrare
            rw [commonMarginalRawMass_rare hd1 hkd 0 (q w) i]
            exact ((hq_good w i).resolve_left (by
              intro hi
              apply hx
              rw [commonMarginalRawMass_rare hd1 hkd 0 (q w) i, hi])).1
          · exfalso
            apply hx
            exact commonMarginalRawMass_unused hd1 hkd 0 (q w) x hx0
              (fun i hi => hrare ⟨i, hi⟩)
        have ha_div_le : a / commonMarginalRawMass hd1 hkd 0 (q w) x ≤ kappa := by
          apply (div_le_iff₀ hp0).2
          nlinarith [(div_le_iff₀ hkappa).1 hlower]
        have heupper : eps *
            (commonMarginalRawMass hd1 hkd 0 (q w) x + a) /
              commonMarginalRawMass hd1 hkd 0 (q w) x ≤ 1 - eps := by
          rw [mul_div_assoc, add_div, div_self (ne_of_gt hp0)]
          dsimp [kappa] at ha_div_le
          calc
            eps * (1 + a / commonMarginalRawMass hd1 hkd 0 (q w) x) ≤
                eps * (1 + kappa) := by gcongr
            _ = 1 - eps := by
              dsimp [kappa]
              field_simp [ne_of_gt heps]
              ring
        change commonMarginalPropensity hd1 hkd eps a (q w) x ∈ Set.Icc eps (1 - eps)
        rw [commonMarginalPropensity, if_neg hx0, if_neg hx]
        constructor
        · rw [mul_div_assoc, add_div, div_self (ne_of_gt hp0)]
          nlinarith [div_nonneg ha_pos.le hp0.le]
        · exact heupper
  have hpropensityField (w : Fin k → Real) (x : Fin d) :
      propensityField w x ∈ Set.Icc (0 : Real) 1 := by
    exact ⟨heps.le.trans (hoverlapField w x).1,
      (hoverlapField w x).2.trans (by linarith)⟩
  let outcomeMeanField : Bool → (Fin k → Real) → Fin d → Real :=
    fun branch w => commonMarginalOutcomeMean hd1 hkd outcomeSign branch (q w)
  have houtcomeMeanField (branch : Bool) (w : Fin k → Real) (x : Fin d) :
      outcomeMeanField branch w x ∈ Set.Icc (0 : Real) 1 :=
    commonMarginalOutcomeMean_mem hd1 hkd outcomeSign houtcomeSign branch (q w) x
  let lawOf : Bool → (Fin k → Real) → DiscreteLaw d := fun branch w =>
    finiteControlZeroLaw (cellProbability w) (propensityField w)
      (outcomeMeanField branch w) (hcellProbability w) (hpropensityField w)
      (houtcomeMeanField branch w) (hcellProbability_sum w)
  have hlawOf_measurable (branch : Bool) : Measurable (lawOf branch) := by
    have hc := measurable_comp_of_finite_range hq_measurable hq_finite (lawOf branch)
    convert hc using 1
    funext w
    change lawOf branch w = lawOf branch (q w)
    dsimp [lawOf, cellProbability, rawMass, rawTotalMass, propensityField,
      outcomeMeanField]
    congr 1 <;> simp only [hq_idem]
  let rawTarget : Bool → (Fin k → Real) → Real := fun branch w =>
    ∑ i, q w i *
      (1 + (if branch then outcomeSign (q w i) else -outcomeSign (q w i))) / 2
  let rawScale : DiscreteLaw d → Real := fun P =>
    reservoirMass / cellMass P (commonMarginalReservoir hd1)
  let prior0 : Measure (DiscreteLaw d) := generator.map (lawOf false)
  let prior1 : Measure (DiscreteLaw d) := generator.map (lawOf true)
  let experimentKernel : ProbabilityTheory.Kernel (DiscreteLaw d) (RawPoissonCounts d) :=
    { toFun := fun P => rawPoissonLaw P (rawScale P) u v
      measurable' := measurable_from_top }
  let rawExperiment0 :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive prior0 experimentKernel
  let rawExperiment1 :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive prior1 experimentKernel
  let targetFn : Real → Real := fun p => p / (p + a)
  let dual0 : Measure Real := cert.orientedPrior0 targetFn
  let dual1 : Measure Real := cert.orientedPrior1 targetFn
  have hdualSupport (branch : Bool) : ∀ᵐ p ∂(if branch then dual1 else dual0),
      p ∈ Set.Icc (a / kappa) B := by
    have hrange := cert.jordanPriors_ae_mem_range
    have hpos : ∀ᵐ p ∂cert.positivePrior, p ∈ Set.Icc (a / kappa) B := by
      filter_upwards [hrange.1] with p hp
      obtain ⟨i, rfl⟩ := hp
      simpa [cert, normalizedCertificateOfFiniteMomentDual, kappa] using D.support i
    have hneg : ∀ᵐ p ∂cert.negativePrior, p ∈ Set.Icc (a / kappa) B := by
      filter_upwards [hrange.2] with p hp
      obtain ⟨i, rfl⟩ := hp
      simpa [cert, normalizedCertificateOfFiniteMomentDual, kappa] using D.support i
    cases branch <;> simp only [Bool.false_eq_true, if_false, if_true]
    · unfold dual0 Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.orientedPrior0
      split <;> assumption
    · unfold dual1 Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.orientedPrior1
      split <;> assumption
  have hrawTarget_formula (branch : Bool) (w : Fin k → Real) :
      rawTarget branch w = rawTotalMass w * ateFunctional (lawOf branch w) := by
    rw [show ateFunctional (lawOf branch w) =
        ∑ x, cellProbability w x * outcomeMeanField branch w x by
      dsimp [lawOf]
      exact finiteControlZeroLaw_ate (cellProbability w) (propensityField w)
        (outcomeMeanField branch w) (hcellProbability w) (hpropensityField w)
        (houtcomeMeanField branch w) (hcellProbability_sum w) heps
        (fun x _ => (hoverlapField w x).1)]
    rw [Finset.mul_sum]
    have hcancel (x : Fin d) : rawTotalMass w *
        (cellProbability w x * outcomeMeanField branch w x) =
        rawMass w x * outcomeMeanField branch w x := by
      dsimp [cellProbability]
      field_simp [ne_of_gt (hrawTotalMass_pos w)]
    simp_rw [hcancel]
    dsimp [rawTarget, rawMass, outcomeMeanField]
    exact (commonMarginalRawMass_mul_outcome_sum hd1 hkd reservoirMass
      outcomeSign branch (q w)).symm
  have hmodel (branch : Bool) (w : Fin k → Real) :
      ModelClass d eps (lawOf branch w) := by
    dsimp [lawOf]
    exact finiteControlZeroLaw_model (cellProbability w) (propensityField w)
      (outcomeMeanField branch w) (hcellProbability w) (hpropensityField w)
      (houtcomeMeanField branch w) (hcellProbability_sum w) hd heps hepsHalf
      (fun x _ => hoverlapField w x)
  have hsigmaSeparation : calibration.dualGap ≤
      ∫ᵛ p, p / (p + a) ∂<•cert.signedMeasure := by
    rw [Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.signedMeasure]
    rw [VectorMeasure.integral_finsetSum_vectorMeasure (fun i _ => by
      change Integrable (fun p : Real => p / (p + a))
        (VectorMeasure.dirac (cert.node i) (cert.weight i)).variation
      rw [VectorMeasure.variation_dirac]
      exact (integrable_dirac (by simp)).smul_measure (by simp))]
    have hgap' : calibration.dualGap ≤
        ∑ i, cert.weight i * (cert.node i / (cert.node i + a)) := by
      exact (min_le_left gap (1 / 4)).trans (by
        simpa [cert, normalizedCertificateOfFiniteMomentDual] using D.gap)
    simpa using hgap'
  let R : CommonMarginalRecipe calibration n m d L B a k := {
    finiteAtomConstruction := True
    kappa := kappa
    degree_ge_two := fun _ => hL
    bandwidth_pos := fun _ => hB
    shift_eq := fun _ => ha
    kappa_eq := rfl
    rareCount_le := by omega
    reservoir := commonMarginalReservoir hd1
    reservoir_is_first := rfl
    rareCell := commonMarginalRareCell hkd
    rareCell_injective := commonMarginalRareCell_injective hkd
    reservoir_ne_rare := commonMarginalReservoir_ne_rareCell hd1 hkd
    outcomeSign := outcomeSign
    outcomeSign_mem := houtcomeSign
    generator := generator
    generatorProbability := hgenerator
    sigma := cert.signedMeasure
    sigmaVariationProbability := by infer_instance
    sigma_support := fun _ => hcertSupport
    outcomeSign_integrable := by
      simpa only [funext houtcomeSign_eq] using cert.integrable_polarSign
    sigma_density := by
      simpa only [funext houtcomeSign_eq] using cert.signedMeasure_eq_withDensity_polarSign
    nu := nu
    nuProbability := hnu
    nu_eq := fun _ => rfl
    generator_eq_iid := rfl
    generator_support := fun _ => hgeneratorSupport
    dual0 := dual0
    dual1 := dual1
    dualProbability0 := by dsimp [dual0]; infer_instance
    dualProbability1 := by dsimp [dual1]; infer_instance
    dualSupport0 := fun _ => by simpa using hdualSupport false
    dualSupport1 := fun _ => by simpa using hdualSupport true
    dualMomentMatch := fun _ j hj => by
      dsimp [dual0, dual1]
      exact cert.orientedPriors_moments_eq targetFn j hj
    dualSeparation := fun _ => by
      rw [show (∫ p, p / (p + a) ∂dual1) - ∫ p, p / (p + a) ∂dual0 =
          2 * |∑ i, cert.weight i * targetFn (cert.node i)| by
        dsimp [dual0, dual1]
        exact cert.orientedPrior_target_separation targetFn]
      have hsum : calibration.dualGap ≤
          ∑ i, cert.weight i * targetFn (cert.node i) := by
        exact (min_le_left gap (1 / 4)).trans (by
          simpa [targetFn, cert, normalizedCertificateOfFiniteMomentDual] using D.gap)
      nlinarith [le_abs_self (∑ i, cert.weight i * targetFn (cert.node i))]
    sigmaMomentZero := fun _ j hj => cert.integral_pow_signedMeasure_eq_zero j hj
    sigmaSeparation := fun _ => hsigmaSeparation
    lawOf := lawOf
    lawOf_measurable := hlawOf_measurable
    rawMass := rawMass
    rawTotalMass := rawTotalMass
    rawTarget := rawTarget
    rawMass_sum := Filter.Eventually.of_forall hrawMass_sum
    rawMass_pos := Filter.Eventually.of_forall hrawTotalMass_pos
    rareRawMass := fun _ => by
      filter_upwards [hq_eq] with w hw
      intro i
      dsimp [rawMass]
      rw [commonMarginalRawMass_rare, hw]
    reservoirRawMass := fun _ => by
      filter_upwards [hq_eq] with w hw
      dsimp [rawMass]
      rw [commonMarginalRawMass_reservoir]
      have hcoord (i : Fin k) : ∫ z, z i ∂generator = mean := by
        rw [show generator = cert.zeroInflatedProductPrior a k from rfl,
          cert.integral_coordinate_zeroInflatedProductPrior
            a kappa B k i ha_pos hkappa hcertSupport]
        exact hmean_eq.symm
      simp_rw [hcoord]
      simp [reservoirMass]
    unusedRawMass := by
      apply Filter.Eventually.of_forall
      intro w x hx hxi
      exact commonMarginalRawMass_unused hd1 hkd reservoirMass (q w) x hx hxi
    normalization := fun branch => by
      apply Filter.Eventually.of_forall
      intro w x
      dsimp [lawOf]
      rw [finiteControlZeroLaw_cellMass]
    rawTarget_formula := fun branch => Filter.Eventually.of_forall (hrawTarget_formula branch)
    rawScale := rawScale
    rawScale_measurable := measurable_from_top
    rawScale_lawOf := fun branch => by
      apply Filter.Eventually.of_forall
      intro w
      dsimp [rawScale, lawOf]
      rw [finiteControlZeroLaw_cellMass]
      dsimp [cellProbability, rawMass]
      rw [commonMarginalRawMass_reservoir]
      field_simp [ne_of_gt hreservoirMass_pos, ne_of_gt (hrawTotalMass_pos w)]
    commonTable_pointwise := by
      apply Filter.Eventually.of_forall
      intro w
      dsimp [lawOf]
      rw [finiteControlZeroLaw_auxTable, finiteControlZeroLaw_auxTable]
    rareTreatmentMass := fun _ branch => by
      filter_upwards [hq_eq] with w hw
      intro i hi
      dsimp [lawOf]
      rw [finiteControlZeroLaw_armMass]
      dsimp [cellProbability, rawMass, propensityField]
      rw [commonMarginalRawMass_rare, hw,
        commonMarginalPropensity_rare hd1 hkd eps a w i hi]
      field_simp [ne_of_gt (hrawTotalMass_pos w), hi]
    reservoirPropensity := fun branch => by
      apply Filter.Eventually.of_forall
      intro w
      dsimp [lawOf]
      rw [finiteControlZeroLaw_propensity]
      · exact commonMarginalPropensity_reservoir hd1 hkd eps a (q w)
      · dsimp [cellProbability, rawMass]
        rw [commonMarginalRawMass_reservoir]
        exact div_pos hreservoirMass_pos (hrawTotalMass_pos w)
    controlOutcomeZero := fun branch => by
      apply Filter.Eventually.of_forall
      intro w x
      dsimp [lawOf]
      exact finiteControlZeroLaw_outcomeMean_false _ _ _ _ _ _ _ x
    reservoirTreatedOutcomeZero := fun _ branch => by
      apply Filter.Eventually.of_forall
      intro w
      dsimp [lawOf]
      rw [finiteControlZeroLaw_outcomeMean_true]
      · exact commonMarginalOutcomeMean_reservoir hd1 hkd outcomeSign branch (q w)
      · dsimp [cellProbability, rawMass, propensityField]
        rw [commonMarginalRawMass_reservoir, commonMarginalPropensity_reservoir]
        exact mul_pos (div_pos hreservoirMass_pos (hrawTotalMass_pos w)) (by norm_num)
    rareOutcomeMeans := fun _ => by
      filter_upwards [hq_eq] with w hw
      intro i hi
      have ht (branch : Bool) : outcomeMean (lawOf branch w) true
          (commonMarginalRareCell hkd i) =
          (1 + (if branch then outcomeSign (w i) else -outcomeSign (w i))) / 2 := by
        dsimp [lawOf]
        rw [finiteControlZeroLaw_outcomeMean_true]
        · dsimp [outcomeMeanField]
          rw [show q w = w from hw, commonMarginalOutcomeMean_rare _ _ _ _ _ _ hi]
        · dsimp [cellProbability, rawMass, propensityField]
          rw [commonMarginalRawMass_rare, hw,
            commonMarginalPropensity_rare hd1 hkd eps a w i hi]
          have hwi : 0 < w i := lt_of_le_of_ne (by
            rw [← congrFun hw i]
            exact hq_nonneg w i) (Ne.symm hi)
          exact mul_pos (div_pos hwi (hrawTotalMass_pos w))
            (div_pos (mul_pos heps (add_pos hwi ha_pos)) hwi)
      constructor
      · rw [ht false]
        rw [houtcomeSign_eq]
        norm_num
        ring
      · rw [ht true, houtcomeSign_eq]
        norm_num
    parametricShape := fun hfalse => False.elim (hfalse trivial)
    model0 := Filter.Eventually.of_forall (hmodel false)
    model1 := Filter.Eventually.of_forall (hmodel true)
    prior0 := prior0
    prior1 := prior1
    prior0_eq := rfl
    prior1_eq := rfl
    probability0 := by
      dsimp [prior0]
      let _ := hgenerator
      exact Measure.isProbabilityMeasure_map (hlawOf_measurable false).aemeasurable
    probability1 := by
      dsimp [prior1]
      let _ := hgenerator
      exact Measure.isProbabilityMeasure_map (hlawOf_measurable true).aemeasurable
    priorModel0 := by
      dsimp [prior0]
      apply (MeasureTheory.ae_map_iff (hlawOf_measurable false).aemeasurable
        MeasurableSpace.measurableSet_top).2
      exact Filter.Eventually.of_forall (hmodel false)
    priorModel1 := by
      dsimp [prior1]
      apply (MeasureTheory.ae_map_iff (hlawOf_measurable true).aemeasurable
        MeasurableSpace.measurableSet_top).2
      exact Filter.Eventually.of_forall (hmodel true)
    labeledIntensity := u
    auxiliaryIntensity := v
    experimentKernel := experimentKernel
    experimentKernel_eq := fun _ => rfl
    rawExperiment0 := rawExperiment0
    rawExperiment1 := rawExperiment1
    rawExperiment0_eq := rfl
    rawExperiment1_eq := rfl }
  refine ⟨R, rfl, rfl, by simp [commonMarginalRecipePriorOf],
    by simp [commonMarginalRecipePriorOf], ?_⟩
  have hsameTable : randomAuxTableLaw R.prior0 = randomAuxTableLaw R.prior1 := by
    unfold randomAuxTableLaw
    rw [R.prior0_eq, R.prior1_eq]
    rw [Measure.map_map (by fun_prop) (R.lawOf_measurable false),
      Measure.map_map (by fun_prop) (R.lawOf_measurable true)]
    exact Measure.map_congr R.commonTable_pointwise
  have hnuIcc : ∀ᵐ p ∂nu, p ∈ Set.Icc (0 : Real) B := by
    filter_upwards [cert.zeroInflatedPrior_support
      a kappa B ha_pos hkappa hcertSupport] with p hp
    rcases hp with rfl | hp
    · exact ⟨le_rfl, hB.le⟩
    · exact ⟨(div_nonneg ha_pos.le hkappa.le).trans hp.1, hp.2⟩
  let branchScalar : Bool → Real → Real := fun branch p =>
    p * (1 + (if branch then outcomeSign p else -outcomeSign p)) / 2
  have houtcomeSign_meas : Measurable outcomeSign := by
    dsimp [outcomeSign, commonMarginalClampSign]
    exact measurable_const.max (measurable_const.min cert.measurable_polarSign)
  have hbranchScalar_meas (branch : Bool) : Measurable (branchScalar branch) := by
    cases branch
    · exact measurable_id.mul (measurable_const.sub houtcomeSign_meas) |>.div_const 2
    · exact measurable_id.mul (measurable_const.add houtcomeSign_meas) |>.div_const 2
  have hbranchScalar_support (branch : Bool) : ∀ᵐ p ∂nu,
      0 ≤ branchScalar branch p ∧ branchScalar branch p ≤ p ∧ p ≤ B := by
    filter_upwards [hnuIcc] with p hp
    have hs := houtcomeSign p
    cases branch
    · change 0 ≤ p * (1 - outcomeSign p) / 2 ∧
        p * (1 - outcomeSign p) / 2 ≤ p ∧ p ≤ B
      constructor
      · exact div_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hs.2)) (by norm_num)
      · constructor
        · apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
          exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) hp.1
        · exact hp.2
    · change 0 ≤ p * (1 + outcomeSign p) / 2 ∧
        p * (1 + outcomeSign p) / 2 ≤ p ∧ p ≤ B
      constructor
      · exact div_nonneg (mul_nonneg hp.1 (by linarith [hs.1])) (by norm_num)
      · constructor
        · apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
          exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hp.1
        · exact hp.2
  have hrawTotalMeas : Measurable rawTotalMass := by
    dsimp [rawTotalMass]
    fun_prop
  have hrawTargetMeas (branch : Bool) : Measurable (rawTarget branch) := by
    dsimp [rawTarget]
    apply Finset.measurable_sum
    intro i _
    have hqi := (measurable_pi_apply i).comp hq_measurable
    cases branch
    · exact hqi.mul (measurable_const.sub (houtcomeSign_meas.comp hqi)) |>.div_const 2
    · exact hqi.mul (measurable_const.add (houtcomeSign_meas.comp hqi)) |>.div_const 2
  have hidIntegrable : Integrable (fun p : Real => p) nu := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable |B|
    filter_upwards [hnuIcc] with p hp
    change |p| ≤ |B|
    simpa [abs_of_nonneg hp.1, abs_of_nonneg (hp.1.trans hp.2)] using hp.2
  have hmassMean : ∫ w, R.rawTotalMass w ∂R.generator = 1 := by
    have hae : R.rawTotalMass =ᵐ[generator]
        fun w => reservoirMass + ∑ i, w i := by
      filter_upwards [hq_eq] with w hw
      dsimp [R, rawTotalMass]
      rw [hw]
    rw [integral_congr_ae hae]
    have hsum := integral_sum_iid (k := k) (nu := nu) hidIntegrable
    have hsumIntegrable : Integrable (fun w : Fin k → Real => ∑ i, w i) generator := by
      simpa [generator, nu,
        Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedProductPrior] using
        (integrable_finset_sum Finset.univ fun i _ =>
          integrable_eval (μ := fun _ : Fin k => nu) (i := i) hidIntegrable)
    rw [integral_add (integrable_const _) hsumIntegrable, integral_const]
    simpa [R, generator, mean, reservoirMass, nu,
      Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedProductPrior]
      using congrArg (fun z : Real => reservoirMass + z) hsum
  have hcoordMemLp (i : Fin k) : MemLp (fun w : Fin k → Real => w i) 2 generator := by
    apply MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable B
    filter_upwards [hgeneratorSupport] with w hw
    rcases hw i with hi | hi
    · simp [hi, hB.le]
    · have hwi0 : 0 ≤ w i := (div_pos ha_pos hkappa).le.trans hi.1
      rw [Real.norm_eq_abs, abs_of_nonneg hwi0]
      exact hi.2
  have hsumMemLp : MemLp (fun w : Fin k → Real => ∑ i, w i) 2 generator := by
    simpa only [Finset.sum_apply] using
      memLp_finset_sum Finset.univ (fun i _ => hcoordMemLp i)
  have hmassMemLp : MemLp R.rawTotalMass 2 R.generator := by
    have hae : R.rawTotalMass =ᵐ[generator]
        fun w => reservoirMass + ∑ i, w i := by
      filter_upwards [hq_eq] with w hw
      dsimp [R, rawTotalMass]
      rw [hw]
    rw [memLp_congr_ae hae]
    exact (memLp_const reservoirMass).add hsumMemLp
  have htargetMemLp (branch : Bool) :
      MemLp (R.rawTarget branch) 2 R.generator := by
    have hcoordScalarMemLp (i : Fin k) :
        MemLp (fun w : Fin k → Real => branchScalar branch (w i)) 2 generator := by
      apply MemLp.of_bound
        ((hbranchScalar_meas branch).comp (measurable_pi_apply i)).aestronglyMeasurable B
      filter_upwards [hgeneratorSupport] with w hw
      have hp : 0 ≤ w i ∧ w i ≤ B := by
        rcases hw i with hi | hi
        · simp [hi, hB.le]
        · exact ⟨(div_pos ha_pos hkappa).le.trans hi.1, hi.2⟩
      have hs := houtcomeSign (w i)
      change |branchScalar branch (w i)| ≤ B
      cases branch
      · change |w i * (1 - outcomeSign (w i)) / 2| ≤ B
        rw [abs_of_nonneg (div_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hs.2)) (by norm_num))]
        calc
          w i * (1 - outcomeSign (w i)) / 2 ≤ w i := by
            apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
            exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) hp.1
          _ ≤ B := hp.2
      · change |w i * (1 + outcomeSign (w i)) / 2| ≤ B
        rw [abs_of_nonneg (div_nonneg (mul_nonneg hp.1 (by linarith [hs.1])) (by norm_num))]
        calc
          w i * (1 + outcomeSign (w i)) / 2 ≤ w i := by
            apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
            exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hp.1
          _ ≤ B := hp.2
    have hsumScalarMemLp : MemLp
        (fun w : Fin k → Real => ∑ i, branchScalar branch (w i)) 2 generator := by
      simpa only [Finset.sum_apply] using
        memLp_finset_sum Finset.univ (fun i _ => hcoordScalarMemLp i)
    have hae : R.rawTarget branch =ᵐ[generator]
        fun w => ∑ i, branchScalar branch (w i) := by
      filter_upwards [hq_eq] with w hw
      dsimp [R, rawTarget, branchScalar]
      rw [hw]
    exact (memLp_congr_ae hae).2 hsumScalarMemLp
  have hmassVariance : generatorVariance R R.rawTotalMass ≤ C * k * B * a := by
    have hae : R.rawTotalMass =ᵐ[generator]
        fun w => reservoirMass + ∑ i, w i := by
      filter_upwards [hq_eq] with w hw
      dsimp [R, rawTotalMass]
      rw [hw]
    have hbase := variance_const_add_sum_iid_le (k := k) (nu := nu)
      (c := reservoirMass) hnuIcc hB.le hmean_le
    unfold generatorVariance
    rw [← variance_eq_integral hrawTotalMeas.aemeasurable, variance_congr hae]
    calc
      variance (fun w : Fin k → Real => reservoirMass + ∑ i, w i) generator ≤
          (k : Real) * B * a := by
            simpa [generator, nu,
              Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedProductPrior]
              using hbase
      _ ≤ C * k * B * a := by
        have hCge : 1 ≤ C := le_max_right C0 1
        have hkBa : 0 ≤ (k : Real) * B * a := by positivity
        calc
          (k : Real) * B * a = 1 * ((k : Real) * B * a) := by ring
          _ ≤ C * ((k : Real) * B * a) :=
            mul_le_mul_of_nonneg_right hCge hkBa
          _ = C * k * B * a := by ring
  have htargetVariance (branch : Bool) :
      generatorVariance R (R.rawTarget branch) ≤ C * k * B * a := by
    have hae : R.rawTarget branch =ᵐ[generator]
        fun w => ∑ i, branchScalar branch (w i) := by
      filter_upwards [hq_eq] with w hw
      dsimp [R, rawTarget, branchScalar]
      rw [hw]
    have hbase := variance_sum_iid_le (k := k) (nu := nu)
      (hbranchScalar_meas branch) (hbranchScalar_support branch) hB.le hmean_le
    unfold generatorVariance
    rw [← variance_eq_integral (hrawTargetMeas branch).aemeasurable,
      variance_congr hae]
    calc
      variance (fun w : Fin k → Real => ∑ i, branchScalar branch (w i)) generator ≤
          (k : Real) * B * a := by
            simpa [generator, nu,
              Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedProductPrior]
              using hbase
      _ ≤ C * k * B * a := by
        have hCge : 1 ≤ C := le_max_right C0 1
        have hkBa : 0 ≤ (k : Real) * B * a := by positivity
        calc
          (k : Real) * B * a = 1 * ((k : Real) * B * a) := by ring
          _ ≤ C * ((k : Real) * B * a) :=
            mul_le_mul_of_nonneg_right hCge hkBa
          _ = C * k * B * a := by ring
  have hbranchScalarInt (branch : Bool) : Integrable (branchScalar branch) nu := by
    apply Integrable.of_bound (hbranchScalar_meas branch).aestronglyMeasurable |B|
    filter_upwards [hbranchScalar_support branch] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2.1.trans hp.2.2 |>.trans (le_abs_self B)
  have hscalarDifference :
      (∫ p, branchScalar true p ∂nu) - ∫ p, branchScalar false p ∂nu =
        a * ∑ i, cert.weight i * (cert.node i / (cert.node i + a)) := by
    rw [← integral_sub (hbranchScalarInt true) (hbranchScalarInt false)]
    calc
      ∫ p, branchScalar true p - branchScalar false p ∂nu =
          ∫ p, p * cert.polarSign p ∂nu := by
        apply integral_congr_ae
        exact ae_of_all _ fun p => by
          dsimp [branchScalar]
          rw [houtcomeSign_eq]
          ring
      _ = a * ∑ i, cert.weight i * (cert.node i / (cert.node i + a)) := by
        simpa [nu] using zeroInflated_polar_firstMoment cert a kappa B
          ha_pos hkappa hcertSupport
  have hrawCenter (branch : Bool) : rawPriorCenter R branch =
      k * ∫ p, branchScalar branch p ∂nu := by
    unfold rawPriorCenter
    rw [integral_congr_ae (show R.rawTarget branch =ᵐ[generator]
        fun w => ∑ i, branchScalar branch (w i) by
      filter_upwards [hq_eq] with w hw
      dsimp [R, rawTarget, branchScalar]
      rw [hw])]
    have hsum := integral_sum_iid (k := k) (nu := nu) (hbranchScalarInt branch)
    simpa [R, generator, nu,
      Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.zeroInflatedProductPrior]
      using hsum
  have hcenterSeparation : calibration.dualGap * k * a ≤
      |rawPriorCenter R true - rawPriorCenter R false| := by
    rw [hrawCenter true, hrawCenter false, ← mul_sub, hscalarDifference]
    have hsum : calibration.dualGap ≤
        ∑ i, cert.weight i * (cert.node i / (cert.node i + a)) := by
      exact (min_le_left gap (1 / 4)).trans (by
        simpa [cert, normalizedCertificateOfFiniteMomentDual] using D.gap)
    have hnonneg : 0 ≤ calibration.dualGap * k * a := by positivity
    calc
      calibration.dualGap * k * a ≤
          (k : Real) * (a * ∑ i, cert.weight i *
            (cert.node i / (cert.node i + a))) := by
        have hka_nonneg : 0 ≤ (k : Real) * a := by positivity
        nlinarith
      _ ≤ |(k : Real) *
          (a * ∑ i, cert.weight i * (cert.node i / (cert.node i + a)))| :=
        le_abs_self _
  have hquantitative :
      calibration.dualGap * k * a ≤
          |rawPriorCenter R true - rawPriorCenter R false| ∧
      generatorVariance R R.rawTotalMass ≤ C * k * B * a ∧
      max (generatorVariance R (R.rawTarget false))
          (generatorVariance R (R.rawTarget true)) ≤ C * k * B * a ∧
      Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤
          C * u * k * a * rho ^ L := by
    have htvTransport :
        Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤
            C * u * k * a * rho ^ L := by
      have hone := htv cert a B u v ha_pos hB hu hv huv hcertSupport hband
      have hscale : (k : Real) * (C0 * u * a * rho ^ L) =
          C0 * u * k * a * rho ^ L := by ring
      let splitQ : unitInterval :=
        ⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one huv]
            linarith⟩
      let splitExperimentKernel (branch : Bool) :=
        markedControlSplitKernel splitQ ∘ₖ
          Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel
            eps a u v cert.polarSign cert.measurable_polarSign branch
      let zeroRare : ((Nat × Nat) × (Nat × (Nat × Nat))) :=
        ((0, 0), (0, (0, 0)))
      let rawRareKernel (branch : Bool) : Kernel Real
          ((Nat × Nat) × (Nat × (Nat × Nat))) :=
        Kernel.piecewise (s := ({0} : Set Real)) (measurableSet_singleton 0)
          (Kernel.const Real (Measure.dirac zeroRare))
          (splitExperimentKernel branch)
      have hsplitExperimentKernel (branch : Bool) :
          IsMarkovKernel (splitExperimentKernel branch) := by
        dsimp [splitExperimentKernel]
        constructor
        intro p
        rw [Kernel.comp_apply,
          Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel_apply]
        infer_instance
      have hrawRareKernel (branch : Bool) : IsMarkovKernel (rawRareKernel branch) := by
        dsimp [rawRareKernel, splitExperimentKernel]
        let _ := hsplitExperimentKernel branch
        infer_instance
      let rawRarePredictive (branch : Bool) :=
        Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive nu
          (rawRareKernel branch)
      have hrawRarePredictive (branch : Bool) :
          IsProbabilityMeasure (rawRarePredictive branch) := by
        dsimp [rawRarePredictive]
        let _ := hnu
        exact Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
          nu (rawRareKernel branch) (fun _ => by
            let _ := hrawRareKernel branch
            infer_instance)
      let rareProductKernel (branch : Bool) : Kernel (Fin k → Real)
          (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) :=
        { toFun := fun w => Measure.pi fun i => rawRareKernel branch (q w i)
          measurable' := measurable_comp_of_finite_range hq_measurable hq_finite
            (fun w => Measure.pi fun i => rawRareKernel branch (w i)) }
      have hrareProductKernel (branch : Bool) :
          IsMarkovKernel (rareProductKernel branch) := by
        constructor
        intro w
        change IsProbabilityMeasure (Measure.pi fun i => rawRareKernel branch (q w i))
        let _ := hrawRareKernel branch
        infer_instance
      have hrareProductKernel_apply (branch : Bool) (w : Fin k → Real) :
          rareProductKernel branch w =
            Measure.pi fun i => rawRareKernel branch (q w i) := rfl
      have hrareProductMixture (branch : Bool) :
          Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive generator
              (rareProductKernel branch) =
            Measure.pi fun _ : Fin k => rawRarePredictive branch := by
        let _ := hgenerator
        let _ := hrawRarePredictive branch
        symm
        refine Measure.pi_eq (μ := fun _ : Fin k => rawRarePredictive branch)
          fun s hs => ?_
        rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
          (MeasurableSet.pi Set.countable_univ fun i _ => hs i)]
        simp_rw [hrareProductKernel_apply, Measure.pi_pi]
        have hcoord_le (i : Fin k) (p : Real) :
            rawRareKernel branch p (s i) ≤ 1 := by
          let _ : IsProbabilityMeasure (rawRareKernel branch p) := by
            let _ := hrawRareKernel branch
            infer_instance
          exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
        have hfun_meas (i : Fin k) :
            Measurable fun p => rawRareKernel branch p (s i) :=
          (rawRareKernel branch).measurable_coe (hs i)
        have hfun_top (i : Fin k) (p : Real) :
            rawRareKernel branch p (s i) < ⊤ := by
          let _ : IsProbabilityMeasure (rawRareKernel branch p) := by
            let _ := hrawRareKernel branch
            infer_instance
          exact measure_lt_top _ _
        have hprod_meas : Measurable (fun w : Fin k → Real =>
            ∏ i, rawRareKernel branch (q w i) (s i)) := by
          exact Finset.univ.measurable_prod fun i _ =>
            (hfun_meas i).comp ((measurable_pi_apply i).comp hq_measurable)
        have hprod_top : ∀ w : Fin k → Real,
            (∏ i, rawRareKernel branch (q w i) (s i)) < ⊤ := fun w =>
          ENNReal.prod_lt_top fun i _ => hfun_top i (q w i)
        have hlhs_ne :
            (∫⁻ w, ∏ i, rawRareKernel branch (q w i) (s i) ∂generator) ≠ ⊤ := by
          apply ne_of_lt
          refine (lintegral_le_const (c := 1) ?_).trans_lt ENNReal.one_lt_top
          exact Filter.Eventually.of_forall fun w =>
            Finset.prod_le_one' fun i _ => hcoord_le i (q w i)
        have hrhs_ne : (∏ i, rawRarePredictive branch (s i)) ≠ ⊤ :=
          (ENNReal.prod_lt_top fun i _ => measure_lt_top _ _).ne
        have hfactor :
            (∫ w, ∏ i, (rawRareKernel branch (q w i) (s i)).toReal ∂generator) =
              ∏ i, ∫ p, (rawRareKernel branch p (s i)).toReal ∂nu := by
          calc
            _ = ∫ w, ∏ i, (rawRareKernel branch (w i) (s i)).toReal
                ∂generator := by
              apply integral_congr_ae
              filter_upwards [hq_eq] with w hw
              rw [hw]
            _ = _ := by
              dsimp [generator]
              exact integral_fintype_prod_eq_prod
                (fun i p => (rawRareKernel branch p (s i)).toReal)
        have hcoord_int (i : Fin k) :
            (∫ p, (rawRareKernel branch p (s i)).toReal ∂nu) =
              (rawRarePredictive branch (s i)).toReal := by
          dsimp [rawRarePredictive]
          rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _ (hs i)]
          exact integral_toReal (hfun_meas i).aemeasurable
            (Filter.Eventually.of_forall (hfun_top i))
        apply (ENNReal.toReal_eq_toReal_iff' hlhs_ne hrhs_ne).mp
        rw [← integral_toReal hprod_meas.aemeasurable
          (Filter.Eventually.of_forall hprod_top)]
        simp_rw [ENNReal.toReal_prod]
        rw [hfactor]
        exact Finset.prod_congr rfl fun i _ => hcoord_int i
      let reservoirLaw : Measure (Bool → (Nat × Nat) × Nat) :=
        Measure.pi fun _arm : Bool =>
          ((poissonMeasure (Real.toNNReal 0)).prod
            (poissonMeasure (Real.toNNReal (u * reservoirMass / 2)))).prod
            (poissonMeasure (Real.toNNReal (v * reservoirMass / 2)))
      have hreservoirLaw : IsProbabilityMeasure reservoirLaw := by
        dsimp [reservoirLaw]
        infer_instance
      let appendReservoir : Kernel
          (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat))))
          ((Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
            (Bool → (Nat × Nat) × Nat)) :=
        (Kernel.id : Kernel
          (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat))))
          (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat))))) ×ₖ
          Kernel.const _ reservoirLaw
      let assemble :
          ((Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
            (Bool → (Nat × Nat) × Nat)) → RawPoissonCounts d := fun zr x arm =>
        if hx : x = commonMarginalReservoir hd1 then zr.2 arm
        else if hi : ∃ i, x = commonMarginalRareCell hkd i then
          let i := Classical.choose hi
          rareObservationToCell (zr.1 i) arm
        else ((0, 0), 0)
      let assembleKernel : Kernel
          ((Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
            (Bool → (Nat × Nat) × Nat)) (RawPoissonCounts d) :=
        Kernel.deterministic assemble (measurable_of_countable assemble)
      let rawAssemblyKernel : Kernel
          (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat))))
          (RawPoissonCounts d) := assembleKernel ∘ₖ appendReservoir
      have hrawAssemblyKernel : IsMarkovKernel rawAssemblyKernel := by
        dsimp [rawAssemblyKernel, assembleKernel, appendReservoir]
        let _ := hreservoirLaw
        infer_instance
      have hcoordinateSource (branch : Bool) : IsProbabilityMeasure
          (cert.markedPoissonPredictive eps a u v branch) :=
        cert.markedPoissonPredictive_isProbabilityMeasure
          eps a u v kappa B branch ha_pos hkappa hcertSupport
      have hsplitCoordinate (branch : Bool) :
          markedControlSplitKernel splitQ ∘ₘ
              cert.markedPoissonPredictive eps a u v branch =
            Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive nu
              (splitExperimentKernel branch) := by
        simpa [nu,
          Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.markedPoissonPredictive]
          using kernel_comp_priorPredictive
            (cert.zeroInflatedPrior a)
            (Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel
              eps a u v cert.polarSign cert.measurable_polarSign branch)
            (markedControlSplitKernel splitQ)
      have hpolarZero : cert.polarSign 0 = 0 := by
        classical
        unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.NormalizedFiniteSignedMomentCertificate.polarSign
        apply Finset.sum_eq_zero
        intro i _hi
        rw [if_neg]
        intro hi
        exact hzero_not_node ⟨i, hi.symm⟩
      have hsplitZero : splitExperimentKernel false 0 =
          splitExperimentKernel true 0 := by
        have hmarkedZero :
            Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel
                eps a u v cert.polarSign cert.measurable_polarSign false 0 =
              Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel
                eps a u v cert.polarSign cert.measurable_polarSign true 0 := by
          rw [Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel_apply,
            Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonKernel_apply]
          unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonLaw
          simp [Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.branchMark,
            hpolarZero]
        dsimp [splitExperimentKernel]
        rw [Kernel.comp_apply, Kernel.comp_apply, hmarkedZero]
      have hrareTV : Causalean.Stat.tvDist
          (rawRarePredictive false) (rawRarePredictive true) ≤
            C0 * u * a * rho ^ L := by
        have heq : Causalean.Stat.tvDist
            (rawRarePredictive false) (rawRarePredictive true) =
              Causalean.Stat.tvDist
                (markedControlSplitKernel splitQ ∘ₘ
                  cert.markedPoissonPredictive eps a u v false)
                (markedControlSplitKernel splitQ ∘ₘ
                  cert.markedPoissonPredictive eps a u v true) := by
          rw [hsplitCoordinate false, hsplitCoordinate true]
          apply tvDist_priorPredictive_eq_of_fiber_sub_eq nu
            (rawRareKernel false) (rawRareKernel true)
            (splitExperimentKernel false) (splitExperimentKernel true)
            (fun _ => by let _ := hrawRareKernel false; infer_instance)
            (fun _ => by let _ := hrawRareKernel true; infer_instance)
            (fun _ => by let _ := hsplitExperimentKernel false; infer_instance)
            (fun _ => by let _ := hsplitExperimentKernel true; infer_instance)
          intro p A hA
          by_cases hp : p = 0
          · subst p
            simp only [rawRareKernel, Kernel.piecewise_apply, Set.mem_singleton_iff]
            rw [hsplitZero]
            rw [sub_self, sub_self]
          · simp only [rawRareKernel, Kernel.piecewise_apply, Set.mem_singleton_iff,
              if_neg hp]
        rw [heq]
        calc
          _ ≤ Causalean.Stat.tvDist
                (cert.markedPoissonPredictive eps a u v false)
                (cert.markedPoissonPredictive eps a u v true) := by
            let _ := hcoordinateSource false
            let _ := hcoordinateSource true
            exact tvDist_bind_le _ _ (markedControlSplitKernel splitQ)
          _ ≤ C0 * u * a * rho ^ L := hone
      have hrawProduct : Causalean.Stat.tvDist
          (Measure.pi fun _ : Fin k => rawRarePredictive false)
          (Measure.pi fun _ : Fin k => rawRarePredictive true) ≤
            C0 * u * k * a * rho ^ L := by
        let _ := hrawRarePredictive false
        let _ := hrawRarePredictive true
        calc
          _ ≤ k * (C0 * u * a * rho ^ L) :=
            tvDist_pi_iid_le_bound k (rawRarePredictive false)
              (rawRarePredictive true) (C0 * u * a * rho ^ L) hrareTV
          _ = C0 * u * k * a * rho ^ L := hscale
      have hrawFiber (branch : Bool) (w : Fin k → Real) :
          (experimentKernel ∘ₖ
              Kernel.deterministic (lawOf branch) (hlawOf_measurable branch)) w =
            (rawAssemblyKernel ∘ₖ rareProductKernel branch) w := by
        -- Remaining pointwise finite-cell partition/reindex identity.
        rw [Kernel.comp_apply, Kernel.deterministic_apply,
          Measure.dirac_bind (experimentKernel.measurable)]
        rw [Kernel.comp_apply]
        dsimp [rawAssemblyKernel]
        rw [← Measure.comp_assoc]
        dsimp [assembleKernel]
        rw [Measure.deterministic_comp_eq_map]
        dsimp [appendReservoir]
        rw [← Measure.compProd_eq_comp_prod, Measure.compProd_const]
        dsimp [experimentKernel, rareProductKernel]
        let zeroCell : Bool → (Nat × Nat) × Nat := fun _ => ((0, 0), 0)
        let rareCellLaw (i : Fin k) : Measure (Bool → (Nat × Nat) × Nat) :=
          (rawRareKernel branch (q w i)).map rareObservationToCell
        have hrareCellLaw (i : Fin k) : IsProbabilityMeasure (rareCellLaw i) := by
          dsimp [rareCellLaw]
          let _ : IsProbabilityMeasure (rawRareKernel branch (q w i)) := by
            let _ := hrawRareKernel branch
            infer_instance
          exact Measure.isProbabilityMeasure_map
            (measurable_of_countable rareObservationToCell).aemeasurable
        let paddedLaw : Measure (RawPoissonCounts d) :=
          Measure.pi (finitePaddedMeasure (commonMarginalRareCell hkd)
            (commonMarginalReservoir hd1) rareCellLaw reservoirLaw zeroCell)
        have hpiMap :
            (Measure.pi fun i => rawRareKernel branch (q w i)).map
                (fun z i => rareObservationToCell (z i)) =
              Measure.pi rareCellLaw := by
          dsimp [rareCellLaw]
          exact Measure.pi_map_pi fun _ => (measurable_of_countable _).aemeasurable
        have hassembly :
            Measure.map assemble
                ((Measure.pi fun i => rawRareKernel branch (q w i)).prod reservoirLaw) =
              paddedLaw := by
          let pad :
              ((Fin k → Bool → (Nat × Nat) × Nat) ×
                (Bool → (Nat × Nat) × Nat)) → RawPoissonCounts d :=
            finitePadding (commonMarginalRareCell hkd)
              (commonMarginalReservoir hd1) zeroCell
          have hpad := pi_prod_map_finitePadding
            (commonMarginalRareCell hkd) (commonMarginalReservoir hd1)
            (commonMarginalRareCell_injective hkd)
            (commonMarginalReservoir_ne_rareCell hd1 hkd)
            rareCellLaw reservoirLaw zeroCell
          change Measure.map assemble
              ((Measure.pi fun i => rawRareKernel branch (q w i)).prod reservoirLaw) = _
          calc
            _ = Measure.map pad
                (((Measure.pi fun i => rawRareKernel branch (q w i)).map
                    (fun z i => rareObservationToCell (z i))).prod reservoirLaw) := by
              have hprod := Measure.map_prod_map
                (Measure.pi fun i => rawRareKernel branch (q w i)) reservoirLaw
                (by fun_prop : Measurable fun z i => rareObservationToCell (z i))
                measurable_id
              have hprod' :
                  ((Measure.pi fun i => rawRareKernel branch (q w i)).map
                      (fun z i => rareObservationToCell (z i))).prod reservoirLaw =
                    Measure.map
                      (Prod.map (fun z i => rareObservationToCell (z i)) id)
                      ((Measure.pi fun i => rawRareKernel branch (q w i)).prod
                        reservoirLaw) := by
                simpa only [Measure.map_id] using hprod
              rw [hprod']
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              apply congrArg (fun f => Measure.map f
                ((Measure.pi fun i => rawRareKernel branch (q w i)).prod reservoirLaw))
              funext zr x arm
              dsimp [assemble, pad, finitePadding, zeroCell]
              split <;> try split <;> rfl
              all_goals rfl
            _ = Measure.map pad ((Measure.pi rareCellLaw).prod reservoirLaw) := by
              rw [hpiMap]
            _ = paddedLaw := by
              dsimp [paddedLaw]
              exact hpad
        rw [hassembly]
        have hscaleLaw : rawScale (lawOf branch w) = rawTotalMass w := by
          dsimp [rawScale, lawOf]
          rw [finiteControlZeroLaw_cellMass]
          dsimp [cellProbability, rawMass]
          rw [commonMarginalRawMass_reservoir]
          field_simp [ne_of_gt hreservoirMass_pos, ne_of_gt (hrawTotalMass_pos w)]
        unfold rawPoissonLaw
        apply congrArg Measure.pi
        funext x
        dsimp [paddedLaw, finitePaddedMeasure]
        by_cases hx : x = commonMarginalReservoir hd1
        · simp only [hx, if_pos]
          subst x
          dsimp [reservoirLaw]
          apply congrArg Measure.pi
          funext arm
          cases arm
          · dsimp [lawOf, markedMass]
            rw [hscaleLaw, finiteControlZeroLaw_jointMass]
            simp only [finiteControlZeroLaw_armMass_false]
            simp only [finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
            dsimp [cellProbability, rawMass, propensityField, outcomeMeanField]
            rw [commonMarginalRawMass_reservoir,
              commonMarginalPropensity_reservoir]
            congr 1 <;>
              field_simp [ne_of_gt (hrawTotalMass_pos w)] <;> ring
          · dsimp [lawOf, markedMass]
            rw [hscaleLaw, finiteControlZeroLaw_jointMass]
            simp only [finiteControlZeroLaw_armMass]
            simp only [finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
            dsimp [cellProbability, rawMass, propensityField, outcomeMeanField]
            rw [commonMarginalRawMass_reservoir,
              commonMarginalPropensity_reservoir,
              commonMarginalOutcomeMean_reservoir]
            congr 1 <;>
              field_simp [ne_of_gt (hrawTotalMass_pos w)] <;> ring
        · simp only [hx, if_false]
          by_cases hi : ∃ i, x = commonMarginalRareCell hkd i
          · simp only [hi, dite_true]
            let i : Fin k := Classical.choose hi
            have hxi : x = commonMarginalRareCell hkd i := Classical.choose_spec hi
            change _ = rareCellLaw i
            rw [hxi]
            by_cases hp : q w i = 0
            · dsimp [rareCellLaw]
              rw [show rawRareKernel branch (q w i) =
                  Kernel.const Real (Measure.dirac zeroRare) (q w i) by
                dsimp [rawRareKernel]
                rw [Kernel.piecewise_apply]
                simp [hp]]
              simp only [Kernel.const_apply, Measure.map_dirac]
              have hzeroImage : rareObservationToCell zeroRare = zeroCell := by
                funext arm
                cases arm <;> rfl
              rw [hzeroImage]
              rw [← rawCellZeroLaw]
              apply congrArg Measure.pi
              funext arm
              dsimp [lawOf, markedMass]
              rw [hscaleLaw, finiteControlZeroLaw_jointMass]
              cases arm <;>
                simp only [finiteControlZeroLaw_armMass,
                  finiteControlZeroLaw_armMass_false,
                  finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true] <;>
                dsimp [cellProbability, rawMass] <;>
                rw [commonMarginalRawMass_rare, hp] <;>
                simp
            · have hp_pos : 0 < q w i :=
                lt_of_le_of_ne (hq_nonneg w i) (Ne.symm hp)
              have hprop_le := (hoverlapField w (commonMarginalRareCell hkd i)).2
              dsimp [propensityField] at hprop_le
              rw [commonMarginalPropensity_rare hd1 hkd eps a (q w) i hp] at hprop_le
              have htreat_le : treatedMass eps a (q w i) ≤ q w i := by
                unfold treatedMass
                have := (div_le_iff₀ hp_pos).mp hprop_le
                nlinarith [heps]
              have hcontrol : 0 ≤ controlMass eps a (q w i) := by
                unfold controlMass
                linarith
              have hk := markedControlSplitKernel_comp_markedPoissonLaw
                eps a u v cert.polarSign branch (q w i) hu hv hcontrol huv
              have hk' : rawRareKernel branch (q w i) =
                  ((poissonMeasure (Real.toNNReal
                    (u * treatedMass eps a (q w i) *
                      (1 + branchMark branch (cert.polarSign (q w i))) / 2))).prod
                    (poissonMeasure (Real.toNNReal
                      (u * treatedMass eps a (q w i) *
                        (1 - branchMark branch (cert.polarSign (q w i))) / 2)))).prod
                    ((poissonMeasure (Real.toNNReal
                      (v * treatedMass eps a (q w i)))).prod
                      ((poissonMeasure (Real.toNNReal
                        (u * controlMass eps a (q w i)))).prod
                        (poissonMeasure (Real.toNNReal
                          (v * controlMass eps a (q w i)))))) := by
                dsimp [rawRareKernel]
                rw [Kernel.piecewise_apply]
                rw [if_neg (by simpa using hp)]
                dsimp [splitExperimentKernel]
                rw [Kernel.comp_apply, markedPoissonKernel_apply]
                exact hk
              dsimp [rareCellLaw]
              rw [hk', fiveProduct_map_rareObservationToCell]
              apply congrArg Measure.pi
              funext arm
              cases arm
              · dsimp [lawOf, markedMass]
                rw [hscaleLaw, finiteControlZeroLaw_jointMass]
                simp only [finiteControlZeroLaw_armMass_false,
                  finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
                dsimp [cellProbability, rawMass, propensityField, outcomeMeanField]
                rw [commonMarginalRawMass_rare,
                  commonMarginalPropensity_rare hd1 hkd eps a (q w) i hp]
                simp only [mul_zero, Real.toNNReal_zero, poissonMeasure_zero]
                congr 1 <;>
                  field_simp [ne_of_gt (hrawTotalMass_pos w), hp] <;>
                  simp [controlMass, treatedMass] <;> ring
              · dsimp [lawOf, markedMass]
                rw [hscaleLaw, finiteControlZeroLaw_jointMass]
                simp only [finiteControlZeroLaw_armMass,
                  finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
                dsimp [cellProbability, rawMass, propensityField, outcomeMeanField]
                rw [commonMarginalRawMass_rare,
                  commonMarginalPropensity_rare hd1 hkd eps a (q w) i hp,
                  commonMarginalOutcomeMean_rare hd1 hkd outcomeSign branch (q w) i hp]
                rw [houtcomeSign_eq]
                congr 1 <;>
                  field_simp [ne_of_gt (hrawTotalMass_pos w), hp] <;>
                  cases branch <;>
                  simp [controlMass, treatedMass, branchMark] <;> ring
          · simp only [hi, dite_false]
            rw [← rawCellZeroLaw]
            apply congrArg Measure.pi
            funext arm
            dsimp [lawOf, markedMass]
            rw [hscaleLaw, finiteControlZeroLaw_jointMass]
            cases arm <;>
              simp only [finiteControlZeroLaw_armMass,
                finiteControlZeroLaw_armMass_false,
                finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true] <;>
              dsimp [cellProbability, rawMass] <;>
              rw [commonMarginalRawMass_unused hd1 hkd reservoirMass (q w) x hx
                (fun i hxi => hi ⟨i, hxi⟩)] <;>
              simp
      have hrawExperimentBranch (branch : Bool) :
          Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
              (generator.map (lawOf branch)) experimentKernel =
            rawAssemblyKernel ∘ₘ
              (Measure.pi fun _ : Fin k => rawRarePredictive branch) := by
        unfold Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        rw [← Measure.deterministic_comp_eq_map (μ := generator)
          (hlawOf_measurable branch), Measure.comp_assoc]
        calc
          (experimentKernel ∘ₖ
              Kernel.deterministic (lawOf branch) (hlawOf_measurable branch)) ∘ₘ
                generator =
              (rawAssemblyKernel ∘ₖ rareProductKernel branch) ∘ₘ generator :=
            Measure.comp_congr (Filter.Eventually.of_forall (hrawFiber branch))
          _ = rawAssemblyKernel ∘ₘ (rareProductKernel branch ∘ₘ generator) :=
            Measure.comp_assoc.symm
          _ = rawAssemblyKernel ∘ₘ
              (Measure.pi fun _ : Fin k => rawRarePredictive branch) := by
            change rawAssemblyKernel ∘ₘ
                Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive generator
                  (rareProductKernel branch) = _
            rw [hrareProductMixture branch]
      have hraw_le :
          Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤
            Causalean.Stat.tvDist
              (Measure.pi fun _ : Fin k => rawRarePredictive false)
              (Measure.pi fun _ : Fin k => rawRarePredictive true) := by
        have hexperiment :
            R.rawExperiment0 = rawAssemblyKernel ∘ₘ
                (Measure.pi fun _ : Fin k => rawRarePredictive false) ∧
              R.rawExperiment1 = rawAssemblyKernel ∘ₘ
                (Measure.pi fun _ : Fin k => rawRarePredictive true) := by
          constructor
          · exact hrawExperimentBranch false
          · exact hrawExperimentBranch true
        rw [hexperiment.1, hexperiment.2]
        let _ : IsProbabilityMeasure
            (Measure.pi fun _ : Fin k => rawRarePredictive false) := by infer_instance
        let _ : IsProbabilityMeasure
            (Measure.pi fun _ : Fin k => rawRarePredictive true) := by infer_instance
        let _ := hrawAssemblyKernel
        exact tvDist_bind_le _ _ rawAssemblyKernel
      calc
        Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤
            Causalean.Stat.tvDist
              (Measure.pi fun _ : Fin k => rawRarePredictive false)
              (Measure.pi fun _ : Fin k => rawRarePredictive true) := hraw_le
        _ ≤ C0 * u * k * a * rho ^ L := hrawProduct
        _ ≤ C * u * k * a * rho ^ L := by
          have hnonneg : 0 ≤ u * (k : Real) * a * rho ^ L :=
            mul_nonneg
              (mul_nonneg (mul_nonneg hu (Nat.cast_nonneg k)) ha_pos.le)
              (pow_nonneg hrho.1.le L)
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hC0_le hnonneg
    exact ⟨hcenterSeparation, hmassVariance,
      max_le (htargetVariance false) (htargetVariance true), htvTransport⟩
  exact {
    finiteAtomConstruction := trivial
    class0 := R.priorModel0
    class1 := R.priorModel1
    sameTable := hsameTable
    separation := hquantitative.1
    massMean := hmassMean
    mass_memLp_two := hmassMemLp
    target_memLp_two := htargetMemLp
    massVariance := hquantitative.2.1
    targetVariance := hquantitative.2.2.1
    mixtureTV := hquantitative.2.2.2 }

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
