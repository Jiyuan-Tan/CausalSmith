import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.Basic

set_option linter.style.longLine false

/-! # Gaussian covariance-shift models

The ambient multi-environment linear Gaussian model and its legal subclass.
The identification results are developed in the companion files.
-/

open scoped BigOperators
open MeasureTheory Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @env: S1
variable {d E r : ℕ}

/-- The observed dimension is at least two. -/
def AdmissibleDimension (d : ℕ) : Prop := 2 ≤ d
  -- @realizes d(observed dimension in {2,3,…})

/-- There are at least two nonbaseline environments. -/
def AdmissibleEnvironmentCount (E : ℕ) : Prop := 2 ≤ E
  -- @realizes E(nonbaseline environment count in {2,3,…})

/-- The target size is nonzero and strictly below the ambient dimension. -/
def AdmissibleTargetSize (d r : ℕ) : Prop := 1 ≤ r ∧ r < d
  -- @realizes r(target size in {1,…,d-1})

/-- A confidence level lies strictly between zero and one. -/
def AdmissibleProbabilityLevel (α : ℝ) : Prop := 0 < α ∧ α < 1
  -- @realizes alpha(probability level in (0,1))

/-- Real square matrices in observed dimension `d`. -/
abbrev RealMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ -- @realizes Id(carrier ℝ^{d×d}) @realizes Symd(ambient matrix space) @realizes SPDd(ambient matrix space)

/-- Observed labels. -/
abbrev Vertex (d : ℕ) := Fin d -- @realizes V(labels Fin d)

/-- Baseline and nonbaseline environment labels. -/
abbrev Environment (E : ℕ) := Fin (E + 1) -- @realizes Env(labels 0,…,E)

/-- Euclidean vectors represented by coordinates. -/
abbrev RealVector (d : ℕ) := Fin d → ℝ

/-- The joint primitive vector `(H, ε, η)`. -/
abbrev PrimitiveVector (d : ℕ) := Fin 3 → RealVector d

/-- The latent block of a primitive vector. -/
def latentPart (z : PrimitiveVector d) : RealVector d := z 0 -- @realizes He(carrier ℝ^d)

/-- The structural-noise block of a primitive vector. -/
def structuralPart (z : PrimitiveVector d) : RealVector d := z 1 -- @realizes epsilone(carrier ℝ^d)

/-- The measurement-error block of a primitive vector. -/
def measurementPart (z : PrimitiveVector d) : RealVector d := z 2 -- @realizes etae(carrier ℝ^d)

/-- The mean vector of a random vector. -/
noncomputable def meanVector (P : Measure (PrimitiveVector d))
    (X : PrimitiveVector d → RealVector d) : RealVector d :=
  fun i => ∫ z, X z i ∂P

/-- The covariance matrix, with the mean outer product subtracted. -/
noncomputable def covariance (P : Measure (PrimitiveVector d))
    (X : PrimitiveVector d → RealVector d) : RealMatrix d :=
  fun i j => ∫ z, X z i * X z j ∂P - meanVector P X i * meanVector P X j

/-- A raw covariance-shift SCM. Distributional restrictions are imposed by
`LegalCovShiftModel`. -/
structure CovShiftModel (d E r : ℕ) where
  B : RealMatrix d -- @realizes Bmu(carrier ℝ^{d×d})
  C : RealMatrix d -- @realizes Cmu(carrier ℝ^{d×d})
  ΩH : RealMatrix d -- @realizes OmegaH(carrier symmetric PSD matrix)
  ΩH_posSemidef : ΩH.PosSemidef -- @realizes OmegaH(positive-semidefinite range)
  ω0 : RealVector d -- @realizes omega0(carrier ℝ^d)
  Ωη : RealMatrix d -- @realizes Omegaeta(carrier symmetric diagonal matrix)
  Ωη_diagonal : ∀ i j, i ≠ j → Ωη i j = 0 -- @realizes Omegaeta(diagonal range)
  target : Finset (Vertex d) -- @realizes Tmu(subset of V)
  shiftVariance : Environment E → Vertex d → ℝ -- @realizes lambda(carrier environment-by-coordinate array)
  baselineShift : shiftVariance 0 = 0 -- @realizes lambda(lambda_0 = 0)
  primitiveLaw : Environment E → Measure (PrimitiveVector d)
  structuralCovariance : ∀ e,
    covariance (primitiveLaw e) structuralPart = Matrix.diagonal (ω0 + shiftVariance e)
    -- @realizes epsilone(Cov(epsilone)=diag(omega0+lambda_e))

/-- The identity matrix in the observed dimension. -/
def identityMatrix (d : ℕ) : RealMatrix d := 1 -- @realizes Id(identity I_d)

/-- The total-effect matrix `(I-B)⁻¹`. -/
noncomputable def CovShiftModel.totalEffect (M : CovShiftModel d E r) : RealMatrix d :=
  (1 - M.B)⁻¹ -- @realizes Umu(Umu = (Id-Bmu)⁻¹)

/-- The observation generated from one primitive draw. -/
noncomputable def CovShiftModel.observation (M : CovShiftModel d E r)
    (_e : Environment E) (z : PrimitiveVector d) : RealVector d :=
  M.totalEffect *ᵥ (M.C *ᵥ latentPart z + structuralPart z) + measurementPart z
  -- @realizes Ye(Ye = Umu(Cmu He + epsilone) + etae)

/-- The covariance implied by the structural parameters in environment `e`. -/
noncomputable def CovShiftModel.covOf (M : CovShiftModel d E r)
    (e : Environment E) : RealMatrix d :=
  M.totalEffect * (M.C * M.ΩH * M.C.transpose +
      Matrix.diagonal (M.ω0 + M.shiftVariance e)) * M.totalEffect.transpose + M.Ωη
  -- @realizes Sigma(Sigma_e = Cov(Ye))

-- @node: ass:acyclic-observed-system
def AcyclicObservedSystem (M : CovShiftModel d E r) : Prop :=
  ∃ σ : Equiv.Perm (Fin d),
    (M.B.submatrix σ σ).BlockTriangular id ∧
      ∀ i, M.B.submatrix σ σ i i = 0

-- @node: ass:centered-gaussian-noises
def CenteredGaussianNoises (M : CovShiftModel d E r) : Prop :=
  ∀ e, ProbabilityTheory.IsGaussian (M.primitiveLaw e) ∧
    ∀ b j, ∫ z, z b j ∂M.primitiveLaw e = 0

/-- Indices for the latent block, the individual structural coordinates, and
the measurement block. -/
inductive NoiseBlockIndex (d : ℕ)
  | latent
  | structural (j : Fin d)
  | measurement

/-- The value space associated with a noise-block index. -/
def NoiseBlockValue : NoiseBlockIndex d → Type
  | .latent => RealVector d
  | .structural _ => ℝ
  | .measurement => RealVector d

instance noiseBlockMeasurableSpace (i : NoiseBlockIndex d) :
    MeasurableSpace (NoiseBlockValue i) := by
  cases i <;> simp only [NoiseBlockValue] <;> infer_instance

/-- Projection of a primitive vector to a heterogeneous independence block. -/
def primitiveBlock (i : NoiseBlockIndex d) (z : PrimitiveVector d) : NoiseBlockValue i :=
  match i with
  | .latent => latentPart z
  | .structural j => structuralPart z j
  | .measurement => measurementPart z

-- @node: ass:block-independent-noises
def BlockIndependentNoises (M : CovShiftModel d E r) : Prop :=
  ∀ e, ProbabilityTheory.iIndepFun (fun i => primitiveBlock i) (M.primitiveLaw e)

-- @node: ass:stationary-latent-noise
def StationaryLatentNoise (M : CovShiftModel d E r) : Prop :=
  ∀ e, covariance (M.primitiveLaw e) latentPart = M.ΩH
  -- @realizes OmegaH(Cov(He)=OmegaH in every environment)

-- @node: ass:stationary-measurement-error
def StationaryMeasurementError (M : CovShiftModel d E r) : Prop :=
  ∀ e, covariance (M.primitiveLaw e) measurementPart = M.Ωη
  -- @realizes Omegaeta(Cov(etae)=Omegaeta in every environment)

-- @node: ass:positive-structural-noise
def PositiveStructuralNoise (M : CovShiftModel d E r) : Prop :=
  ∀ j, 0 < M.ω0 j -- @realizes omega0(strictly positive coordinates)

-- @node: ass:positive-measurement-noise
def PositiveMeasurementNoise (M : CovShiftModel d E r) : Prop :=
  M.Ωη.PosDef -- @realizes Omegaeta(positive-definite range)

-- @node: ass:target-cardinality
def TargetCardinality (M : CovShiftModel d E r) : Prop :=
  AdmissibleTargetSize d r ∧ M.target.card = r
  -- @realizes r(target cardinality and range 1,…,d-1)

-- @node: ass:no-off-target-shifts
def NoOffTargetShifts (M : CovShiftModel d E r) : Prop :=
  ∀ e j, j ∉ M.target → M.shiftVariance e j = 0

-- @node: ass:nonnegative-variance-shifts
def NonnegativeVarianceShifts (M : CovShiftModel d E r) : Prop :=
  ∀ e j, j ∈ M.target → 0 ≤ M.shiftVariance e j

-- @node: ass:reference-shifts-all-targets
def PanelTargetCoverage (M : CovShiftModel d E r) : Prop :=
  ∀ j ∈ M.target, ∃ e : Fin E, 0 < M.shiftVariance e.succ j

-- @node: def:legal-scm-class
structure LegalCovShiftModel (M : CovShiftModel d E r) : Prop where
  dimension : AdmissibleDimension d -- @realizes d(standing constraint 2 ≤ d)
  environmentCount : AdmissibleEnvironmentCount E -- @realizes E(standing constraint 2 ≤ E)
  acyclic : AcyclicObservedSystem M
  centeredGaussian : CenteredGaussianNoises M
  blockIndependent : BlockIndependentNoises M
  stationaryLatent : StationaryLatentNoise M
  stationaryMeasurement : StationaryMeasurementError M
  positiveStructural : PositiveStructuralNoise M
  positiveMeasurement : PositiveMeasurementNoise M
  targetCardinality : TargetCardinality M
  noOffTarget : NoOffTargetShifts M
  nonnegativeShifts : NonnegativeVarianceShifts M
  panelCoverage : PanelTargetCoverage M
  -- @realizes mu(member of the legal SCM class)
  -- @realizes Mscm(the legal class M_{d,E,r})

end CausalSmith.ExactID.CovshiftProfilequotientTargets
