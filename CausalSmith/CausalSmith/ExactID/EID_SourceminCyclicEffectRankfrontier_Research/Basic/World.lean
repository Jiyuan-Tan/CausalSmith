import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Causalean.Stat.Nonparametric.MomentProblems.Cumulant

/-!
# Source-minimal cyclic effect frontiers: observational world

This module fixes the finite-dimensional overcomplete ICA world and its population assumptions.
The graphical Causalean substrate is intentionally bypassed: the paper studies cyclic matrix
completions sharing an observational law, rather than DAG-indexed kernels sharing a SWIG.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

abbrev Vec (p : ℕ) := Fin p → ℝ
abbrev MixingMatrix (p n : ℕ) := Matrix (Fin p) (Fin n) ℝ

noncomputable def finiteEuclideanNorm {ι : Type*} [Fintype ι] (z : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (z i) ^ 2)

noncomputable def euclideanNorm {p : ℕ} (z : Vec p) : ℝ := finiteEuclideanNorm z

def dot {p : ℕ} (z w : Vec p) : ℝ := ∑ i, z i * w i

/-- Nonzero vectors are represented projectively by their complete nonzero-scaling orbit. -/
def projectiveClass {p : ℕ} (z : Vec p) : Set (Vec p) :=
  {w | ∃ t : ℝ, t ≠ 0 ∧ w = t • z}

/-- The observed linear mixture `X = C ε`. -/
noncomputable def observedVector {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) : Ω → Vec p :=
  fun ω i => ∑ j, C i j * ε j ω
  -- @realizes X(X = C epsilon)

/-- The observational law `P_X = Law(C ε)`. -/
noncomputable def observedLaw {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) : Measure (Vec p) :=
  μ.map (observedVector C ε)
  -- @realizes PX(PX = Law(C epsilon))

/-- The source cumulant vector at order `r`. -/
noncomputable def sourceCumulants {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ε : Fin n → Ω → ℝ) (r : ℕ) : Fin n → ℝ :=
  fun j => Causalean.Stat.MomentProblems.sourceCumulant μ (ε j) r
  -- @realizes lambda(lambda_j = cum_r(epsilon_j))

/-- Symmetric-array realization of the order-`r` observational cumulant tensor. -/
noncomputable def cumulantTensor {p n r : ℕ} (C : MixingMatrix p n)
    (lam : Fin n → ℝ) : (Fin r → Fin p) → ℝ :=
  fun I => ∑ j, lam j * ∏ k, C (I k) j
  -- @realizes Tr(Tr = sum_j lambda_j c_j tensor-power r)

/-- The degree-`d` lifted direction matrix. -/
noncomputable def liftedDirections {p n d : ℕ} (C : MixingMatrix p n) :
    Matrix (Fin d → Fin p) (Fin n) ℝ :=
  fun I j => ∏ k, C (I k) j
  -- @realizes Vd(Vd columns are c_j tensor-power d)

-- @env: S1
variable {Ω : Type*} [MeasurableSpace Ω] {p n d q r : ℕ}
  (μ : Measure Ω)
  (C : MixingMatrix p n) -- @realizes C(carrier real p by n matrix)
  (ε : Fin n → Ω → ℝ) -- @realizes epsilon(carrier n real random variables)
  (u v : Vec p) -- @realizes u(unit probe; range constrained in theorem/class)
                  -- @realizes v(unit probe; range constrained in theorem/class)

/-- The observed/source/latent index sets. -/
def observedIndices (p : ℕ) : Finset (Fin p) := Finset.univ
  -- @realizes Obs(Obs = all Fin p observed indices)

def sourceIndices (n : ℕ) : Finset (Fin n) := Finset.univ
  -- @realizes Src(Src = all Fin n source indices)

def latentIndices (p n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => p ≤ i.1)
  -- @realizes Lat(Lat = source indices p through n-1)

/-- Population dimensions and tensor orders have the ranges stated in the paper. -/
def ValidPopulationDimensions (p n : ℕ) : Prop := 2 ≤ p ∧ p ≤ n
  -- @realizes p(p >= 2)
  -- @realizes n(n >= p)

def ValidTensorOrders (d q r : ℕ) : Prop := 1 ≤ d ∧ 1 ≤ q ∧ r = 2 * d + q
  -- @realizes d(d >= 1)
  -- @realizes q(q >= 1)
  -- @realizes r(r = 2d + q; hence r >= 3)

-- @node: ass:full-row-rank
def FullRowRank (C : MixingMatrix p n) : Prop := C.rank = p

-- @node: ass:nonzero-columns
def NonzeroColumns (C : MixingMatrix p n) : Prop := ∀ j, C.col j ≠ 0

-- @node: ass:distinct-directions
def DistinctDirections (C : MixingMatrix p n) : Prop :=
  ∀ j k, j ≠ k → ∀ t : ℝ, C.col j ≠ t • C.col k

-- @node: ass:unit-normalization
def UnitNormalizedColumns (C : MixingMatrix p n) : Prop := ∀ j, euclideanNorm (C.col j) = 1

-- @node: ass:independent-sources
export ProbabilityTheory (iIndepFun)

-- @node: ass:nondegenerate-sources
def NondegenerateSources (μ : Measure Ω) (ε : Fin n → Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ j, AEMeasurable (ε j) μ) ∧
    ∀ j, 0 < ProbabilityTheory.variance (ε j) μ

-- @node: ass:nongaussian-sources
def NonGaussianSources (μ : Measure Ω) (ε : Fin n → Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ j, AEMeasurable (ε j) μ) ∧
    ∀ j, ¬ Causalean.Stat.MomentProblems.IsGaussianLaw (μ.map (ε j))

-- @node: ass:moment-determinate-sources
def AllFiniteSourceMoments (μ : Measure Ω) (ε : Fin n → Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ j, AEMeasurable (ε j) μ) ∧
    ∀ j k, 1 ≤ k → Integrable (fun ω => |ε j ω| ^ k) μ

/-- Qualitative nondegeneracy used by ICA uniqueness, without a finite-variance restriction. -/
def QualitativelyNondegenerateSources (μ : Measure Ω) (ε : Fin n → Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ j, AEMeasurable (ε j) μ) ∧
    ∀ j, ¬ ∃ c : ℝ, μ.map (ε j) = Measure.dirac c

/-- Irreducible ICA representations used in the law-level projective union. -/
def IsIrreducibleICARepresentation {p m : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) (A : MixingMatrix p m) (ξ : Fin m → Ξ → ℝ)
    (P : Measure (Vec p)) : Prop :=
  p ≤ m ∧ IsProbabilityMeasure ν ∧ (∀ j, AEMeasurable (ξ j) ν) ∧
    NonzeroColumns A ∧ DistinctDirections A ∧
    ProbabilityTheory.iIndepFun ξ ν ∧ QualitativelyNondegenerateSources ν ξ ∧
    NonGaussianSources ν ξ ∧
    ν.map (observedVector A ξ) = P

universe uDirections

/-- The union of the projective column sets of every irreducible all-non-Gaussian ICA
representation of the observational law. No uniqueness or evaluation procedure is built in. -/
-- @node: def:law-projective-direction-functional
def projectiveDirections (P : Measure (Vec p)) : Set (Set (Vec p)) :=
  {D | ∃ (m : ℕ) (Ξ : Type uDirections) (_ : MeasurableSpace Ξ) (ν : Measure Ξ)
      (A : MixingMatrix p m) (ξ : Fin m → Ξ → ℝ),
      p ≤ m ∧ IsProbabilityMeasure ν ∧ (∀ j, AEMeasurable (ξ j) ν) ∧
      IsIrreducibleICARepresentation ν A ξ P ∧
      ∃ j, D = projectiveClass (A.col j)}
  -- @realizes Dlaw(D(PX) is the union over all irreducible ICA directions)

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
