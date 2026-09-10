import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Frontier
import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Separated common-order ICA class

Quantitative margins, the tensor-factor inverse relation, and the six explicit local constants.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Euclidean least singular value on the domain; used when the columns are required independent. -/
noncomputable def euclideanLeastColumnSingularValue {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq b] (A : Matrix a b ℝ) : ℝ :=
  Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue A

/-- Euclidean least nonzero singular value for a full-row-rank rectangular matrix, expressed via
the transpose on the row space. -/
noncomputable def euclideanLeastRowSingularValue {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] (A : Matrix a b ℝ) : ℝ :=
  sInf {z : ℝ | ∃ v : a → ℝ, finiteEuclideanNorm v = 1 ∧
    z = finiteEuclideanNorm (A.transpose.mulVec v)}

-- @env: S4
variable {Ω : Type*} [MeasurableSpace Ω] {p n r d q N : ℕ}
  (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ)
  (lam : Fin n → ℝ) (u v : Vec p)
  (a delta sigma kappa Lambda M : ℝ)

/-- Parameter ranges of the separated inference world. -/
-- @realizes a(real margin constrained to (0,1])
-- @realizes delta(real margin constrained to (0,1])
-- @realizes sigma(real margin constrained to (0,1])
def ValidInferenceMargins (alpha : ℝ)
    (a : ℝ) -- @realizes a(carrier Real; range constrained below)
    (delta : ℝ) -- @realizes delta(carrier Real; range constrained below)
    (sigma : ℝ) -- @realizes sigma(carrier Real; range constrained below)
    (kappa Lambda M : ℝ) : Prop :=
  (0 < alpha ∧ alpha < 1) ∧ -- @realizes alpha(alpha in (0,1))
  (0 < a ∧ a ≤ 1) ∧ -- @realizes a(a in (0,1])
  (0 < delta ∧ delta ≤ 1) ∧ -- @realizes delta(delta in (0,1])
  (0 < sigma ∧ sigma ≤ 1) ∧ -- @realizes sigma(sigma in (0,1])
  0 < kappa ∧ kappa ≤ Lambda ∧ 1 ≤ M
  -- @realizes kappa(kappa positive)
  -- @realizes Lambda(Lambda >= kappa)
  -- @realizes M(M >= 1)

-- @realizes a(real margin constrained to (0,1])
-- @realizes delta(real margin constrained to (0,1])
-- @realizes sigma(real margin constrained to (0,1])
def ValidSeparatedMargins
    (a : ℝ) -- @realizes a(carrier Real; range constrained below)
    (delta : ℝ) -- @realizes delta(carrier Real; range constrained below)
    (sigma : ℝ) -- @realizes sigma(carrier Real; range constrained below)
    (kappa Lambda M : ℝ) : Prop :=
  (0 < a ∧ a ≤ 1) ∧ -- @realizes a(a in (0,1])
  (0 < delta ∧ delta ≤ 1) ∧ -- @realizes delta(delta in (0,1])
  (0 < sigma ∧ sigma ≤ 1) ∧ -- @realizes sigma(sigma in (0,1])
  0 < kappa ∧ kappa ≤ Lambda ∧ 1 ≤ M

-- @node: ass:cumulant-magnitude-margin
def CumulantMagnitudeMargin (lam : Fin n → ℝ) (kappa Lambda : ℝ) : Prop :=
  ∀ j, kappa ≤ |lam j| ∧ |lam j| ≤ Lambda

-- @node: ass:probe-orientation-margin
def ProbeOrientationMargin (C : MixingMatrix p n) (u : Vec p) (sigma : ℝ) : Prop :=
  ∀ j, sigma ≤ dot u (C.col j)

-- @node: ass:lifted-rank-margin
def LiftedRankMargin (C : MixingMatrix p n) (d : ℕ) (sigma : ℝ) : Prop :=
  sigma ≤ euclideanLeastColumnSingularValue (liftedDirections (d := d) C)

-- @node: ass:pencil-gap
def PencilGap (C : MixingMatrix p n) (u v : Vec p) (sigma : ℝ) : Prop :=
  ∀ j k, j ≠ k → sigma ≤
    |(dot v (C.col j) / dot u (C.col j)) -
      (dot v (C.col k) / dot u (C.col k))|

-- @node: ass:source-moment-envelope
def SourceMomentEnvelope (μ : Measure Ω) (ε : Fin n → Ω → ℝ) (r : ℕ) (M : ℝ) : Prop :=
  ∀ j, Integrable (fun ω => |ε j ω| ^ (2 * r)) μ ∧
    (∫ ω, |ε j ω| ^ (2 * r) ∂μ) ≤ M

-- @node: ass:mixing-singular-margin
def MixingSingularMargin (C : MixingMatrix p n) (delta : ℝ) : Prop :=
  delta ≤ euclideanLeastRowSingularValue C

-- @node: ass:loading-selection-margin
def LoadingSelectionMargin (C : MixingMatrix p n) (a : ℝ) : Prop :=
  ∀ i j, C i j = 0 ∨ a ≤ |C i j|

-- @node: ass:deletion-rank-margin
def DeletionRankMargin (C : MixingMatrix p n) (delta : ℝ) : Prop :=
  ∀ i j, euclideanLeastRowSingularValue (deleteRowCol C i j) = 0 ∨
    delta ≤ euclideanLeastRowSingularValue (deleteRowCol C i j)

/-- Membership in the separated common-order representation class. -/
-- @node: def:regular-oica-class
structure SeparatedOICAClass (μ : Measure Ω) (C : MixingMatrix p n)
    (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ) (u v : Vec p)
    (r d q : ℕ) (a delta sigma kappa Lambda M : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  populationDimensions : ValidPopulationDimensions p n
  validMargins : ValidSeparatedMargins a delta sigma kappa Lambda M
  d_pos : 1 ≤ d
  q_pos : 1 ≤ q
  order_eq : r = 2 * d + q
  dimension_bound : n ≤ Nat.choose (p + d - 1) d
  lambda_eq : lam = sourceCumulants μ ε r -- @realizes zeta(tuple PX,C,epsilon,lambda)
  probe_u_unit : euclideanNorm u = 1
  probe_v_unit : euclideanNorm v = 1
  fullRowRank : FullRowRank C
  nonzeroColumns : NonzeroColumns C
  distinctDirections : DistinctDirections C
  unitNormalized : UnitNormalizedColumns C
  independent : ProbabilityTheory.iIndepFun ε μ
  nondegenerate : NondegenerateSources μ ε
  nonGaussian : NonGaussianSources μ ε
  cumulantMargin : CumulantMagnitudeMargin lam kappa Lambda
  probeMargin : ProbeOrientationMargin C u sigma
  liftedMargin : LiftedRankMargin C d sigma
  pencilGap : PencilGap C u v sigma
  momentEnvelope : SourceMomentEnvelope μ ε r M
  mixingMargin : MixingSingularMargin C delta
  loadingMargin : LoadingSelectionMargin C a
  deletionMargin : DeletionRankMargin C delta
  -- @realizes Mreg(separated common-order OICA class)

/-- Complete specification witness for the contraction, compression, pencil, spectral-projector,
trace-coordinate, normalization pipeline. -/
structure TensorPencilCertificate {p r : ℕ} (T : (Fin r → Fin p) → ℝ)
    (u v : Vec p) where
  n : ℕ
  d : ℕ
  q : ℕ
  d_pos : 1 ≤ d
  q_pos : 1 ≤ q
  order_eq : r = 2 * d + q
  weights : Fin n → ℝ
  directions : Fin n → Vec p
  tensor_eq : T = cumulantTensor (fun i j => directions j i) weights
  lifted : Matrix (Fin d → Fin p) (Fin n) ℝ
  lifted_eq : lifted = fun I j => ∏ k, directions j (I k)
  contraction : Vec p → Matrix (Fin d → Fin p) (Fin d → Fin p) ℝ
  contraction_eq : ∀ w, contraction w =
    lifted * Matrix.diagonal (fun j =>
      weights j * (dot u (directions j)) ^ (q - 1) * dot w (directions j)) *
      lifted.transpose
  basis : Matrix (Fin d → Fin p) (Fin n) ℝ
  basis_orthonormal : ∀ j k, (∑ i, basis i j * basis i k) = if j = k then 1 else 0
  basis_spans_range : ∀ z : (Fin d → Fin p) → ℝ,
    (∃ w, z = (contraction u).mulVec w) ↔ ∃ coeff, z = basis.mulVec coeff
  compressed : Vec p → SquareMatrix n
  compressed_eq : ∀ w, compressed w = basis.transpose * contraction w * basis
  pencil : Vec p → SquareMatrix n
  pencil_eq : ∀ w, pencil w = compressed w * (compressed u)⁻¹
  projectors : Fin n → SquareMatrix n
  projector_idempotent : ∀ j, projectors j * projectors j = projectors j
  projector_orthogonal : ∀ j k, j ≠ k → projectors j * projectors k = 0
  projector_complete : ∑ j, projectors j = 1
  projector_rank_one : ∀ j, (projectors j).rank = 1
  projector_eigen : ∀ j,
    pencil v * projectors j = (dot v (directions j) / dot u (directions j)) • projectors j
  traceCoordinates : Fin n → Vec p
  trace_eq : ∀ j i, traceCoordinates j i =
    Matrix.trace (pencil (fun k => if k = i then 1 else 0) * projectors j)
  output_eq : ∀ j, directions j =
    (euclideanNorm (traceCoordinates j))⁻¹ • traceCoordinates j
  oriented : ∀ j, 0 < dot u (directions j)

-- @node: def:tensor-pencil-inverse
def tensorPencilInverse {p r : ℕ} (n d q : ℕ) (T : (Fin r → Fin p) → ℝ)
    (u v : Vec p) : Set (Fin n → Vec p) :=
  {D | ∃ cert : TensorPencilCertificate T u v,
    cert.n = n ∧ cert.d = d ∧ cert.q = q ∧ HEq cert.directions D}
  -- @realizes OICAInv(tensor pencil inverse solution set)

/-- The six explicit constants `(eta, chi, h, eps0, Lz, LC)`. -/
-- @node: def:inverse-constants
noncomputable def inverseConstants (p n q : ℕ) (sigma kappa Lambda : ℝ) :
    ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  let eta := kappa * sigma ^ (q + 2) -- @realizes eta(eta = kappa sigma^(q+2))
  let chi := Real.sqrt n / sigma -- @realizes chi(chi = sqrt(n)/sigma)
  let h := 2 / eta + 2 * n * Lambda / eta ^ 2
    -- @realizes hconst(h = 2/eta + 2n Lambda/eta^2)
  let eps0 := min (eta / 2) (sigma / (6 * chi * h))
    -- @realizes eps0(eps0 = min(eta/2,sigma/(6 chi h)))
  let Lz := n * h * (2 * chi + 6 * n * Lambda * chi ^ 2 / (eta * sigma))
    -- @realizes Lz(Lz explicit ratio-coordinate modulus)
  let LC := 2 * Real.sqrt (n * p) * Lz
    -- @realizes LC(LC = 2 sqrt(np) Lz)
  (eta, chi, h, eps0, Lz, LC)

def separatedRepresentations (μ : Measure Ω) (u v : Vec p) (r d q : ℕ)
    (a delta sigma kappa Lambda M : ℝ) :
    Set (MixingMatrix p n × (Fin n → Ω → ℝ) × (Fin n → ℝ)) :=
  {z | SeparatedOICAClass μ z.1 z.2.1 z.2.2 u v r d q
    a delta sigma kappa Lambda M}

-- @node: ass:regular-class-nonempty
def SeparatedClassNonempty (μ : Measure Ω) (u v : Vec p) (r d q : ℕ)
    (a delta sigma kappa Lambda M : ℝ) : Prop :=
  (separatedRepresentations (n := n) μ u v r d q a delta sigma kappa Lambda M).Nonempty

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
