import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.BoundedClass
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Semialgebraic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Certified semialgebraic approximate selectors

The strict approximate-minimizer graph, its ordered-certificate augmentation,
a genuine cylindrical algebraic decomposition, and the first-cell definable
choice selector with its measurability and strict-approximation properties.
-/

open scoped BigOperators

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

variable {d E r : ℕ}

/-- Flattened real coordinates of a covariance tuple. -/
abbrev CovarianceIndex (d E : ℕ) := Environment E × Fin d × Fin d

/-- An unconstrained covariance statistic in ambient real coordinates. -/
abbrev CovarianceStatistic (d E : ℕ) := CovarianceIndex d E → ℝ

/-- Coordinates of a symmetric covariance tuple. -/
def covarianceCoordinates (θ : CovarianceTuple d E) : CovarianceStatistic d E :=
  fun p => θ.cov p.1 p.2.1 p.2.2

/-- Sample-size weighted squared Frobenius distance. -/
def weightedDistanceSq (n : Environment E → ℕ) (x y : CovarianceStatistic d E) : ℝ :=
  ∑ e, (n e : ℝ) * ∑ i, ∑ j, (x (e, i, j) - y (e, i, j)) ^ 2
  -- @realizes n(positive environment-specific sample-size array)

/-- Sample-size weighted Frobenius distance. -/
noncomputable def weightedDistance (n : Environment E → ℕ)
    (x y : CovarianceStatistic d E) : ℝ :=
  Real.sqrt (weightedDistanceSq n x y)
  -- @realizes normw(sample-size weighted Frobenius norm)

/-- Distance from a covariance statistic to the nonclosed bounded class. -/
noncomputable def covarianceClassValue (r : ℕ) (n : Environment E → ℕ) (m M : ℝ)
    (x : CovarianceStatistic d E) : ℝ :=
  sInf {a | ∃ ζ ∈ ThetaK d E r m M, a = weightedDistance n (covarianceCoordinates ζ) x}

/-- Strict approximate-minimizer graph. -/
def approximateMinimizerGraph (r : ℕ) (n : Environment E → ℕ) (m M ε : ℝ) :
    Set (CovarianceStatistic d E × CovarianceTuple d E) :=
  {p | p.2 ∈ ThetaK d E r m M ∧
    weightedDistance n (covarianceCoordinates p.2) p.1 < covarianceClassValue r n m M p.1 + ε}
  -- @realizes Gepsilon(strict epsilon approximate-minimizer correspondence)

/-- The finite ordered-certificate coordinates retained in the CAD. -/
structure OrderedCertificateWitness (d r : ℕ) where
  target : Finset (Fin d)
  ordering : Fin r → Fin d

/-- A point of the witness-augmented approximate-minimizer graph. -/
structure CertifiedGraphPoint (d E r : ℕ) where
  statistic : CovarianceStatistic d E
  covariance : CovarianceTuple d E
  witness : OrderedCertificateWitness d r

/-- The approximate-minimizer graph augmented by the ordered certificate
witness used to certify membership in `ThetaK`. -/
def certifiedApproximateGraph (r : ℕ) (n : Environment E → ℕ) (m M ε : ℝ) :
    Set (CertifiedGraphPoint d E r) :=
  {p | (p.statistic, p.covariance) ∈ approximateMinimizerGraph r n m M ε ∧
    p.witness.target.card = r ∧
    Orders p.witness.ordering p.witness.target ∧
    Cert p.covariance p.witness.target p.witness.ordering}

/-- Real coordinates of the statistic, covariance, target-membership vector,
and ordered target tuple. -/
inductive CertifiedCADCoordinate (d E r : ℕ)
  | statistic (i : CovarianceIndex d E)
  | covariance (i : CovarianceIndex d E)
  | target (j : Fin d)
  | ordering (i : Fin r)
  deriving DecidableEq, Fintype

/-- Flatten a certified graph point, including its ordered-witness data, into
the ambient real coordinates of a CAD cell. -/
def certifiedCADCoordinates (p : CertifiedGraphPoint d E r) :
    CertifiedCADCoordinate d E r → ℝ
  | .statistic i => p.statistic i
  | .covariance i => covarianceCoordinates p.covariance i
  | .target j => if j ∈ p.witness.target then 1 else 0
  | .ordering i => ((p.witness.ordering i : Fin d) : ℕ)

/-- The coordinates preceding `k` in a fixed CAD variable ordering. -/
def cadCoordinatePrefix
    (order : CertifiedCADCoordinate d E r ≃
      Fin (Fintype.card (CertifiedCADCoordinate d E r))) (k : ℕ) :
    Set (CertifiedCADCoordinate d E r) :=
  {a | (order a).1 < k}

/-- Projection of a cell onto an initial segment of the CAD variable order. -/
def cadPrefixProjection
    (order : CertifiedCADCoordinate d E r ≃
      Fin (Fintype.card (CertifiedCADCoordinate d E r))) (k : ℕ)
    (C : Set (CertifiedGraphPoint d E r)) :
    Set (CertifiedCADCoordinate d E r → ℝ) :=
  {z | ∃ p ∈ C, ∀ a ∈ cadCoordinatePrefix order k,
    z a = certifiedCADCoordinates p a}

/-- A fixed cylindrical algebraic decomposition of the entire certified,
witness-augmented graph, together with a definable within-cell choice rule. -/
structure FixedCertifiedCAD (d E r : ℕ) (n : Environment E → ℕ)
    (m M ε : ℝ) where
  cellCount : ℕ
  cells : Fin cellCount → Set (CertifiedGraphPoint d E r)
  cellNonempty : ∀ i, (cells i).Nonempty
  cellSemialgebraic : ∀ i,
    IsSemialgebraicSet (certifiedCADCoordinates '' cells i)
  graphPartition : certifiedApproximateGraph r n m M ε = ⋃ i, cells i
  cellsDisjoint : ∀ i j, i ≠ j → Disjoint (cells i) (cells j)
  coordinateOrder : CertifiedCADCoordinate d E r ≃
    Fin (Fintype.card (CertifiedCADCoordinate d E r))
  cylindrical : ∀ i j
      (k : Fin (Fintype.card (CertifiedCADCoordinate d E r) + 1)),
    cadPrefixProjection coordinateOrder k.1 (cells i) =
        cadPrefixProjection coordinateOrder k.1 (cells j) ∨
      Disjoint (cadPrefixProjection coordinateOrder k.1 (cells i))
        (cadPrefixProjection coordinateOrder k.1 (cells j))
  cellChoice : Fin cellCount → CovarianceStatistic d E → CertifiedGraphPoint d E r
  cellChoiceInFiber : ∀ i x,
    (∃ p ∈ cells i, p.statistic = x) →
      cellChoice i x ∈ cells i ∧ (cellChoice i x).statistic = x
  cellChoiceSemialgebraic : ∀ i,
    IsSemialgebraicMap (fun x => certifiedCADCoordinates (cellChoice i x))
  firstCell : CovarianceStatistic d E → Fin cellCount
  firstCellFiberNonempty : ∀ x, ∃ p ∈ cells (firstCell x), p.statistic = x
  earlierCellsEmptyOver : ∀ x i, i < firstCell x →
    ¬∃ p ∈ cells i, p.statistic = x
  chosenSemialgebraic : IsSemialgebraicMap (fun x =>
    covarianceCoordinates (cellChoice (firstCell x) x).covariance)
  chosenMeasurable : Measurable (fun x =>
    covarianceCoordinates (cellChoice (firstCell x) x).covariance)

/-- The canonical first-nonempty-cell section of a fixed decomposition. -/
def canonicalCADSelector (cad : FixedCertifiedCAD d E r n m M ε) :
    CovarianceStatistic d E → CovarianceTuple d E :=
  fun x => (cad.cellChoice (cad.firstCell x) x).covariance

-- @node: def:certified-approximate-selector
def IsCertifiedSemialgebraicSelector (r : ℕ) (n : Environment E → ℕ) (m M ε : ℝ)
    (cad : FixedCertifiedCAD d E r n m M ε)
    (s : CovarianceStatistic d E → CovarianceTuple d E) : Prop :=
  s = canonicalCADSelector cad ∧
  IsSemialgebraicMap (fun x => covarianceCoordinates (s x)) ∧
  Measurable (fun x => covarianceCoordinates (s x)) ∧
  (∀ x, s x ∈ ThetaK d E r m M) ∧
  (∀ x, ∃ T : Finset (Fin d), T.card = r ∧
    ∃ t : Fin r → Fin d, Orders t T ∧ Cert (s x) T t) ∧
  ∀ x, weightedDistance n (covarianceCoordinates (s x)) x <
    covarianceClassValue r n m M x + ε
  -- @realizes stilde(semialgebraic Borel certified section)
  -- @realizes epsilon(strict positive approximation tolerance)

-- @node: lem:measurable-certified-selection
lemma measurable_certified_selection (d E r : ℕ) (m M : ℝ)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hm : 0 < m) (hM : m < M) (n : Environment E → ℕ)
    (hn : ∀ e, 0 < n e) :
    ∀ ε > 0, ∃ cad : FixedCertifiedCAD d E r n m M ε,
      IsCertifiedSemialgebraicSelector r n m M ε cad (canonicalCADSelector cad) := by
  -- BLOCKER: needs-substrate(semialgebraic cylindrical decomposition with definable choice)
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
