import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.ExactMultinomial
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Exact real-algebraic specifications and the CAD gate -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

-- @env: S4
variable (m : ℕ) (ε : ℝ)

/-- Atomic rational polynomial relations. -/
inductive RationalPolyAtom where
  | eqZero (p : MvPolynomial ℕ ℚ)
  | leZero (p : MvPolynomial ℕ ℚ)
  | ltZero (p : MvPolynomial ℕ ℚ)

/-- First-order formulas over the reals with rational polynomial atoms. -/
inductive RationalFirstOrderFormula where
  | atom (a : RationalPolyAtom)
  | and (φ ψ : RationalFirstOrderFormula)
  | or (φ ψ : RationalFirstOrderFormula)
  | not (φ : RationalFirstOrderFormula)
  | existsReal (varIndex : ℕ) (φ : RationalFirstOrderFormula)
  | forallReal (varIndex : ℕ) (φ : RationalFirstOrderFormula)

/-- Semantic evaluation of a rational first-order formula. -/
def RationalFirstOrderFormula.Holds (x : ℕ → ℝ) :
    RationalFirstOrderFormula → Prop
  | .atom (.eqZero p) => MvPolynomial.eval₂ (Rat.castHom ℝ) x p = 0
  | .atom (.leZero p) => MvPolynomial.eval₂ (Rat.castHom ℝ) x p ≤ 0
  | .atom (.ltZero p) => MvPolynomial.eval₂ (Rat.castHom ℝ) x p < 0
  | .and φ ψ => φ.Holds x ∧ ψ.Holds x
  | .or φ ψ => φ.Holds x ∨ ψ.Holds x
  | .not φ => ¬ φ.Holds x
  | .existsReal i φ => ∃ r : ℝ, φ.Holds (Function.update x i r)
  | .forallReal i φ => ∀ r : ℝ, φ.Holds (Function.update x i r)

/-- A formula contains no real quantifier. -/
def RationalFirstOrderFormula.QuantifierFree :
    RationalFirstOrderFormula → Prop
  | .atom _ => True
  | .and φ ψ | .or φ ψ => φ.QuantifierFree ∧ ψ.QuantifierFree
  | .not φ => φ.QuantifierFree
  | .existsReal _ _ | .forallReal _ _ => False

/-- A real number given by a rational defining polynomial and a rational
isolating interval containing it as the unique root. -/
def HasRationalAlgebraicDescription (x : ℝ) : Prop :=
  ∃ p : Polynomial ℚ, p ≠ 0 ∧
    ∃ a b : ℚ, (a : ℝ) < x ∧ x < (b : ℝ) ∧
      Polynomial.eval x (p.map (Rat.castHom ℝ)) = 0 ∧
      ∀ y : ℝ, (a : ℝ) < y → y < (b : ℝ) →
        Polynomial.eval y (p.map (Rat.castHom ℝ)) = 0 → y = x

/-- Projection of the realization of a formula to its first `k` coordinates. -/
def RationalFirstOrderFormula.projection (k : ℕ)
    (φ : RationalFirstOrderFormula) : Set (Fin k → ℝ) :=
  {u | ∃ x : ℕ → ℝ, φ.Holds x ∧ ∀ i : Fin k, x i = u i}

/-- The one-free-variable section of a formula, with all other coordinates fixed
to zero. -/
def RationalFirstOrderFormula.realSection
    (φ : RationalFirstOrderFormula) : Set ℝ :=
  {r | φ.Holds (fun i => if i = 0 then r else 0)}

/-- A family is cylindrical when every pair of cells has equal or disjoint
projections at every coordinate level. -/
def IsCylindricalFormulaFamily
    (cells : Finset RationalFirstOrderFormula) : Prop :=
  ∀ c₁ ∈ cells, ∀ c₂ ∈ cells, ∀ k,
    c₁.projection k = c₂.projection k ∨
      Disjoint (c₁.projection k) (c₂.projection k)

/-- The finite boundary of a one-dimensional section is returned together with
rational defining polynomials and isolating intervals for every endpoint. -/
def HasIsolatedOneDimensionalBoundary
    (φ : RationalFirstOrderFormula) : Prop :=
  ∃ boundary : Finset ℝ,
    frontier φ.realSection = boundary ∧
      ∀ x ∈ boundary, HasRationalAlgebraicDescription x

/-- A total CAD implementation has the complete elimination, disjointness,
cylindricity, sampling, and one-dimensional isolation specification. -/
def CadAlgorithmCorrect
    (cad : ℕ → RationalFirstOrderFormula →
      Finset RationalFirstOrderFormula) : Prop :=
  ∀ (freeVars : ℕ) (φ : RationalFirstOrderFormula),
    let cells := cad freeVars φ
    (∀ cell ∈ cells, cell.QuantifierFree) ∧
    (∀ c₁ ∈ cells, ∀ c₂ ∈ cells, c₁ ≠ c₂ →
      Disjoint {x | c₁.Holds x} {x | c₂.Holds x}) ∧
    IsCylindricalFormulaFamily cells ∧
    (∀ x, φ.Holds x ↔ ∃ cell ∈ cells, cell.Holds x) ∧
    (∀ cell ∈ cells, (∃ x, cell.Holds x) →
      ∃ sample : ℕ → ℝ, cell.Holds sample ∧
        ∀ i, HasRationalAlgebraicDescription (sample i)) ∧
    (freeVars = 1 →
      ∀ cell ∈ cells, HasIsolatedOneDimensionalBoundary cell)

/-- G. E. Collins (1975), “Quantifier elimination for real closed fields by
cylindrical algebraic decomposition,” Section 3 algorithm ELIM, pp. 157–160;
Section 4 Theorems 17–18, pp. 174–175; DECOMP and ISOL specifications,
pp. 145–152, DOI 10.1007/3-540-07407-4_17. -/
-- @node: lem:cad-quantifier-elimination
def CylindricalAlgebraicDecompositionQE : Sort 0 :=
  ∃ cad : ℕ → RationalFirstOrderFormula →
      Finset RationalFirstOrderFormula,
    CadAlgorithmCorrect cad

/-- Endpoint certificate: value, bounded atom array, masses, dual coefficients,
and a flag indicating whether the matching global dual certificate exists. -/
abbrev CadEndpointCertificate (m : ℕ) :=
  ℝ × (Fin (countIndexCard m) → CellLaw) ×
    (Fin (countIndexCard m) → ℝ) × (CountIndex m → ℝ) × Bool

/-- The two endpoint certificates returned by finite-support recovery. -/
abbrev CadRecoveryOutput (m : ℕ) := CadEndpointCertificate m × CadEndpointCertificate m

/-- Atomic measure encoded by one endpoint certificate. -/
noncomputable def CadEndpointCertificate.measure {m : ℕ}
    (certificate : CadEndpointCertificate m) : Measure CellLaw :=
  ∑ k, ENNReal.ofReal (certificate.2.2.1 k) • Measure.dirac (certificate.2.1 k)

/-- The rational input discipline of the endpoint-recovery CAD world. -/
def CadRecoveryInputRational {m : ℕ} (ε : ℝ)
    (b : CountIndex m → ℝ) : Prop :=
  (∃ e : ℚ, (e : ℝ) = ε) ∧ ∀ c, ∃ r : ℚ, (r : ℝ) = b c

/-- The denominator-cleared equation defining one causal value.  Positivity of
the multiplier is recorded separately in the endpoint certificate. -/
def ClearedCausalValue (q : CellLaw) (t : ℝ) : Prop :=
  t * (treatmentProb q * (1 - treatmentProb q)) =
    q (true, true) * (1 - treatmentProb q) -
      q (false, true) * treatmentProb q

/-- Existence of a globally feasible dual polynomial which attains and contacts
the primal endpoint certificate. -/
def MatchingDualCertificate (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ)
    (isLower : Bool) (certificate : CadEndpointCertificate m) : Prop :=
  ∃ coeff : CountIndex m → ℝ,
    (if isLower then IsMinorant m ε coeff else IsMajorant m ε coeff) ∧
    coefficientValue coeff b = certificate.1 ∧
    (∀ c, HasRationalAlgebraicDescription (coeff c)) ∧
    ∀ k, 0 < certificate.2.2.1 k →
      (∑ c, coeff c * bernsteinCoordinate m c (certificate.2.1 k)) =
        causalIntegrand (certificate.2.1 k)

/-- Embed a scalar as the first coordinate of a real assignment. -/
def scalarAssignment (t : ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then t else 0

/-- The returned endpoint values occur in one-dimensional sections produced by
the particular total CAD algorithm supplied by the gate. -/
def CadCertifiesRecovery
    (cad : ℕ → RationalFirstOrderFormula → Finset RationalFirstOrderFormula)
    {m : ℕ} (out : CadRecoveryOutput m) : Prop :=
  ∃ problem lowerCell upperCell,
    lowerCell ∈ cad 1 problem ∧ upperCell ∈ cad 1 problem ∧
    lowerCell.Holds (scalarAssignment out.1.1) ∧
    upperCell.Holds (scalarAssignment out.2.1)

/-- All primal equations and, when requested, the global dual/contact equations
carried by one endpoint certificate. -/
def CadEndpointValid (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ)
    (isLower : Bool) (certificate : CadEndpointCertificate m) : Prop :=
  HasRationalAlgebraicDescription certificate.1 ∧
  (∀ k c, HasRationalAlgebraicDescription (certificate.2.1 k c)) ∧
  (∀ k, HasRationalAlgebraicDescription (certificate.2.2.1 k)) ∧
  (∀ k, certificate.2.1 k ∈ overlapSimplex ε) ∧
  (∀ k, 0 < treatmentProb (certificate.2.1 k) *
      (1 - treatmentProb (certificate.2.1 k))) ∧
  (∀ k, ClearedCausalValue (certificate.2.1 k)
      (causalIntegrand (certificate.2.1 k))) ∧
  (∀ k, 0 ≤ certificate.2.2.1 k) ∧
  (∑ k, certificate.2.2.1 k) = 1 ∧
  (∀ c, ∑ k, certificate.2.2.1 k *
      bernsteinCoordinate m c (certificate.2.1 k) = b c) ∧
  certificate.1 = (∑ k, certificate.2.2.1 k *
      causalIntegrand (certificate.2.1 k)) ∧
  certificate.1 = (if isLower then lowerEndpoint m ε b else upperEndpoint m ε b) ∧
  (certificate.2.2.2.2 = true ↔
    MatchingDualCertificate m ε b isLower certificate) ∧
  (certificate.2.2.2.2 = true →
    (if isLower then IsMinorant m ε certificate.2.2.2.1
      else IsMajorant m ε certificate.2.2.2.1) ∧
    coefficientValue certificate.2.2.2.1 b = certificate.1 ∧
    (∀ c, HasRationalAlgebraicDescription (certificate.2.2.2.1 c)) ∧
    ∀ k, 0 < certificate.2.2.1 k →
      (∑ c, certificate.2.2.2.1 c *
        bernsteinCoordinate m c (certificate.2.1 k)) =
          causalIntegrand (certificate.2.1 k))

/-- Specification returned by the relative-interior and boundary-capable CAD branches. -/
-- @node: def:cad-recovery-procedure
noncomputable def cadRecoveryProcedure (m : ℕ) (ε : ℝ)
    (b : CountIndex m → ℝ) : Set (Option (CadRecoveryOutput m)) :=
  {result | CadRecoveryInputRational ε b ∧
    match result with
    | none => b ∉ bernsteinMomentBody m ε
    | some out =>
        b ∈ bernsteinMomentBody m ε ∧
        CadEndpointValid m ε b true out.1 ∧
        CadEndpointValid m ε b false out.2 ∧
        (b ∈ intrinsicInterior ℝ (bernsteinMomentBody m ε) →
          out.1.2.2.2.2 = true ∧ out.2.2.2.2.2 = true)}
  -- @realizes CAD_m(two-branch finite-support primal/dual recovery specification)

/-- Confidence-CAD output: exact set, returned cells, certified hull,
endpoint-attainment flags, and a flag selecting full decomposition versus hull output. -/
abbrev ConfidenceCadOutput :=
  Set ℝ × Finset (Set ℝ) × (ℝ × ℝ) × (Bool × Bool) × Bool

def ConfidenceCadOutput.resultSet (out : ConfidenceCadOutput) : Set ℝ := out.1
def ConfidenceCadOutput.cells (out : ConfidenceCadOutput) : Finset (Set ℝ) := out.2.1
def ConfidenceCadOutput.hull (out : ConfidenceCadOutput) : ℝ × ℝ := out.2.2.1
def ConfidenceCadOutput.attained (out : ConfidenceCadOutput) : Bool × Bool := out.2.2.2.1
def ConfidenceCadOutput.fullDecomposition (out : ConfidenceCadOutput) : Bool := out.2.2.2.2

/-- A finite disjoint decomposition into algebraic points and intervals. -/
def IsFiniteAlgebraicCellDecomposition
    (S : Set ℝ) (cells : Finset (Set ℝ)) : Prop :=
    S = ⋃ cell ∈ cells, cell ∧
    (∀ c₁ ∈ cells, ∀ c₂ ∈ cells, c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
    ∀ cell ∈ cells,
      (∃ x, HasRationalAlgebraicDescription x ∧ cell = {x}) ∨
      (∃ a b, HasRationalAlgebraicDescription a ∧
        HasRationalAlgebraicDescription b ∧
        (cell = Set.Ioo a b ∨ cell = Set.Ioc a b ∨
          cell = Set.Ico a b ∨ cell = Set.Icc a b))

/-- Existential form used by statements which do not expose returned cell data. -/
def HasFiniteAlgebraicCellDecomposition (S : Set ℝ) : Prop :=
  ∃ cells, IsFiniteAlgebraicCellDecomposition S cells

/-- Fixed `N_m+1`-slot certificate for membership in the confidence set.  Zero
masses permit smaller supports.  The final array records denominator-cleared
per-atom objective values. -/
abbrev ConfidenceAtomWitness (m : ℕ) :=
  (CountIndex m → ℝ) ×
    (Fin (countIndexCard m + 1) → CellLaw) ×
    (Fin (countIndexCard m + 1) → ℝ) ×
    (Fin (countIndexCard m + 1) → ℝ)

/-- The monomial comparison obtained after exponentiating a finite deviance
comparison, including its extended-real zero-pattern branches. -/
def ClearedDevianceComparison {m : ℕ} (n : ℕ)
    (bprime : CountIndex m → ℝ) (z w : AggregateSpace m n) : Prop :=
  (∃ c, 0 < aggregateCount w c ∧ bprime c = 0) ∨
    ((¬ ∃ c, 0 < aggregateCount z c ∧ bprime c = 0) ∧
      (∏ c, (aggregateCount z c : ℝ) ^ aggregateCount z c) *
          (∏ c, (bprime c) ^ aggregateCount w c) ≤
        (∏ c, (aggregateCount w c : ℝ) ^ aggregateCount w c) *
          (∏ c, (bprime c) ^ aggregateCount z c))

/-- A finite deviance-order cell, with its Boolean labels tied both to the
extended-real comparisons and to their cleared monomial inequalities. -/
def DevianceOrderCellCertificate {m : ℕ} (n : ℕ) (α : ℝ)
    (zobs : AggregateSpace m n) (bprime : CountIndex m → ℝ) : Prop :=
  ∃ upperTail : AggregateSpace m n → Bool,
    (∀ w, upperTail w = true ↔ deviance n zobs bprime ≤ deviance n w bprime) ∧
    (∀ w, upperTail w = true ↔ ClearedDevianceComparison n bprime zobs w) ∧
    α < ∑ w, if upperTail w then multinomialPmf n bprime w else 0

/-- Every atom, mass, moment, objective, deviance-cell, and positive-factor
constraint in the finite-support confidence-set membership formula. -/
def ConfidenceAtomWitness.Valid {m n : ℕ} (ε α : ℝ)
    (zobs : AggregateSpace m n) (t : ℝ) (w : ConfidenceAtomWitness m) : Prop :=
  let bprime := w.1
  let atoms := w.2.1
  let masses := w.2.2.1
  let values := w.2.2.2
  ValidConfidenceLevel α ∧
  bprime ∈ stdSimplex ℝ (CountIndex m) ∧
  bprime ∈ exactMultinomialRegion n α zobs ∧
  DevianceOrderCellCertificate n α zobs bprime ∧
  (∀ k, atoms k ∈ overlapSimplex ε) ∧
  (∀ k, 0 ≤ masses k) ∧
  (∑ k, masses k) = 1 ∧
  (∀ c, bprime c = ∑ k, masses k * bernsteinCoordinate m c (atoms k)) ∧
  (∀ k, 0 < treatmentProb (atoms k) * (1 - treatmentProb (atoms k))) ∧
  (∀ k, ClearedCausalValue (atoms k) (values k)) ∧
  t = ∑ k, masses k * values k

/-- Every component returned by confidence CAD is constrained: the set is
exact, cells are returned in decomposition mode, the hull is exact, and each
Boolean is equivalent to endpoint attainability. -/
def ConfidenceCadOutput.Valid (S : Set ℝ) (out : ConfidenceCadOutput) : Prop :=
  out.resultSet = S ∧ out.resultSet ⊆ Set.Icc (-1) 1 ∧
  out.hull.1 = sInf out.resultSet ∧ out.hull.2 = sSup out.resultSet ∧
  (out.attained.1 = true ↔ out.hull.1 ∈ out.resultSet) ∧
  (out.attained.2 = true ↔ out.hull.2 ∈ out.resultSet) ∧
  ((out.fullDecomposition = true ∧
      IsFiniteAlgebraicCellDecomposition out.resultSet out.cells) ∨
    (out.fullDecomposition = false ∧ out.cells = ∅ ∧
      HasRationalAlgebraicDescription out.hull.1 ∧
      HasRationalAlgebraicDescription out.hull.2))

/-- The exact returned confidence set is the realization of the cells produced
by the particular one-free-variable CAD run supplied by the gate. -/
def CadCertifiesConfidence
    (cad : ℕ → RationalFirstOrderFormula → Finset RationalFirstOrderFormula)
    (out : ConfidenceCadOutput) : Prop :=
  ∃ problem, ∀ t,
    t ∈ out.resultSet ↔
      ∃ cell ∈ cad 1 problem, cell.Holds (scalarAssignment t)

/-- Specification of exact confidence-set elimination after finite atom reduction. -/
-- @node: def:confidence-set-cad
noncomputable def confidenceSetCadProcedure (m n : ℕ) (ε α : ℝ)
    (zobs : AggregateSpace m n) : Set ConfidenceCadOutput :=
  {out | ValidConfidenceLevel α ∧
    (∃ e : ℚ, (e : ℝ) = ε) ∧ (∃ a : ℚ, (a : ℝ) = α) ∧
    out.Valid (wholeSetConfidenceSet m n ε α zobs) ∧
    ∀ t, t ∈ out.resultSet ↔
      ∃ witness : ConfidenceAtomWitness m, witness.Valid ε α zobs t}
  -- @realizes CAD_conf(exact confidence-set decomposition or certified endpoint hull)

/-- Boundary atlas labels: point identification and minimum lower/upper support sizes. -/
abbrev BoundaryLabel := Bool × ℕ × ℕ

/-- Encode a moment vector in the first `N_m` coordinates of a real assignment. -/
noncomputable def momentVectorAssignment {m : ℕ}
    (b : CountIndex m → ℝ) : ℕ → ℝ :=
  fun i => if hi : i < Fintype.card (CountIndex m) then
    b ((Fintype.equivFin (CountIndex m)).symm ⟨i, hi⟩) else 0

/-- A returned rational quantifier-free formula defines exactly the given cell. -/
def RationalFormulaDefinesMomentCell {m : ℕ}
    (cell : Set (CountIndex m → ℝ)) (φ : RationalFirstOrderFormula) : Prop :=
  φ.QuantifierFree ∧ ∀ b, b ∈ cell ↔ φ.Holds (momentVectorAssignment b)

/-- Elementary face criterion inside the moment body. -/
def IsMomentFaceCell (m : ℕ) (ε : ℝ)
    (cell : Set (CountIndex m → ℝ)) : Prop :=
  cell ⊆ bernsteinMomentBody m ε ∧ Convex ℝ cell ∧
  ∀ x ∈ bernsteinMomentBody m ε, ∀ y ∈ bernsteinMomentBody m ε,
    (2 : ℝ)⁻¹ • (x + y) ∈ cell → x ∈ cell ∧ y ∈ cell

/-- The causal integrand restricted to a support variety lies in the affine
span of the restricted Bernstein coordinates. -/
def CausalIntegrandAffineOnSupport (m : ℕ) (support : Set CellLaw) : Prop :=
  ∃ intercept : ℝ, ∃ coeff : CountIndex m → ℝ,
    ∀ q ∈ support, causalIntegrand q = intercept +
      ∑ c, coeff c * bernsteinCoordinate m c q

/-- A representing support variety is cut out inside the overlap simplex by a
finite family of rational polynomial equations. -/
def IsRationalSupportVariety (ε : ℝ) (support : Set CellLaw) : Prop :=
  ∃ equations : Finset (MvPolynomial Cell ℚ),
    support = {q | q ∈ overlapSimplex ε ∧
      ∀ p ∈ equations, MvPolynomial.eval₂ (Rat.castHom ℝ) q p = 0}

/-- A paper-local finite-support predicate used to state minimum support labels. -/
def MeasureSupportedOnAtMost (ν : Measure CellLaw) (k : ℕ) : Prop :=
  ∃ atoms : Finset CellLaw, atoms.card ≤ k ∧ ν (atoms : Set CellLaw)ᶜ = 0

/-- The Boolean and both natural-number labels have their full cellwise
semantics, including restricted affine-span membership and minimum supports. -/
def BoundaryLabelSemantics (m : ℕ) (ε : ℝ)
    (cell : Set (CountIndex m → ℝ)) (support : Set CellLaw)
    (label : BoundaryLabel) : Prop :=
  (label.1 = true ↔ CausalIntegrandAffineOnSupport m support) ∧
  (∀ b ∈ cell, label.1 = true ↔
    lowerEndpoint m ε b = upperEndpoint m ε b) ∧
  1 ≤ label.2.1 ∧ label.2.1 ≤ countIndexCard m ∧
  1 ≤ label.2.2 ∧ label.2.2 ≤ countIndexCard m ∧
  (∀ b ∈ cell,
    (∃ ν ∈ momentFiber m ε b, ateFunctional ν = lowerEndpoint m ε b ∧
      MeasureSupportedOnAtMost ν label.2.1) ∧
    (∀ k < label.2.1, ¬ ∃ ν ∈ momentFiber m ε b,
      ateFunctional ν = lowerEndpoint m ε b ∧ MeasureSupportedOnAtMost ν k) ∧
    (∃ ν ∈ momentFiber m ε b, ateFunctional ν = upperEndpoint m ε b ∧
      MeasureSupportedOnAtMost ν label.2.2) ∧
    (∀ k < label.2.2, ¬ ∃ ν ∈ momentFiber m ε b,
      ateFunctional ν = upperEndpoint m ε b ∧ MeasureSupportedOnAtMost ν k))

/-- Returned boundary cells, formulas, support varieties, constant labels,
one sample per cell, and endpoint certificates at those samples. -/
abbrev BoundaryAtlasOutput (m : ℕ) :=
  Finset (Set (CountIndex m → ℝ)) ×
    (Set (CountIndex m → ℝ) → RationalFirstOrderFormula) ×
    (Set (CountIndex m → ℝ) → Set CellLaw) ×
    (Set (CountIndex m → ℝ) → BoundaryLabel) ×
    (Set (CountIndex m → ℝ) → CountIndex m → ℝ) ×
    (Set (CountIndex m → ℝ) → CadRecoveryOutput m)

def BoundaryAtlasOutput.cells {m : ℕ} (atlas : BoundaryAtlasOutput m) := atlas.1
def BoundaryAtlasOutput.formula {m : ℕ} (atlas : BoundaryAtlasOutput m) := atlas.2.1
def BoundaryAtlasOutput.support {m : ℕ} (atlas : BoundaryAtlasOutput m) := atlas.2.2.1
def BoundaryAtlasOutput.label {m : ℕ} (atlas : BoundaryAtlasOutput m) := atlas.2.2.2.1
def BoundaryAtlasOutput.sample {m : ℕ} (atlas : BoundaryAtlasOutput m) := atlas.2.2.2.2.1
def BoundaryAtlasOutput.sampleEndpoints {m : ℕ} (atlas : BoundaryAtlasOutput m) :=
  atlas.2.2.2.2.2

/-- Every defining formula returned in the atlas comes from one common CAD run
of the particular terminating algorithm supplied by the gate. -/
def CadGeneratesBoundaryAtlas
    (cad : ℕ → RationalFirstOrderFormula → Finset RationalFirstOrderFormula)
    {m : ℕ} (atlas : BoundaryAtlasOutput m) : Prop :=
  ∃ problem, ∀ cell ∈ atlas.cells,
    atlas.formula cell ∈ cad (countIndexCard m) problem

/-- Number of strictly positive atom weights in an endpoint certificate. -/
noncomputable def CadEndpointCertificate.activeAtoms {m : ℕ}
    (certificate : CadEndpointCertificate m) : ℕ :=
  (Finset.univ.filter fun k => 0 < certificate.2.2.1 k).card

/-- A finite disjoint semialgebraic face stratification with defining formulas,
support varieties, exact labels, and algebraic minimum-size sample witnesses. -/
-- @node: def:boundary-atlas-handle
noncomputable def boundaryAtlasHandle (m : ℕ) (ε : ℝ) :
    Set (BoundaryAtlasOutput m) :=
  {atlas |
    (⋃ cell ∈ atlas.cells, cell) =
      intrinsicFrontier ℝ (bernsteinMomentBody m ε) ∧
    (∀ c₁ ∈ atlas.cells, ∀ c₂ ∈ atlas.cells, c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
    ∀ cell ∈ atlas.cells,
      IsMomentFaceCell m ε cell ∧
      RationalFormulaDefinesMomentCell cell (atlas.formula cell) ∧
      IsRationalSupportVariety ε (atlas.support cell) ∧
      (∀ b ∈ cell,
        b ∈ convexHull ℝ (momentMap m '' atlas.support cell)) ∧
      BoundaryLabelSemantics m ε cell (atlas.support cell) (atlas.label cell) ∧
      atlas.sample cell ∈ cell ∧
      (∀ c, HasRationalAlgebraicDescription (atlas.sample cell c)) ∧
      CadEndpointValid m ε (atlas.sample cell) true
        (atlas.sampleEndpoints cell).1 ∧
      CadEndpointValid m ε (atlas.sample cell) false
        (atlas.sampleEndpoints cell).2 ∧
      (atlas.sampleEndpoints cell).1.activeAtoms = (atlas.label cell).2.1 ∧
      (atlas.sampleEndpoints cell).2.activeAtoms = (atlas.label cell).2.2}
  -- @realizes A_boundary(finite truth-invariant CAD boundary stratification handle)

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
