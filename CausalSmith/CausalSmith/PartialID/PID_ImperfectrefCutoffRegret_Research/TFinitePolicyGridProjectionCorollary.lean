import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TProjectionOptimizerSandwich
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TLinearWholeCurveScan
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSubmeasureBijection
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.MvPolynomial.Eval

set_option linter.style.longLine false

/-! Exact arbitrary-Borel atom reduction, asymptotic projection exactness,
sign--comparator cell identities, complexity, and scan audit agreement. -/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def FeasibleAtomAllocation {K : ℕ} (θ : PrimitiveTuple K)
    (v : Bool → Fin (K + 1) → ℝ) : Prop :=
  (∀ r k, 0 ≤ v r k ∧ v r k ≤ θ.omega r k) ∧
  ∀ r, (∑ k : Fin (K + 1), v r k) = θ.a r

def latentDiseaseMassBetween {K : ℕ} (v : Bool → Fin (K + 1) → ℝ)
    (r : Bool) (i j : ℕ) : ℝ :=
  ∑ k : Fin (K + 1),
    if min i j ≤ (k : ℕ) ∧ (k : ℕ) < max i j then v r k else 0

def latentPairObjective (M : ImperfectReferenceModel) {K : ℕ}
    (θ : PrimitiveTuple K) (v : Bool → Fin (K + 1) → ℝ)
    (i j : ℕ) : ℝ :=
  if i < j then
    (M.b + M.c) * ∑ r : Bool, latentDiseaseMassBetween v r i j -
      M.c * ∑ r : Bool, candDisagree θ r i j
  else if j < i then
    M.c * ∑ r : Bool, candDisagree θ r i j -
      (M.b + M.c) * ∑ r : Bool, latentDiseaseMassBetween v r i j
  else 0

/-- The pairwise latent disease-atom linear program. -/
noncomputable def pairwiseLatentAtomOpt (M : ImperfectReferenceModel) {K : ℕ}
    (θ : PrimitiveTuple K) (i j : ℕ) : ℝ :=
  sSup {x | ∃ v, FeasibleAtomAllocation θ v ∧
    x = latentPairObjective M θ v i j}

def atomAllocationCoefficient {K : ℕ} (θ : PrimitiveTuple K)
    (v : Bool → Fin (K + 1) → ℝ) (r : Bool) (k : Fin (K + 1)) : ℝ :=
  if θ.omega r k = 0 then 0 else v r k / θ.omega r k

def atomIntersectionBorel {M : ImperfectReferenceModel} (G : PolicyGrid M)
    (B : BorelScoreSet) (k : Fin (G.K + 1)) : BorelScoreSet :=
  ⟨B.1 ∩ policyAtom G k, B.2.inter (measurableSet_policyAtom G k)⟩

/-- The explicit atom-to-Borel lift using constant densities on each atom. -/
def AtomAllocationLift (M : ImperfectReferenceModel) (G : PolicyGrid M)
    (θ : PrimitiveTuple G.K) (v : Bool → Fin (G.K + 1) → ℝ)
    (ν : Bool → Measure ℝ) : Prop :=
  (∀ r (k : Fin (G.K + 1)), (ν r).real (policyAtom G k) = v r k) ∧
  (∀ (r : Bool) (B : BorelScoreSet),
    (ν r).real B =
      ∑ k : Fin (G.K + 1), atomAllocationCoefficient θ v r k *
        (obsMeasure M r).real (atomIntersectionBorel G B k))

/-- The candidate reference-stratum submeasure induced by a synthetic observed
score-reference law. -/
noncomputable def candidateSyntheticSubmeasure
    (P : Measure (ℝ × Bool)) (r : Bool) : Measure ℝ :=
  (P.restrict {z | z.2 = r}).map Prod.fst
  -- @realizes \(\mu_{r,\vartheta}\)(computed synthetic candidate submeasure)

/-- A candidate tuple has an actual finite atomic score-reference law and a
latent completion realizing its atom and accuracy coordinates for every
feasible disease-atom allocation. -/
def CandidateSyntheticLift {M : ImperfectReferenceModel} (G : PolicyGrid M)
    (θ : PrimitiveTuple G.K) : Prop :=
  ∀ v : Bool → Fin (G.K + 1) → ℝ, FeasibleAtomAllocation θ v →
  ∃ (P : Measure (ℝ × Bool)) (Q : Measure (ℝ × Bool × Bool)),
    IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
    Q.map (fun z => (z.1, z.2.1)) = P ∧
    Q.real {z | z.2.1 = true ∧ z.2.2 = true} =
      θ.alpha * Q.real {z | z.2.2 = true} ∧
    Q.real {z | z.2.1 = false ∧ z.2.2 = false} =
      θ.beta * Q.real {z | z.2.2 = false} ∧
    (∀ r (k : Fin (G.K + 1)),
      (candidateSyntheticSubmeasure P r).real (policyAtom G k) = θ.omega r k) ∧
    Q.real {z | z.2.2 = true} = θ.pi ∧
    (∀ r, Q.real {z | z.2.1 = r ∧ z.2.2 = true} = θ.a r) ∧
    ∀ r (k : Fin (G.K + 1)),
      Q.real {z | z.1 ∈ policyAtom G k ∧ z.2.1 = r ∧ z.2.2 = true} = v r k

noncomputable def allocationAtomMass (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (ν : Bool → Measure ℝ)
    (r : Bool) (k : Fin (G.K + 1)) : ℝ :=
  (ν r).real (policyAtom G k)

noncomputable def allocationPolicyValue (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (ν : Bool → Measure ℝ) (j : PolicyVertex G) : ℝ :=
  (M.b + M.c) * ∑ r : Bool, (diseaseMass M r -
    ∑ k : Fin (G.K + 1), if (k : ℕ) < j.1 then
      allocationAtomMass M G ν r k else 0) -
  M.c * ∑ r : Bool, (obsMass M r - atomPrefix M G r j.1)

def AllocationPolicyFactorization (M : ImperfectReferenceModel)
    (G : PolicyGrid M) : Prop :=
  ∀ ν, DominatedAllocation M ν →
    FeasibleAtomAllocation (populationPrimitive M G) (allocationAtomMass M G ν) ∧
    (∀ j : PolicyVertex G,
      allocationPolicyValue M G ν j =
        (M.b + M.c) * ∑ r : Bool, (ν r).real (policyRegion G j.1) -
          M.c * ∑ r : Bool, (obsMeasure M r).real (policyRegion G j.1)) ∧
    (∀ i j : PolicyVertex G,
      allocationPolicyValue M G ν i - allocationPolicyValue M G ν j =
        latentPairObjective M (populationPrimitive M G)
          (allocationAtomMass M G ν) i.1 j.1)

def ExactArbitraryBorelReduction (M : ImperfectReferenceModel)
    (G : PolicyGrid M) : Prop :=
  PopulationGridReduction M G ∧ AllocationPolicyFactorization M G ∧
  (∀ v, FeasibleAtomAllocation (populationPrimitive M G) v →
    ∃ ν, DominatedAllocation M ν ∧
      AtomAllocationLift M G (populationPrimitive M G) v ν) ∧
  (∀ θ, PrimitiveAlgebraicallyCompatible θ →
    CandidateSyntheticLift G θ)

/-- A finite coordinate distance on the cutoff-atom tuple. -/
def primitiveTupleDistance {K : ℕ} (θ θ₀ : PrimitiveTuple K) : ℝ :=
  (∑ r : Bool, ∑ k : Fin (K + 1), |θ.omega r k - θ₀.omega r k|) +
  |θ.alpha - θ₀.alpha| + |θ.beta - θ₀.beta| + |θ.pi - θ₀.pi| +
  ∑ r : Bool, |θ.a r - θ₀.a r|

def IsPrimitiveNeighborhood {K : ℕ} (θ₀ : PrimitiveTuple K)
    (N : Set (PrimitiveTuple K)) : Prop :=
  ∃ ε > 0, {θ | primitiveTupleDistance θ θ₀ < ε} ⊆ N

def AsymptoticProjectionExactness (M : ImperfectReferenceModel)
    (G : PolicyGrid M) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → EvaluationDesign M μ) (N : Set (PrimitiveTuple G.K)),
    (hSizes : ∀ k, PositiveSampleSizes (D k).n (D k).n₁ (D k).n₀) →
    IsPrimitiveNeighborhood (populationPrimitive M G) N →
    (∀ θ ∈ N, PrimitiveAlgebraicallyCompatible θ →
      {t.1 | t ∈ candidateArgmin M G θ} = optimizerSet M) →
    Tendsto (fun k => μ.real {sample |
      (compatiblePrimitiveSet (D k) G sample (hSizes k)).Nonempty ∧
      compatiblePrimitiveSet (D k) G sample (hSizes k) ⊆ N}) atTop (nhds 1) →
    Tendsto (fun k => μ.real {sample |
      projectionInner (D k) G sample (hSizes k) = optimizerSet M ∧
      projectionOuter (D k) G sample (hSizes k) = optimizerSet M}) atTop (nhds 1)

def PositiveGapProjectionSufficiency (M : ImperfectReferenceModel)
    (G : PolicyGrid M) : Prop :=
  ∀ (t₀ : Cutoff M),
    (∃ Δ > 0, ∀ u : Cutoff M,
      (policyIndexOf G u).1 ≠ (policyIndexOf G t₀).1 →
      regretAt M t₀ + Δ ≤ regretAt M u) →
    ∃ N : Set (PrimitiveTuple G.K),
      IsPrimitiveNeighborhood (populationPrimitive M G) N ∧
      ∀ θ ∈ N, PrimitiveAlgebraicallyCompatible θ →
        {t.1 | t ∈ candidateArgmin M G θ} =
          {t ∈ M.T | ∀ ht : t ∈ M.T,
            (policyIndexOf G ⟨t, ht⟩).1 = (policyIndexOf G t₀).1}

abbrev CellCoordinate {M : ImperfectReferenceModel} (G : PolicyGrid M) :=
  Sum (Bool × Fin (G.K + 1)) (Sum (Fin 5) (PolicyVertex G))

def graphCoordinate {M : ImperfectReferenceModel} (G : PolicyGrid M)
    (z : PrimitiveTuple G.K × RegretVector G) (i : CellCoordinate G) : ℝ :=
  match i with
  | Sum.inl rk => z.1.omega rk.1 rk.2
  | Sum.inr (Sum.inl q) =>
      match q.1 with
      | 0 => z.1.alpha
      | 1 => z.1.beta
      | 2 => z.1.pi
      | 3 => z.1.a false
      | _ => z.1.a true
  | Sum.inr (Sum.inr j) => z.2 j

def graphCellSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (C : SaturationMask G) (κ : ActiveComparator G) :
    Set (PrimitiveTuple G.K × RegretVector G) :=
  {z | z.1 ∈ compatiblePrimitiveSet D G sample hSizes ∧
    graphCell M G z.1 z.2 C κ}

def IsPolynomialCellDegreeAtMost (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (degree : ℕ)
    (cell : Set (PrimitiveTuple G.K × RegretVector G)) : Prop :=
  ∃ constraints :
      List (MvPolynomial (CellCoordinate G) ℝ × Bool),
    (∀ ps ∈ constraints, ps.1.totalDegree ≤ degree) ∧
    cell = {z | ∀ ps ∈ constraints,
      if ps.2 then MvPolynomial.eval (graphCoordinate G z) ps.1 < 0
      else MvPolynomial.eval (graphCoordinate G z) ps.1 ≤ 0}

def StrictConstraintSystemFeasible {ι : Type*}
    (constraints : List (MvPolynomial ι ℝ × Bool)) : Prop :=
  ∃ x : ι → ℝ, ∀ ps ∈ constraints,
    if ps.2 then MvPolynomial.eval x ps.1 < 0
    else MvPolynomial.eval x ps.1 ≤ 0

/-- The common-slack program used to decide all strict affine inequalities. -/
noncomputable def commonSlackValue {ι : Type*}
    (constraints : List (MvPolynomial ι ℝ × Bool)) : ℝ :=
  sSup {δ | 0 ≤ δ ∧ δ ≤ 1 ∧ ∃ x : ι → ℝ, ∀ ps ∈ constraints,
    if ps.2 then MvPolynomial.eval x ps.1 ≤ -δ
    else MvPolynomial.eval x ps.1 ≤ 0}

def CommonSlackDecidesStrictFeasibility {ι : Type*}
    (constraints : List (MvPolynomial ι ℝ × Bool)) : Prop :=
  StrictConstraintSystemFeasible constraints ↔ 0 < commonSlackValue constraints

/-- Passing a nonempty strict cell to its weak closure does not change any
regret-coordinate extremum. -/
def WeakClosurePreservesRegretExtrema {M : ImperfectReferenceModel}
    (G : PolicyGrid M)
    (cell : Set (PrimitiveTuple G.K × RegretVector G)) : Prop :=
  cell.Nonempty → ∀ j : PolicyVertex G,
    let coordinates := graphCoordinate G '' cell
    let regretCoordinate : CellCoordinate G := Sum.inr (Sum.inr j)
    sInf ((fun x => x regretCoordinate) '' closure coordinates) =
        sInf ((fun x => x regretCoordinate) '' coordinates) ∧
      sSup ((fun x => x regretCoordinate) '' closure coordinates) =
        sSup ((fun x => x regretCoordinate) '' coordinates)

/-- The primitive confidence set for the fixed-accuracy regime.  The accuracy
coordinates are pinned directly to the transported model values; no
singleton realization of a positive-size exact-binomial interval is assumed. -/
noncomputable def fixedAccuracyPrimitiveSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω) : Set (PrimitiveTuple G.K) :=
  {θ |
    candidateTotalMass θ = 1 ∧
    (∀ r j, j ≤ G.K + 1 →
      |candPrefix θ r j - empAtomPrefix G D.Z sample r j| ≤
        bandRadius D.ηs D.n) ∧
    θ.alpha = M.alpha ∧ θ.beta = M.beta ∧
    PrimitiveAlgebraicallyCompatible θ}

/-- A sign--comparator cell in the fixed-accuracy primitive set. -/
def fixedAccuracyGraphCellSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (C : SaturationMask G) (κ : ActiveComparator G) :
    Set (PrimitiveTuple G.K × RegretVector G) :=
  {z | z.1 ∈ fixedAccuracyPrimitiveSet D G sample ∧
    graphCell M G z.1 z.2 C κ}

def FixedAccuracyCellProgramExact {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (_hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ sample C κ, ∃ constraints : List (MvPolynomial (CellCoordinate G) ℝ × Bool),
      (∀ ps ∈ constraints, ps.1.totalDegree ≤ 1) ∧
      fixedAccuracyGraphCellSet D G sample C κ =
        {z | ∀ ps ∈ constraints,
          if ps.2 then MvPolynomial.eval (graphCoordinate G z) ps.1 < 0
          else MvPolynomial.eval (graphCoordinate G z) ps.1 ≤ 0} ∧
      CommonSlackDecidesStrictFeasibility constraints ∧
      WeakClosurePreservesRegretExtrema G (fixedAccuracyGraphCellSet D G sample C κ)

def IntervalAccuracyCellProgramExact {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ sample C κ, ∃ constraints : List (MvPolynomial (CellCoordinate G) ℝ × Bool),
    (∀ ps ∈ constraints, ps.1.totalDegree ≤ 2) ∧
    graphCellSet D G sample hSizes C κ =
      {z | ∀ ps ∈ constraints,
        if ps.2 then MvPolynomial.eval (graphCoordinate G z) ps.1 < 0
        else MvPolynomial.eval (graphCoordinate G z) ps.1 ≤ 0}

def GraphOuterMembershipIff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ t (ht : t ∈ M.T),
    t ∈ projectionOuter D G sample hSizes ↔
      compatiblePrimitiveSet D G sample hSizes = ∅ ∨
      ∃ z ∈ signComparatorGraph D G sample hSizes,
        ∀ j : PolicyVertex G,
          (policyIndexOf G ⟨t, ht⟩).1 = j.1 →
          ∀ k : PolicyVertex G, z.2 j ≤ z.2 k

def GraphInnerExclusionIff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ t (ht : t ∈ M.T),
    t ∉ projectionInner D G sample hSizes ↔
      compatiblePrimitiveSet D G sample hSizes = ∅ ∨
      ∃ z ∈ signComparatorGraph D G sample hSizes,
        ∃ j k : PolicyVertex G,
          (policyIndexOf G ⟨t, ht⟩).1 = j.1 ∧ z.2 k < z.2 j

def SignComparatorGraphExact {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ sample,
    signComparatorGraph D G sample hSizes =
      {z | ∃ hθ : z.1 ∈ compatiblePrimitiveSet D G sample hSizes,
        ∀ j : PolicyVertex G,
          z.2 j = (projectedRegretMap D G sample hSizes z.1 hθ).regret
            (policyRepresentative G j)} ∧
    (signComparatorGraph D G sample hSizes = ∅ ↔
      compatiblePrimitiveSet D G sample hSizes = ∅) ∧
    GraphOuterMembershipIff D G sample hSizes ∧
    GraphInnerExclusionIff D G sample hSizes ∧
    ∀ C κ, IsPolynomialCellDegreeAtMost M G 2
      (graphCellSet D G sample hSizes C κ)

/-- Exact envelope extrema read from the same graph, including its empty branch. -/
def GraphComputesEnvelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ sample t (ht : t ∈ M.T),
    (compatiblePrimitiveSet D G sample hSizes = ∅ →
      regretLowerEnv D G sample hSizes t = 0 ∧
      regretUpperEnv D G sample hSizes t = M.b + M.c) ∧
    ((compatiblePrimitiveSet D G sample hSizes).Nonempty →
      regretLowerEnv D G sample hSizes t =
        sInf {x | ∃ z ∈ signComparatorGraph D G sample hSizes,
          ∃ j : PolicyVertex G,
            (policyIndexOf G ⟨t, ht⟩).1 = j.1 ∧ x = z.2 j} ∧
      regretUpperEnv D G sample hSizes t =
        sSup {x | ∃ z ∈ signComparatorGraph D G sample hSizes,
          ∃ j : PolicyVertex G,
            (policyIndexOf G ⟨t, ht⟩).1 = j.1 ∧ x = z.2 j})

def CandidateScanInput (M : ImperfectReferenceModel) (G : PolicyGrid M)
    (θ : PrimitiveTuple G.K) (input : ScanInput M) : Prop :=
  ∃ hm : input.m = G.K + 1,
    (∀ r k, input.atom r k = θ.omega r (Fin.cast hm k)) ∧
    (∀ r j, j ≤ G.K + 1 → input.prefixes r j = candPrefix θ r j) ∧
    input.a = θ.a ∧ input.q = candMass θ ∧
    input.b = M.b ∧ input.c = M.c ∧
    (∀ j, j ∈ input.indices ↔ j ∈ policyIndexSet G) ∧
    (∀ j (_hj : j ∈ input.indices), ∃ _hjG : j ∈ policyIndexSet G,
      (referSet (input.representative j) : Set ℝ) = policyRegion G j)

/-- Exact agreement of the latent-atom programs, graph cells, and one
tuple-derived scan input shared by every represented policy coordinate. -/
def ThreeWayAuditAgreement {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ θ ∈ compatiblePrimitiveSet D G sample hSizes,
    ∃ input : ScanInput M, CandidateScanInput M G θ input ∧
    ∀ j : PolicyVertex G,
    candidateRegret M G θ (policyRepresentative G j) =
        ((policyIndexSet G).image (fun i =>
          pairwiseLatentAtomOpt M θ i j.1)).max'
            ((policyIndexSet_nonempty G).image _) ∧
      (∃ z ∈ signComparatorGraph D G sample hSizes,
        z.1 = θ ∧ z.2 j = candidateRegret M G θ (policyRepresentative G j)) ∧
      ∃ entry ∈ (scan input).entries,
        input.m = G.K + 1 ∧
        input.indices.length = (policyIndexSet G).card ∧
        entry.policyIndex = j.1 ∧
        entry.regret = candidateRegret M G θ (policyRepresentative G j) ∧
        (scan input).operations ≤
          64 * (G.K + 1 + (policyIndexSet G).card) ∧
        (scan input).peakMemory ≤ 12 * (G.K + 2)

structure GraphCellCertificate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) where
  mask : SaturationMask G
  comparator : ActiveComparator G
  constraints : List (MvPolynomial (CellCoordinate G) ℝ × Bool)
  exactCell : graphCellSet D G sample hSizes mask comparator =
    {z | ∀ ps ∈ constraints,
      if ps.2 then MvPolynomial.eval (graphCoordinate G z) ps.1 < 0
      else MvPolynomial.eval (graphCoordinate G z) ps.1 ≤ 0}

def CellComplexityAndAudit : Prop :=
  (∃ C₀ : ℕ, 0 < C₀ ∧
    ∀ (M : ImperfectReferenceModel) (G : PolicyGrid M)
      (_hg : InformativeReference M) (_hπ : InteriorPrevalence M)
      (_hb : PositiveBenefit M) (_hc : PositiveCost M),
      let p := (policyIndexSet G).card
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
        (D : EvaluationDesign M μ) (sample : Ω),
        ∀ hSizes : PositiveSampleSizes D.n D.n₁ D.n₀,
        ∃ cells : List (GraphCellCertificate D G sample hSizes),
          cells.length ≤ 4 ^ (p * (p - 1)) * p ^ p ∧
          signComparatorGraph D G sample hSizes =
            {z | ∃ cert ∈ cells,
              z ∈ graphCellSet D G sample hSizes cert.mask cert.comparator} ∧
          (∀ cert ∈ cells,
            Fintype.card (CellCoordinate G) ≤ C₀ * (G.K + p) ∧
            cert.constraints.length ≤ C₀ * (G.K + p * p))) ∧
  (∀ (M : ImperfectReferenceModel) (G : PolicyGrid M)
      (_hg : InformativeReference M) (_hπ : InteriorPrevalence M)
      (_hb : PositiveBenefit M) (_hc : PositiveCost M)
      {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (D : EvaluationDesign M μ) (sample : Ω),
      ∀ hSizes : PositiveSampleSizes D.n D.n₁ D.n₀,
    ThreeWayAuditAgreement D G sample hSizes)

theorem exact_arbitrary_borel_atom_reduction (M : ImperfectReferenceModel)
    (G : PolicyGrid M)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hb : PositiveBenefit M) (hc : PositiveCost M) :
    ExactArbitraryBorelReduction M G := by sorry

theorem projection_asymptotic_exactness (M : ImperfectReferenceModel)
    (G : PolicyGrid M) :
    AsymptoticProjectionExactness M G ∧
      PositiveGapProjectionSufficiency M G := by sorry

theorem sign_comparator_graph_exact {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) :
    SignComparatorGraphExact D G hSizes ∧
      GraphComputesEnvelope D G hSizes := by sorry

theorem projection_complexity_and_scan_audit :
    CellComplexityAndAudit := by sorry

def FinitePolicyGridProjectionCorollaryConclusion {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {M : ImperfectReferenceModel}
    (D : EvaluationDesign M μ) (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ExactArbitraryBorelReduction M G ∧
  AsymptoticProjectionExactness M G ∧
  PositiveGapProjectionSufficiency M G ∧
  SignComparatorGraphExact D G hSizes ∧
  GraphComputesEnvelope D G hSizes ∧
  FixedAccuracyCellProgramExact D G hSizes ∧
  IntervalAccuracyCellProgramExact D G hSizes ∧
  CellComplexityAndAudit

-- @node: thm:finite-policy-grid-projection-corollary
theorem finite_policy_grid_projection_corollary {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (M : ImperfectReferenceModel)
    (D : EvaluationDesign M μ) (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hb : PositiveBenefit M) (hc : PositiveCost M) :
    FinitePolicyGridProjectionCorollaryConclusion D G hSizes := by
  -- BLOCKER: needs-substrate(fixed-accuracy affine sign-cell compiler with
  -- common-slack feasibility and weak-closure extremum preservation)
  sorry

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
