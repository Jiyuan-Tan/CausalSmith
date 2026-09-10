import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Sampling
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.DerivedMargins
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.IntervalArithmetic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.longLine false

/-! Finite cutoff-atom primitive tuples, common-tuple regret projection, exact
envelopes, optimizer sets, and the weak-contact sign--comparator graph. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

/-- The frozen finite cutoff-atom tuple.  Compatibility is imposed by
`compatiblePrimitiveSet`, not by dividing by the Youden coordinate. -/
-- @env: S4
structure PrimitiveTuple (K : ℕ) where
  omega : Bool → Fin (K + 1) → ℝ
    -- @realizes \(\vartheta\)(finite tuple carrier) @realizes \(\omega_{rk,\vartheta}\)(candidate atom masses)
  nonneg : ∀ r k, 0 ≤ omega r k
    -- @realizes \(\omega_{rk,\vartheta}\)(nonnegative candidate masses)
  le_one : ∀ r k, omega r k ≤ 1
    -- @realizes \(\omega_{rk,\vartheta}\)(coordinatewise upper bound one)
  alpha : ℝ -- @realizes \(\alpha_\vartheta\)(real carrier)
  alpha_mem_Icc : alpha ∈ Set.Icc (0 : ℝ) 1
    -- @realizes \(\alpha_\vartheta\)(range [0,1])
  beta : ℝ -- @realizes \(\beta_\vartheta\)(real carrier)
  beta_mem_Icc : beta ∈ Set.Icc (0 : ℝ) 1
    -- @realizes \(\beta_\vartheta\)(range [0,1])
  pi : ℝ -- @realizes \(\pi_\vartheta\)(carried prevalence coordinate)
  a : Bool → ℝ -- @realizes \(a_{r,\vartheta}\)(carried disease-reference masses)

def candidateTotalMass {K : ℕ} (θ : PrimitiveTuple K) : ℝ :=
  ∑ r : Bool, ∑ k : Fin (K + 1), θ.omega r k

/-- Candidate prefix over exactly the atoms with index below `j`. -/
def candPrefix {K : ℕ} (θ : PrimitiveTuple K) (r : Bool) (j : ℕ) : ℝ :=
  ∑ k : Fin (K + 1), if (k : ℕ) < j then θ.omega r k else 0
  -- @realizes \(\Phi_{r,\vartheta}(j)\)(candidate atom prefix)

/-- Candidate terminal stratum mass. -/
def candMass {K : ℕ} (θ : PrimitiveTuple K) (r : Bool) : ℝ :=
  candPrefix θ r (K + 1)
  -- @realizes \(q_{r,\vartheta}\)(terminal candidate prefix)

def candYouden {K : ℕ} (θ : PrimitiveTuple K) : ℝ :=
  θ.alpha + θ.beta - 1
  -- @realizes \(g_\vartheta\)(candidate Youden index)

lemma candYouden_mem_Icc {K : ℕ} (θ : PrimitiveTuple K) :
    candYouden θ ∈ Set.Icc (-1 : ℝ) 1 := by
  simp only [candYouden, Set.mem_Icc] at *
  constructor <;>
    linarith [θ.alpha_mem_Icc.1, θ.alpha_mem_Icc.2,
      θ.beta_mem_Icc.1, θ.beta_mem_Icc.2]
  -- @realizes \(g_\vartheta\)(range [-1,1] from αϑ,βϑ ∈ [0,1])

/-- Candidate mass between two ordered policy indices. -/
def candDisagree {K : ℕ} (θ : PrimitiveTuple K) (r : Bool)
    (i j : ℕ) : ℝ :=
  candPrefix θ r (max i j) - candPrefix θ r (min i j)
  -- @realizes \(d_{r,ij}(\vartheta)\)(nonnegative prefix difference)

/-- Candidate lower sharp disease-mass endpoint on a represented disagreement
region.  It is computed entirely from the finite cutoff-atom tuple. -/
def candidateMassLower {K : ℕ} (θ : PrimitiveTuple K) (i j : ℕ) : ℝ :=
  ∑ r : Bool, max 0 (θ.a r - candMass θ r + candDisagree θ r i j)
  -- @realizes \(L_\vartheta(I)\)(computed lower candidate mass endpoint)

/-- Candidate upper sharp disease-mass endpoint on a represented disagreement
region.  It is computed entirely from the finite cutoff-atom tuple. -/
def candidateMassUpper {K : ℕ} (θ : PrimitiveTuple K) (i j : ℕ) : ℝ :=
  ∑ r : Bool, min (θ.a r) (candDisagree θ r i j)
  -- @realizes \(U_\vartheta(I)\)(computed upper candidate mass endpoint)

noncomputable def bandRadius (η : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (4 / η) / (2 * (n : ℝ)))
  -- @realizes \(\varepsilon_n\)(sqrt(log(4/η_s)/(2n)))

lemma bandRadius_pos {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) : 0 < bandRadius η n := by
  unfold bandRadius
  apply Real.sqrt_pos.2
  apply div_pos
  · apply Real.log_pos
    apply (one_lt_div hη.1).2
    linarith [hη.2]
  · exact mul_pos (by norm_num) (Nat.cast_pos.2 hn)
  -- @realizes \(\varepsilon_n\)(positive DKW radius)

/-- Raw finite rectangle before the compatibility equations are imposed. -/
noncomputable def primitiveRectangleCore {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω) : Set (PrimitiveTuple G.K) :=
  {θ |
    candidateTotalMass θ = 1 ∧
    (∀ r j, j ≤ G.K + 1 →
      |candPrefix θ r j - empAtomPrefix G D.Z sample r j| ≤
        bandRadius D.ηs D.n) ∧
    θ.alpha ∈ D.Iα sample ∧ θ.beta ∈ D.Iβ sample}

def PrimitiveAlgebraicallyCompatible {K : ℕ} (θ : PrimitiveTuple K) : Prop :=
  candidateTotalMass θ = 1 ∧
  0 < candYouden θ ∧ 0 < θ.pi ∧ θ.pi < 1 ∧
  candYouden θ * θ.pi = candMass θ true + θ.beta - 1 ∧
  θ.a true = θ.alpha * θ.pi ∧
  θ.a false = (1 - θ.alpha) * θ.pi ∧
  ∀ r, 0 ≤ θ.a r ∧ θ.a r ≤ candMass θ r

noncomputable def compatiblePrimitiveSetCore {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω) : Set (PrimitiveTuple G.K) :=
  {θ | θ ∈ primitiveRectangleCore D G sample ∧
    PrimitiveAlgebraicallyCompatible θ}

/-- The two sets jointly introduced by the primitive-confidence-set node. -/
structure PrimitiveConfidenceSetData (K : ℕ) where
  primitiveRectangle : Set (PrimitiveTuple K)
  compatiblePrimitiveSet : Set (PrimitiveTuple K)

/-- The raw rectangle and its compatible slice, scoped to positive evaluation
and external-validation sample sizes. -/
-- @node: def:primitive-confidence-set
noncomputable def primitiveConfidenceSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (_hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) :
    PrimitiveConfidenceSetData G.K :=
  { primitiveRectangle := primitiveRectangleCore D G sample
    compatiblePrimitiveSet := compatiblePrimitiveSetCore D G sample }
  -- @realizes \(\mathcal H_{n,\mathcal T}\)(finite prefix-and-accuracy rectangle)
  -- @realizes \(\Theta_{n,\mathcal T}\)(compatible finite-atom set)

noncomputable def primitiveRectangle {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set (PrimitiveTuple G.K) :=
  (primitiveConfidenceSet D G sample hSizes).primitiveRectangle

noncomputable def compatiblePrimitiveSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set (PrimitiveTuple G.K) :=
  (primitiveConfidenceSet D G sample hSizes).compatiblePrimitiveSet

abbrev PolicyVertex {M : ImperfectReferenceModel} (G : PolicyGrid M) :=
  {j : ℕ // j ∈ policyIndexSet G}

/-- The sharp value advantage of represented policy `i` over policy `j`. -/
def pairContrast (M : ImperfectReferenceModel) {K : ℕ}
    (θ : PrimitiveTuple K) (i j : ℕ) : ℝ :=
  if _hij : i < j then
    (M.b + M.c) * candidateMassUpper θ i j -
      M.c * ∑ r : Bool, candDisagree θ r i j
  else if _hji : j < i then
    M.c * (∑ r : Bool, candDisagree θ r i j) -
      (M.b + M.c) * candidateMassLower θ i j
  else 0
  -- @realizes \(H_{ij}(\vartheta)\)(sharp pairwise regret contrast)

/-- Raw finite maximum used inside the jointly scoped regret-map bundle. -/
noncomputable def candidateRegret (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (θ : PrimitiveTuple G.K) (t : Cutoff M) : ℝ :=
  ((policyIndexSet G).image
    (fun i => pairContrast M θ i (policyIndexOf G t).1)).max'
      ((policyIndexSet_nonempty G).image _)

noncomputable def candidateArgmin (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (θ : PrimitiveTuple G.K) : Set (Cutoff M) :=
  {t | ∀ u : Cutoff M, candidateRegret M G θ t ≤ candidateRegret M G θ u}

structure ProjectedRegretMapData (M : ImperfectReferenceModel) where
  regret : Cutoff M → ℝ
  argmin : Set (Cutoff M)

/-- The complete regret vector and full argmin correspondence of one tuple in
the compatible set. -/
-- @node: def:projected-regret-map
noncomputable def projectedRegretMap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (θ : PrimitiveTuple G.K) (_hθ : θ ∈ compatiblePrimitiveSet D G sample hSizes) :
    ProjectedRegretMapData M :=
  { regret := candidateRegret M G θ
    argmin := candidateArgmin M G θ }
  -- @realizes \(\mathcal R_\vartheta(t)\)(finite complete regret vector on Θ)
  -- @realizes \(\Gamma(\vartheta)\)(full argmin correspondence on Θ)

lemma projectedRegret_policy_congr {M : ImperfectReferenceModel}
    (G : PolicyGrid M) (θ : PrimitiveTuple G.K) (t u : Cutoff M)
    (h : (policyIndexOf G t).1 = (policyIndexOf G u).1) :
    candidateRegret M G θ t = candidateRegret M G θ u := by
  simp [candidateRegret, h]

/-- Coordinatewise lower envelope over the one compatible primitive set, with
the exact empty-set fallback. -/
noncomputable def regretLowerEnv {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) (t : EReal) : ℝ := by
  classical
  let Θ := compatiblePrimitiveSet D G sample hSizes
  exact if hΘ : Θ.Nonempty then
    sInf {x : ℝ | ∃ θ ∈ Θ, ∃ ht : t ∈ M.T,
      x = candidateRegret M G θ ⟨t, ht⟩}
  else 0
  -- @realizes \(\mathcal R_{n,\mathcal T}^-(t)\)(common-set infimum or zero fallback)

/-- Coordinatewise upper envelope over the same compatible primitive set, with
the exact empty-set fallback. -/
noncomputable def regretUpperEnv {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) (t : EReal) : ℝ := by
  classical
  let Θ := compatiblePrimitiveSet D G sample hSizes
  exact if hΘ : Θ.Nonempty then
    sSup {x : ℝ | ∃ θ ∈ Θ, ∃ ht : t ∈ M.T,
      x = candidateRegret M G θ ⟨t, ht⟩}
  else M.b + M.c
  -- @realizes \(\mathcal R_{n,\mathcal T}^+(t)\)(common-set supremum or b+c fallback)

def logicalEnvelope (M : ImperfectReferenceModel) : (EReal → ℝ) × (EReal → ℝ) :=
  (fun _ => 0, fun _ => M.b + M.c)

noncomputable def optimizerConfSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set EReal :=
  {t ∈ M.T | regretLowerEnv D G sample hSizes t ≤
    sInf (regretUpperEnv D G sample hSizes '' M.T)}
  -- @realizes \(\mathcal C_{n,\mathcal T}\)(coordinatewise optimizer screen)

structure RegretEnvelopeData (M : ImperfectReferenceModel) where
  lower : EReal → ℝ
  upper : EReal → ℝ
  optimizer : Set EReal

/-- The exact common-compatible-set finite-sample envelope. -/
-- @node: def:finite-sample-envelope
noncomputable def regretEnvelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : RegretEnvelopeData M :=
  { lower := regretLowerEnv D G sample hSizes
    upper := regretUpperEnv D G sample hSizes
    optimizer := optimizerConfSet D G sample hSizes }
  -- @realizes \(\mathcal B_{n,\mathcal T}\)(common-set lower and upper envelope)

/-- Inner intersection over a nonempty compatible set, with empty fallback. -/
noncomputable def projectionInner {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set EReal := by
  classical
  let Θ := compatiblePrimitiveSet D G sample hSizes
  exact if hΘ : Θ.Nonempty then
    {t | ∃ ht : t ∈ M.T, ∀ θ, ∀ hθ : θ ∈ Θ,
      (⟨t, ht⟩ : Cutoff M) ∈ (projectedRegretMap D G sample hSizes θ hθ).argmin}
  else ∅
  -- @realizes \(\mathcal I_{n,\mathcal T}\)(intersection or empty fallback)

noncomputable def projectionOuter {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set EReal := by
  classical
  let Θ := compatiblePrimitiveSet D G sample hSizes
  exact if hΘ : Θ.Nonempty then
    {t | ∃ ht : t ∈ M.T, ∃ θ, ∃ hθ : θ ∈ Θ,
      (⟨t, ht⟩ : Cutoff M) ∈ (projectedRegretMap D G sample hSizes θ hθ).argmin}
  else M.T
  -- @realizes \(\mathcal O_{n,\mathcal T}\)(union or full-policy fallback)

structure ProjectionOptimizerData where
  inner : Set EReal
  outer : Set EReal

/-- The common-tuple inner intersection and outer union, jointly packaged with
their respective empty-set fallbacks. -/
-- @node: def:projection-optimizer-sets
noncomputable def projectionOptimizerSets {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : ProjectionOptimizerData :=
  { inner := projectionInner D G sample hSizes
    outer := projectionOuter D G sample hSizes }
  -- @realizes \(\mathcal I_{n,\mathcal T}\)(intersection or empty fallback)
  -- @realizes \(\mathcal O_{n,\mathcal T}\)(union or full-policy fallback)

abbrev SaturationMask {M : ImperfectReferenceModel} (G : PolicyGrid M) :=
  PolicyVertex G → PolicyVertex G → Bool → Bool

abbrev ActiveComparator {M : ImperfectReferenceModel} (G : PolicyGrid M) :=
  PolicyVertex G → PolicyVertex G

abbrev RegretVector {M : ImperfectReferenceModel} (G : PolicyGrid M) :=
  PolicyVertex G → ℝ

/-- Weak saturation inequalities.  Both adjacent masks are allowed at contact. -/
def signCell {M : ImperfectReferenceModel} (G : PolicyGrid M)
    (θ : PrimitiveTuple G.K) (C : SaturationMask G) : Prop :=
  ∀ i j : PolicyVertex G, i ≠ j → ∀ r : Bool,
    if i.1 < j.1 then
      if C i j r then θ.a r ≤ candDisagree θ r i.1 j.1
      else candDisagree θ r i.1 j.1 ≤ θ.a r
    else
      if C i j r then candMass θ r - θ.a r ≤ candDisagree θ r i.1 j.1
      else candDisagree θ r i.1 j.1 ≤ candMass θ r - θ.a r

/-- Affine branch selected by a saturation mask. -/
def maskedContrast (M : ImperfectReferenceModel) {K : ℕ}
    (θ : PrimitiveTuple K) (i j : ℕ) (C : Bool → Bool) : ℝ :=
  if _hij : i < j then
    (M.b + M.c) *
        (∑ r : Bool, if C r then θ.a r else candDisagree θ r i j) -
      M.c * ∑ r : Bool, candDisagree θ r i j
  else if _hji : j < i then
    M.c * (∑ r : Bool, candDisagree θ r i j) -
      (M.b + M.c) *
        ∑ r : Bool, if C r then
          θ.a r - candMass θ r + candDisagree θ r i j else 0
  else 0

/-- One active-comparator cell of the complete regret graph. -/
def graphCell (M : ImperfectReferenceModel) (G : PolicyGrid M)
    (θ : PrimitiveTuple G.K) (ρ : RegretVector G)
    (C : SaturationMask G) (κ : ActiveComparator G) : Prop :=
  signCell G θ C ∧
  ∀ j : PolicyVertex G,
    ρ j = maskedContrast M θ (κ j).1 j.1 (C (κ j) j) ∧
    ∀ i : PolicyVertex G,
      maskedContrast M θ i.1 j.1 (C i j) ≤ ρ j

/-- Finite union of all weak-contact sign masks and active comparators. -/
-- @node: def:finite-support-projection-slice
noncomputable def signComparatorGraph {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) :
    Set (PrimitiveTuple G.K × RegretVector G) :=
  {z | z.1 ∈ compatiblePrimitiveSet D G sample hSizes ∧
    ∃ C : SaturationMask G, ∃ κ : ActiveComparator G,
      graphCell M G z.1 z.2 C κ}
  -- @realizes \(\mathfrak F_{n,\mathcal T}\)(finite sign-comparator regret graph)

/-- Population cutoff-atom tuple. -/
lemma population_atom_total_one (M : ImperfectReferenceModel)
    (G : PolicyGrid M) :
    (∑ r : Bool, ∑ k : Fin (G.K + 1), atomMass M G r k) = 1 := by
  have hterminal (r : Bool) :
      (∑ k : Fin (G.K + 1), atomMass M G r k) = obsMass M r := by
    rw [← atomPrefix_terminal M G r]
    exact Fin.sum_univ_eq_sum_range _ _
  simp_rw [hterminal]
  rw [Fintype.sum_bool]
  simpa [add_comm] using obsMass_false_add_true M

lemma population_atom_nonneg (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (r : Bool) (k : Fin (G.K + 1)) :
    0 ≤ atomMass M G r k := by
  exact measureReal_nonneg

lemma population_atom_le_one (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (r : Bool) (k : Fin (G.K + 1)) :
    atomMass M G r k ≤ 1 := by
  calc
    atomMass M G r k ≤ (obsMeasure M r).real Set.univ :=
      measureReal_mono (Set.subset_univ _)
    _ = obsMass M r := rfl
    _ ≤ 1 := (obsMass_mem_Icc M r).2

noncomputable def populationPrimitive (M : ImperfectReferenceModel)
    (G : PolicyGrid M) : PrimitiveTuple G.K :=
  { omega := fun r k => atomMass M G r k
    nonneg := population_atom_nonneg M G
    le_one := population_atom_le_one M G
    alpha := M.alpha
    alpha_mem_Icc := M.alpha_mem_Icc
    beta := M.beta
    beta_mem_Icc := M.beta_mem_Icc
    pi := prevalence M
    a := diseaseMass M }

def PopulationPrefixBandEvent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) : Set Ω :=
  {sample | (∀ r j, j ≤ G.K + 1 →
      |atomPrefix M G r j - empAtomPrefix G D.Z sample r j| ≤
        bandRadius D.ηs D.n) ∧
    M.alpha ∈ D.Iα sample ∧ M.beta ∈ D.Iβ sample}

/-- Shared population-tuple membership step used by both grid coverage results. -/
-- @node: population_tuple_mem_compatible_on_event
lemma population_tuple_mem_compatible_on_event {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (sample : Ω)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hevent : sample ∈ PopulationPrefixBandEvent D G) :
    populationPrimitive M G ∈ compatiblePrimitiveSet D G sample hSizes := by
  have hprefix (r : Bool) (j : ℕ) (hj : j ≤ G.K + 1) :
      candPrefix (populationPrimitive M G) r j = atomPrefix M G r j := by
    simp only [candPrefix, populationPrimitive, atomPrefix]
    calc
      _ = ∑ k ∈ Finset.range (G.K + 1),
          if k < j then atomMass M G r k else 0 :=
        Fin.sum_univ_eq_sum_range _ _
      _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
  have hmass (r : Bool) :
      candMass (populationPrimitive M G) r = obsMass M r := by
    rw [candMass, hprefix _ _ le_rfl, atomPrefix_terminal]
  have htotal : candidateTotalMass (populationPrimitive M G) = 1 :=
    population_atom_total_one M G
  have hproduct :
      candYouden (populationPrimitive M G) *
          (populationPrimitive M G).pi =
        candMass (populationPrimitive M G) true +
          (populationPrimitive M G).beta - 1 := by
    rw [hmass]
    change youden M * prevalence M = obsMass M true + M.beta - 1
    rw [prevalence]
    field_simp [ne_of_gt hg]
  change populationPrimitive M G ∈ compatiblePrimitiveSetCore D G sample
  refine ⟨?_, ?_⟩
  · refine ⟨htotal, ?_, hevent.2.1, hevent.2.2⟩
    intro r j hj
    rw [hprefix r j hj]
    exact hevent.1 r j hj
  · refine ⟨htotal, hg, hπ.1, hπ.2, hproduct, rfl, rfl, ?_⟩
    intro r
    rw [hmass]
    exact diseaseMass_nonneg_le_obsMass M hg hπ r

def RegretUniformNeighborhood (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (θ₀ : PrimitiveTuple G.K) (δ : ℝ) :
    Set (PrimitiveTuple G.K) :=
  {θ | ∀ t : Cutoff M,
    |candidateRegret M G θ t - candidateRegret M G θ₀ t| < δ / 3}

lemma positive_gap_local_argmin_constancy (M : ImperfectReferenceModel)
    (G : PolicyGrid M) (θ₀ : PrimitiveTuple G.K) (t₀ : Cutoff M)
    (hgap : ∃ δ > 0, ∀ u : Cutoff M, u ≠ t₀ →
      candidateRegret M G θ₀ t₀ + δ ≤ candidateRegret M G θ₀ u) :
    ∃ δ > 0, ∀ θ ∈ RegretUniformNeighborhood M G θ₀ δ,
      candidateArgmin M G θ = {t₀} := by
  obtain ⟨δ, hδ, hgap⟩ := hgap
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ
  ext t
  constructor
  · intro ht
    by_contra hne
    have hne' : t ≠ t₀ := by simpa using hne
    have ht_le := ht t₀
    have ht_close := hθ t
    have ht₀_close := hθ t₀
    have hsep := hgap t hne'
    rw [abs_lt] at ht_close ht₀_close
    linarith
  · intro ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    intro u
    by_cases hu : u = t₀
    · simpa [hu]
    · have hu_close := hθ u
      have ht₀_close := hθ t₀
      have hsep := hgap u hu
      rw [abs_lt] at hu_close ht₀_close
      linarith

/-- Convex interpolation from a strict point reaches the weak closure without
changing continuous envelope extrema. -/
lemma strict_to_weak_closure_segment {n : ℕ} (strict weak : Set (Fin n → ℝ))
    (xInterior : Fin n → ℝ) (hInterior : xInterior ∈ strict)
    (hstrict : strict ⊆ weak)
    (hsegment : ∀ x ∈ weak, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      (fun i => (1 - ε) * x i + ε * xInterior i) ∈ strict) :
    weak ⊆ closure strict := by
  intro x hx
  rw [mem_closure_iff_seq_limit]
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 2)
  refine ⟨fun m i => (1 - ε m) * x i + ε m * xInterior i, ?_, ?_⟩
  · intro m
    apply hsegment x hx (ε m)
    dsimp [ε]
    constructor
    · positivity
    · apply (div_lt_one (by positivity)).2
      have hm : (0 : ℝ) ≤ m := by positivity
      linarith
  · have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      convert h using 1 <;> simp only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one]
      funext m
      congr 1
      ring
    apply tendsto_pi_nhds.mpr
    intro i
    simpa using (((tendsto_const_nhds.sub hε).mul tendsto_const_nhds).add
      (hε.mul tendsto_const_nhds) :
        Filter.Tendsto
          (fun m => (1 - ε m) * x i + ε m * xInterior i)
          Filter.atTop (nhds ((1 - 0) * x i + 0 * xInterior i)))

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
