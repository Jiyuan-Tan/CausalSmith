module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Hidden-allocation fixed-schedule prior
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

-- @env: S4
variable (n B d : ℕ)
-- @realizes B(block count; B ≥ 1 in construction lemmas)
-- @realizes m(source count B*d)

/-- The compactly supported cos-squared baseline density. -/
def cosSqDensity (w : ℝ) : ℝ := if |w| ≤ 1 / 4 then 4 * Real.cos (2 * Real.pi * w) ^ 2 else 0
-- @realizes f(density 4 cos²(2πw) on [-1/4,1/4], zero elsewhere)
-- @realizes w(real density argument)

/-- Ordered partitions represented by a label for each source with exactly d sources per label. -/
abbrev SourcePartition : Type :=
  {g : Fin (B * d) → Fin B // ∀ ℓ, (Finset.univ.filter (fun j => g j = ℓ)).card = d}
-- @realizes S(ordered labeled partition with block size d)

/-- Uniform finite measure; zero when the finite carrier is empty. -/
def partitionLaw : Measure (SourcePartition B d) :=
  (Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ •
    ∑ s : SourcePartition B d, Measure.dirac s

/-- The recipient block in the second half of the bipartite layout. -/
def recipientBlock (ℓ : Fin B) : Finset (Fin n) := -- @realizes ell(Fin B; paper label ℓ.val+1)
  Finset.univ.filter (fun i => B * d + ℓ.val * d ≤ i.val ∧ i.val < B * d + (ℓ.val + 1) * d)
-- @realizes Cblocks(recipient labels m+ell*d through m+(ell+1)*d-1)

/-- Independent baseline levels. -/
def blockBaselineLaw : Measure (Fin B → ℝ) :=
  Measure.pi (fun _ : Fin B => volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w)))
-- @realizes U(independent cos-squared baselines, supported in [-1/4,1/4]^B)

/-- Partition and baselines are drawn independently before assignment. -/
def blockParamLaw : Measure (SourcePartition B d × (Fin B → ℝ)) :=
  (partitionLaw B d).prod (blockBaselineLaw B)

/-- The labeled source-to-recipient block graph, with no diagonal arrows. -/
def blockEdge (s : SourcePartition B d) (j i : Fin n) : Prop :=
  (∃ hj : j.val < B * d, ∃ ℓ : Fin B,
    s.1 ⟨j.val, hj⟩ = ℓ ∧ i ∈ recipientBlock n B d ℓ) ∧ j ≠ i

/-- The source-to-recipient block graph has no diagonal arrows.  [For the stated data and conditions](hyp:s), [the stated conclusion holds](goal). -/
-- @node: blockEdge_irrefl
lemma blockEdge_irrefl (s : SourcePartition B d) : ∀ i, ¬ blockEdge n B d s i i := by
  intro i h
  exact h.2 rfl

/-- The amplitude domain of the auxiliary block family. -/
def BlockAmplitude (h : ℝ) : Prop := 0 ≤ h ∧ h ≤ 1 / 4
-- @realizes h(auxiliary-family domain 0 ≤ h ≤ 1/4)

/-- The fixed schedule map. Source and padding rows are zero; each recipient has its block
baseline. -/
def blockSchedule (σ : Bool) (h : ℝ)
    (ξ : SourcePartition B d × (Fin B → ℝ)) : Schedule (Fin n) where
  edge := blockEdge n B d ξ.1
  decEdge := Classical.decRel _
  irrefl := blockEdge_irrefl n B d ξ.1
  a := fun i => ∑ ℓ : Fin B,
    if i ∈ recipientBlock n B d ℓ then ξ.2 ℓ - signOf σ * h / 2 else 0
  t := fun _ => 0
  b := fun _ _ => signOf σ * h / d
-- @realizes h(real amplitude carrier; domain pinned by BlockAmplitude)

/-- The prior is its parameter law paired with the concrete fixed-schedule map. -/
-- @node: def:block-prior
def blockPrior (σ : Bool) (h : ℝ) :
    Measure (SourcePartition B d × (Fin B → ℝ)) ×
      ((SourcePartition B d × (Fin B → ℝ)) → Schedule (Fin n)) :=
  (blockParamLaw B d, blockSchedule n B d σ h)
-- @realizes Pi(prior on fixed schedules via independent partition and baseline parameters)

/-- Apply the complete-record channel after drawing a fixed schedule from the parameter prior. -/
def mixtureLaw {V Ξ : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ξ]
    (D : Measure (Assign V × Audit V)) (π : Measure Ξ) (s : Ξ → Schedule V) :
    Measure (Record V) := π.bind (fun ξ => D.map (recordOf (s ξ)))

/-- Mixture law of the entire original record, without removing any coordinates. -/
def blockMixtureLawOf (D : Measure (Assign (Fin n) × Audit (Fin n))) (σ : Bool) (h : ℝ) :
    Measure (Record (Fin n)) := mixtureLaw D (blockParamLaw B d) (blockSchedule n B d σ h)
-- @realizes Psign(complete original-record mixture law)

/-- The complete-record block mixture under the canonical assignment-audit product design. -/
def blockMixtureLaw (q : ℝ) (σ : Bool) (h : ℝ) : Measure (Record (Fin n)) :=
  blockMixtureLawOf n B d (thinnedDesign (Fin n) q) σ h

/-- Probability that at least one of a source's d arrows is retained. -/
def retentionP (d : ℕ) (q : ℝ) : ℝ := 1 - (1 - q) ^ d
-- @realizes p(source-association reveal probability 1-(1-q)^d)

/-- Admissible audit probability for the source-association retention formula. -/
def RetentionDomain (q : ℝ) : Prop := q ∈ Set.Icc 0 1
-- @realizes p(retention formula is interpreted for q ∈ [0,1])

/-- Source-association retention lies in the probability interval.  [For the stated data and conditions](hyp:d,q,hq), [the stated conclusion holds](goal). -/
-- @node: retentionP_mem_Icc
lemma retentionP_mem_Icc (d : ℕ) (q : ℝ) (hq : RetentionDomain q) :
    retentionP d q ∈ Set.Icc 0 1 := by
  have hnonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
  have hle : 1 - q ≤ 1 := sub_le_self _ hq.1
  have hp : (1 - q) ^ d ≤ 1 := pow_le_one₀ hnonneg hle
  exact ⟨sub_nonneg.mpr hp, sub_le_self _ (pow_nonneg hnonneg d)⟩
-- @realizes p(derived range 0 ≤ 1-(1-q)^d ≤ 1)

/-- The nonlocal testing scale is clipped at one and equals one when no association is retained. -/
def testingScale (B d : ℕ) (q : ℝ) : ℝ :=
  if 0 < retentionP d q then min 1 ((d : ℝ) / Real.sqrt ((B * d : ℕ) * retentionP d q)) else 1

/-- One hundred pi inverse times the nonlocal testing scale. -/
def testingAmplitude (B d : ℕ) (q : ℝ) : ℝ := (100 * Real.pi)⁻¹ * testingScale B d q

/-- Names both constructed priors and their complete original-record mixture laws. -/
-- @node: def:testing-handle
def testingHandle (q : ℝ) :
    ((Measure (SourcePartition B d × (Fin B → ℝ)) ×
       ((SourcePartition B d × (Fin B → ℝ)) → Schedule (Fin n))) ×
     (Measure (SourcePartition B d × (Fin B → ℝ)) ×
       ((SourcePartition B d × (Fin B → ℝ)) → Schedule (Fin n)))) ×
    (Measure (Record (Fin n)) × Measure (Record (Fin n))) :=
  ((blockPrior n B d true (testingAmplitude B d q),
    blockPrior n B d false (testingAmplitude B d q)),
   (blockMixtureLaw n B d q true (testingAmplitude B d q),
    blockMixtureLaw n B d q false (testingAmplitude B d q)))

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
