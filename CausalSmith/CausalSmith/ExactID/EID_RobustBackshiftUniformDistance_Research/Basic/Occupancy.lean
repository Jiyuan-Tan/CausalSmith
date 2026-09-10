import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Affine occupancy and sparse-design vocabulary

Finite indexed affine-line occupancy, deletion distance, affine-minor separation, and the
prespecified sparse-support genericity assumptions.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open MeasureTheory Set
open scoped BigOperators

noncomputable section

-- @env: S2
variable {ι Ωsample : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ωsample]

/-- The signed affine `3 × 3` minor of three indexed planar shift points. -/
def affineMinor {p : ℕ} (s : ι → Fin p → ℝ) (k l : Fin p) (e f g : ι) : ℝ :=
  s f k * s g l - s g k * s f l -
    (s e k * s g l - s g k * s e l) +
    (s e k * s f l - s f k * s e l)

/-- An indexed shift subfamily is contained in one affine line exactly when all of its
affine minors vanish.

@realizes L(affine line represented by vanishing affine minors)
-/
def CollinearPairs {p : ℕ} (s : ι → Fin p → ℝ) (k l : Fin p) (S : Finset ι) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, ∀ g ∈ S, affineMinor s k l e f g = 0

/-- [Membership in the affine-collinearity predicate is classically decidable](goal). -/
instance {p : ℕ} (s : ι → Fin p → ℝ) (k l : Fin p) (S : Finset ι) :
    Decidable (CollinearPairs s k l S) := Classical.propDecidable _

-- @node: def:max-line-occupancy
/-- Maximum number of indexed points lying on a common affine line; coincident indices retain
their full multiplicity.

@realizes Mkl(maximum indexed affine-line occupancy)
-/
def maxLineOccupancy {p : ℕ} (I : Finset ι) (s : ι → Fin p → ℝ)
    (k l : Fin p) : ℕ :=
  (I.powerset.filter (CollinearPairs s k l)).sup Finset.card

/-- Ordered coordinate pairs used for pairwise shift comparisons. -/
def offDiagPairs (p : ℕ) : Finset (Fin p × Fin p) :=
  Finset.univ.filter fun kl ↦ kl.1 < kl.2

-- @node: def:environment-distance
/-- Minimum number of indexed environments that must be deleted to make a coordinate-pair
shift cloud collinear.

@realizes delta(minimum h - Mkl over coordinate pairs)
-/
def envDeletionDistance {p : ℕ} (I : Finset ι) (s : ι → Fin p → ℝ) : ℕ :=
  Finset.fold min I.card
    (fun kl ↦ I.card - maxLineOccupancy I s kl.1 kl.2) (offDiagPairs p)

/-- The active coordinates of a fixed binary support pattern. -/
abbrev ActiveIndex {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) :=
  {q : ι × Fin p // q.1 ∈ I ∧ Z q.1 q.2 = true}

/-- Projection of a full amplitude array onto the jointly active subarray. -/
def activeProjection {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (a : ι → Fin p → ℝ) : ActiveIndex I Z → ℝ :=
  fun q ↦ a q.1.1 q.1.2

/-- The strictly positive orthant of the active-coordinate Euclidean space. -/
def positiveOrthant {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) :
    Set (ActiveIndex I Z → ℝ) :=
  {x | ∀ q, 0 < x q}

-- @node: ass:support-factorization
/-- A realized shift array is the product of the fixed binary support and positive amplitudes.

@realizes Z(prespecified binary support array)
-/
def SupportFactorization {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (a s : ι → Fin p → ℝ) : Prop :=
  (∀ e ∈ I, ∀ k, s e k = if Z e k then a e k else 0) ∧
    ∀ e ∈ I, ∀ k, Z e k = true → 0 < a e k

-- @node: ass:generic-active-amplitudes
/-- The joint active-amplitude law is absolutely continuous relative to Lebesgue measure
restricted to its positive orthant.

@realizes a(joint positive active-amplitude random array)
-/
def GenericActiveAmplitudes {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (a : Ωsample → ι → Fin p → ℝ) : Prop :=
  Measurable (fun ω ↦ activeProjection I Z (a ω)) ∧
    Measure.map (fun ω ↦ activeProjection I Z (a ω)) μ ≪
      volume.restrict (positiveOrthant I Z)

/-- Pairwise support-incidence count.

@realizes nab(number of indices of support type (u,v))
-/
def incidenceCount {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (k l : Fin p) (u v : Bool) : ℕ :=
  (I.filter fun e ↦ Z e k = u ∧ Z e l = v).card

-- @node: def:generic-occupancy
/-- Closed-form generic affine occupancy determined by a binary support pattern.

@realizes Mgen(max of the four forced-incidence terms)
-/
def genericOccupancy {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (k l : Fin p) : ℕ :=
  let n00 := incidenceCount I Z k l false false
  let n10 := incidenceCount I Z k l true false
  let n01 := incidenceCount I Z k l false true
  let n11 := incidenceCount I Z k l true true
  max (max (n00 + n10) (n00 + n01))
    (max (n00 + if 0 < n11 then 1 else 0) (min 2 I.card))

/-- Pairwise-distinct triples from an indexed finite set. -/
def indexTriples (I : Finset ι) : Finset (ι × ι × ι) :=
  (I ×ˢ I ×ˢ I).filter fun efg ↦
    efg.1 ≠ efg.2.1 ∧ efg.1 ≠ efg.2.2 ∧ efg.2.1 ≠ efg.2.2

/-- Largest absolute affine minor on a finite indexed subset. -/
noncomputable def maxAffineMinor {p : ℕ} (I : Finset ι) (s : ι → Fin p → ℝ)
    (k l : Fin p) : ℝ :=
  Finset.fold max 0
    (fun efg ↦ |affineMinor s k l efg.1 efg.2.1 efg.2.2|) (indexTriples I)

-- @node: def:affine-separation
/-- Worst overlap affine-minor separation, with the stipulated zero convention below three
retained environments.

@realizes gamma(min over coordinate pairs and retained subsets of max absolute minor)
-/
noncomputable def affineSeparation {p m c : ℕ} (_hp : 2 ≤ p) (H : Finset ι)
    (_hH : H.card = honestCount m c) (s : ι → Fin p → ℝ)
    (_hs : ∀ e ∈ H, ∀ k, 0 ≤ s e k) : ℝ :=
  if H.card - c < 3 then 0
  else sInf {x : ℝ | ∃ kl ∈ offDiagPairs p,
    ∃ S ∈ H.powersetCard (H.card - c), x = maxAffineMinor S s kl.1 kl.2}

-- @node: maxLineOccupancy_congr_on
/-- Maximum line occupancy only depends on the shift values at indices in the indexed family. [Under the stated hypotheses](hyp:h) [this conclusion](goal) applies. -/
lemma maxLineOccupancy_congr_on {p : ℕ} (I : Finset ι)
    (s t : ι → Fin p → ℝ) (h : ∀ e ∈ I, s e = t e) (k l : Fin p) :
    maxLineOccupancy I s k l = maxLineOccupancy I t k l := by
  unfold maxLineOccupancy
  apply congrArg (fun F : Finset (Finset ι) ↦ F.sup Finset.card)
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hSI, hcol⟩
    refine ⟨hSI, ?_⟩
    intro e he f hf g hg
    simpa only [affineMinor, h e (hSI he), h f (hSI hf), h g (hSI hg)] using
      hcol e he f hf g hg
  · rintro ⟨hSI, hcol⟩
    refine ⟨hSI, ?_⟩
    intro e he f hf g hg
    simpa only [affineMinor, h e (hSI he), h f (hSI hf), h g (hSI hg)] using
      hcol e he f hf g hg

-- @node: envDeletionDistance_gt_iff
/-- Deletion distance exceeds `c` exactly when every pairwise line occupancy is below the
retained-overlap size. [Under the stated hypotheses](hyp:hp) [this conclusion](goal) applies. -/
lemma envDeletionDistance_gt_iff {p : ℕ} (hp : 2 ≤ p) (I : Finset ι)
    (s : ι → Fin p → ℝ) (c : ℕ) :
    envDeletionDistance I s > c ↔
      ∀ k l : Fin p, k < l → maxLineOccupancy I s k l < I.card - c := by
  have hocc (k l : Fin p) : maxLineOccupancy I s k l ≤ I.card := by
    unfold maxLineOccupancy
    exact Finset.sup_le fun S hS ↦ Finset.card_le_card (Finset.mem_powerset.mp
      (Finset.mem_filter.mp hS).1)
  unfold envDeletionDistance
  change c < Finset.fold min I.card
      (fun kl ↦ I.card - maxLineOccupancy I s kl.1 kl.2) (offDiagPairs p) ↔ _
  rw [Finset.lt_fold_min]
  constructor
  · rintro ⟨_, hall⟩ k l hkl
    have h := hall (k, l) (by simp [offDiagPairs, hkl])
    change c < I.card - maxLineOccupancy I s k l at h
    omega
  · intro hall
    let k0 : Fin p := ⟨0, by omega⟩
    let k1 : Fin p := ⟨1, by omega⟩
    have h01 : k0 < k1 := by exact Fin.mk_lt_mk.mpr (by omega)
    have hcI : c < I.card := by
      have := hall k0 k1 h01
      omega
    refine ⟨hcI, ?_⟩
    intro kl hkl
    have hlt : kl.1 < kl.2 := (Finset.mem_filter.mp hkl).2
    have := hall kl.1 kl.2 hlt
    have := hocc kl.1 kl.2
    omega

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
