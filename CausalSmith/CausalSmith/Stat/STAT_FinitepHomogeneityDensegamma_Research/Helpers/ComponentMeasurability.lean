module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentBounds
public import Mathlib.MeasureTheory.Function.Floor

/-! Borel frame, label and component densities for the full-record augmentation. -/
public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Piecewise trigonometric frame coordinates are Borel for every public rank. [This is the stated conclusion](goal). -/
-- @node: measurable_frameCoord
@[fun_prop] lemma measurable_frameCoord (K : ℕ) (i : Fin (K+1)) :
    Measurable (fun x : unitInterval => frameCoord K i x) := by
  unfold frameCoord
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_subtype_coe).inter
      (measurableSet_le measurable_subtype_coe measurable_const)
  · fun_prop
  · apply Measurable.ite
    · exact (show MeasurableSet {x : unitInterval | 0 < i.val} from by
        by_cases hi : 0 < i.val <;> simp [hi]).inter
        ((measurableSet_le measurable_const measurable_subtype_coe).inter
          (measurableSet_le measurable_subtype_coe measurable_const))
    · fun_prop
    · fun_prop

/-- Every record-label density is Borel, including the zero-rank input branch. [This is the stated conclusion](goal). -/
-- @node: measurable_labelDensity
@[fun_prop] lemma measurable_labelDensity (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (label : Bool × Bool) :
    Measurable (fun z : unitInterval × Bool => labelDensity ν K M a u idx z.1 z.2 label) := by
  have hf (i : Fin (K+1)) : Measurable (fun z : unitInterval × Bool => frameCoord K i z.1) :=
    (measurable_frameCoord K i).comp measurable_fst
  simp only [labelDensity, copulaZeta, copulaXi, copulaUpsilon, copulaT, smoothedTent, frameField]
  apply Measurable.ite
  · exact measurableSet_preimage measurable_snd (measurableSet_singleton true)
  · fun_prop
  · fun_prop

/-- Finite disclosure selects coefficient weights by a measurable discrete map. [This is the stated conclusion](goal). -/
-- @node: measurable_conditionalPairWeight
@[fun_prop] lemma measurable_conditionalPairWeight (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (pairs : CoefficientPairs K) :
    Measurable (fun δ => conditionalPairWeight ν K M σ δ pairs) := by
  fun_prop

/-- Histogram cell indices are Borel, including the right endpoint convention. [This is the stated conclusion](goal). -/
-- @node: measurable_fineIndex
@[fun_prop] lemma measurable_fineIndex (K : ℕ) : Measurable (fineIndex K) := by
  unfold fineIndex
  fun_prop

/-- [The set of augmentations in which a fixed vertex set is a component is measurable](goal),
because component membership depends only on finite vectors of coarse and fine cell indices. -/
-- @node: measurableSet_componentMembership
lemma measurableSet_componentMembership (n K M : ℕ) (C : Finset (Fin n)) :
    MeasurableSet {aug : Augmentation n K | C ∈ components n K M aug} := by
  let f (aug : Augmentation n K) : (Fin n → ℕ) × (Fin n → ℕ) :=
    (fun i => fineIndex M (aug.1 i), fun i => fineIndex K (aug.1 i))
  let edge (z : (Fin n → ℕ) × (Fin n → ℕ)) (i j : Fin n) : Prop :=
    z.1 i = z.1 j ∧ (z.2 i = z.2 j ∨
      ((z.2 i+1=z.2 j ∨ z.2 j+1=z.2 i) ∧ max (z.2 i) (z.2 j)*M % K ≠ 0))
  let S : Set ((Fin n → ℕ) × (Fin n → ℕ)) :=
    {z | C ∈ Finset.univ.image (fun i => Finset.univ.filter
      (fun j => Relation.ReflTransGen (edge z) i j))}
  have hf : Measurable f := by fun_prop
  have hS : MeasurableSet S := MeasurableSet.of_discrete
  exact hS.preimage hf

/-- A fixed observation component has a Borel coefficient-averaged label density. [This is the stated conclusion](goal). -/
-- @node: measurable_componentDensity
@[fun_prop] lemma measurable_componentDensity (ν sign : Bool) (n K M : ℕ) (a u : ℝ)
    (C : Finset (Fin n)) (labels : Labels n) :
    Measurable (fun aug => componentDensity ν sign n K M a u aug C labels) := by
  unfold componentDensity
  fun_prop


end CausalSmith.Stat.FinitepHomogeneityDensegamma
