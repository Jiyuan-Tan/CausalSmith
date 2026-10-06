module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentOneMark
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! First outcome-amplitude derivative cancellation from exact one-mark likelihood identities. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Every record likelihood is affine in the outcome amplitude, including its copula correction. [This is the stated conclusion](goal). -/
-- @node: labelDensity_affine_outcome
lemma labelDensity_affine_outcome (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    labelDensity ν K M a u idx x marked label =
      labelDensity ν K M a 0 idx x marked label +
        u * (labelDensity ν K M a 1 idx x marked label -
          labelDensity ν K M a 0 idx x marked label) := by
  cases ν <;> cases marked <;>
    simp [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT] <;> ring

/-- The derivative at zero of an affine product is the sum of its single-factor changes. [This is the stated conclusion](goal). -/
-- @node: affine_product_hasDerivAt_zero
lemma affine_product_hasDerivAt_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b d : ι → ℝ) :
    HasDerivAt (fun u : ℝ => ∏ i ∈ S, (b i + u*d i))
      (∑ i ∈ S, ((b i+d i)*(∏ j ∈ S.erase i, b j) - ∏ j ∈ S, b j)) 0 := by
  have hd : ∀ i ∈ S, HasDerivAt (fun u : ℝ => b i + u*d i) (d i) 0 := by
    intro i _
    convert ((hasDerivAt_id (0:ℝ)).mul_const (d i)).const_add (b i) using 1 <;>
      first | rfl | simp
  have hp : HasDerivAt (fun u : ℝ => ∏ i ∈ S, (b i + u*d i))
      (∑ i ∈ S, (∏ j ∈ S.erase i, (b j + 0*d j)) * d i) 0 :=
    HasDerivAt.fun_finsetProd hd
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase S b hi]
  simp only [zero_mul, add_zero]
  ring

/-- Retain just one record's original mark flag and retain the complete design and disclosure. This statement assumes [the aug parameter](hyp:aug), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
-- @node: singleMarkAugmentation
def singleMarkAugmentation {n K : ℕ} (aug : Augmentation n K) (j : Fin n) :
    Augmentation n K := (aug.1, (fun i => if i = j then aug.2.1 i else false), aug.2.2)

/-- Removing all other marks makes the even likelihood discrepancy vanish. [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_singleMarkAugmentation
lemma evenDiscrepancy_singleMarkAugmentation (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) (j : Fin n) :
    evenDiscrepancy n K M a u (singleMarkAugmentation aug j) C labels = 0 := by
  apply evenDiscrepancy_at_most_one_mark
  have hsub : C.filter (fun i => (singleMarkAugmentation aug j).2.1 i) ⊆ {j} := by
    intro i hi
    have hm := (Finset.mem_filter.mp hi).2
    by_cases hij : i = j
    · simp [hij]
    · simp [singleMarkAugmentation, hij] at hm
  exact (Finset.card_le_card hsub).trans (by simp)

/-- The complete conditional component likelihood has a first outcome derivative given by single-mark likelihood differences; the coefficient prior is independent of the amplitude. [This is the stated conclusion](goal). -/
-- @node: componentDensity_hasDerivAt_outcome_zero
lemma componentDensity_hasDerivAt_outcome_zero (ν s : Bool) (n K M : ℕ) (a : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun u => componentDensity ν s n K M a u aug C labels)
      (∑ i ∈ C, (componentDensity ν s n K M a 1 (singleMarkAugmentation aug i) C labels -
        componentDensity ν s n K M a 0 aug C labels)) 0 := by
  classical
  let f (p : CoefficientPairs K) (i : Fin n) (u : ℝ) :=
    labelDensity ν K M a u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)
  have hzero (p : CoefficientPairs K) (i : Fin n) (m : Bool) :
      labelDensity ν K M a 0 ((fun _ => s),p) (aug.1 i) m (labels i) = f p i 0 := by
    cases m <;> cases hm : aug.2.1 i <;>
      simp [f, labelDensity, hm, copulaUpsilon, copulaZeta, copulaT]
  have hprod (p : CoefficientPairs K) (i : Fin n) (hi : i ∈ C) :
      (f p i 0 + (f p i 1 - f p i 0)) * (∏ j ∈ C.erase i, f p j 0) =
        ∏ j ∈ C, labelDensity ν K M a 1 ((fun _ => s),p)
          (aug.1 j) ((singleMarkAugmentation aug i).2.1 j) (labels j) := by
    rw [← Finset.mul_prod_erase C _ hi]
    simp only [singleMarkAugmentation, add_sub_cancel]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
    exact (hzero p j false).symm
  have hd (p : CoefficientPairs K) :=
    (affine_product_hasDerivAt_zero C (fun i => f p i 0) (fun i => f p i 1-f p i 0)).const_mul
      (conditionalPairWeight ν K M (fun _ => s) aug.2.2 p)
  have he (u : ℝ) (p : CoefficientPairs K) :
      (∏ i ∈ C, (f p i 0 + u*(f p i 1-f p i 0))) = ∏ i ∈ C, f p i u := by
    apply Finset.prod_congr rfl
    intro i _
    exact (labelDensity_affine_outcome ν K M a u _ _ _ _).symm
  simp_rw [he] at hd
  have hs : HasDerivAt (fun u : ℝ => ∑ p : CoefficientPairs K,
      conditionalPairWeight ν K M (fun _ => s) aug.2.2 p * ∏ i ∈ C, f p i u)
      (∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
        ∑ i ∈ C, ((f p i 0 + (f p i 1-f p i 0)) *
          (∏ j ∈ C.erase i, f p j 0) - ∏ j ∈ C, f p j 0)) 0 :=
    HasDerivAt.fun_sum (fun p _ => hd p)
  convert hs using 1
  · rfl
  · simp only [Finset.mul_sum, mul_sub]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [hprod _ i hi]
    rw [Finset.sum_sub_distrib]
    rfl

/-- The first outcome-amplitude derivative of the even discrepancy vanishes on the axis. Each differentiated product selects one marked factor, so exact one-mark cancellation applies before any quantitative mixed derivative bound is used. [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_hasDerivAt_outcome_zero
lemma evenDiscrepancy_hasDerivAt_outcome_zero (n K M : ℕ) (a : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun u => evenDiscrepancy n K M a u aug C labels) 0 0 := by
  let D (ν s : Bool) : ℝ := ∑ i ∈ C,
    (componentDensity ν s n K M a 1 (singleMarkAugmentation aug i) C labels -
      componentDensity ν s n K M a 0 aug C labels)
  have hd (ν s : Bool) :
      HasDerivAt (fun u => componentDensity ν s n K M a u aug C labels) (D ν s) 0 :=
    componentDensity_hasDerivAt_outcome_zero ν s n K M a aug C labels
  have hcancel : (D true true + D true false)/2 - D false false = 0 := by
    have hbase := (component_discrepancies_on_axes n K M a 0 aug C labels).1
    unfold evenDiscrepancy averageComponent nullComponent at hbase
    have hterm (i : Fin n) := evenDiscrepancy_singleMarkAugmentation n K M a 1 aug C labels i
    unfold evenDiscrepancy averageComponent nullComponent at hterm
    dsimp only [D]
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i _
    linear_combination hterm i - hbase
  have hh := (((hd true true).add (hd true false)).div_const 2).sub (hd false false)
  rw [hcancel] at hh
  convert hh using 1 <;> rfl

end CausalSmith.Stat.FinitepHomogeneityDensegamma
