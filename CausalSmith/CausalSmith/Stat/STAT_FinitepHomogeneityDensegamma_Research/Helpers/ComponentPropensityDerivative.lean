module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentAxisDerivative
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! First propensity-amplitude derivative cancellation with all outcome labels retained. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Swapping the two coefficient coordinates and disclosed coordinates preserves their weight. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_swap
lemma conditionalPairWeight_swap (ν : Bool) (K M : ℕ) (σ : Fin (M / 2) → Bool)
    (δ : Disclosure K) (p : CoefficientPairs K) :
    conditionalPairWeight ν K M σ (fun i => (δ i).map Prod.swap)
      (fun i => (p i).swap) = conditionalPairWeight ν K M σ δ p := by
  unfold conditionalPairWeight
  apply Finset.prod_congr rfl
  intro i _
  cases hd : δ i with
  | none =>
    simp only [hd, Option.map_none, Prod.swap]
    unfold pairWeight
    congr 1
    ring
  | some q =>
    simp only [hd, Option.map_some, Prod.swap_inj]

/-- Opposite coarse signs remove a likelihood affine in propensity coefficients; the remaining factor can depend arbitrarily on every outcome coefficient and on the disclosure. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_affine_fst_even
lemma conditionalPairWeight_affine_fst_even (K M : ℕ) (δ : Disclosure K)
    (F H : (Fin (K + 1) → Bool) → ℝ)
    (G : Fin (K + 1) → (Fin (K + 1) → Bool) → ℝ) (t : ℝ) :
    let V (ν s : Bool) (p : CoefficientPairs K) :=
      F (fun i => (p i).2) + ∑ j, G j (fun i => (p i).2) * signVal (p j).1 +
        (if ν then (if s then t else -t) else 0) * H (fun i => (p i).2)
    (∑ p, conditionalPairWeight true K M (fun _ => true) δ p * V true true p) +
    (∑ p, conditionalPairWeight true K M (fun _ => false) δ p * V true false p) =
    2 * ∑ p, conditionalPairWeight false K M (fun _ => false) δ p * V false false p := by
  classical
  let e : CoefficientPairs K ≃ CoefficientPairs K :=
    { toFun := fun p i => (p i).swap
      invFun := fun p i => (p i).swap
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he (ν s : Bool) :
      (∑ p, conditionalPairWeight ν K M (fun _ => s) δ p *
        (F (fun i => (p i).2) + ∑ j, G j (fun i => (p i).2) * signVal (p j).1 +
          (if ν then (if s then t else -t) else 0) * H (fun i => (p i).2))) =
      ∑ p, conditionalPairWeight ν K M (fun _ => s) (fun i => (δ i).map Prod.swap) p *
        (F (fun i => (p i).1) + ∑ j, G j (fun i => (p i).1) * signVal (p j).2 +
          (if ν then (if s then t else -t) else 0) * H (fun i => (p i).1)) := by
    apply Fintype.sum_equiv e
    intro p
    rw [show e p = (fun i => (p i).swap) from rfl, conditionalPairWeight_swap]
    rfl
  dsimp only
  rw [he true true, he true false, he false false]
  exact conditionalPairWeight_affine_snd_even K M (fun i => (δ i).map Prod.swap) F H G t

/-- The actual record-density propensity slope at the axis, including the rational correction. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. -/
-- @node: labelPropensitySlope
def labelPropensitySlope (ν : Bool) (K M : ℕ) (u : ℝ) (idx : CopulaIndex K M)
    (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  signVal label.1 * Λ + if marked then
    signVal label.1 * signVal label.2 * u *
      (Λ * H - (if ν then kappa0 * smoothedTent K M idx.1 x else 0)) else 0

/-- Differentiating the correction at zero leaves its signed tent term; the squared propensity factor has zero derivative there. [This is the stated conclusion](goal). -/
-- @node: labelDensity_hasDerivAt_propensity_zero
lemma labelDensity_hasDerivAt_propensity_zero (ν : Bool) (K M : ℕ) (u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun a => labelDensity ν K M a u idx x marked label)
      (labelPropensitySlope ν K M u idx x marked label) 0 := by
  have hid := hasDerivAt_id (0:ℝ)
  have hxi := hid.mul_const (frameField K (fun j => signVal (idx.2 j).1) x)
  have hden := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hid.pow 2)
  have ht := ((((hid.const_mul (-(if ν then (1:ℝ) else 0))).mul_const u).mul_const kappa0).div
    hden (by norm_num)).mul_const (smoothedTent K M idx.1 x)
  have hz := (hxi.mul_const (copulaUpsilon K M u idx x)).add
    (ht.mul ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hxi.pow 2)))
  cases marked with
  | false =>
    convert (hxi.const_mul (signVal label.1)).const_add 1 using 1 <;>
      first | rfl | (simp [labelPropensitySlope])
  | true =>
    have hh := (((hxi.const_mul (signVal label.1)).const_add 1).add
      (hasDerivAt_const (0:ℝ) (signVal label.2 * copulaUpsilon K M u idx x))).add
        (hz.const_mul (signVal label.1 * signVal label.2))
    convert hh using 1 <;>
      first
      | rfl
      | (cases ν <;> simp [labelPropensitySlope, copulaUpsilon, id] <;> ring)

/-- Finite product differentiation selects exactly one propensity slope, while every other record retains its outcome-axis density and every coefficient retains its prior weight. [This is the stated conclusion](goal). -/
-- @node: componentDensity_hasDerivAt_propensity_zero
lemma componentDensity_hasDerivAt_propensity_zero (ν s : Bool) (n K M : ℕ) (u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun a => componentDensity ν s n K M a u aug C labels)
      (∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
        ∑ i ∈ C, (∏ j ∈ C.erase i,
          labelDensity ν K M 0 u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
            labelPropensitySlope ν K M u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)) 0 := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  exact HasDerivAt.fun_finsetProd (fun i _ =>
    labelDensity_hasDerivAt_propensity_zero ν K M u _ _ _ _)

/-- Each differentiated record contributes a term affine in just one propensity coefficient. Averaging its coarse sign cancels both the changed conditional moment and the tent correction. [This is the stated conclusion](goal). -/
-- @node: component_propensity_slope_even
lemma component_propensity_slope_even (n K M : ℕ) (u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) (i : Fin n) :
    let D (ν s : Bool) := ∑ p : CoefficientPairs K,
      conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
        ((∏ j ∈ C.erase i,
          labelDensity ν K M 0 u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
            labelPropensitySlope ν K M u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i))
    D true true + D true false = 2 * D false false := by
  classical
  let H (h : Fin (K + 1) → Bool) (j : Fin n) :=
    frameField K (fun k => signVal (h k)) (aug.1 j)
  let R (h : Fin (K + 1) → Bool) := ∏ j ∈ C.erase i,
    (if aug.2.1 j then 1 + signVal (labels j).2 * (u * H h j) else 1)
  let G (k : Fin (K + 1)) (h : Fin (K + 1) → Bool) :=
    R h * signVal (labels i).1 * frameCoord K k (aug.1 i) *
      (1 + if aug.2.1 i then signVal (labels i).2 * u * H h i else 0)
  let J (h : Fin (K + 1) → Bool) :=
    R h * (if aug.2.1 i then signVal (labels i).1 * signVal (labels i).2 else 0)
  let t := -u * kappa0 * smoothedTent K M (fun _ => true) (aug.1 i)
  have hbase (ν s : Bool) (p : CoefficientPairs K) :
      (∏ j ∈ C.erase i,
        labelDensity ν K M 0 u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) =
        R (fun k => (p k).2) := by
    apply Finset.prod_congr rfl
    intro j _
    cases hm : aug.2.1 j <;>
      simp [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT, H]
  have he (ν s : Bool) (p : CoefficientPairs K) :
      (∏ j ∈ C.erase i,
        labelDensity ν K M 0 u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
          labelPropensitySlope ν K M u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i) =
      (0:ℝ) + ∑ k, G k (fun j => (p j).2) * signVal (p k).1 +
        (if ν then (if s then t else -t) else 0) * J (fun j => (p j).2) := by
    rw [hbase]
    have hg : (∑ k, G k (fun j => (p j).2) * signVal (p k).1) =
        R (fun j => (p j).2) * signVal (labels i).1 *
          (1 + if aug.2.1 i then signVal (labels i).2 * u * H (fun j => (p j).2) i else 0) *
            frameField K (fun k => signVal (p k).1) (aug.1 i) := by
      unfold frameField
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [G]
      ring
    rw [hg]
    cases ν <;> cases s <;> cases hm : aug.2.1 i <;>
      simp [labelPropensitySlope, J, t, H, hm, smoothedTent_constant_sign_neg] <;> ring
  dsimp only
  simp_rw [he]
  exact conditionalPairWeight_affine_fst_even K M aug.2.2 (fun _ => 0) J G t

/-- The first propensity derivative of the sign-averaged discrepancy vanishes on its axis. The finite product rule and the single-propensity conditional moment cancellation establish this for every design and disclosure, before quantitative derivative bounds are used. [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_hasDerivAt_propensity_zero
lemma evenDiscrepancy_hasDerivAt_propensity_zero (n K M : ℕ) (u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun a => evenDiscrepancy n K M a u aug C labels) 0 0 := by
  let D (ν s : Bool) := ∑ p : CoefficientPairs K,
    conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
      ∑ i ∈ C, (∏ j ∈ C.erase i,
        labelDensity ν K M 0 u ((fun _ => s),p) (aug.1 j) (aug.2.1 j) (labels j)) *
          labelPropensitySlope ν K M u ((fun _ => s),p) (aug.1 i) (aug.2.1 i) (labels i)
  have hd (ν s : Bool) : HasDerivAt (fun a => componentDensity ν s n K M a u aug C labels)
      (D ν s) 0 := componentDensity_hasDerivAt_propensity_zero ν s n K M u aug C labels
  have hc : (D true true + D true false)/2 - D false false = 0 := by
    have hsum : D true true + D true false = 2 * D false false := by
      dsimp only [D]
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := C)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum]
      exact component_propensity_slope_even n K M u aug C labels i
    linear_combination hsum / 2
  have hh := (((hd true true).add (hd true false)).div_const 2).sub (hd false false)
  rw [hc] at hh
  convert hh using 1 <;> rfl

end CausalSmith.Stat.FinitepHomogeneityDensegamma
