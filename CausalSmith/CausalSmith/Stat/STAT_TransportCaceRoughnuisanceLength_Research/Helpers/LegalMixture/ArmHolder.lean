module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.TiledHolder

/-! # Exact arm means of the primitive lower experiment

Finite summation identifies the receipt and outcome arm means in roadmap
(10); the rational outcome mean is controlled using the overlap denominator.
-/

public section

open Set MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The primitive receipt arm mean is the baseline receipt probability.  Under [the displayed assumptions and inputs](hyp:a,u,v,x,ha,z), [the stated conclusion holds](goal). -/
-- @node: armMeanFrom_primitive_receipt_eq
lemma armMeanFrom_primitive_receipt_eq (a u v x : ℝ) (ha : a ≠ 0) (z : Bool) :
    armMeanFrom (fun _ => primitiveMass a u v) false z x = receiptBase a z := by
  cases z <;>
    simp [armMeanFrom, primitiveMass, complierMargin, receiptBase, sign, boolReal]
  all_goals field_simp; ring

/-- The exact outcome arm mean agrees with roadmap (10) on the overlap domain.  Under [the displayed assumptions and inputs](hyp:a,u,v,x,ha,hu,z), [the stated conclusion holds](goal). -/
-- @node: armMeanFrom_primitive_outcome_eq
lemma armMeanFrom_primitive_outcome_eq (a u v x : ℝ) (ha : a ≠ 0)
    (hu : |u| ≤ 1 / 100) (z : Bool) :
    armMeanFrom (fun _ => primitiveMass a u v) true z x =
      1 / 2 + v / (1 + 2 * sign z * u) := by
  have hul : -(1 / 100 : ℝ) ≤ u := (abs_le.mp hu).1
  have huh : u ≤ 1 / 100 := (abs_le.mp hu).2
  have hp : (1 / 2 : ℝ) + u ≠ 0 := by linarith
  have hm : (1 / 2 : ℝ) - u ≠ 0 := by linarith
  have hp' : (1 : ℝ) + 2 * u ≠ 0 := by linarith
  have hm' : (1 : ℝ) - 2 * u ≠ 0 := by linarith
  have hq : (1 / 4 : ℝ) - u ^ 2 ≠ 0 := by
    have : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith [sq_nonneg (u + 1 / 100), sq_nonneg (u - 1 / 100)]
    linarith
  cases z <;>
    simp [armMeanFrom, primitiveMass, complierMargin, receiptBase, sign,
      boolReal, assignmentWeight]
  all_goals
    field_simp [ha, hp, hm, hp', hm', hq,
      show 1 - u ^ 2 * 4 ≠ 0 by nlinarith [sq_nonneg (u + 1 / 100), sq_nonneg (u - 1 / 100)],
      show 1 - u * 2 ≠ 0 by linarith, show 1 + u * 2 ≠ 0 by linarith]
    <;> ring_nf
    all_goals
      field_simp [show 1 - u ^ 2 * 4 ≠ 0 by nlinarith [sq_nonneg (u + 1 / 100), sq_nonneg (u - 1 / 100)],
        show 1 - u * 2 ≠ 0 by linarith, show 1 + u * 2 ≠ 0 by linarith]
      <;> ring

/-- On the small-amplitude overlap domain the rational arm mean has
Lipschitz constant two as a function of the tiled perturbation. Under [the displayed assumptions and inputs](hyp:u,v,z,hu,hv,hτ), [the stated conclusion holds](goal). -/
-- @node: rational_arm_mean_abs_sub_le
lemma rational_arm_mean_abs_sub_le (u v τ : ℝ) (z : Bool)
    (hu : |u| ≤ 1 / 100) (hv : |v| ≤ 1 / 100) (hτ : |τ| ≤ 1) :
    |(1 / 2 + τ * u / (1 + 2 * sign z * u)) -
      (1 / 2 + τ * v / (1 + 2 * sign z * v))| ≤ 2 * |u - v| := by
  have hs : |sign z| = 1 := by cases z <;> norm_num [sign]
  have hdu : (49 / 50 : ℝ) ≤ 1 + 2 * sign z * u := by
    have h := (abs_le.mp (show |sign z * u| ≤ 1 / 100 by simpa [abs_mul, hs] using hu)).1
    linarith
  have hdv : (49 / 50 : ℝ) ≤ 1 + 2 * sign z * v := by
    have h := (abs_le.mp (show |sign z * v| ≤ 1 / 100 by simpa [abs_mul, hs] using hv)).1
    linarith
  have hpu : 0 < 1 + 2 * sign z * u := by linarith
  have hpv : 0 < 1 + 2 * sign z * v := by linarith
  have hid : (1 / 2 + τ * u / (1 + 2 * sign z * u)) -
      (1 / 2 + τ * v / (1 + 2 * sign z * v)) =
      τ * (u - v) / ((1 + 2 * sign z * u) * (1 + 2 * sign z * v)) := by
    field_simp [ne_of_gt hpu, ne_of_gt hpv]
    <;> ring_nf
    field_simp [show 1 + u * sign z * 2 ≠ 0 by nlinarith [hpu]]
    <;> ring
  rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos hpu hpv)]
  apply (div_le_iff₀ (mul_pos hpu hpv)).2
  have hprod : (49 / 50 : ℝ) ^ 2 ≤
      (1 + 2 * sign z * u) * (1 + 2 * sign z * v) :=
    by simpa only [pow_two] using mul_le_mul hdu hdv (by norm_num) hpu.le
  have hnum : |τ| * |u - v| ≤ |u - v| := by
    simpa using mul_le_mul_of_nonneg_right hτ (abs_nonneg (u - v))
  have hden : 1 ≤ 2 * ((1 + 2 * sign z * u) * (1 + 2 * sign z * v)) := by linarith
  have := mul_le_mul_of_nonneg_right hden (abs_nonneg (u - v))
  nlinarith

/-- The exact rational outcome arm mean has radius `L` under the amplitude
ceiling used for roadmap (12). Under [the displayed assumptions and inputs](hyp:cStar,L,n,sgn,z,hc,hsmall,hcap,hn,hL,hτ), [the stated conclusion holds](goal). -/
-- @node: rational_tiled_arm_mean_holderOn
lemma rational_tiled_arm_mean_holderOn (cStar τ L : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (z : Bool)
    (hc : 0 ≤ cStar) (hsmall : cStar ≤ 1 / 100)
    (hcap : cStar ≤ (L - 3 / 4) / (6 * Real.pi))
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n) (hL : 1 < L) :
    HolderOn (fun x => 1 / 2 + τ * tiledPerturbation cStar n sgn x /
      (1 + 2 * sign z * tiledPerturbation cStar n sgn x)) L := by
  have hnpos : 0 < n := by have : 256 ≤ n := hn; omega
  have hu (x : ℝ) : |tiledPerturbation cStar n sgn x| ≤ 1 / 100 :=
    (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc).trans
      ((lowerHeight_le_amplitude cStar n hc hn).trans hsmall)
  have ht : |τ| ≤ 1 := abs_le.mpr hτ
  have hs : |sign z| = 1 := by cases z <;> norm_num [sign]
  have hd (x : ℝ) : 0 < 1 + 2 * sign z * tiledPerturbation cStar n sgn x := by
    have h := (abs_le.mp (show |sign z * tiledPerturbation cStar n sgn x| ≤ 1 / 100 by
      simpa [abs_mul, hs] using hu x)).1
    linarith
  have hcL : 2 * (cStar * (1 + 2 * Real.pi)) ≤ L := by
    have hb := (le_div_iff₀ (by positivity : 0 < 6 * Real.pi)).mp hcap
    have hp : 2 * (1 + 2 * Real.pi) ≤ 6 * Real.pi := by linarith [Real.two_le_pi]
    have := mul_le_mul_of_nonneg_left hp hc
    nlinarith
  apply holderOn_of_bound_modulus _ L hL
  · have hcont := tiledPerturbation_continuousOn cStar n sgn hc hnpos
    exact continuousOn_const.add ((continuousOn_const.mul hcont).div
      (continuousOn_const.add (continuousOn_const.mul hcont)) (fun x _ => ne_of_gt (hd x)))
  · intro x hx
    have hb := rational_arm_mean_abs_sub_le (tiledPerturbation cStar n sgn x) 0 τ z
      (hu x) (by norm_num) ht
    simp only [mul_zero, zero_div, add_zero, sub_zero] at hb
    calc
      |1 / 2 + τ * tiledPerturbation cStar n sgn x /
          (1 + 2 * sign z * tiledPerturbation cStar n sgn x)| ≤
          |(1 / 2 + τ * tiledPerturbation cStar n sgn x /
            (1 + 2 * sign z * tiledPerturbation cStar n sgn x)) - 1 / 2| + |(1 / 2 : ℝ)| :=
          by
            have hh := abs_add_le ((1 / 2 + τ * tiledPerturbation cStar n sgn x /
              (1 + 2 * sign z * tiledPerturbation cStar n sgn x)) - 1 / 2) (1 / 2)
            simpa only [sub_add_cancel] using hh
      _ ≤ 2 * |tiledPerturbation cStar n sgn x| + 1 / 2 := by
          simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), add_comm] using
            add_le_add_right hb |(1 / 2 : ℝ)|
      _ ≤ L := by linarith [hu x]
  · intro x hx y hy
    exact (rational_arm_mean_abs_sub_le _ _ τ z (hu x) (hu y) ht).trans
      ((mul_le_mul_of_nonneg_left
        (tiledPerturbation_holder_modulus cStar n sgn hc hnpos x y hx hy)
        (by norm_num : (0 : ℝ) ≤ 2)).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcL
            (Real.rpow_nonneg (abs_nonneg (x - y)) holderExponent)))

/-- All four primitive arm means satisfy the Hölder clause of model
membership, using the exact finite-sum formulas rather than contrasts alone. Under [the displayed assumptions and inputs](hyp:a,cStar,L,n,sgn,ha,hc,hsmall,hcap,hn,hL,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_arm_means_holder
lemma legalIVComponent_arm_means_holder (a cStar τ L : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 ≤ cStar) (hsmall : cStar ≤ 1 / 100)
    (hcap : cStar ≤ (L - 3 / 4) / (6 * Real.pi))
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n) (hL : 1 < L) :
    ∀ A z, HolderOn ((legalIVComponent a n cStar τ sgn).m A z) L := by
  have hb := actualStrength_bounds a n hn ha
  have hu (x : ℝ) : |tiledPerturbation cStar n sgn x| ≤ 1 / 100 :=
    (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc).trans
      ((lowerHeight_le_amplitude cStar n hc hn).trans hsmall)
  intro A z
  cases A
  · have hm : (legalIVComponent a n cStar τ sgn).m false z =
        fun _ => receiptBase (actualStrength a n) z := by
      funext x
      exact armMeanFrom_primitive_receipt_eq _ _ _ x (ne_of_gt hb.1) z
    rw [hm]
    apply const_holderOn _ L hL
    cases z <;> simp [receiptBase, sign] <;> rw [abs_of_nonneg (by linarith)] <;>
      linarith [hb.2]
  · have hm : (legalIVComponent a n cStar τ sgn).m true z =
        fun x => 1 / 2 + τ * tiledPerturbation cStar n sgn x /
          (1 + 2 * sign z * tiledPerturbation cStar n sgn x) := by
      funext x
      exact armMeanFrom_primitive_outcome_eq _ _ _ x (ne_of_gt hb.1) (hu x) z
    rw [hm]
    exact rational_tiled_arm_mean_holderOn cStar τ L n sgn z hc hsmall hcap hτ hn hL

/-- The center's four arm means belong to the same Hölder ball.  Under [the displayed assumptions and inputs](hyp:a,L,n,ha,hn,hL), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_arm_means_holder
lemma mixtureCenter_arm_means_holder (a L : ℝ) (n : ℕ)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hn : threshold ≤ n) (hL : 1 < L) :
    ∀ A z, HolderOn ((mixtureCenter a n).m A z) L := by
  have hb := actualStrength_bounds a n hn ha
  intro A z
  cases A
  · have hm : (mixtureCenter a n).m false z = fun _ => receiptBase (actualStrength a n) z := by
      funext x
      exact armMeanFrom_primitive_receipt_eq _ 0 0 x (ne_of_gt hb.1) z
    rw [hm]
    apply const_holderOn _ L hL
    cases z <;> simp [receiptBase, sign] <;> rw [abs_of_nonneg (by linarith)] <;> linarith [hb.2]
  · have hm : (mixtureCenter a n).m true z = fun _ => (1 / 2 : ℝ) := by
      funext x
      simpa only [mixtureCenter, lawFromMass, zero_div, add_zero] using
        armMeanFrom_primitive_outcome_eq (actualStrength a n) 0 0 x (ne_of_gt hb.1) (by norm_num) z
    rw [hm]
    exact const_holderOn (1 / 2) L hL (by norm_num; linarith)

/-- Coordinatewise measurability of primitive masses implies measurable arm means.  Under [the displayed assumptions and inputs](hyp:mass,hm,A,z), [the stated conclusion holds](goal). -/
-- @node: armMeanFrom_measurable_of
@[fun_prop]
lemma armMeanFrom_measurable_of (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1) (A z : Bool) :
    Measurable (armMeanFrom mass A z) := by
  unfold armMeanFrom
  fun_prop

/-- All four component arm means are measurable and lie in the unit interval. Under [the displayed assumptions and inputs](hyp:a,cStar,n,sgn,ha,hc,hsmall,hn,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_arm_means_regular
lemma legalIVComponent_arm_means_regular (a cStar τ : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 ≤ cStar) (hsmall : cStar ≤ 1 / 100)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n) :
    ∀ A z, MeasurableSet covariateSpace ∧
      Measurable (Set.indicator covariateSpace ((legalIVComponent a n cStar τ sgn).m A z)) ∧
      ∀ x ∈ covariateSpace, (legalIVComponent a n cStar τ sgn).m A z x ∈ Icc (0 : ℝ) 1 := by
  have hb := actualStrength_bounds a n hn ha
  have hu (x : ℝ) : |tiledPerturbation cStar n sgn x| ≤ 1 / 100 :=
    (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc).trans
      ((lowerHeight_le_amplitude cStar n hc hn).trans hsmall)
  intro A z
  have hm : Measurable ((legalIVComponent a n cStar τ sgn).m A z) := by
    change Measurable (armMeanFrom (lowerMass a n cStar τ sgn) A z)
    exact armMeanFrom_measurable_of _ (lowerMass_measurable a n cStar τ sgn) A z
  refine ⟨measurableSet_Icc, hm.indicator measurableSet_Icc, ?_⟩
  intro x hx
  cases A
  · change armMeanFrom (lowerMass a n cStar τ sgn) false z x ∈ _
    rw [show armMeanFrom (lowerMass a n cStar τ sgn) false z x =
      receiptBase (actualStrength a n) z from
      armMeanFrom_primitive_receipt_eq _ _ _ x (ne_of_gt hb.1) z]
    cases z <;> simp [receiptBase, sign, mem_Icc] <;> constructor <;> linarith [hb.2]
  · change armMeanFrom (lowerMass a n cStar τ sgn) true z x ∈ _
    rw [show armMeanFrom (lowerMass a n cStar τ sgn) true z x =
      1 / 2 + τ * tiledPerturbation cStar n sgn x /
        (1 + 2 * sign z * tiledPerturbation cStar n sgn x) from
      armMeanFrom_primitive_outcome_eq _ _ _ x (ne_of_gt hb.1) (hu x) z]
    have hdiff := rational_arm_mean_abs_sub_le (tiledPerturbation cStar n sgn x) 0 τ z
      (hu x) (by norm_num) (abs_le.mpr hτ)
    simp only [mul_zero, zero_div, add_zero, sub_zero] at hdiff
    have hdiff' := abs_le.mp hdiff
    constructor <;> linarith [hu x]

/-- The center's constant arm means are measurable and lie in the unit interval.  Under [the displayed assumptions and inputs](hyp:a,n,ha,hn), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_arm_means_regular
lemma mixtureCenter_arm_means_regular (a : ℝ) (n : ℕ)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hn : threshold ≤ n) :
    ∀ A z, MeasurableSet covariateSpace ∧
      Measurable (Set.indicator covariateSpace ((mixtureCenter a n).m A z)) ∧
      ∀ x ∈ covariateSpace, (mixtureCenter a n).m A z x ∈ Icc (0 : ℝ) 1 := by
  have hb := actualStrength_bounds a n hn ha
  intro A z
  have hm : Measurable ((mixtureCenter a n).m A z) := by
    change Measurable (armMeanFrom (fun _ => primitiveMass (actualStrength a n) 0 0) A z)
    fun_prop
  refine ⟨measurableSet_Icc, hm.indicator measurableSet_Icc, ?_⟩
  intro x hx
  cases A
  · change armMeanFrom (fun _ => primitiveMass (actualStrength a n) 0 0) false z x ∈ _
    rw [armMeanFrom_primitive_receipt_eq _ 0 0 x (ne_of_gt hb.1) z]
    cases z <;> simp [receiptBase, sign, mem_Icc] <;> constructor <;> linarith [hb.2]
  · change armMeanFrom (fun _ => primitiveMass (actualStrength a n) 0 0) true z x ∈ _
    rw [armMeanFrom_primitive_outcome_eq _ 0 0 x (ne_of_gt hb.1) (by norm_num) z]
    norm_num

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
