module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Basic
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.GlobalLipschitz
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! Bounded-variation Lipschitz estimate for the threshold process. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open scoped BigOperators

/-- Total-variation norm on the unit shadow-price interval. -/
noncomputable def bvNorm (h : ℝ → ℝ) : ℝ :=
  |h 0| + (eVariationOn h (Set.Icc 0 1)).toReal

/-- The arm value agrees on nonnegative cells with the predecessor's totalized extension. With [the specified inputs and conditions](hyp:epsilon,a,u), [the stated relationship holds](goal). -/
-- @node: budget_armValue_eq_predecessor
lemma budget_armValue_eq_predecessor (epsilon : ℝ) (a : Fin 2)
    (u : Cell → ℝ) :
    armValue epsilon a u =
      DiscreteOptimalValueMinimaxMatched.armCellValue epsilon a u := by
  have hm : DiscreteOptimalValueMinimaxMatched.vectorMass u = totalMass u := rfl
  have ha : DiscreteOptimalValueMinimaxMatched.vectorArmMass u a = armMassFn a u := rfl
  rw [DiscreteOptimalValueMinimaxMatched.armCellValue, hm, ha]
  by_cases h : totalMass u = 0
  · simp [armValue, h]
  · simp [armValue, h]

/-- Each arm value is Lipschitz in the four masses on the nonnegative cone. With [the specified inputs and conditions](hyp:epsilon,he,u,v,hu,hv,a), [the stated relationship holds](goal). -/
-- @node: budget_armValue_lipschitz
lemma budget_armValue_lipschitz {epsilon : ℝ} (he : 0 < epsilon)
    (u v : Cell → ℝ) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (a : Fin 2) :
    |armValue epsilon a u - armValue epsilon a v| ≤
      (1 + epsilon⁻¹) * ∑ z, |u z - v z| := by
  rw [budget_armValue_eq_predecessor, budget_armValue_eq_predecessor]
  simpa [DiscreteOptimalValueMinimaxMatched.l1CellDistance] using
    DiscreteOptimalValueMinimaxMatched.armCellValue_lipschitz he u v hu hv a

/-- The total mass changes by at most the coordinatewise L1 distance. With [the specified inputs and conditions](hyp:u,v), [the stated relationship holds](goal). -/
-- @node: budget_totalMass_lipschitz
lemma budget_totalMass_lipschitz (u v : Cell → ℝ) :
    |totalMass u - totalMass v| ≤ ∑ z, |u z - v z| := by
  have h := Finset.abs_sum_le_sum_abs (s := Finset.univ)
    (f := fun z : Cell => u z - v z)
  have hsum : (∑ z : Cell, (u z - v z)) = totalMass u - totalMass v := by
    simp [totalMass, armMassFn, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← hsum]
  exact h

/-- Perturbing both arm values and the total mass perturbs a threshold hinge. With [the specified inputs and conditions](hyp:a,b,c,d,s,t,lambda), [the stated relationship holds](goal). -/
-- @node: budget_hinge_pointwise_lipschitz
lemma budget_hinge_pointwise_lipschitz (a b c d s t lambda : ℝ) :
    |(a + max 0 (b - a - lambda * s)) -
      (c + max 0 (d - c - lambda * t))| ≤
      2 * |a - c| + |b - d| + |lambda| * |s - t| := by
  have hmax := abs_max_sub_max_le_abs
    (b - a - lambda * s) (d - c - lambda * t) 0
  have hinner :
      |(b - a - lambda * s) - (d - c - lambda * t)| ≤
        |b - d| + |a - c| + |lambda| * |s - t| := by
    have heq : (b - a - lambda * s) - (d - c - lambda * t) =
        (b - d) - (a - c) - lambda * (s - t) := by ring
    rw [heq]
    calc
      |(b - d) - (a - c) - lambda * (s - t)| ≤
          |(b - d) - (a - c)| + |lambda * (s - t)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le ((b - d) - (a - c)) (-(lambda * (s - t))))
      _ ≤ |b - d| + |a - c| + |lambda| * |s - t| := by
        rw [abs_mul]
        have h : |(b - d) - (a - c)| ≤ |b - d| + |a - c| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (b - d) (-(a - c)))
        linarith
  have houter :
      |(a + max 0 (b - a - lambda * s)) -
        (c + max 0 (d - c - lambda * t))| ≤
        |a - c| + |max 0 (b - a - lambda * s) - max 0 (d - c - lambda * t)| := by
    have heq : (a + max 0 (b - a - lambda * s)) -
        (c + max 0 (d - c - lambda * t)) =
        (a - c) + (max 0 (b - a - lambda * s) -
          max 0 (d - c - lambda * t)) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hmax' :
      |max 0 (b - a - lambda * s) - max 0 (d - c - lambda * t)| ≤
        |(b - a - lambda * s) - (d - c - lambda * t)| := by
    simpa only [max_comm 0 (b - a - lambda * s),
      max_comm 0 (d - c - lambda * t)] using hmax
  linarith

/-- At each shadow price, the threshold process inherits a cellwise L1 bound. With [the specified inputs and conditions](hyp:epsilon,he,lambda,hlambda,u,v,hu,hv), [the stated relationship holds](goal). -/
-- @node: budget_thresholdFunReal_pointwise_lipschitz
lemma budget_thresholdFunReal_pointwise_lipschitz {epsilon : ℝ} (he : 0 < epsilon)
    (lambda : ℝ) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1)
    (u v : Cell → ℝ) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z) :
    |thresholdFunReal epsilon lambda u - thresholdFunReal epsilon lambda v| ≤
      (3 * (1 + epsilon⁻¹) + 1) * ∑ z, |u z - v z| := by
  let D := ∑ z, |u z - v z|
  let L := 1 + epsilon⁻¹
  have h0 := budget_armValue_lipschitz he u v hu hv 0
  have h1 := budget_armValue_lipschitz he u v hu hv 1
  have hs := budget_totalMass_lipschitz u v
  have hD : 0 ≤ D := Finset.sum_nonneg (fun z _ => abs_nonneg _)
  have hlam : |lambda| ≤ 1 := by rw [abs_of_nonneg hlambda.1]; exact hlambda.2
  have hmass : |lambda| * |totalMass u - totalMass v| ≤ D := by
    calc
      |lambda| * |totalMass u - totalMass v| ≤
          1 * |totalMass u - totalMass v| := by
            exact mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
      _ ≤ D := by simpa only [one_mul, D] using hs
  have hhinge := budget_hinge_pointwise_lipschitz
    (armValue epsilon 0 u) (armValue epsilon 1 u)
    (armValue epsilon 0 v) (armValue epsilon 1 v)
    (totalMass u) (totalMass v) lambda
  simp only [thresholdFunReal, dif_pos hlambda, thresholdFun] at ⊢
  dsimp [D, L] at *
  nlinarith

/-- The hinge height is a nonnegative fraction of the cell mass. With [the specified inputs and conditions](hyp:epsilon,he,u,hu), [the stated relationship holds](goal). -/
-- @node: budget_positiveGain_bounds
lemma budget_positiveGain_bounds {epsilon : ℝ} (he : 0 < epsilon)
    (u : Cell → ℝ) (hu : ∀ z, 0 ≤ u z) :
    0 ≤ max 0 (armValue epsilon 1 u - armValue epsilon 0 u) ∧
      max 0 (armValue epsilon 1 u - armValue epsilon 0 u) ≤ totalMass u := by
  have h0 := DiscreteOptimalValueMinimaxMatched.armCellValue_bounds he u hu 0
  have h1 := DiscreteOptimalValueMinimaxMatched.armCellValue_bounds he u hu 1
  rw [← budget_armValue_eq_predecessor] at h0
  rw [← budget_armValue_eq_predecessor] at h1
  change 0 ≤ armValue epsilon 0 u ∧ armValue epsilon 0 u ≤ totalMass u at h0
  change 0 ≤ armValue epsilon 1 u ∧ armValue epsilon 1 u ≤ totalMass u at h1
  change 0 ≤ max 0 (armValue epsilon 1 u - armValue epsilon 0 u) ∧
    max 0 (armValue epsilon 1 u - armValue epsilon 0 u) ≤ totalMass u
  constructor
  · exact le_max_left _ _
  · exact max_le (le_trans h1.1 h1.2) (by linarith)

/-- The positive treatment gain inherits the two arm-value perturbation bounds. With [the specified inputs and conditions](hyp:epsilon,he,u,v,hu,hv), [the stated relationship holds](goal). -/
-- @node: budget_positiveGain_lipschitz
lemma budget_positiveGain_lipschitz {epsilon : ℝ} (he : 0 < epsilon)
    (u v : Cell → ℝ) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z) :
    |max 0 (armValue epsilon 1 u - armValue epsilon 0 u) -
      max 0 (armValue epsilon 1 v - armValue epsilon 0 v)| ≤
      2 * (1 + epsilon⁻¹) * ∑ z, |u z - v z| := by
  have h0 := budget_armValue_lipschitz he u v hu hv 0
  have h1 := budget_armValue_lipschitz he u v hu hv 1
  have hmax := abs_max_sub_max_le_abs
    (armValue epsilon 1 u - armValue epsilon 0 u)
    (armValue epsilon 1 v - armValue epsilon 0 v) 0
  have htriangle :
      |(armValue epsilon 1 u - armValue epsilon 0 u) -
        (armValue epsilon 1 v - armValue epsilon 0 v)| ≤
        |armValue epsilon 1 u - armValue epsilon 1 v| +
          |armValue epsilon 0 u - armValue epsilon 0 v| := by
    have heq :
        (armValue epsilon 1 u - armValue epsilon 0 u) -
          (armValue epsilon 1 v - armValue epsilon 0 v) =
        (armValue epsilon 1 u - armValue epsilon 1 v) -
          (armValue epsilon 0 u - armValue epsilon 0 v) := by ring
    rw [heq]
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (armValue epsilon 1 u - armValue epsilon 1 v)
        (-(armValue epsilon 0 u - armValue epsilon 0 v)))
  have hmax' :
      |max 0 (armValue epsilon 1 u - armValue epsilon 0 u) -
        max 0 (armValue epsilon 1 v - armValue epsilon 0 v)| ≤
        |(armValue epsilon 1 u - armValue epsilon 0 u) -
          (armValue epsilon 1 v - armValue epsilon 0 v)| := by
    simpa only [max_comm 0 (armValue epsilon 1 u - armValue epsilon 0 u),
      max_comm 0 (armValue epsilon 1 v - armValue epsilon 0 v)] using hmax
  linarith

/-- Subtracting a nonnegative threshold commutes with taking positive gain. With [the specified inputs and conditions](hyp:gain,threshold,hthreshold), [the stated relationship holds](goal). -/
-- @node: budget_positiveGain_threshold_rewrite
lemma budget_positiveGain_threshold_rewrite (gain threshold : ℝ)
    (hthreshold : 0 ≤ threshold) :
    max 0 (gain - threshold) = max 0 (max 0 gain - threshold) := by
  rcases le_total gain 0 with hgain | hgain
  · rw [max_eq_left hgain]
    have h : gain - threshold ≤ 0 := by linarith
    have h' : 0 - threshold ≤ 0 := by linarith
    rw [max_eq_left h, max_eq_left h']
  · rw [max_eq_right hgain]

/-- On the unit interval the threshold cell functional is a constant plus a hinge. With [the specified inputs and conditions](hyp:epsilon,lambda,hlambda,u,hu), [the stated relationship holds](goal). -/
-- @node: budget_thresholdFunReal_hinge_decomposition
lemma budget_thresholdFunReal_hinge_decomposition {epsilon : ℝ}
    (lambda : ℝ) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1)
    (u : Cell → ℝ) (hu : ∀ z, 0 ≤ u z) :
    thresholdFunReal epsilon lambda u =
      armValue epsilon 0 u +
        max 0 (max 0 (armValue epsilon 1 u - armValue epsilon 0 u) -
          lambda * totalMass u) := by
  have hs : 0 ≤ totalMass u := by
    simp only [totalMass, armMassFn]
    nlinarith [hu (0, 0), hu (0, 1), hu (1, 0), hu (1, 1)]
  have ht : 0 ≤ lambda * totalMass u := mul_nonneg hlambda.1 hs
  simp only [thresholdFunReal, dif_pos hlambda, thresholdFun]
  rw [budget_positiveGain_threshold_rewrite _ _ ht]

/-- The positive hinge changes formula at its mass-normalized cutoff. With [the specified inputs and conditions](hyp:a,s,lambda,ha,hs,has), [the stated relationship holds](goal). -/
-- @node: budget_hinge_cutoff
lemma budget_hinge_cutoff (a s lambda : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a ≤ s) :
    max 0 (a - lambda * s) =
      if lambda ≤ (if s = 0 then 0 else a / s) then a - lambda * s else 0 := by
  by_cases hzero : s = 0
  · have ha0 : a = 0 := le_antisymm (hzero ▸ has) ha
    simp [hzero, ha0]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    have hiff : lambda ≤ a / s ↔ lambda * s ≤ a := by
      rw [le_div_iff₀ hspos]
    simp only [hzero, ↓reduceIte]
    split_ifs with h
    · exact max_eq_right (by linarith [(hiff.mp h)] )
    · exact max_eq_left (by have := (hiff.not.mp h); linarith)

/-- An affine path has variation equal to its endpoint displacement. With [the specified inputs and conditions](hyp:f,c,m,l,u,hlu,heq), [the stated relationship holds](goal). -/
-- @node: budget_affine_variation_eq
lemma budget_affine_variation_eq (f : ℝ → ℝ) (c m l u : ℝ) (hlu : l ≤ u)
    (heq : Set.EqOn f (fun x => c + m * x) (Set.Icc l u)) :
    eVariationOn f (Set.Icc l u) = ENNReal.ofReal |f u - f l| := by
  have hvar : eVariationOn f (Set.Icc l u) =
      eVariationOn (fun x => c + m * x) (Set.Icc l u) :=
    eVariationOn.eq_of_eqOn heq
  rw [hvar]
  have hm : 0 ≤ m ∨ m ≤ 0 := le_total 0 m
  rcases hm with hm | hm
  · have hmono : MonotoneOn (fun x : ℝ => c + m * x) (Set.Icc l u) := by
      intro x hx y hy hxy
      dsimp
      nlinarith [mul_nonneg hm (sub_nonneg.mpr hxy)]
    have h := hmono.eVariationOn_eq (Set.left_mem_Icc.mpr hlu)
      (Set.right_mem_Icc.mpr hlu)
    simp only [Set.inter_eq_self_of_subset_left (Set.Subset.refl _)] at h
    rw [h]
    congr 1
    rw [heq (Set.right_mem_Icc.mpr hlu), heq (Set.left_mem_Icc.mpr hlu)]
    have hle := hmono (Set.left_mem_Icc.mpr hlu) (Set.right_mem_Icc.mpr hlu) hlu
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hanti : AntitoneOn (fun x : ℝ => c + m * x) (Set.Icc l u) := by
      intro x hx y hy hxy
      dsimp
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hm (sub_nonneg.mpr hxy)]
    have hanti' : eVariationOn (fun x : ℝ => c + m * x) (Set.Icc l u) =
        ENNReal.ofReal ((c + m*l) - (c + m*u)) := by
      have hmono : MonotoneOn (fun x : ℝ => -(c + m*x)) (Set.Icc l u) := by
        intro x hx y hy hxy
        exact neg_le_neg (hanti hx hy hxy)
      have h := hmono.eVariationOn_eq (Set.left_mem_Icc.mpr hlu)
        (Set.right_mem_Icc.mpr hlu)
      simp only [Set.inter_eq_self_of_subset_left (Set.Subset.refl _)] at h
      have hneg : eVariationOn (fun x : ℝ => -(c + m*x)) (Set.Icc l u) =
          eVariationOn (fun x : ℝ => c + m*x) (Set.Icc l u) := by
        unfold eVariationOn
        congr 1 with p
        congr 1 with i
        simp [edist_dist, Real.dist_eq]
      rw [hneg] at h
      convert h using 1
      congr 1
      ring
    rw [hanti']
    congr 1
    rw [heq (Set.right_mem_Icc.mpr hlu), heq (Set.left_mem_Icc.mpr hlu)]
    have hle := hanti (Set.left_mem_Icc.mpr hlu) (Set.right_mem_Icc.mpr hlu) hlu
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring

/-- A three-piece affine path has variation bounded by six times its sup norm. With [the specified inputs and conditions](hyp:f,r,t,M,h0r,hrt,ht1,hbound,h₁,h₂,h₃), [the stated relationship holds](goal). -/
-- @node: budget_three_piece_variation_le
lemma budget_three_piece_variation_le (f : ℝ → ℝ) (r t M : ℝ)
    (h0r : 0 ≤ r) (hrt : r ≤ t) (ht1 : t ≤ 1)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M)
    (h₁ : ∃ c m, Set.EqOn f (fun x => c + m * x) (Set.Icc 0 r))
    (h₂ : ∃ c m, Set.EqOn f (fun x => c + m * x) (Set.Icc r t))
    (h₃ : ∃ c m, Set.EqOn f (fun x => c + m * x) (Set.Icc t 1)) :
    (eVariationOn f (Set.Icc 0 1)).toReal ≤ 6*M := by
  rcases h₁ with ⟨c₁, m₁, h₁⟩
  rcases h₂ with ⟨c₂, m₂, h₂⟩
  rcases h₃ with ⟨c₃, m₃, h₃⟩
  have hv₁ := budget_affine_variation_eq f c₁ m₁ 0 r h0r h₁
  have hv₂ := budget_affine_variation_eq f c₂ m₂ r t hrt h₂
  have hv₃ := budget_affine_variation_eq f c₃ m₃ t 1 ht1 h₃
  have hs₁ : eVariationOn f (Set.Icc 0 r) + eVariationOn f (Set.Icc r 1) =
      eVariationOn f (Set.Icc 0 1) := by
    simpa using eVariationOn.Icc_add_Icc f (s := Set.univ) h0r (hrt.trans ht1) (Set.mem_univ r)
  have hs₂ : eVariationOn f (Set.Icc r t) + eVariationOn f (Set.Icc t 1) =
      eVariationOn f (Set.Icc r 1) := by
    simpa using eVariationOn.Icc_add_Icc f (s := Set.univ) hrt ht1 (Set.mem_univ t)
  rw [← hs₁, ← hs₂, hv₁, hv₂, hv₃]
  rw [ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
  have h0 := hbound 0 ⟨le_refl _, by norm_num⟩
  have hr := hbound r ⟨h0r, hrt.trans ht1⟩
  have ht := hbound t ⟨h0r.trans hrt, ht1⟩
  have h1 := hbound 1 ⟨by norm_num, le_refl _⟩
  have h01 := abs_sub_le (f r) 0 (f 0)
  have h12 := abs_sub_le (f t) 0 (f r)
  have h23 := abs_sub_le (f 1) 0 (f t)
  simp only [sub_zero, zero_sub, abs_neg] at h01 h12 h23
  linarith

/-- The normalized breakpoint of a nonnegative hinge. -/
-- @node: budget_hinge_breakpoint
noncomputable def budget_hinge_breakpoint (a s : ℝ) : ℝ := if s = 0 then 0 else a / s

/-- The hinge breakpoint lies in the unit interval. With [the specified inputs and conditions](hyp:a,s,ha,hs,has), [the stated relationship holds](goal). -/
-- @node: budget_hinge_breakpoint_bounds
lemma budget_hinge_breakpoint_bounds (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (has : a ≤ s) : 0 ≤ budget_hinge_breakpoint a s ∧ budget_hinge_breakpoint a s ≤ 1 := by
  by_cases hzero : s = 0
  · simp [budget_hinge_breakpoint, hzero]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    simp only [budget_hinge_breakpoint, hzero, ↓reduceIte]
    constructor
    · exact div_nonneg ha hs
    · exact (div_le_iff₀ hspos).mpr (by simpa using has)

/-- A hinge agrees with its affine branch before the breakpoint. With [the specified inputs and conditions](hyp:a,s,lambda,ha,hs,has,hl), [the stated relationship holds](goal). -/
-- @node: hinge_active
lemma hinge_active (a s lambda : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (has : a ≤ s) (hl : lambda ≤ budget_hinge_breakpoint a s) :
    max 0 (a - lambda * s) = a - lambda * s := by
  rw [budget_hinge_cutoff a s lambda ha hs has]
  change (if lambda ≤ budget_hinge_breakpoint a s then a - lambda * s else 0) = _
  rw [if_pos hl]

/-- A hinge vanishes after the breakpoint. With [the specified inputs and conditions](hyp:a,s,lambda,ha,hs,has,hl), [the stated relationship holds](goal). -/
-- @node: hinge_inactive
lemma hinge_inactive (a s lambda : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (has : a ≤ s) (hl : budget_hinge_breakpoint a s ≤ lambda) :
    max 0 (a - lambda * s) = 0 := by
  by_cases hzero : s = 0
  · have ha0 : a = 0 := le_antisymm (hzero ▸ has) ha
    simp [ha0, hzero]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    have hle : a ≤ lambda * s := by
      have hdiv : a / s ≤ lambda := by simpa [budget_hinge_breakpoint, hzero] using hl
      exact (div_le_iff₀ hspos).mp hdiv
    exact max_eq_left (by linarith)

/-- Two hinges are uniformly close under parameter perturbations. With [the specified inputs and conditions](hyp:a,b,s,t,lambda,hl), [the stated relationship holds](goal). -/
-- @node: hinge_difference_pointwise
lemma hinge_difference_pointwise (a b s t lambda : ℝ)
    (hl : lambda ∈ Set.Icc (0 : ℝ) 1) :
    |max 0 (a - lambda * s) - max 0 (b - lambda * t)| ≤
      |a - b| + |s - t| := by
  have h := budget_hinge_pointwise_lipschitz 0 a 0 b s t lambda
  have hlam : |lambda| ≤ 1 := by rw [abs_of_nonneg hl.1]; exact hl.2
  have hst : 0 ≤ |s - t| := abs_nonneg _
  simp only [zero_add, sub_zero, abs_zero] at h
  nlinarith

/-- The difference of two hinges has controlled total variation. With [the specified inputs and conditions](hyp:a,b,s,t,ha,hs,has,hb,ht,hbt), [the stated relationship holds](goal). -/
-- @node: hinge_difference_variation_le
lemma hinge_difference_variation_le (a b s t : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a ≤ s)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hbt : b ≤ t) :
    (eVariationOn (fun lambda : ℝ =>
      max 0 (a - lambda * s) - max 0 (b - lambda * t)) (Set.Icc 0 1)).toReal ≤
      6 * (|a - b| + |s - t|) := by
  let r := budget_hinge_breakpoint a s
  let q := budget_hinge_breakpoint b t
  obtain ⟨hr0, hr1⟩ := budget_hinge_breakpoint_bounds a s ha hs has
  obtain ⟨hq0, hq1⟩ := budget_hinge_breakpoint_bounds b t hb ht hbt
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |max 0 (a - x * s) - max 0 (b - x * t)| ≤ |a-b| + |s-t| := by
    intro x hx
    exact hinge_difference_pointwise a b s t x hx
  by_cases hrq : r ≤ q
  · apply budget_three_piece_variation_le
      (fun lambda : ℝ => max 0 (a - lambda*s) - max 0 (b - lambda*t))
      r q (|a-b| + |s-t|) hr0 hrq hq1 hbound
    · refine ⟨a-b, t-s, ?_⟩
      intro x hx
      dsimp only
      rw [hinge_active a s x ha hs has hx.2,
        hinge_active b t x hb ht hbt (hx.2.trans hrq)]
      ring
    · refine ⟨-b, t, ?_⟩
      intro x hx
      dsimp only
      rw [hinge_inactive a s x ha hs has hx.1,
        hinge_active b t x hb ht hbt hx.2]
      ring
    · refine ⟨0, 0, ?_⟩
      intro x hx
      dsimp only
      rw [hinge_inactive a s x ha hs has (hrq.trans hx.1),
        hinge_inactive b t x hb ht hbt hx.1]
      ring
  · have hqr : q ≤ r := le_of_not_ge hrq
    apply budget_three_piece_variation_le
      (fun lambda : ℝ => max 0 (a - lambda*s) - max 0 (b - lambda*t))
      q r (|a-b| + |s-t|) hq0 hqr hr1 hbound
    · refine ⟨a-b, t-s, ?_⟩
      intro x hx
      dsimp only
      rw [hinge_active a s x ha hs has (hx.2.trans hqr),
        hinge_active b t x hb ht hbt hx.2]
      ring
    · refine ⟨a, -s, ?_⟩
      intro x hx
      dsimp only
      rw [hinge_active a s x ha hs has hx.2,
        hinge_inactive b t x hb ht hbt hx.1]
      ring
    · refine ⟨0, 0, ?_⟩
      intro x hx
      dsimp only
      rw [hinge_inactive a s x ha hs has hx.1,
        hinge_inactive b t x hb ht hbt (hqr.trans hx.1)]
      ring

/-- Adding a constant does not change the variation of a real path. With [the specified inputs and conditions](hyp:f,c,s), [the stated relationship holds](goal). -/
-- @node: budget_variation_add_const
lemma budget_variation_add_const (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun x => c + f x) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1 with p
  congr 1 with i
  simp [edist_dist, Real.dist_eq]

-- @node: lem:bv-lipschitz
/-- The threshold fun bv lipschitz result. Under [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
lemma thresholdFun_bv_lipschitz (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Cell → ℝ,
      (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ v z) →
      bvNorm (fun lambda => thresholdFunReal epsilon lambda u - thresholdFunReal epsilon lambda v) ≤
        C * ∑ z, |u z - v z| := by
  let L : ℝ := 1 + epsilon⁻¹
  refine ⟨15 * L + 7, by dsimp [L]; positivity, ?_⟩
  intro u v hu hv
  let D : ℝ := ∑ z, |u z - v z|
  let a : ℝ := max 0 (armValue epsilon 1 u - armValue epsilon 0 u)
  let b : ℝ := max 0 (armValue epsilon 1 v - armValue epsilon 0 v)
  let s : ℝ := totalMass u
  let t : ℝ := totalMass v
  obtain ⟨ha, has⟩ := budget_positiveGain_bounds he u hu
  obtain ⟨hb, hbt⟩ := budget_positiveGain_bounds he v hv
  have hs : 0 ≤ s := ha.trans has
  have ht : 0 ≤ t := hb.trans hbt
  have hvar := hinge_difference_variation_le a b s t ha hs has hb ht hbt
  have hvarEq :
      eVariationOn (fun lambda => thresholdFunReal epsilon lambda u -
        thresholdFunReal epsilon lambda v) (Set.Icc 0 1) =
      eVariationOn (fun lambda => max 0 (a - lambda * s) -
        max 0 (b - lambda * t)) (Set.Icc 0 1) := by
    let f : ℝ → ℝ := fun lambda => thresholdFunReal epsilon lambda u -
      thresholdFunReal epsilon lambda v
    let g : ℝ → ℝ := fun lambda => max 0 (a - lambda * s) -
      max 0 (b - lambda * t)
    have heq : Set.EqOn f (fun lambda =>
        (armValue epsilon 0 u - armValue epsilon 0 v) + g lambda)
        (Set.Icc 0 1) := by
      intro lambda hlambda
      dsimp [f, g]
      rw [budget_thresholdFunReal_hinge_decomposition lambda hlambda u hu,
        budget_thresholdFunReal_hinge_decomposition lambda hlambda v hv]
      ring
    exact (eVariationOn.eq_of_eqOn heq).trans
      (budget_variation_add_const g (armValue epsilon 0 u - armValue epsilon 0 v)
        (Set.Icc 0 1))
  have hzero := budget_thresholdFunReal_pointwise_lipschitz he 0
    ⟨le_refl _, by norm_num⟩ u v hu hv
  have haLip := budget_positiveGain_lipschitz he u v hu hv
  have hsLip := budget_totalMass_lipschitz u v
  have hD : 0 ≤ D := Finset.sum_nonneg (fun z _ => abs_nonneg _)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  unfold bvNorm
  rw [hvarEq]
  dsimp [a, b, s, t, D, L] at *
  nlinarith

end CausalSmith.Stat.DiscreteBudgetvalueCurve
