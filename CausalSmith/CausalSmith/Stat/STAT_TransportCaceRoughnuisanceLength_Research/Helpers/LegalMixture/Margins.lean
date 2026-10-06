module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Mixture
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Identification
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.Floor.Semifield

/-! # Complier-share, effect, and separation identities -/

public section

open Set MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: bump_sq_integral
/-- [the stated result about bump sq integral holds](goal). -/
lemma bump_sq_integral :
    (∫ t in (0 : ℝ)..1, bump t ^ 2) = 1 / 2 := by
  have h := intervalIntegral.mul_integral_comp_mul_add
    (f := fun x : ℝ => Real.sin x ^ 2) (2 * Real.pi) 0
    (a := 0) (b := 1)
  have h' : 2 * Real.pi * (∫ t in (0 : ℝ)..1, bump t ^ 2) = Real.pi := by
    simpa [bump, integral_sin_sq, Real.sin_two_pi] using h
  apply (mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity))
  calc
    2 * Real.pi * (∫ t in (0 : ℝ)..1, bump t ^ 2) = Real.pi := h'
    _ = 2 * Real.pi * (1 / 2) := by ring

-- @node: bump_integral_zero
/-- [the stated result about bump integral zero holds](goal). -/
lemma bump_integral_zero : (∫ t in (0 : ℝ)..1, bump t) = 0 := by
  have h := intervalIntegral.mul_integral_comp_mul_add
    (f := Real.sin) (2 * Real.pi) 0 (a := 0) (b := 1)
  have h' : 2 * Real.pi * (∫ t in (0 : ℝ)..1, bump t) = 0 := by
    simpa [bump, integral_sin, Real.cos_two_pi] using h
  exact (mul_eq_zero.mp h').resolve_left (by positivity)

-- @node: bump_odd_ratio_integral_zero
/-- Given [the supplied inputs](hyp:h), [the stated result about bump odd ratio integral zero holds](goal). -/
lemma bump_odd_ratio_integral_zero (h : ℝ) :
    (∫ t in (0 : ℝ)..1,
      bump t ^ 3 / (1 / 4 - h ^ 2 * bump t ^ 2)) = 0 := by
  let f : ℝ → ℝ := fun t => bump t ^ 3 / (1 / 4 - h ^ 2 * bump t ^ 2)
  have hb (t : ℝ) : bump (1 - t) = -bump t := by
    unfold bump
    convert Real.sin_two_pi_sub (2 * Real.pi * t) using 1 <;> ring
  have hf (t : ℝ) : f (1 - t) = -f t := by
    simp only [f, hb]
    ring
  have href := intervalIntegral.integral_comp_sub_left f 1 (a := (0 : ℝ)) (b := 1)
  have heq : (∫ t in (0 : ℝ)..1, f t) = -(∫ t in (0 : ℝ)..1, f t) := by
    calc
      (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, f (1 - t) := by
        simpa using href.symm
      _ = ∫ t in (0 : ℝ)..1, -f t := by congr 1; funext t; exact hf t
      _ = -(∫ t in (0 : ℝ)..1, f t) := by rw [intervalIntegral.integral_neg]
  change (∫ t in (0 : ℝ)..1, f t) = 0
  linarith

-- @node: bump_cell_integral_zero
/-- Given [the supplied inputs](hyp:K,hK), [the stated result about bump cell integral zero holds](goal). -/
lemma bump_cell_integral_zero (K : ℕ) (hK : 0 < K) (ℓ : Fin K) :
    (∫ x in ((ℓ.val : ℝ) / K)..(((ℓ.val : ℝ) + 1) / K),
      bump ((K : ℝ) * x - ℓ.val)) = 0 := by
  have h := intervalIntegral.mul_integral_comp_mul_sub
    (f := bump) (K : ℝ) (ℓ.val : ℝ)
    (a := (ℓ.val : ℝ) / K) (b := ((ℓ.val : ℝ) + 1) / K)
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have h' : (K : ℝ) *
      (∫ x in ((ℓ.val : ℝ) / K)..(((ℓ.val : ℝ) + 1) / K),
        bump ((K : ℝ) * x - ℓ.val)) = 0 := by
    convert h using 1 <;> field_simp <;> ring
    exact bump_integral_zero.symm
  exact (mul_eq_zero.mp h').resolve_left hK'

-- @node: tiled_bump_cell_integral_zero
/-- Given [the supplied inputs](hyp:K,hK), [the stated result about tiled bump cell integral zero holds](goal). -/
lemma tiled_bump_cell_integral_zero (K : ℕ) (hK : 0 < K) (ℓ : Fin K) :
    (∫ x in cell K ℓ, bump ((K : ℝ) * x - ℓ.val)) = 0 := by
  unfold cell
  split_ifs with hlast
  · have hend : ((ℓ.val : ℝ) + 1) / K = 1 := by
      have hlast' : (ℓ.val : ℝ) + 1 = K := by exact_mod_cast hlast
      rw [hlast']
      simp [Nat.ne_of_gt hK]
    rw [← hend, integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      apply div_le_div_of_nonneg_right (by linarith : (ℓ.val : ℝ) ≤ (ℓ.val : ℝ) + 1)
      positivity)]
    exact bump_cell_integral_zero K hK ℓ
  · rw [integral_Ico_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      apply div_le_div_of_nonneg_right (by linarith : (ℓ.val : ℝ) ≤ (ℓ.val : ℝ) + 1)
      positivity)]
    exact bump_cell_integral_zero K hK ℓ

-- @node: tiled_bump_odd_ratio_cell_integral_zero
/-- Given [the supplied inputs](hyp:K,hK,h), [the stated result about tiled bump odd ratio cell integral zero holds](goal). -/
lemma tiled_bump_odd_ratio_cell_integral_zero (K : ℕ) (hK : 0 < K)
    (ℓ : Fin K) (h : ℝ) :
    (∫ x in cell K ℓ,
      bump ((K : ℝ) * x - ℓ.val) ^ 3 /
        (1 / 4 - h ^ 2 * bump ((K : ℝ) * x - ℓ.val) ^ 2)) = 0 := by
  let f : ℝ → ℝ := fun t => bump t ^ 3 / (1 / 4 - h ^ 2 * bump t ^ 2)
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hcell : (∫ x in ((ℓ.val : ℝ) / K)..(((ℓ.val : ℝ) + 1) / K),
      f ((K : ℝ) * x - ℓ.val)) = 0 := by
    have hc := intervalIntegral.mul_integral_comp_mul_sub (f := f) (K : ℝ) (ℓ.val : ℝ)
      (a := (ℓ.val : ℝ) / K) (b := ((ℓ.val : ℝ) + 1) / K)
    have heq : (K : ℝ) *
        (∫ x in ((ℓ.val : ℝ) / K)..(((ℓ.val : ℝ) + 1) / K),
          f ((K : ℝ) * x - ℓ.val)) = 0 := by
      convert hc using 1 <;> field_simp <;> ring
      exact (bump_odd_ratio_integral_zero h).symm
    exact (mul_eq_zero.mp heq).resolve_left hK'
  unfold cell
  split_ifs with hlast
  · have hend : ((ℓ.val : ℝ) + 1) / K = 1 := by
      have hlast' : (ℓ.val : ℝ) + 1 = K := by exact_mod_cast hlast
      rw [hlast']
      simp [hK']
    change (∫ x in Set.Icc _ _, f ((K : ℝ) * x - ℓ.val)) = 0
    rw [← hend, integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by
      apply div_le_div_of_nonneg_right (by linarith) (by exact_mod_cast hK.le))]
    exact hcell
  · change (∫ x in Set.Ico _ _, f ((K : ℝ) * x - ℓ.val)) = 0
    rw [integral_Ico_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by
      apply div_le_div_of_nonneg_right (by linarith) (by exact_mod_cast hK.le))]
    exact hcell

-- @node: cell_subset_covariateSpace
/-- Given [the supplied inputs](hyp:K,hK,i), [the stated result about cell subset covariate space holds](goal). -/
lemma cell_subset_covariateSpace (K : ℕ) (hK : 0 < K) (i : Fin K) :
    cell K i ⊆ covariateSpace := by
  intro x hx
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hir : (i.val : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
  unfold cell at hx
  unfold covariateSpace
  split_ifs at hx with hlast
  · rcases hx with ⟨hlo, hhi⟩
    exact ⟨le_trans (by positivity) hlo, hhi⟩
  · rcases hx with ⟨hlo, hhi⟩
    exact ⟨le_trans (by positivity) hlo,
      le_trans hhi.le (by apply (div_le_iff₀ hKr).2; simpa using hir)⟩

-- @node: tiledPerturbation_integrable_and_integral_zero
/-- Given [the supplied inputs](hyp:cStar,n,sgn,hn), [the stated result about tiled perturbation integrable and integral zero holds](goal). -/
lemma tiledPerturbation_integrable_and_integral_zero (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hn : 0 < n) :
    IntegrableOn (tiledPerturbation cStar n sgn) covariateSpace ∧
    (∫ x in covariateSpace, tiledPerturbation cStar n sgn x) = 0 := by
  classical
  have hK : 0 < lowerCells n := by
    unfold lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  have hcell (i : Fin (lowerCells n)) : MeasurableSet (cell (lowerCells n) i) := by
    unfold cell
    split_ifs <;> measurability
  have hcont (i : Fin (lowerCells n)) :
      Continuous (fun x : ℝ =>
        lowerHeight cStar n * sign (sgn i) *
          bump ((lowerCells n : ℝ) * x - i.val)) := by
    unfold bump
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hint (i : Fin (lowerCells n)) :
      Integrable (fun x : ℝ =>
        if x ∈ cell (lowerCells n) i then
          lowerHeight cStar n * sign (sgn i) *
            bump ((lowerCells n : ℝ) * x - i.val) else 0)
        (volume.restrict covariateSpace) := by
    have hm : Measurable (fun x : ℝ =>
        if x ∈ cell (lowerCells n) i then
          lowerHeight cStar n * sign (sgn i) *
            bump ((lowerCells n : ℝ) * x - i.val) else 0) :=
      (hcont i).measurable.ite (hcell i) measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable (|lowerHeight cStar n|)
    filter_upwards [] with x
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hs : |sign (sgn i)| = 1 := by cases sgn i <;> simp [sign]
      have hb : |bump ((lowerCells n : ℝ) * x - i.val)| ≤ 1 := by
        simpa [bump] using Real.abs_sin_le_one
          (2 * Real.pi * ((lowerCells n : ℝ) * x - i.val))
      rw [hs, mul_one]
      exact mul_le_of_le_one_right (abs_nonneg _) hb
    · simp
  constructor
  · unfold tiledPerturbation
    exact integrable_finsetSum Finset.univ (fun i _ => hint i)
  simp only [tiledPerturbation]
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  apply Finset.sum_eq_zero
  intro i _
  have h := integral_indicator (μ := volume.restrict covariateSpace)
    (s := cell (lowerCells n) i)
    (f := fun x : ℝ => lowerHeight cStar n * sign (sgn i) *
      bump ((lowerCells n : ℝ) * x - i.val)) (hcell i)
  simp only [Set.indicator] at h
  rw [h]
  rw [Measure.restrict_restrict_of_subset (cell_subset_covariateSpace _ hK i)]
  rw [integral_const_mul]
  simp [tiled_bump_cell_integral_zero _ hK i]

-- @node: separation_integral_bounds
/-- Given [the supplied inputs](hyp:h,hh), [the stated result about separation integral bounds holds](goal). -/
lemma separation_integral_bounds (h : ℝ) (hh : h ^ 2 ≤ 1 / 8) :
    2 ≤ (∫ t in (0 : ℝ)..1,
      bump t ^ 2 / (1 / 4 - h ^ 2 * bump t ^ 2)) ∧
    (∫ t in (0 : ℝ)..1,
      bump t ^ 2 / (1 / 4 - h ^ 2 * bump t ^ 2)) ≤ 4 := by
  have hs (t : ℝ) : bump t ^ 2 ≤ 1 := by
    have ha : |bump t| ≤ 1 := by
      simpa [bump] using Real.abs_sin_le_one (2 * Real.pi * t)
    rcases abs_le.mp ha with ⟨hl, hu⟩
    nlinarith
  have hd (t : ℝ) : 0 < 1 / 4 - h ^ 2 * bump t ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left (hs t) (sq_nonneg h)
    nlinarith
  have hb : Continuous bump := by unfold bump; fun_prop
  have hcont : Continuous (fun t : ℝ =>
      bump t ^ 2 / (1 / 4 - h ^ 2 * bump t ^ 2)) :=
    (hb.pow 2).div (continuous_const.sub (continuous_const.mul (hb.pow 2)))
      (fun t => ne_of_gt (hd t))
  have hlo (t : ℝ) : 4 * bump t ^ 2 ≤
      bump t ^ 2 / (1 / 4 - h ^ 2 * bump t ^ 2) := by
    rw [le_div_iff₀ (hd t)]
    nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg (bump t ^ 2))]
  have hhi (t : ℝ) :
      bump t ^ 2 / (1 / 4 - h ^ 2 * bump t ^ 2) ≤
        8 * bump t ^ 2 := by
    rw [div_le_iff₀ (hd t)]
    have hp := mul_le_mul_of_nonneg_left (hs t) (sq_nonneg h)
    nlinarith [sq_nonneg (bump t)]
  have hlower := intervalIntegral.integral_mono (μ := volume) (a := (0 : ℝ)) (b := 1)
    (by norm_num)
    ((continuous_const.mul (hb.pow 2)).intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1) hlo
  have hupper := intervalIntegral.integral_mono (μ := volume) (a := (0 : ℝ)) (b := 1)
    (by norm_num) (hcont.intervalIntegrable 0 1)
    ((continuous_const.mul (hb.pow 2)).intervalIntegrable 0 1)
    hhi
  change (∫ t in (0 : ℝ)..1, 4 * bump t ^ 2) ≤ _ at hlower
  change _ ≤ (∫ t in (0 : ℝ)..1, 8 * bump t ^ 2) at hupper
  rw [intervalIntegral.integral_const_mul] at hlower hupper
  rw [bump_sq_integral] at hlower hupper
  norm_num at hlower hupper
  exact ⟨hlower, hupper⟩

-- @node: primitiveMass_complier_sum
/-- Given [the supplied inputs](hyp:a,u,v,ha,s,x), [the stated result about primitive mass complier sum holds](goal). -/
lemma primitiveMass_complier_sum (a u v : ℝ) (ha : a ≠ 0)
    (s : Bool) (x : ℝ) :
    (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      primitiveMass a u v d0 d1 y0 y1 *
        complier (s, x, d0, d1, boolReal y0, boolReal y1)) = a := by
  simp [primitiveMass, complier, complierMargin, sign, receipt1, receipt0, receiptBase]
  field_simp
  ring

-- @node: primitiveMass_complier_outcome_sum
/-- Given [the supplied inputs](hyp:a,u,v,ha,s,x), [the stated result about primitive mass complier outcome sum holds](goal). -/
lemma primitiveMass_complier_outcome_sum (a u v : ℝ) (ha : a ≠ 0)
    (s : Bool) (x : ℝ) :
    (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      primitiveMass a u v d0 d1 y0 y1 *
        ((outcome1 (s, x, d0, d1, boolReal y0, boolReal y1) -
          outcome0 (s, x, d0, d1, boolReal y0, boolReal y1)) *
          complier (s, x, d0, d1, boolReal y0, boolReal y1))) =
      -(u * v) / (1 / 4 - u ^ 2) := by
  simp [primitiveMass, complier, complierMargin, sign, receipt1, receipt0,
    receiptBase, outcome1, outcome0, boolReal]
  field_simp
  ring

-- @node: lowerPointwiseMean_complier_margins
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,s,x,ha), [the stated result about lower pointwise mean complier margins holds](goal). -/
lemma lowerPointwiseMean_complier_margins (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) (s : Bool) (x : ℝ)
    (ha : actualStrength a n ≠ 0) :
    lowerPointwiseMean a n cStar τ sgn s complier x = actualStrength a n ∧
    lowerPointwiseMean a n cStar τ sgn s
      (fun o => (outcome1 o - outcome0 o) * complier o) x =
      -(tiledPerturbation cStar n sgn x *
        coupledPerturbation cStar τ n sgn x) /
        (1 / 4 - tiledPerturbation cStar n sgn x ^ 2) := by
  constructor
  · simpa [lowerPointwiseMean, lowerMass] using
      primitiveMass_complier_sum (actualStrength a n)
        (tiledPerturbation cStar n sgn x)
        (coupledPerturbation cStar τ n sgn x) ha s x
  · simpa [lowerPointwiseMean, lowerMass] using
      primitiveMass_complier_outcome_sum (actualStrength a n)
        (tiledPerturbation cStar n sgn x)
        (coupledPerturbation cStar τ n sgn x) ha s x

-- @node: armMeanFrom_primitive_receipt_contrast
/-- Given [the supplied inputs](hyp:a,u,v,x,ha), [the stated result about arm mean from primitive receipt contrast holds](goal). -/
lemma armMeanFrom_primitive_receipt_contrast (a u v x : ℝ) (ha : a ≠ 0) :
    armMeanFrom (fun _ => primitiveMass a u v) false true x -
      armMeanFrom (fun _ => primitiveMass a u v) false false x = a := by
  simp [armMeanFrom, primitiveMass, complierMargin, receiptBase, sign, boolReal]
  field_simp
  ring

-- @node: armMeanFrom_primitive_outcome_contrast
/-- Given [the supplied inputs](hyp:a,u,v,x,ha), [the stated result about arm mean from primitive outcome contrast holds](goal). -/
lemma armMeanFrom_primitive_outcome_contrast (a u v x : ℝ) (ha : a ≠ 0) :
    armMeanFrom (fun _ => primitiveMass a u v) true true x -
      armMeanFrom (fun _ => primitiveMass a u v) true false x =
        -(u * v) / (1 / 4 - u ^ 2) := by
  simp [armMeanFrom, primitiveMass, complierMargin, receiptBase, sign, boolReal]
  field_simp
  ring

-- @node: legalIVComponent_arm_contrasts
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,x,ha), [the stated result about legal ivcomponent arm contrasts holds](goal). -/
lemma legalIVComponent_arm_contrasts (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) (x : ℝ)
    (ha : actualStrength a n ≠ 0) :
    armContrast (legalIVComponent a n cStar τ sgn) false x = actualStrength a n ∧
    armContrast (legalIVComponent a n cStar τ sgn) true x =
      -(tiledPerturbation cStar n sgn x *
        coupledPerturbation cStar τ n sgn x) /
        (1 / 4 - tiledPerturbation cStar n sgn x ^ 2) := by
  constructor
  · simpa [armContrast, legalIVComponent, lawFromMass, lowerMass, armMeanFrom] using
      armMeanFrom_primitive_receipt_contrast (actualStrength a n)
        (tiledPerturbation cStar n sgn x)
        (coupledPerturbation cStar τ n sgn x) x ha
  · simpa [armContrast, legalIVComponent, lawFromMass, lowerMass, armMeanFrom] using
      armMeanFrom_primitive_outcome_contrast (actualStrength a n)
        (tiledPerturbation cStar n sgn x)
        (coupledPerturbation cStar τ n sgn x) x ha

-- @node: mixtureCenter_arm_contrasts
/-- Given [the supplied inputs](hyp:a,n,ha,x), [the stated result about mixture center arm contrasts holds](goal). -/
lemma mixtureCenter_arm_contrasts (a : ℝ) (n : ℕ)
    (ha : actualStrength a n ≠ 0) (x : ℝ) :
    armContrast (mixtureCenter a n) false x = actualStrength a n ∧
    armContrast (mixtureCenter a n) true x = 0 := by
  constructor
  · simpa [armContrast, mixtureCenter, lawFromMass] using
      armMeanFrom_primitive_receipt_contrast (actualStrength a n) 0 0 x ha
  · simpa [armContrast, mixtureCenter, lawFromMass] using
      armMeanFrom_primitive_outcome_contrast (actualStrength a n) 0 0 x ha

-- @node: mixtureCenter_firstStage
/-- Given [the supplied inputs](hyp:a,n,ha), [the stated result about mixture center first stage holds](goal). -/
lemma mixtureCenter_firstStage (a : ℝ) (n : ℕ)
    (ha : actualStrength a n ≠ 0) :
    firstStage (mixtureCenter a n) = actualStrength a n := by
  have h (x : ℝ) := (mixtureCenter_arm_contrasts a n ha x).1
  simp_rw [firstStage, transportedForm, h]
  simp [mixtureCenter, lawFromMass, covariateSpace]

-- @node: mixtureCenter_transportedOutcome
/-- Given [the supplied inputs](hyp:a,n,ha), [the stated result about mixture center transported outcome holds](goal). -/
lemma mixtureCenter_transportedOutcome (a : ℝ) (n : ℕ)
    (ha : actualStrength a n ≠ 0) :
    transportedForm (mixtureCenter a n) true = 0 := by
  have h (x : ℝ) := (mixtureCenter_arm_contrasts a n ha x).2
  simp_rw [transportedForm, h]
  simp
/-- Given [the supplied inputs](hyp:n,hn,cStar,hc), [the stated result about legal mixture separation holds](goal). -/

lemma legal_mixture_separation (n : ℕ) (hn : threshold ≤ n)
    (cStar : ℝ) (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    2 ^ ((3 : ℝ) / 4) * cStar ^ 2 *
      (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ separation cStar n ∧
    separation cStar n ≤ 4 * cStar ^ 2 *
      (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hn256 : 256 ≤ n := hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hbase : (1 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := by
    simpa using Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hKlo : (n : ℝ) ^ ((4 : ℝ) / 3) ≤ lowerCells n := by
    unfold lowerCells
    exact Nat.le_ceil _
  have hKhi : (lowerCells n : ℝ) ≤
      2 * (n : ℝ) ^ ((4 : ℝ) / 3) := by
    unfold lowerCells
    exact Nat.ceil_le_two_mul (by linarith : (2 : ℝ)⁻¹ ≤ (n : ℝ) ^ ((4 : ℝ) / 3))
  have hKpos : (0 : ℝ) < lowerCells n := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hbase) hKlo
  have hfac : (lowerCells n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_trans hbase hKlo) (by norm_num)
  have hh0 : 0 ≤ lowerHeight cStar n := by
    unfold lowerHeight
    exact mul_nonneg hc.1.le (Real.rpow_nonneg hKpos.le _)
  have hhsmall : lowerHeight cStar n ≤ 1 / 100 := by
    unfold lowerHeight
    nlinarith [mul_le_mul_of_nonneg_left hfac (le_of_lt hc.1)]
  have hhsq : lowerHeight cStar n ^ 2 ≤ 1 / 8 := by nlinarith
  have hI := separation_integral_bounds (lowerHeight cStar n) hhsq
  have hpow : lowerHeight cStar n ^ 2 =
      cStar ^ 2 * (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    unfold lowerHeight
    rw [mul_pow, ← Real.rpow_mul_natCast (le_of_lt hKpos)]
    norm_num
  have hrootHi : (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hbase) hKlo
      (by norm_num : (-(1 / 4 : ℝ)) ≤ 0)
    rw [← Real.rpow_mul hnpos.le] at h
    convert h using 1 <;> congr 1 <;> ring
  have hrootLo :
      (2 * (n : ℝ) ^ ((4 : ℝ) / 3)) ^ (-(1 / 4 : ℝ)) ≤
        (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hKpos hKhi (by norm_num)
  have hpowLo : 2 ^ ((3 : ℝ) / 4) *
      (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
      2 * (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have heq : 2 * (2 * (n : ℝ) ^ ((4 : ℝ) / 3)) ^ (-(1 / 4 : ℝ)) =
        2 ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (le_of_lt (Real.rpow_pos_of_pos hnpos _)), ← Real.rpow_mul hnpos.le]
      have hexp : (4 / 3 : ℝ) * (-(1 / 4 : ℝ)) = -(1 / 3 : ℝ) := by ring
      rw [hexp]
      have htwo : 2 * (2 : ℝ) ^ (-(1 / 4 : ℝ)) = 2 ^ ((3 : ℝ) / 4) := by
        nth_rw 1 [← Real.rpow_one (2 : ℝ)]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1 <;> ring
      rw [← htwo]
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hrootLo (by norm_num)
  unfold separation
  constructor
  · calc
      2 ^ ((3 : ℝ) / 4) * cStar ^ 2 * (n : ℝ) ^ (-(1 / 3 : ℝ)) =
          cStar ^ 2 * (2 ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ cStar ^ 2 * (2 * (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpowLo (sq_nonneg _)
      _ = 2 * lowerHeight cStar n ^ 2 := by rw [hpow]; ring
      _ ≤ lowerHeight cStar n ^ 2 *
          (∫ t in (0 : ℝ)..1,
            bump t ^ 2 / (1 / 4 - lowerHeight cStar n ^ 2 * bump t ^ 2)) := by
        nlinarith [hI.1, sq_nonneg (lowerHeight cStar n)]
  · calc
      lowerHeight cStar n ^ 2 *
          (∫ t in (0 : ℝ)..1,
            bump t ^ 2 / (1 / 4 - lowerHeight cStar n ^ 2 * bump t ^ 2)) ≤
        4 * lowerHeight cStar n ^ 2 := by
          nlinarith [hI.2, sq_nonneg (lowerHeight cStar n)]
      _ = 4 * cStar ^ 2 * (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [hpow]; ring
      _ ≤ 4 * cStar ^ 2 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
        gcongr

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
