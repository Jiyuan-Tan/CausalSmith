module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorPair
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Stat.Minimax.MinimaxRisk

/-!
Scaled diagnostic KL and testing bounds for the rare-label pair, including common randomness.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:d,hd,hdelta,heps,heps',eps,delta), The diagnostic pair has the stated KL formula at every legal amplitude.  This gives [the stated result](goal).-/
-- @node: labelFloor_KL_formula
lemma labelFloor_KL_formula (d : Nat) (eps delta : Real) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    finiteKL (labelFloorLaw d eps delta true hd hdelta)
      (labelFloorLaw d eps delta false hd hdelta) =
      2 * eps * delta * Real.log ((1 / 2 + delta) / (1 / 2 - delta)) := by
  have heps0 : eps ≠ 0 := heps.ne'
  have heps1 : 1 - eps ≠ 0 := by linarith
  have hlog : Real.log ((1 / 2 - delta) / (1 / 2 + delta)) =
      -Real.log ((1 / 2 + delta) / (1 / 2 - delta)) := by
    rw [← inv_div, Real.log_inv]
  unfold finiteKL
  change (∑ z : Obs d,
    jointMass (labelFloorLaw d eps delta true hd hdelta) z.1 z.2.1 z.2.2 *
      Real.log (jointMass (labelFloorLaw d eps delta true hd hdelta) z.1 z.2.1 z.2.2 /
        jointMass (labelFloorLaw d eps delta false hd hdelta) z.1 z.2.1 z.2.2)) = _
  simp only [Fintype.sum_prod_type]
  have hcell (j : Fin d) :
      (∑ a : Bool, ∑ y : Bool,
        jointMass (labelFloorLaw d eps delta true hd hdelta) j a y *
          Real.log (jointMass (labelFloorLaw d eps delta true hd hdelta) j a y /
            jointMass (labelFloorLaw d eps delta false hd hdelta) j a y)) =
      if j.val < 2 then eps * delta * Real.log ((1 / 2 + delta) / (1 / 2 - delta)) else 0 := by
    simp only [labelFloor_jointMass d eps delta true hd hdelta heps heps',
      labelFloor_jointMass d eps delta false hd hdelta heps heps', Fintype.sum_bool]
    by_cases hj : j.val < 2
    · simp [hj, bernoulliMass, ← sub_eq_add_neg]
      rw [mul_div_mul_left _ _ (mul_ne_zero (by norm_num : (2 : Real)⁻¹ ≠ 0) heps0),
        mul_div_mul_left _ _ (mul_ne_zero (by norm_num : (2 : Real)⁻¹ ≠ 0) heps0)]
      rw [show (1 - (2⁻¹ + delta) : Real) = 1 / 2 - delta by ring,
        show (1 - (2⁻¹ - delta) : Real) = 1 / 2 + delta by ring, hlog]
      ring
    · simp [hj]
  simp_rw [hcell]
  rw [labelFloor_sum_two_cells d hd]
  ring

/-- [Under the stated inputs and conditions](hyp:d,hd,hdelta,heps,heps',eps,delta), The diagnostic one-record KL is bounded by sixteen times overlap times amplitude squared.  This gives [the stated result](goal).-/
-- @node: labelFloor_KL_bound
lemma labelFloor_KL_bound (d : Nat) (eps delta : Real) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    finiteKL (labelFloorLaw d eps delta true hd hdelta)
      (labelFloorLaw d eps delta false hd hdelta) ≤ 16 * eps * delta ^ 2 := by
  have hd0 := hdelta.1
  have hd1 := hdelta.2
  have hden : 0 < (1 / 2 : Real) - delta := by linarith
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (show (0 : Real) < 1 / 2 + delta by linarith) hden)
  have hratio : (1 / 2 + delta) / (1 / 2 - delta) - 1 ≤ 8 * delta := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hden).2
    nlinarith
  rw [labelFloor_KL_formula d eps delta hd hdelta heps heps']
  calc
    _ ≤ (2 * eps * delta) * (8 * delta) :=
      mul_le_mul_of_nonneg_left (hlog.trans hratio) (by positivity)
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:d,hd,hdelta,heps,heps',eps,delta), The diagnostic laws have common support even when the remaining cells are null.  This gives [the stated result](goal).-/
-- @node: labelFloor_absolutelyContinuous
lemma labelFloor_absolutelyContinuous (d : Nat) (eps delta : Real) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    obsLaw (labelFloorLaw d eps delta true hd hdelta) ≪
      obsLaw (labelFloorLaw d eps delta false hd hdelta) := by
  let P := labelFloorLaw d eps delta true hd hdelta
  let Q := labelFloorLaw d eps delta false hd hdelta
  have hsupport (z : Obs d) (hq : Q.pmf z = 0) : P.pmf z = 0 := by
    have hqreal : jointMass Q z.1 z.2.1 z.2.2 = 0 := by
      change (Q.pmf z).toReal = 0
      rw [hq, ENNReal.toReal_zero]
    have hj : ¬z.1.val < 2 := by
      intro hj
      rw [labelFloor_jointMass d eps delta false hd hdelta heps heps', if_pos hj] at hqreal
      have hp : 0 < (1 / 2 : Real) * bernoulliMass eps z.2.1 *
          bernoulliMass (if z.2.1 then 1 / 2 - delta else 1 / 2) z.2.2 := by
        have hδ := hdelta.2
        have he1 : 0 < 1 - eps := by linarith
        have hd1 : 0 < 1 / 2 - delta := by linarith
        have hd2 : 0 < 1 - (1 / 2 - delta) := by linarith [hdelta.1]
        cases ha : z.2.1 <;> cases hy : z.2.2 <;> dsimp [bernoulliMass] <;> positivity
      simpa only [Bool.false_eq_true, if_false, ← sub_eq_add_neg] using hp.ne' hqreal
    apply (ENNReal.toReal_eq_toReal_iff'
      (P.pmf.apply_ne_top z) ENNReal.zero_ne_top).mp
    change jointMass P z.1 z.2.1 z.2.2 = 0
    rw [labelFloor_jointMass d eps delta true hd hdelta heps heps', if_neg hj]
  intro s hs
  change P.pmf.toMeasure s = 0
  rw [P.pmf.toMeasure_apply_eq_toOuterMeasure_apply (by exact Set.toFinite s |>.countable.measurableSet),
    PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  by_cases hz : z ∈ s
  · have hq : Q.pmf z = 0 := by
      have h := measure_mono_null (Set.singleton_subset_iff.mpr hz) hs
      simpa [obsLaw, Q] using h
    simp [Set.indicator_of_mem hz, hsupport z hq]
  · simp [Set.indicator_of_notMem hz]

/-- [Under the stated inputs and conditions](hyp:hd,hdelta,heps,heps',n,d,eps,delta), The ordered labeled arrays have divergence at most sixteen times their rare-label scale.  This gives [the stated result](goal).-/
-- @node: labelFloor_labeled_KL_bound
lemma labelFloor_labeled_KL_bound (n d : Nat) (eps delta : Real) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    InformationTheory.klDiv
      (labeledProductLaw (labelFloorLaw d eps delta true hd hdelta) n)
      (labeledProductLaw (labelFloorLaw d eps delta false hd hdelta) n) ≠ ⊤ ∧
    (InformationTheory.klDiv
      (labeledProductLaw (labelFloorLaw d eps delta true hd hdelta) n)
      (labeledProductLaw (labelFloorLaw d eps delta false hd hdelta) n)).toReal ≤
      16 * ((n : Real) * eps) * delta ^ 2 := by
  let P := labelFloorLaw d eps delta true hd hdelta
  let Q := labelFloorLaw d eps delta false hd hdelta
  letI : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  letI : IsProbabilityMeasure (obsLaw Q) := by unfold obsLaw; infer_instance
  have hac := labelFloor_absolutelyContinuous d eps delta hd hdelta heps heps'
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization n
    (obsLaw P) (obsLaw Q) hac (by exact Integrable.of_finite)
  refine ⟨ht.1, ?_⟩
  have hKL : (InformationTheory.klDiv (obsLaw P) (obsLaw Q)).toReal = finiteKL P Q := by
    rw [Causalean.Mathlib.InformationTheory.klDiv_toReal_eq_sum_measureReal _ _ hac]
    simp [obsLaw, finiteKL, Measure.real_def, P, Q]
  calc
    _ ≤ (n : Real) * (InformationTheory.klDiv (obsLaw P) (obsLaw Q)).toReal := ht.2.2
    _ = (n : Real) * finiteKL P Q := by rw [hKL]
    _ ≤ (n : Real) * (16 * eps * delta ^ 2) :=
      mul_le_mul_of_nonneg_left (labelFloor_KL_bound d eps delta hd hdelta heps heps')
        (Nat.cast_nonneg _)
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:S), Squaring the chosen amplitude gives the inverse maximum-scale expression.  This gives [the stated result](goal).-/
-- @node: labelFloor_scaled_square
lemma labelFloor_scaled_square (S : Real) :
    (1 / (16 * Real.sqrt (max 1 S))) ^ 2 = 1 / (256 * max 1 S) := by
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- [Under the stated inputs and conditions](hyp:eps,hd,heps,heps',n,d), The scaled labeled pair is uniformly close in total variation.  This gives [the stated result](goal).-/
-- @node: labelFloor_scaled_tv
lemma labelFloor_scaled_tv (n d : Nat) (eps : Real) (hd : 2 ≤ d)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    Causalean.Stat.tvDist
      (labeledProductLaw (labelFloorLaw d eps
        (1 / (16 * Real.sqrt (max 1 ((n : Real) * eps)))) true hd
        (labelFloorAmplitude_scaled _)) n)
      (labeledProductLaw (labelFloorLaw d eps
        (1 / (16 * Real.sqrt (max 1 ((n : Real) * eps)))) false hd
        (labelFloorAmplitude_scaled _)) n) ≤ 1 / 4 := by
  let delta := 1 / (16 * Real.sqrt (max 1 ((n : Real) * eps)))
  let hdelta := labelFloorAmplitude_scaled ((n : Real) * eps)
  let P := labelFloorLaw d eps delta true hd hdelta
  let Q := labelFloorLaw d eps delta false hd hdelta
  letI : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  letI : IsProbabilityMeasure (obsLaw Q) := by unfold obsLaw; infer_instance
  letI : IsProbabilityMeasure (labeledProductLaw P n) := by unfold labeledProductLaw; infer_instance
  letI : IsProbabilityMeasure (labeledProductLaw Q n) := by unfold labeledProductLaw; infer_instance
  have hac := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
    (obsLaw P) (obsLaw Q) (labelFloor_absolutelyContinuous d eps delta hd hdelta heps heps') n
  obtain ⟨hfin, hKL⟩ := labelFloor_labeled_KL_bound n d eps delta hd hdelta heps heps'
  have hbudget : 16 * ((n : Real) * eps) * delta ^ 2 ≤ 1 / 16 := by
    rw [show delta ^ 2 = 1 / (256 * max 1 ((n : Real) * eps)) from labelFloor_scaled_square _]
    have hmax : 0 < max 1 ((n : Real) * eps) := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 16)).2
    field_simp
    nlinarith [le_max_right (1 : Real) ((n : Real) * eps)]
  have htv := Causalean.Stat.pinskerBound_of_ac_of_ne_top
    (labeledProductLaw P n) (labeledProductLaw Q n) hac hfin
  apply htv.trans
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · nlinarith [hKL.trans hbudget]

/-- [Under the stated inputs and conditions](hyp:n,eps,hn,heps), The amplitude squared divided by four is exactly the asserted label benchmark constant.  This gives [the stated result](goal).-/
-- @node: labelFloor_scaled_rate
lemma labelFloor_scaled_rate (n : Nat) (eps : Real) (hn : 1 ≤ n) (heps : 0 < eps) :
    (1 / (16 * Real.sqrt (max 1 ((n : Real) * eps)))) ^ 2 / 4 =
      (1 / 1024 : Real) * labelBenchmark n eps := by
  have hS : 0 < (n : Real) * eps := mul_pos (by exact_mod_cast (show 0 < n by omega)) heps
  rw [labelFloor_scaled_square]
  dsimp [labelBenchmark, labelScale]
  by_cases h : (n : Real) * eps ≤ 1
  · rw [max_eq_left h, min_eq_left ((one_le_inv₀ hS).2 h)]
    norm_num
  · rw [max_eq_right (le_of_not_ge h), min_eq_right (inv_le_one_of_one_le₀ (le_of_not_ge h))]
    ring

/-- [Under the stated inputs and conditions](hyp:Z,delta,hd,htv,T,hT,hbound,mu,nu), A close pair with opposite targets forces squared loss for every clipped Borel rule.  This gives [the stated result](goal).-/
-- @node: labelFloor_testing_mse
lemma labelFloor_testing_mse {Z : Type*} [MeasurableSpace Z]
    (mu nu : Measure Z) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (delta : Real) (hd : 0 ≤ delta) (htv : Causalean.Stat.tvDist mu nu ≤ 1 / 4)
    (T : Z → Real) (hT : Measurable T) (hbound : ∀ z, T z ∈ Set.Icc (-1) 1) :
    delta ^ 2 / 4 ≤ max (∫ z, (T z - delta) ^ 2 ∂mu) (∫ z, (T z - -delta) ^ 2 ∂nu) := by
  have hsep : 2 * delta ≤ dist delta (-delta) := by
    rw [Real.dist_eq, show delta - -delta = 2 * delta by ring, abs_of_nonneg (by positivity)]
  have htest := Causalean.Stat.half_one_sub_tvDist_le_max_error
    (P₀ := mu) (P₁ := nu) hT hsep
  have hloss (rho : Measure Z) [IsProbabilityMeasure rho] (theta : Real) :
      delta ^ 2 * rho.real {z | delta ≤ dist (T z) theta} ≤
        ∫ z, (T z - theta) ^ 2 ∂rho := by
    have hset : {z | delta ≤ dist (T z) theta} =
        {z | delta ^ 2 ≤ (T z - theta) ^ 2} := by
      ext z
      simp only [Set.mem_setOf_eq, Real.dist_eq]
      constructor <;> intro h <;>
        nlinarith [abs_nonneg (T z - theta), sq_abs (T z - theta)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg _))
      (Causalean.Stat.mse_integrable_of_estimator_bound rho T hT (by norm_num) hbound) _
  have hmax := max_le_max (hloss mu delta) (hloss nu (-delta))
  rw [← mul_max_of_nonneg _ _ (sq_nonneg delta)] at hmax
  have hfloor : (1 / 4 : Real) ≤
      max (mu.real {z | delta ≤ dist (T z) delta})
        (nu.real {z | delta ≤ dist (T z) (-delta)}) := by linarith
  exact (show delta ^ 2 / 4 = delta ^ 2 * (1 / 4 : Real) by ring).le.trans
    ((mul_le_mul_of_nonneg_left hfloor (sq_nonneg delta)).trans hmax)

/-- [Under the stated inputs and conditions](hyp:rho,A,B,mu,nu), Adjoining an independent common probability law preserves total variation.  This gives [the stated result](goal).-/
-- @node: labelFloor_tv_common_product
lemma labelFloor_tv_common_product {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) (rho : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure rho] :
    Causalean.Stat.tvDist (mu.prod rho) (nu.prod rho) = Causalean.Stat.tvDist mu nu := by
  simpa only [Measure.compProd_const] using
    Causalean.Stat.tvDist_compProd_eq mu nu (Kernel.const A rho)

/-- [Under the stated inputs and conditions](hyp:Z,rho,T,hbound,theta,htheta), Clipping the rule and target bounds squared risk by four under any probability law.  This gives [the stated result](goal).-/
-- @node: labelFloor_bounded_mse
lemma labelFloor_bounded_mse {Z : Type*} [MeasurableSpace Z]
    (rho : Measure Z) [IsProbabilityMeasure rho] (T : Z → Real)
    (hbound : ∀ z, T z ∈ Set.Icc (-1) 1) (theta : Real) (htheta : theta ∈ Set.Icc (-1) 1) :
    (∫ z, (T z - theta) ^ 2 ∂rho) ≤ 4 := by
  have hpoint (z : Z) : (T z - theta) ^ 2 ≤ 4 := by
    have h := hbound z
    have habs : |T z - theta| ≤ 2 := abs_le.mpr ⟨by linarith [h.1, htheta.2],
      by linarith [h.2, htheta.1]⟩
    nlinarith [sq_abs (T z - theta), abs_nonneg (T z - theta)]
  have h := integral_mono_of_nonneg (μ := rho)
    (Filter.Eventually.of_forall (fun z => sq_nonneg (T z - theta)))
    (integrable_const (4 : Real)) (Filter.Eventually.of_forall hpoint)
  simpa using h

end CausalSmith.Stat.AnnotationRarearmFrontier
