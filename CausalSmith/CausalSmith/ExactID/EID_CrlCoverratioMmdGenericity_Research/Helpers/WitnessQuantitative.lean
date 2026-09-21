module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessSigns
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rational bounds for the explicit sparse witness

This file isolates the elementary exponential and rational estimates used in
the quantitative moment and Gaussian-MMD certificate.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- The one-dimensional weight appearing after differentiating the sparse
second-moment integrand with respect to its parent coefficient. -/
-- @node: sparseWeight
def sparseWeight (a y : ℝ) : ℝ :=
  exponentialInterventionDensity y ^ 2 /
    (1 + a * centeredCoordinate y) ^ 2

/-- The logarithmic derivative of the sparse weight has the explicit form used
in the quantitative moment-gap argument.  Given [the stated inputs and conditions](hyp:hden), [the stated conclusion](goal) follows. -/
-- @node: sparseWeight_log_hasDerivAt
lemma sparseWeight_log_hasDerivAt {a y : ℝ}
    (hden : 1 + a * centeredCoordinate y ≠ 0) :
    HasDerivAt (fun z => Real.log (sparseWeight a z))
      (8 - 4 * a / (1 + a * centeredCoordinate y)) y := by
  have hq : HasDerivAt exponentialInterventionDensity
      (4 * exponentialInterventionDensity y) y := by
    simpa [mul_comm] using exponentialInterventionDensity_hasDerivAt y
  have hp0 : HasDerivAt (fun z : ℝ => 2 * z - 1) 2 y := by
    convert (hasDerivAt_const_mul (x := y) 2).sub_const 1 using 1
  have hp : HasDerivAt (fun z : ℝ => 1 + a * centeredCoordinate z) (2 * a) y := by
    simpa only [centeredCoordinate, mul_comm] using (hp0.const_mul a).const_add 1
  have hw := (hq.pow 2).div (hp.pow 2) (pow_ne_zero 2 hden)
  have hwne : sparseWeight a y ≠ 0 := by
    unfold sparseWeight
    exact div_ne_zero
      (pow_ne_zero 2 (ne_of_gt (exponentialInterventionDensity_pos y)))
      (pow_ne_zero 2 hden)
  have hlog := hw.log hwne
  have hqne : exponentialInterventionDensity y ≠ 0 :=
    ne_of_gt (exponentialInterventionDensity_pos y)
  convert hlog using 1
  · rfl
  · simp only [Pi.pow_apply, Pi.div_apply]
    field_simp [hqne, hden]
    ring

/-- For every parent coefficient in `[-1/10,1/10]`, the logarithmic derivative
of the sparse weight is at least `68/9` on the unit interval.  Given [the stated inputs and conditions](hyp:ha,hy), [the stated conclusion](goal) follows. -/
-- @node: sparseWeight_log_deriv_lower_bound
lemma sparseWeight_log_deriv_lower_bound {a y : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (68 / 9 : ℝ) ≤ deriv (fun z => Real.log (sparseWeight a z)) y := by
  have hh := abs_centeredCoordinate_le_one hy
  have ha' : |a| ≤ (1 / 10 : ℝ) := by
    rw [abs_le]
    constructor <;> norm_num at ha ⊢
    · exact ha.1
    · exact ha.2
  have haprod : |a * centeredCoordinate y| ≤ (1 / 10 : ℝ) := by
    rw [abs_mul]
    calc
      |a| * |centeredCoordinate y| ≤ (1 / 10 : ℝ) * 1 :=
        mul_le_mul ha' hh (abs_nonneg _) (by norm_num)
      _ = 1 / 10 := by norm_num
  rw [abs_le] at haprod
  have hden_pos : 0 < 1 + a * centeredCoordinate y := by
    nlinarith [haprod.1]
  have hfactor_nonneg : 0 ≤ 9 - centeredCoordinate y := by
    rw [abs_le] at hh
    linarith
  have hmul := mul_le_mul_of_nonneg_right ha.2 hfactor_nonneg
  have hratio : a / (1 + a * centeredCoordinate y) ≤ (1 / 9 : ℝ) := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [hmul]
  have hratio4 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
  rw [(sparseWeight_log_hasDerivAt hden_pos.ne').deriv]
  rw [show 4 * a / (1 + a * centeredCoordinate y) =
      4 * (a / (1 + a * centeredCoordinate y)) by ring]
  norm_num at hratio4 ⊢
  nlinarith

-- @node: sparseWeight_hasDerivAt
/-- The sparse weight derivative is its value times the explicit logarithmic
derivative factor.  Given [the stated inputs and conditions](hyp:hden), [the stated conclusion](goal) follows. -/
lemma sparseWeight_hasDerivAt {a y : ℝ}
    (hden : 1 + a * centeredCoordinate y ≠ 0) :
    HasDerivAt (sparseWeight a)
      (sparseWeight a y * (8 - 4 * a / (1 + a * centeredCoordinate y))) y := by
  have hq : HasDerivAt exponentialInterventionDensity
      (4 * exponentialInterventionDensity y) y := by
    simpa [mul_comm] using exponentialInterventionDensity_hasDerivAt y
  have hp0 : HasDerivAt (fun z : ℝ => 2 * z - 1) 2 y := by
    convert (hasDerivAt_const_mul (x := y) 2).sub_const 1 using 1
  have hp : HasDerivAt (fun z : ℝ => 1 + a * centeredCoordinate z) (2 * a) y := by
    simpa only [centeredCoordinate, mul_comm] using (hp0.const_mul a).const_add 1
  have hw := (hq.pow 2).div (hp.pow 2) (pow_ne_zero 2 hden)
  change HasDerivAt (sparseWeight a) _ y at hw
  apply hw.congr_deriv
  simp only [Pi.pow_apply]
  unfold sparseWeight
  field_simp [hden]
  ring

-- @node: exp_four_lt_fifty_five
/-- The exponential normalizer in the witness is strictly below `55`.  [the stated conclusion](goal) follows. -/
lemma exp_four_lt_fifty_five : Real.exp 4 < 55 := by
  calc
    Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    _ < (2.7182818286 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    _ < 55 := by norm_num

-- @node: exponentialNormalizer_gt_two_div_twenty_seven
/-- The normalizing constant `4 / (exp 4 - 1)` exceeds `2/27`.  [the stated conclusion](goal) follows. -/
lemma exponentialNormalizer_gt_two_div_twenty_seven :
    (2 / 27 : ℝ) < 4 / (Real.exp 4 - 1) := by
  have hden : 0 < Real.exp 4 - 1 := by linarith [thirteen_lt_exp_four]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 27) hden]
  nlinarith [exp_four_lt_fifty_five]

-- @node: sparseWeight_gt_rational_floor
/-- On the coefficient strip used by the witness, the sparse weight is
strictly above the rational floor obtained from `c > 2/27` and `p₂ ≤ 11/10`.  Given [the stated inputs and conditions](hyp:ha,hy), [the stated conclusion](goal) follows. -/
lemma sparseWeight_gt_rational_floor {a y : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (4 / 729 : ℝ) * (100 / 121) < sparseWeight a y := by
  have hh := abs_centeredCoordinate_le_one hy
  rw [abs_le] at hh
  have hden : 0 < 1 + a * centeredCoordinate y := by
    have ha1 : (-1 / 10 : ℝ) ≤ a := ha.1
    have ha2 : a ≤ (1 / 10 : ℝ) := ha.2
    nlinarith
  have hdenUpper : 1 + a * centeredCoordinate y ≤ (11 / 10 : ℝ) := by
    have ha1 : (-1 / 10 : ℝ) ≤ a := ha.1
    have ha2 : a ≤ (1 / 10 : ℝ) := ha.2
    nlinarith
  have hexp : 1 ≤ Real.exp (4 * y) := Real.one_le_exp (by nlinarith [hy.1])
  have hc := exponentialNormalizer_gt_two_div_twenty_seven
  have hq : (2 / 27 : ℝ) < exponentialInterventionDensity y := by
    unfold exponentialInterventionDensity
    have hnormalizer_pos : 0 < 4 / (Real.exp 4 - 1) := lt_trans (by norm_num) hc
    rw [show 4 * Real.exp (4 * y) / (Real.exp 4 - 1) =
      (4 / (Real.exp 4 - 1)) * Real.exp (4 * y) by ring]
    nlinarith
  have hdenSq : 0 < (1 + a * centeredCoordinate y) ^ 2 := sq_pos_of_pos hden
  have hupperSq : (1 + a * centeredCoordinate y) ^ 2 ≤ (11 / 10 : ℝ) ^ 2 := by
    nlinarith
  have hqSq : (2 / 27 : ℝ) ^ 2 < exponentialInterventionDensity y ^ 2 := by
    nlinarith [exponentialInterventionDensity_pos y]
  unfold sparseWeight
  calc
    (4 / 729 : ℝ) * (100 / 121) =
        (2 / 27 : ℝ) ^ 2 / (11 / 10 : ℝ) ^ 2 := by norm_num
    _ < exponentialInterventionDensity y ^ 2 /
        (1 + a * centeredCoordinate y) ^ 2 := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < (11 / 10) ^ 2) hdenSq]
      have hleft := mul_le_mul_of_nonneg_left hupperSq
        (sq_nonneg (2 / 27 : ℝ))
      have hright := mul_lt_mul_of_pos_right hqSq
        (by norm_num : (0 : ℝ) < (11 / 10) ^ 2)
      exact lt_of_le_of_lt hleft hright

-- @node: sparseWeight_deriv_gt_rational_floor
/-- The derivative of the sparse weight has the uniform rational lower bound
used in the moment certificate.  Given [the stated inputs and conditions](hyp:ha,hy), [the stated conclusion](goal) follows. -/
lemma sparseWeight_deriv_gt_rational_floor {a y : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (68 / 9 : ℝ) * ((4 / 729) * (100 / 121)) < deriv (sparseWeight a) y := by
  have hden : 0 < 1 + a * centeredCoordinate y := by
    have hh := abs_centeredCoordinate_le_one hy
    rw [abs_le] at hh
    have ha1 : (-1 / 10 : ℝ) ≤ a := ha.1
    have ha2 : a ≤ (1 / 10 : ℝ) := ha.2
    nlinarith
  have hw := sparseWeight_gt_rational_floor ha hy
  have hlog := sparseWeight_log_deriv_lower_bound ha hy
  have hfactor : (68 / 9 : ℝ) ≤
      8 - 4 * a / (1 + a * centeredCoordinate y) := by
    simpa [(sparseWeight_log_hasDerivAt hden.ne').deriv] using hlog
  rw [(sparseWeight_hasDerivAt hden.ne').deriv]
  have hfloor : 0 < (4 / 729 : ℝ) * (100 / 121) := by norm_num
  have hfactorPos : 0 < 8 - 4 * a / (1 + a * centeredCoordinate y) :=
    lt_of_lt_of_le (by norm_num) hfactor
  nlinarith

-- @node: sparseWeight_secant_lower_bound
/-- The derivative certificate integrates to a uniform secant lower bound on
the unit interval.  This is the monotonicity input for the covariance step in
the sparse moment calculation.  Given [the stated inputs and conditions](hyp:ha,hz,hy,hzy), [the stated conclusion](goal) follows. -/
lemma sparseWeight_secant_lower_bound {a z y : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hzy : z ≤ y) :
    (68 / 9 : ℝ) * (4 / 729) * (100 / 121) * (y - z) ≤
      sparseWeight a y - sparseWeight a z := by
  have ha' : -(1 / 10 : ℝ) ≤ a ∧ a ≤ 1 / 10 := by
    constructor
    · norm_num at ha ⊢
      exact ha.1
    · exact ha.2
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (sparseWeight a) x := by
    intro x hx
    have hc : |centeredCoordinate x| ≤ 1 := abs_centeredCoordinate_le_one hx
    have habs : |a| ≤ 1 / 10 := by rw [abs_le]; exact ha'
    have hp : |a * centeredCoordinate x| ≤ 1 / 10 := by
      rw [abs_mul]
      exact (mul_le_mul habs hc (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [abs_le] at hp
    exact (sparseWeight_hasDerivAt (by nlinarith)).differentiableAt
  apply (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
  · exact fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  · intro x hx
    apply (hdiff x ?_).differentiableWithinAt
    rw [interior_Icc] at hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      rw [interior_Icc] at hx
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    simpa only [mul_assoc] using
      le_of_lt (sparseWeight_deriv_gt_rational_floor ha hx')
  · exact hz
  · exact hy
  · exact hzy

-- @node: sparseWeight_centered_product_lower_bound
/-- Centering at the midpoint turns the secant estimate into the pointwise
quadratic lower bound whose integral is the `1/6` covariance factor.  Given [the stated inputs and conditions](hyp:ha,hy), [the stated conclusion](goal) follows. -/
lemma sparseWeight_centered_product_lower_bound {a y : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (68 / 9 : ℝ) * (4 / 729) * (100 / 121) *
        (2 * (y - 1 / 2) ^ 2) ≤
      centeredCoordinate y * (sparseWeight a y - sparseWeight a (1 / 2)) := by
  by_cases hmid : (1 / 2 : ℝ) ≤ y
  · have hsec := sparseWeight_secant_lower_bound ha
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1) hy hmid
    simp only [centeredCoordinate]
    nlinarith
  · have hsec := sparseWeight_secant_lower_bound ha hy
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1) (le_of_not_ge hmid)
    simp only [centeredCoordinate]
    nlinarith

-- @node: sparseWeight_centered_integral_lower_bound
/-- Integrating the centered secant estimate supplies the exact `1/6` factor
used in the sparse second-moment certificate.  Given [the stated inputs and conditions](hyp:ha), [the stated conclusion](goal) follows. -/
lemma sparseWeight_centered_integral_lower_bound {a : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10)) :
    (1 / 6 : ℝ) * ((68 / 9 : ℝ) * (4 / 729) * (100 / 121)) ≤
      ∫ y in Set.Icc (0 : ℝ) 1, centeredCoordinate y * sparseWeight a y := by
  let C : ℝ := (68 / 9 : ℝ) * (4 / 729) * (100 / 121)
  have hden : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      1 + a * centeredCoordinate y ≠ 0 := by
    intro y hy
    have hh := abs_centeredCoordinate_le_one hy
    rw [abs_le] at hh
    have ha1 : (-1 / 10 : ℝ) ≤ a := ha.1
    have ha2 : a ≤ (1 / 10 : ℝ) := ha.2
    nlinarith
  have hc : Continuous centeredCoordinate := by
    unfold centeredCoordinate
    fun_prop
  have hwcont : ContinuousOn (sparseWeight a) (Set.Icc (0 : ℝ) 1) := by
    unfold sparseWeight
    apply ContinuousOn.div
    · unfold exponentialInterventionDensity
      fun_prop
    · exact (continuous_const.add (continuous_const.mul hc)).pow 2 |>.continuousOn
    · intro y hy
      exact pow_ne_zero 2 (hden y hy)
  have hwint : IntegrableOn
      (fun y => centeredCoordinate y * sparseWeight a y) (Set.Icc (0 : ℝ) 1) :=
    (hc.continuousOn.mul hwcont).integrableOn_Icc
  have hconst : IntegrableOn
      (fun y => sparseWeight a (1 / 2) * centeredCoordinate y) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul hc).continuousOn.integrableOn_Icc
  have hright : IntegrableOn
      (fun y => centeredCoordinate y *
        (sparseWeight a y - sparseWeight a (1 / 2))) (Set.Icc (0 : ℝ) 1) :=
    (hc.continuousOn.mul (hwcont.sub continuousOn_const)).integrableOn_Icc
  have hleft : IntegrableOn (fun y : ℝ => C * (2 * (y - 1 / 2) ^ 2))
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hmono :
      (∫ y in Set.Icc (0 : ℝ) 1, C * (2 * (y - 1 / 2) ^ 2)) ≤
        ∫ y in Set.Icc (0 : ℝ) 1,
          centeredCoordinate y * (sparseWeight a y - sparseWeight a (1 / 2)) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact sparseWeight_centered_product_lower_bound ha hy
  have hquad : (∫ y in Set.Icc (0 : ℝ) 1, 2 * (y - 1 / 2) ^ 2) = 1 / 6 := by
    have hfun : (fun y : ℝ => 2 * (y - 1 / 2) ^ 2) =
        fun y => 2 * y ^ 2 - 2 * y ^ 1 + 1 / 2 := by
      funext y
      ring
    rw [hfun, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_add
      ((intervalIntegral.intervalIntegrable_pow 2).const_mul 2 |>.sub
        ((intervalIntegral.intervalIntegrable_pow 1).const_mul 2))
      intervalIntegrable_const,
      intervalIntegral.integral_sub
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul 2)
        ((intervalIntegral.intervalIntegrable_pow 1).const_mul 2),
      intervalIntegral.integral_const_mul,
      integral_pow,
      intervalIntegral.integral_const_mul,
      integral_pow,
      intervalIntegral.integral_const]
    norm_num
  have hcentered :
      (∫ y in Set.Icc (0 : ℝ) 1,
        centeredCoordinate y * (sparseWeight a y - sparseWeight a (1 / 2))) =
      ∫ y in Set.Icc (0 : ℝ) 1, centeredCoordinate y * sparseWeight a y := by
    have hfun : (fun y => centeredCoordinate y *
        (sparseWeight a y - sparseWeight a (1 / 2))) =
      fun y => centeredCoordinate y * sparseWeight a y -
        sparseWeight a (1 / 2) * centeredCoordinate y := by
      funext y
      ring
    rw [hfun, integral_sub hwint hconst, MeasureTheory.integral_const_mul,
      centeredCoordinate_integral, mul_zero, sub_zero]
  rw [MeasureTheory.integral_const_mul, hquad, hcentered] at hmono
  dsimp only [C] at hmono ⊢
  nlinarith

-- @node: cancellationPrimitive_mem_negUnitInterval
/-- Convexity of the exponential puts the cancellation primitive in `[-1,0]`
on the unit interval.  Given [the stated inputs and conditions](hyp:hx), [the stated conclusion](goal) follows. -/
lemma cancellationPrimitive_mem_negUnitInterval {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    cancellationPrimitive x ∈ Set.Icc (-1 : ℝ) 0 := by
  have hden : 0 < Real.exp 4 - 1 := by linarith [thirteen_lt_exp_four]
  have hfrac0 : 0 ≤ (Real.exp (4 * x) - 1) / (Real.exp 4 - 1) := by
    apply div_nonneg
    · have : 1 ≤ Real.exp (4 * x) := Real.one_le_exp (by nlinarith [hx.1])
      linarith
    · exact hden.le
  have hconv : Real.exp (4 * x) ≤ 1 + x * (Real.exp 4 - 1) := by
    rw [mul_comm 4 x]
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (4 : ℝ))
      (sub_nonneg.mpr hx.2) hx.1 (by ring : (1 - x) + x = 1)
    calc
      Real.exp (x * 4) ≤ 1 - x + x * Real.exp 4 := by simpa [smul_eq_mul] using h
      _ = 1 + x * (Real.exp 4 - 1) := by ring
  have hfracx : (Real.exp (4 * x) - 1) / (Real.exp 4 - 1) ≤ x := by
    rw [div_le_iff₀ hden]
    nlinarith
  unfold cancellationPrimitive
  constructor <;> linarith [hx.1, hx.2]

-- @node: reflectedCenteredCoordinate_nonconstant_on_unitInterval
/-- Reflection preserves the nonconstancy of the centered coordinate on the unit interval.  [the stated conclusion](goal) follows. -/
lemma reflectedCenteredCoordinate_nonconstant_on_unitInterval (s : SignVector 3) (i : Fin 3) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ x' ∈ Set.Icc (0 : ℝ) 1,
      centeredCoordinate (reflectedCoordinate s i x) ≠
        centeredCoordinate (reflectedCoordinate s i x') := by
  rcases s.signed i with hi | hi
  · refine ⟨0, by norm_num, 1, by norm_num, ?_⟩
    norm_num [centeredCoordinate, reflectedCoordinate, reflect, hi,
      show (-1 : ℝ) ≠ 1 by norm_num]
  · refine ⟨0, by norm_num, 1, by norm_num, ?_⟩
    norm_num [centeredCoordinate, reflectedCoordinate, reflect, hi]

-- @node: cancellationPrimitive_half_neg
/-- The cancellation primitive is strictly negative at the midpoint of the unit interval.  [the stated conclusion](goal) follows. -/
lemma cancellationPrimitive_half_neg : cancellationPrimitive (1 / 2 : ℝ) < 0 := by
  have he2 : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hfac : Real.exp 4 - 1 = (Real.exp 2 - 1) * (Real.exp 2 + 1) := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    ring
  have hne1 : Real.exp 2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr he2)
  have hne2 : Real.exp 2 + 1 ≠ 0 := by positivity
  unfold cancellationPrimitive
  rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num, hfac]
  have hcancel :
      (Real.exp 2 - 1) / ((Real.exp 2 - 1) * (Real.exp 2 + 1)) =
        1 / (Real.exp 2 + 1) := by
    field_simp
  rw [hcancel]
  have hhalf : 1 / (Real.exp 2 + 1) < (1 / 2 : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity : 0 < Real.exp 2 + 1) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  linarith

-- @node: reflectedCancellationPrimitive_nonconstant_on_unitInterval
/-- Reflection preserves the nonconstancy of the cancellation coefficient on the unit interval.  [the stated conclusion](goal) follows. -/
lemma reflectedCancellationPrimitive_nonconstant_on_unitInterval
    (s : SignVector 3) (i : Fin 3) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ x' ∈ Set.Icc (0 : ℝ) 1,
      cancellationPrimitive (reflectedCoordinate s i x) ≠
        cancellationPrimitive (reflectedCoordinate s i x') := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  rcases s.signed i with hi | hi
  · refine ⟨1, by norm_num, ?_⟩
    simp only [reflectedCoordinate, reflect, hi,
      if_neg (show (-1 : ℝ) ≠ 1 by norm_num)]
    norm_num [cancellationPrimitive_zero.1]
    exact ne_of_lt cancellationPrimitive_half_neg
  · refine ⟨0, by norm_num, ?_⟩
    simp [reflectedCoordinate, reflect, hi, cancellationPrimitive_zero.1]
    simpa only [one_div] using ne_of_lt cancellationPrimitive_half_neg

-- @node: reflectedCoefficient_child_nonconstant
/-- A nonconstant reflected parent coefficient makes the affine child conditional genuinely
depend on that parent somewhere on the unit square.  Given [the stated inputs and conditions](hyp:hK), [the stated conclusion](goal) follows. -/
lemma reflectedCoefficient_child_nonconstant (s : SignVector 3) (K : ℝ → ℝ)
    (hK : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ x' ∈ Set.Icc (0 : ℝ) 1,
      K (reflectedCoordinate s 0 x) ≠ K (reflectedCoordinate s 0 x')) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ x' ∈ Set.Icc (0 : ℝ) 1,
      ∃ y ∈ Set.Icc (0 : ℝ) 1,
        1 + (1 / 10 : ℝ) * K (reflectedCoordinate s 0 x) *
            centeredCoordinate (reflectedCoordinate s 1 y) ≠
          1 + (1 / 10 : ℝ) * K (reflectedCoordinate s 0 x') *
            centeredCoordinate (reflectedCoordinate s 1 y) := by
  rcases hK with ⟨x, hx, x', hx', hxx'⟩
  refine ⟨x, hx, x', hx', 0, by norm_num, ?_⟩
  rcases s.signed 1 with hi | hi
  · simp only [centeredCoordinate, reflectedCoordinate, reflect, hi,
      if_neg (show (-1 : ℝ) ≠ 1 by norm_num)]
    norm_num
    intro heq
    apply hxx'
    simpa [reflectedCoordinate, reflect] using heq
  · simp only [centeredCoordinate, reflectedCoordinate, reflect, hi]
    norm_num
    intro heq
    apply hxx'
    simpa [reflectedCoordinate, reflect] using heq

-- @node: explicitWitness_child_parent_dependence
/-- Both explicit witness child conditionals genuinely depend on the reflected parent coordinate
on the unit square.  [the stated conclusion](goal) follows. -/
lemma explicitWitness_child_parent_dependence (s : SignVector 3) :
    (∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ x' ∈ Set.Icc (0 : ℝ) 1,
      ∃ y ∈ Set.Icc (0 : ℝ) 1,
        1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) *
            centeredCoordinate (reflectedCoordinate s 1 y) ≠
          1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x') *
            centeredCoordinate (reflectedCoordinate s 1 y)) ∧
    (∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ x' ∈ Set.Icc (0 : ℝ) 1,
      ∃ y ∈ Set.Icc (0 : ℝ) 1,
        1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 x) *
            centeredCoordinate (reflectedCoordinate s 1 y) ≠
          1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 x') *
            centeredCoordinate (reflectedCoordinate s 1 y)) := by
  exact ⟨reflectedCoefficient_child_nonconstant s centeredCoordinate
      (reflectedCenteredCoordinate_nonconstant_on_unitInterval s 0),
    reflectedCoefficient_child_nonconstant s cancellationPrimitive
      (reflectedCancellationPrimitive_nonconstant_on_unitInterval s 0)⟩

-- @node: sparseP_bounds
/-- The sparse child conditional lies between `9/10` and `11/10` on the latent cube.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma sparseP_bounds (s : SignVector 3) (v : LatentState 3) (hv : v ∈ latentCube 3) :
    (9 / 10 : ℝ) ≤ sparseP s 1 v ∧ sparseP s 1 v ≤ (11 / 10 : ℝ) := by
  have hv0 : v 0 ∈ Set.Icc (0 : ℝ) 1 := hv 0 (Set.mem_univ 0)
  have hv1 : v 1 ∈ Set.Icc (0 : ℝ) 1 := hv 1 (Set.mem_univ 1)
  have h0 := abs_centeredCoordinate_le_one
    (reflectedCoordinate_mem_unitInterval s 0 hv0)
  have h1 := abs_centeredCoordinate_le_one
    (reflectedCoordinate_mem_unitInterval s 1 hv1)
  rw [abs_le] at h0 h1
  simp only [sparseP, if_true]
  constructor <;> nlinarith

-- @node: sparseWitness_child_ratio_bounds
/-- On the latent cube the sparse child ratio is strictly between zero and five.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma sparseWitness_child_ratio_bounds (s : SignVector 3) (v : LatentState 3)
    (hv : v ∈ latentCube 3) :
    0 < (sparseWitness s).q 1 (v 1) / (sparseWitness s).p 1 v ∧
      (sparseWitness s).q 1 (v 1) / (sparseWitness s).p 1 v < 5 := by
  have hv1 : v 1 ∈ Set.Icc (0 : ℝ) 1 := hv 1 (Set.mem_univ 1)
  have href : reflectedCoordinate s 1 (v 1) ∈ Set.Icc (0 : ℝ) 1 :=
    reflectedCoordinate_mem_unitInterval s 1 hv1
  have hqpos : 0 < (sparseWitness s).q 1 (v 1) := by
    exact exponentialInterventionDensity_pos _
  have hq : (sparseWitness s).q 1 (v 1) < (13 / 3 : ℝ) := by
    exact exponentialInterventionDensity_lt_thirteen_div_three href
  have hp := sparseP_bounds s v hv
  change (9 / 10 : ℝ) ≤ (sparseWitness s).p 1 v ∧
    (sparseWitness s).p 1 v ≤ (11 / 10 : ℝ) at hp
  have hppos : 0 < (sparseWitness s).p 1 v := lt_of_lt_of_le (by norm_num) hp.1
  constructor
  · positivity
  · rw [div_lt_iff₀ hppos]
    nlinarith

-- @node: exponentialTiltMeanGap_gt
/-- The rational lower bound for the exponential-tilt mean excess used in the
sparse moment calculation.  [the stated conclusion](goal) follows. -/
lemma exponentialTiltMeanGap_gt :
    (29 / 108 : ℝ) < 1 / (1 - Real.exp (-4)) - 3 / 4 := by
  have hEpos : 0 < Real.exp 4 := Real.exp_pos 4
  have hden : 0 < Real.exp 4 - 1 := by linarith [thirteen_lt_exp_four]
  rw [Real.exp_neg, inv_eq_one_div]
  field_simp
  nlinarith [exp_four_lt_fifty_five]

-- @node: sparseMomentCoefficient_exact
/-- The product of rational lower bounds in the sparse moment argument is the
stated exact certificate.  [the stated conclusion](goal) follows. -/
lemma sparseMomentCoefficient_exact :
    (1 / 30 : ℝ) * (68 / 9) * (4 / 729) * (100 / 121) * (29 / 108) =
      19720 / 64304361 := by
  norm_num

-- @node: sparseMomentRationalCertificate
/-- The exact rational lower certificate in the sparse moment calculation is
strictly larger than `3 / 10000`.  [the stated conclusion](goal) follows. -/
lemma sparseMomentRationalCertificate :
    (3 / 10000 : ℝ) < 19720 / 64304361 := by norm_num

-- @node: sparseWeight_moment_certificate
/-- The integrated sparse-weight covariance and exponential-tilt mean gap
combine to exceed the paper's `3 / 10000` moment threshold.  Given [the stated inputs and conditions](hyp:ha), [the stated conclusion](goal) follows. -/
lemma sparseWeight_moment_certificate {a : ℝ}
    (ha : a ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10)) :
    (3 / 10000 : ℝ) <
      (1 / 5) * (∫ y in Set.Icc (0 : ℝ) 1,
        centeredCoordinate y * sparseWeight a y) *
        (1 / (1 - Real.exp (-4)) - 3 / 4) := by
  have hI := sparseWeight_centered_integral_lower_bound ha
  have hgap := exponentialTiltMeanGap_gt
  have hcert := sparseMomentRationalCertificate
  have hexact := sparseMomentCoefficient_exact
  have hC : 0 < (68 / 9 : ℝ) * (4 / 729) * (100 / 121) := by norm_num
  have hgapPos : 0 < 1 / (1 - Real.exp (-4)) - 3 / 4 := by
    linarith
  have hIPos : 0 < ∫ y in Set.Icc (0 : ℝ) 1,
      centeredCoordinate y * sparseWeight a y := by
    nlinarith
  nlinarith

-- @node: sparseMmdRationalCertificate
/-- After the coordinate and tail estimates, the remaining numerical MMD
comparison is strictly larger than `5 / 10^8`.  [the stated conclusion](goal) follows. -/
lemma sparseMmdRationalCertificate :
    (5 / 100000000 : ℝ) < ((3 / 10000 : ℝ) - 1 / 10 ^ 15) / 5151 := by
  norm_num

-- @node: sparseMmdTailRationalCertificate
/-- The geometric majorant for the factorial tail beyond degree one hundred
is below `10⁻¹⁵`.  [the stated conclusion](goal) follows. -/
lemma sparseMmdTailRationalCertificate :
    (50 : ℝ) * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77) <
      1 / 10 ^ 15 := by
  norm_num [Nat.factorial]

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
