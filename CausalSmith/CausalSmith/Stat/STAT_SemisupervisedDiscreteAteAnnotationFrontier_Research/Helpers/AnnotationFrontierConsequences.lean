module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Filter Topology Asymptotics

-- @node: logEN_pos_of_one_le
/-- [the stated conditions](hyp:hn) establishes [the stated conclusion](goal). -/
lemma logEN_pos_of_one_le (n : Nat) (hn : 1 ≤ n) : 0 < logEN n := by
  rw [logEN]
  apply Real.log_pos
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  exact he.trans_le (by simpa using mul_le_mul_of_nonneg_left hnR (Real.exp_nonneg 1))

-- @node: frontierRate_sequence_formula
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma frontierRate_sequence_formula (mSeq dSeq : Nat → Nat) (n : Nat) :
    frontierRate n (mSeq n) (dSeq n) =
      min 1 (1 / (n : Real) +
        ((dSeq n : Real) /
          (((n + mSeq n : Nat) : Real) * logEN n)) ^ 2) := by
  rw [frontierRate]
  simp only [Nat.cast_add, div_pow]
  ring

-- @node: annotation_frontier_consistency_iff
/-- [the stated conditions](hyp:_hd) establishes [the stated conclusion](goal). -/
lemma annotation_frontier_consistency_iff
    (mSeq dSeq : Nat → Nat) (_hd : ∀ n, 1 ≤ n → 2 ≤ dSeq n) :
    Tendsto (fun n ↦ frontierRate n (mSeq n) (dSeq n)) atTop (nhds 0) ↔
      Tendsto (fun n ↦ (dSeq n : Real) /
        (((n + mSeq n : Nat) : Real) * logEN n)) atTop (nhds 0) := by
  let b : Nat → Real := fun n ↦ (dSeq n : Real) /
    (((n + mSeq n : Nat) : Real) * logEN n)
  have hnat : Tendsto (fun n : Nat ↦ (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat ↦ 1 / (n : Real)) atTop (nhds 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hb_nonneg : ∀ᶠ n in atTop, 0 ≤ b n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [b]
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (logEN_pos_of_one_le n hn).le)
  constructor
  · intro hr
    have hsmall : ∀ᶠ n in atTop,
        frontierRate n (mSeq n) (dSeq n) < 1 / 2 :=
      (tendsto_order.1 hr).2 (1 / 2) (by norm_num)
    have hbsq : Tendsto (fun n ↦ (b n) ^ 2) atTop (nhds 0) := by
      apply squeeze_zero' (g := fun n ↦ frontierRate n (mSeq n) (dSeq n))
      · exact Filter.Eventually.of_forall fun n ↦ sq_nonneg (b n)
      · filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hs
        rw [frontierRate_sequence_formula]
        have hsum : 1 / (n : Real) + b n ^ 2 ≤ 1 := by
          by_contra h
          rw [frontierRate_sequence_formula, min_eq_left (le_of_not_ge h)] at hs
          norm_num at hs
        rw [min_eq_right hsum]
        exact le_add_of_nonneg_left (by positivity)
      · exact hr
    have hsqrt : Tendsto (fun n ↦ Real.sqrt ((b n) ^ 2)) atTop (nhds 0) := by
      simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hbsq
    apply (hsqrt.congr' ?_)
    filter_upwards [hb_nonneg] with n hn
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hn]
  · intro hb
    have hb' : Tendsto b atTop (nhds 0) := by simpa [b] using hb
    have hsum : Tendsto (fun n : Nat ↦ 1 / (n : Real) + b n ^ 2) atTop (nhds 0) := by
      convert hinv.add (hb'.pow 2) using 1 <;> norm_num
    have hmin : Tendsto (fun n : Nat ↦
        min (1 : Real) (1 / (n : Real) + b n ^ 2)) atTop (nhds 0) := by
      convert (tendsto_const_nhds.min hsum) using 1 <;> norm_num
    apply hmin.congr'
    filter_upwards with n
    exact (frontierRate_sequence_formula mSeq dSeq n).symm

-- @node: annotation_frontier_parametric_iff
/-- [the stated conditions](hyp:_hd) establishes [the stated conclusion](goal). -/
lemma annotation_frontier_parametric_iff
    (mSeq dSeq : Nat → Nat) (_hd : ∀ n, 1 ≤ n → 2 ≤ dSeq n) :
    (fun n ↦ frontierRate n (mSeq n) (dSeq n)) =O[atTop]
        (fun n ↦ 1 / (n : Real)) ↔
      (fun n ↦ (dSeq n : Real)) =O[atTop]
        (fun n ↦ ((n + mSeq n : Nat) : Real) * logEN n / Real.sqrt n) := by
  let D : Nat → Real := fun n ↦ ((n + mSeq n : Nat) : Real) * logEN n
  let b : Nat → Real := fun n ↦ (dSeq n : Real) / D n
  let inv : Nat → Real := fun n ↦ 1 / (n : Real)
  let rate : Nat → Real := fun n ↦ frontierRate n (mSeq n) (dSeq n)
  have hDpos : ∀ᶠ n in atTop, 0 < D n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [D]
    exact mul_pos (by exact_mod_cast (hn.trans (Nat.le_add_right n (mSeq n))))
      (logEN_pos_of_one_le n hn)
  have hinv_nonneg : ∀ᶠ n in atTop, 0 ≤ inv n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [inv]
    positivity
  have hinv_zero : Tendsto inv atTop (nhds 0) := by
    dsimp [inv]
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb_nonneg : ∀ᶠ n in atTop, 0 ≤ b n := by
    filter_upwards [hDpos] with n hD
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  constructor
  · intro hr
    have hr' : rate =O[atTop] inv := by simpa [rate, inv] using hr
    have hrzero := hr'.trans_tendsto hinv_zero
    have hsmall : ∀ᶠ n in atTop, rate n < 1 / 2 :=
      (tendsto_order.1 hrzero).2 (1 / 2) (by norm_num)
    have hb_sq_le : (fun n ↦ b n ^ 2) =O[atTop] rate := by
      apply IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hs
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (frontierRate_mem_Ioc_zero_one _ _ _ hn).1.le, one_mul]
      have hsum : 1 / (n : Real) + b n ^ 2 ≤ 1 := by
        by_contra h
        change frontierRate n (mSeq n) (dSeq n) < 1 / 2 at hs
        rw [frontierRate_sequence_formula] at hs
        rw [min_eq_left (le_of_not_ge (by simpa [b, D] using h))] at hs
        norm_num at hs
      change b n ^ 2 ≤ frontierRate n (mSeq n) (dSeq n)
      rw [frontierRate_sequence_formula, min_eq_right (by simpa [b, D] using hsum)]
      exact le_add_of_nonneg_left (by positivity)
    have hb2 : (fun n ↦ b n ^ 2) =O[atTop] inv := hb_sq_le.trans hr'
    have hbsqrt : (fun n ↦ Real.sqrt (b n ^ 2)) =O[atTop]
        (fun n ↦ Real.sqrt (inv n)) := hb2.sqrt hinv_nonneg
    have hbO : b =O[atTop] (fun n ↦ Real.sqrt (inv n)) :=
      hbsqrt.congr' (by
        filter_upwards [hb_nonneg] with n hn
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hn]) Filter.EventuallyEq.rfl
    have hmul := hbO.mul (isBigO_refl D atTop)
    apply hmul.congr'
    · filter_upwards [hDpos] with n hD
      dsimp [b]
      field_simp
    · filter_upwards [eventually_ge_atTop 1] with n hn
      dsimp [inv, D]
      rw [Real.sqrt_div (by norm_num : (0 : Real) ≤ 1), Real.sqrt_one]
      ring
  · intro hdO
    have hdiv := hdO.mul (isBigO_refl (fun n ↦ (D n)⁻¹) atTop)
    have hbO : b =O[atTop] (fun n ↦ 1 / Real.sqrt n) := by
      apply hdiv.congr'
      · filter_upwards [hDpos] with n hD
        dsimp [b]
        rw [div_eq_mul_inv]
      · filter_upwards [hDpos, eventually_ge_atTop 1] with n hD hn
        dsimp [D]
        dsimp [D] at hD
        have hlog := logEN_pos_of_one_le n hn
        field_simp [hD.ne', hlog.ne']
    have hb2 := hbO.pow 2
    have hb2' : (fun n ↦ b n ^ 2) =O[atTop] inv := by
      apply hb2.congr' Filter.EventuallyEq.rfl
      filter_upwards [eventually_ge_atTop 1] with n hn
      dsimp [inv]
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      rw [div_pow, one_pow, Real.sq_sqrt hnR.le]
    have hsum : (fun n ↦ inv n + b n ^ 2) =O[atTop] inv :=
      (isBigO_refl inv atTop).add hb2'
    refine (show rate =O[atTop] (fun n ↦ inv n + b n ^ 2) by
      apply IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (frontierRate_mem_Ioc_zero_one _ _ _ hn).1.le,
        abs_of_nonneg (add_nonneg (by dsimp [inv]; positivity) (sq_nonneg _)), one_mul]
      rw [frontierRate_sequence_formula]
      exact min_le_right _ _).trans hsum

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
