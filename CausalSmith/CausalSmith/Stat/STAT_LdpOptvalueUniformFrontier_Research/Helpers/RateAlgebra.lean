module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers/RateAlgebra

Finite original-record private value frontiers: Helpers/RateAlgebra.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


/-- Fix [the function f and the function g](hyp:f,g). [Eventual comparison of two real numerical sequences by fixed positive constants](goal). -/
def Comparable (f g : ℕ → ℝ) : Prop :=
  ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧ ∀ᶠ k in Filter.atTop, c*g k ≤ f k ∧ f k ≤ C0*g k
/-- [All numerical resource conclusions carried by rho](goal). -/
def RateResourceConclusions : Prop :=
  (∀ (d : ℕ) (t : ℝ), 2 ≤ d → 0 < t → t < (d : ℝ)^2 * logDim d →
    (rho t d = 1 ↔ t ≤ (d : ℝ)^2 * logDim d / (Real.exp 1*d - Real.exp 1))) ∧
  (∀ (ns ds : ℕ → ℕ) (es : ℕ → ℝ), (∀ k, Allowed (ns k) (ds k) (es k)) →
    (Filter.Tendsto (fun k => rho (ns k * (es k)^2) (ds k)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun k => (ns k : ℝ) * (es k)^2) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => Real.log (1+(ds k : ℝ)^2/(ns k*(es k)^2)) / logDim (ds k))
        Filter.atTop (nhds 0)) ∧
    (Comparable (fun k => rho (ns k*(es k)^2) (ds k)) (fun k => 1/(ns k*(es k)^2)) ↔
      (∃ a : ℝ, 0 < a ∧ ∀ᶠ k in Filter.atTop, a ≤ ns k*(es k)^2) ∧
      (∃ M : ℝ, ∀ᶠ k in Filter.atTop, min (ns k*(es k)^2) (ds k : ℝ) ≤ M)) ∧
    (Filter.Tendsto (fun k => (ns k : ℝ)*(es k)^2) Filter.atTop Filter.atTop →
      (Comparable (fun k => rho (ns k*(es k)^2) (ds k)) (fun k => 1/(ns k*(es k)^2)) ↔
        ∃ M : ℕ, ∀ᶠ k in Filter.atTop, ds k ≤ M))) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b → ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧
    ∃ D0 : ℕ, ∀ d : ℕ, D0 ≤ d → 2 ≤ d → ∀ t : ℝ,
      t/(d : ℝ)^2 ∈ Set.Icc a b →
        c * (Real.log (logDim d)/logDim d)^2 ≤ rho t d ∧
        rho t d ≤ C0 * (Real.log (logDim d)/logDim d)^2)
/-- Assume [dimension at least two](hyp:hd). [The logarithmic dimension is positive on the declared dimension domain](goal). -/
-- @node: logDim_pos
lemma logDim_pos (d : ℕ) (hd : 2 ≤ d) : 0 < logDim d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
  apply Real.log_pos
  nlinarith

/-- Assume [dimension at least two](hyp:hd), [the stated ht condition](hyp:ht), and [the stated hbranch condition](hyp:hbranch). [In the nondense branch, the rate saturates exactly at the paper's threshold](goal). -/
-- @node: rho_saturation_iff
lemma rho_saturation_iff (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : 0 < t)
    (hbranch : t < (d : ℝ)^2 * logDim d) :
    rho t d = 1 ↔ t ≤ (d : ℝ)^2 * logDim d / (Real.exp 1*d - Real.exp 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
  have hL : 0 < logDim d := logDim_pos d hd
  have ha : 0 < (d : ℝ)^2 * logDim d := mul_pos (by positivity) hL
  have hb : 0 < Real.exp 1 * d - Real.exp 1 := by nlinarith
  have hw : 0 < Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) := by
    apply Real.log_pos
    have he1 : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
    have hz : 0 < (d : ℝ)^2 * logDim d / t := div_pos ha ht
    linarith
  rw [rho, if_neg (not_le.mpr hbranch)]
  have hratio : 0 ≤ Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d :=
    (div_pos hw hL).le
  have hmin : min 1 (Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d)^2 = 1 ↔
      1 ≤ Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d := by
    constructor
    · intro h
      have hlo := le_min (show (0 : ℝ) ≤ 1 by norm_num) hratio
      have hhi := min_le_left (1 : ℝ)
        (Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d)
      have heq : min 1 (Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d) = 1 := by
        nlinarith
      calc
        1 = min 1 (Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d) := heq.symm
        _ ≤ _ := min_le_right _ _
    · intro h
      rw [min_eq_left h]
      norm_num
  rw [hmin]
  rw [le_div_iff₀ hL, one_mul]
  change Real.log (Real.exp 1 * d) ≤
    Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) ↔ _
  rw [Real.log_le_log_iff (by positivity) (by positivity), le_div_iff₀ hb]
  constructor
  · intro h
    have h' : Real.exp 1 * d - Real.exp 1 ≤ (d : ℝ)^2 * logDim d / t := by linarith
    have h'' := (le_div_iff₀ ht).mp h'
    nlinarith
  · intro h
    have h' : Real.exp 1 * d - Real.exp 1 ≤ (d : ℝ)^2 * logDim d / t := by
      apply (le_div_iff₀ ht).mpr
      nlinarith
    linarith

/-- Assume [dimension at least two](hyp:hd). [The logarithmic dimension lies between one and the dimension itself](goal). -/
-- @node: logDim_bounds
lemma logDim_bounds (d : ℕ) (hd : 2 ≤ d) : 1 ≤ logDim d ∧ logDim d ≤ d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  rw [logDim, Real.log_mul (Real.exp_pos 1).ne' hdpos.ne', Real.log_exp]
  have hlo : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by linarith)
  have hhi := Real.log_le_sub_one_of_pos hdpos
  constructor <;> linarith

/-- Assume [dimension at least two](hyp:hd), [the stated ht condition](hyp:ht), and [the stated hbranch condition](hyp:hbranch). [All three elementary resource comparisons hold in the dense branch](goal). -/
-- @node: rho_dense_comparisons
lemma rho_dense_comparisons (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : 0 < t)
    (hbranch : (d : ℝ)^2 * logDim d ≤ t) :
    min 1 (1/t) ≤ rho t d ∧
    rho t d ≤ 4 * min 1 ((d : ℝ)^2/t) ∧
    (1/4 : ℝ) * min t (d : ℝ) ≤ t * rho t d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hL := logDim_pos d hd
  obtain ⟨hLone, hLd⟩ := logDim_bounds d hd
  have hLd2 : logDim d ≤ (d : ℝ)^2 := by nlinarith
  have hrho : rho t d = (d : ℝ)^2 / (t * logDim d) := by rw [rho, if_pos hbranch]
  have hparam : 1/t ≤ rho t d := by
    rw [hrho, div_le_div_iff₀ ht (mul_pos ht hL)]
    nlinarith
  have hunit : rho t d ≤ 1 := by
    rw [hrho, div_le_one (mul_pos ht hL)]
    have hdt : (d : ℝ)^2 ≤ t := by nlinarith
    nlinarith
  have hdim : rho t d ≤ (d : ℝ)^2/t := by
    rw [hrho, div_le_div_iff₀ (mul_pos ht hL) ht]
    have hp : 0 ≤ (d : ℝ)^2 * t := by positivity
    nlinarith
  have hscale : t * rho t d = (d : ℝ)^2/logDim d := by
    rw [hrho]
    field_simp
  have hscaled : (1/4 : ℝ) * d ≤ t * rho t d := by
    rw [hscale, le_div_iff₀ hL]
    nlinarith
  refine ⟨(min_le_right _ _).trans hparam, ?_, ?_⟩
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    apply le_min
    · linarith
    · have : 0 ≤ (d : ℝ)^2 / t := by positivity
      linarith
  · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans hscaled

/-- Assume [the stated hv condition](hyp:hv). [The logarithmic derivative factor in the weighted resource comparison is nonnegative](goal). -/
-- @node: log_shift_score_nonneg
lemma log_shift_score_nonneg (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ Real.log (Real.exp 1 + v) - 2*v/(Real.exp 1 + v) := by
  have he := Real.exp_pos (1 : ℝ)
  have hx : 0 < Real.exp 1 + v := by positivity
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hx he)
  rw [Real.log_div hx.ne' he.ne', Real.log_exp, inv_div] at hh
  have hsum : Real.exp 1 / (Real.exp 1 + v) + v / (Real.exp 1 + v) = 1 := by
    rw [← add_div, div_self hx.ne']
  have hp : 0 ≤ Real.exp 1 / (Real.exp 1 + v) := (div_pos he hx).le
  rw [mul_div_assoc]
  linarith

/-- Assume [the stated ha condition](hyp:ha). [The squared weighted logarithm increases with the positive resource variable](goal). -/
-- @node: weighted_log_square_monotone
lemma weighted_log_square_monotone (a : ℝ) (ha : 0 < a) :
    MonotoneOn (fun t : ℝ => t * (Real.log (Real.exp 1 + a/t))^2) (Set.Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t : ℝ => t * (Real.log (Real.exp 1 + a/t))^2)
        (Real.log (Real.exp 1 + a/t) *
          (Real.log (Real.exp 1 + a/t) - 2*(a/t)/(Real.exp 1 + a/t))) t := by
    have hx : 0 < Real.exp 1 + a/t := by positivity
    have hg := ((hasDerivAt_const t a).div (hasDerivAt_id t) ht.ne').const_add (Real.exp 1)
    have hw := hg.log hx.ne'
    convert (hasDerivAt_id t).mul (hw.pow 2) using 1 <;> try dsimp
    all_goals first | rfl | (field_simp; ring)
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have htpos : 0 < t := interior_subset ht
    rw [(hd t htpos).deriv]
    apply mul_nonneg
    · apply Real.log_nonneg
      have he1 : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
      have hv : 0 ≤ a/t := (div_pos ha htpos).le
      linarith
    · exact log_shift_score_nonneg (a/t) (by positivity)


/-- Assume [the stated hz condition](hyp:hz). [For z at least one, the squared shifted logarithm is at most four times z](goal). -/
-- @node: log_shift_square_upper
lemma log_shift_square_upper (z : ℝ) (hz : 1 ≤ z) :
    (Real.log (Real.exp 1 + z))^2 ≤ 4*z := by
  have hzpos : 0 < z := by linarith
  have he := Real.exp_pos (1 : ℝ)
  have hroot : 0 < Real.sqrt z := Real.sqrt_pos.mpr hzpos
  have hlogs := Real.log_le_sub_one_of_pos hroot
  rw [Real.log_sqrt hzpos.le] at hlogs
  have hlog2 : Real.log (Real.exp 1 + 1) ≤ 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hupper := Real.log_le_log (by positivity : 0 < Real.exp 1 + z)
    (show Real.exp 1 + z ≤ (Real.exp 1 + 1)*z by nlinarith)
  rw [Real.log_mul (by positivity) hzpos.ne'] at hupper
  have hw : 0 ≤ Real.log (Real.exp 1 + z) := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hzpos.le
  nlinarith

/-- Assume [the stated hx condition](hyp:hx). [Squaring commutes with truncation at one for a nonnegative argument](goal). -/
-- @node: sq_min_one_nonneg
lemma sq_min_one_nonneg (x : ℝ) (hx : 0 ≤ x) : (min 1 x)^2 = min 1 (x^2) := by
  by_cases h : x ≤ 1
  · rw [min_eq_right h, min_eq_right (show x^2 ≤ 1 by nlinarith)]
  · have hh : 1 ≤ x := le_of_not_ge h
    rw [min_eq_left hh, min_eq_left (show 1 ≤ x^2 by nlinarith)]
    norm_num

/-- Assume [dimension at least two](hyp:hd). [The dimension times its logarithmic dimension is at least the exponential constant](goal). -/
-- @node: dimension_log_product_ge_exp
lemma dimension_log_product_ge_exp (d : ℕ) (hd : 2 ≤ d) :
    Real.exp 1 ≤ (d : ℝ)*logDim d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hdpos
  have hL : logDim d = 1 + Real.log d := by
    rw [logDim, Real.log_mul (Real.exp_pos 1).ne' hdpos.ne', Real.log_exp]
  have hh := mul_le_mul_of_nonneg_left hlog hdpos.le
  have hi : (d : ℝ) * (d : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hdpos.ne'
  nlinarith [Real.exp_one_lt_three]

/-- Assume [dimension at least two](hyp:hd). [The shifted logarithm at resource t = d is at least half the logarithmic dimension](goal). -/
-- @node: log_shift_dimension_half
lemma log_shift_dimension_half (d : ℕ) (hd : 2 ≤ d) :
    logDim d / 2 ≤ Real.log (Real.exp 1 + (d : ℝ)*logDim d) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  obtain ⟨hLone, _⟩ := logDim_bounds d hd
  have he := Real.exp_pos (1 : ℝ)
  have h1 := Real.log_le_log he (show Real.exp 1 ≤ Real.exp 1 + (d : ℝ)*logDim d by nlinarith)
  rw [Real.log_exp] at h1
  have h2 := Real.log_le_log hdpos
    (show (d : ℝ) ≤ Real.exp 1 + (d : ℝ)*logDim d by nlinarith)
  have hL : logDim d = 1 + Real.log d := by
    rw [logDim, Real.log_mul he.ne' hdpos.ne', Real.log_exp]
  linarith


/-- Assume [dimension at least two](hyp:hd), [the stated ht condition](hyp:ht), and [the stated hbranch condition](hyp:hbranch). [All three elementary resource comparisons hold in the nondense branch](goal). -/
-- @node: rho_nondense_comparisons
lemma rho_nondense_comparisons (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : 0 < t)
    (hbranch : ¬ (d : ℝ)^2 * logDim d ≤ t) :
    min 1 (1/t) ≤ rho t d ∧
    rho t d ≤ 4 * min 1 ((d : ℝ)^2/t) ∧
    (1/4 : ℝ) * min t (d : ℝ) ≤ t * rho t d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hL := logDim_pos d hd
  obtain ⟨hLone, _⟩ := logDim_bounds d hd
  let a : ℝ := (d : ℝ)^2 * logDim d
  let w : ℝ := Real.log (Real.exp 1 + a/t)
  let x : ℝ := w / logDim d
  have ha : 0 < a := by dsimp [a]; positivity
  have he := Real.exp_pos (1 : ℝ)
  have hw : 0 < w := by
    apply Real.log_pos
    have he1 : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
    have hz := div_pos ha ht
    linarith
  have hx : 0 ≤ x := (div_pos hw hL).le
  have hrho : rho t d = min 1 (x^2) := by
    rw [rho, if_neg hbranch]
    exact sq_min_one_nonneg x hx
  have hbase1 : logDim d ≤ Real.log (Real.exp 1 + a) := by
    have had := mul_le_mul_of_nonneg_left (dimension_log_product_ge_exp d hd) hdpos.le
    apply Real.log_le_log (mul_pos he hdpos)
    dsimp [a]
    nlinarith
  have hadiv : a / (d : ℝ) = (d : ℝ)*logDim d := by dsimp [a]; field_simp <;> ring
  have hbaseD : logDim d/2 ≤ Real.log (Real.exp 1 + a/(d : ℝ)) := by
    rw [hadiv]
    exact log_shift_dimension_half d hd
  have hupper : x^2 ≤ 4 * ((d : ℝ)^2/t) := by
    have hz : 1 ≤ a/t := (le_div_iff₀ ht).mpr (by dsimp [a]; nlinarith)
    have hlog := log_shift_square_upper (a/t) hz
    dsimp [x]
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hL)]
    have hcompare : 4*(a/t) ≤ (4*((d : ℝ)^2/t))*(logDim d)^2 := by
      dsimp [a]
      simp only [← mul_div_assoc, div_mul_eq_mul_div]
      rw [div_le_div_iff_of_pos_right ht]
      have hd2 : 0 ≤ (d : ℝ)^2 := sq_nonneg _
      nlinarith
    exact hlog.trans hcompare
  have hparam : min 1 (1/t) ≤ rho t d := by
    rw [hrho]
    by_cases ht1 : t ≤ 1
    · have hfrac : a ≤ a/t := (le_div_iff₀ ht).mpr (by nlinarith)
      have hlog := Real.log_le_log (show 0 < Real.exp 1 + a by positivity)
        (show Real.exp 1 + a ≤ Real.exp 1 + a/t by linarith)
      have hx1 : 1 ≤ x := (le_div_iff₀ hL).mpr (by dsimp [w]; linarith)
      rw [min_eq_left (show 1 ≤ x^2 by nlinarith)]
      exact min_le_left _ _
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      have hm := weighted_log_square_monotone a ha (show 0 < (1 : ℝ) by norm_num) ht ht1'
      simp only [div_one, one_mul] at hm
      have hbasepos : 0 ≤ Real.log (Real.exp 1 + a) := by linarith
      have hparam' : 1/t ≤ x^2 := by
        dsimp [x]
        rw [div_pow, div_le_div_iff₀ ht (sq_pos_of_pos hL)]
        dsimp [w]
        nlinarith
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans hparam')
  have hscaled : (1/4 : ℝ) * min t (d : ℝ) ≤ t*x^2 := by
    by_cases htd : t ≤ (d : ℝ)
    · have hfrac : a/(d : ℝ) ≤ a/t := div_le_div_of_nonneg_left ha.le ht htd
      have hlog := Real.log_le_log (show 0 < Real.exp 1 + a/(d : ℝ) by positivity)
        (show Real.exp 1 + a/(d : ℝ) ≤ Real.exp 1 + a/t by linarith)
      have hquarter : (1/4 : ℝ) ≤ x^2 := by
        dsimp [x]
        rw [div_pow, le_div_iff₀ (sq_pos_of_pos hL)]
        have hwbase : logDim d/2 ≤ w := by dsimp [w]; linarith
        nlinarith
      rw [min_eq_left htd]
      nlinarith
    · have hdt : (d : ℝ) ≤ t := le_of_not_ge htd
      have hm := weighted_log_square_monotone a ha hdpos ht hdt
      have hbasepos : 0 ≤ Real.log (Real.exp 1 + a/(d : ℝ)) := by linarith
      rw [min_eq_right hdt]
      dsimp [x]
      rw [div_pow, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hL)]
      have hs : (logDim d)^2/4 ≤ (Real.log (Real.exp 1 + a/(d : ℝ)))^2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hs hdpos.le
      dsimp [w]
      nlinarith
  refine ⟨hparam, ?_, ?_⟩
  · rw [hrho, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    exact le_min ((min_le_left _ _).trans (by norm_num)) ((min_le_right _ _).trans hupper)
  · rw [hrho, mul_min_of_nonneg _ _ ht.le, mul_one]
    apply le_min
    · have hmin := min_le_left t (d : ℝ)
      have hm0 : 0 ≤ min t (d : ℝ) := le_min ht.le hdpos.le
      nlinarith
    · exact hscaled


/-- [Elementary global rate comparisons used for small dimensions](goal). -/
-- @node: rho_elementary_comparisons
lemma rho_elementary_comparisons (n d : ℕ) (eps : ℝ) (h : Allowed n d eps) :
    min 1 (1/(n*eps^2)) ≤ rho (n*eps^2) d ∧
    rho (n*eps^2) d ≤ 4 * min 1 ((d : ℝ)^2/(n*eps^2)) ∧
    (1/4 : ℝ) * min (n*eps^2) (d : ℝ) ≤ n*eps^2 * rho (n*eps^2) d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) h.1)
  have ht : 0 < (n : ℝ) * eps^2 := mul_pos hn (sq_pos_of_pos h.2.2.1)
  by_cases hbranch : (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2
  · exact rho_dense_comparisons d (n*eps^2) h.2.1 ht hbranch
  · exact rho_nondense_comparisons d (n*eps^2) h.2.1 ht hbranch

/-- Assume [dimension at least two](hyp:hd) and [the stated ht condition](hyp:ht). [The rate is at most one at every positive allowed resource](goal). -/
-- @node: rho_le_one
lemma rho_le_one (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : 0 < t) :
    rho t d ≤ 1 := by
  by_cases hb : (d : ℝ)^2 * logDim d ≤ t
  · have hL := (logDim_bounds d hd).1
    have hLp := logDim_pos d hd
    rw [rho, if_pos hb, div_le_one (mul_pos ht hLp)]
    have hd2 : 0 ≤ (d : ℝ)^2 := sq_nonneg _
    have hdt : (d : ℝ)^2 ≤ t := by nlinarith
    nlinarith
  · rw [rho, if_neg hb]
    have hx : 0 ≤ Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d := by
      apply div_nonneg _ (logDim_pos d hd).le
      apply Real.log_nonneg
      have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
      have hz : 0 ≤ (d : ℝ)^2 * logDim d / t :=
        div_nonneg (mul_nonneg (sq_nonneg _) (logDim_pos d hd).le) ht.le
      linarith
    have hlo : 0 ≤ min 1 (Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d) :=
      le_min (by norm_num) hx
    have hhi := min_le_left (1 : ℝ)
      (Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / t) / logDim d)
    nlinarith

/-- Assume [the stated h condition](hyp:h). [The elementary comparisons characterize parametric order even for oscillating resources](goal). -/
-- @node: rho_parametric_comparable_iff
lemma rho_parametric_comparable_iff (ns ds : ℕ → ℕ) (es : ℕ → ℝ)
    (h : ∀ k, Allowed (ns k) (ds k) (es k)) :
    Comparable (fun k => rho (ns k*(es k)^2) (ds k)) (fun k => 1/(ns k*(es k)^2)) ↔
      (∃ a : ℝ, 0 < a ∧ ∀ᶠ k in Filter.atTop, a ≤ ns k*(es k)^2) ∧
      (∃ M : ℝ, ∀ᶠ k in Filter.atTop, min (ns k*(es k)^2) (ds k : ℝ) ≤ M) := by
  have ht (k : ℕ) : 0 < (ns k : ℝ)*(es k)^2 := by
    have hn : (0 : ℝ) < ns k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (h k).1)
    exact mul_pos hn (sq_pos_of_pos (h k).2.2.1)
  constructor
  · rintro ⟨c, C, hc, hcC, he⟩
    constructor
    · refine ⟨c, hc, he.mono ?_⟩
      intro k hk
      have hu := rho_le_one (ds k) (ns k*(es k)^2) (h k).2.1 (ht k)
      have hh : c / (ns k*(es k)^2) ≤ 1 := by simpa [div_eq_mul_inv] using hk.1.trans hu
      exact (div_le_one (ht k)).mp hh
    · refine ⟨4*C, he.mono ?_⟩
      intro k hk
      have hb := (rho_elementary_comparisons (ns k) (ds k) (es k) (h k)).2.2
      have hu := mul_le_mul_of_nonneg_left hk.2 (ht k).le
      have heq : (ns k : ℝ)*(es k)^2*(C*(1/(ns k*(es k)^2))) = C := by
        calc
          _ = C * (((ns k : ℝ)*(es k)^2) * ((ns k : ℝ)*(es k)^2)⁻¹) := by ring
          _ = C := by rw [mul_inv_cancel₀ (ht k).ne', mul_one]
      rw [heq] at hu
      linarith
  · rintro ⟨⟨a, ha, hea⟩, ⟨M, heM⟩⟩
    let B : ℝ := max 1 M
    have hB : 1 ≤ B := le_max_left _ _
    have hMB : M ≤ B := le_max_right _ _
    let c : ℝ := min 1 a
    have hc : 0 < c := lt_min (by norm_num) ha
    have hc1 : c ≤ 1 := min_le_left _ _
    have hca : c ≤ a := min_le_right _ _
    refine ⟨c, 4*B^2, hc, by nlinarith, ?_⟩
    filter_upwards [hea, heM] with k hka hkM
    obtain ⟨hlo, hhi, _⟩ := rho_elementary_comparisons (ns k) (ds k) (es k) (h k)
    constructor
    · apply le_trans _ hlo
      apply le_min
      · rw [mul_one_div, div_le_one (ht k)]
        exact hca.trans hka
      · exact mul_le_of_le_one_left (by positivity) hc1
    · have hm : min ((ns k : ℝ)*(es k)^2) (ds k : ℝ) ≤ B := hkM.trans hMB
      rcases le_total ((ns k : ℝ)*(es k)^2) (ds k : ℝ) with hk | hk
      · rw [min_eq_left hk] at hm
        have hu := rho_le_one (ds k) (ns k*(es k)^2) (h k).2.1 (ht k)
        apply hu.trans
        rw [mul_one_div, le_div_iff₀ (ht k)]
        nlinarith
      · rw [min_eq_right hk] at hm
        apply hhi.trans
        have hs : (ds k : ℝ)^2 ≤ B^2 := by
          have hd0 : (0 : ℝ) ≤ ds k := Nat.cast_nonneg _
          nlinarith
        calc
          4 * min 1 ((ds k : ℝ)^2 / (ns k*(es k)^2)) ≤
              4 * ((ds k : ℝ)^2 / (ns k*(es k)^2)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
          _ ≤ 4*B^2*(1/(ns k*(es k)^2)) := by
            rw [mul_one_div, ← mul_div_assoc, div_le_div_iff_of_pos_right (ht k)]
            linarith

/-- Assume [the stated ht condition](hyp:ht). [Diverging resources turn an eventual bound on the minimum into bounded dimension](goal). -/
-- @node: bounded_min_iff_bounded_dimension
lemma bounded_min_iff_bounded_dimension (t : ℕ → ℝ) (ds : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop Filter.atTop) :
    (∃ M : ℝ, ∀ᶠ k in Filter.atTop, min (t k) (ds k : ℝ) ≤ M) ↔
      ∃ M : ℕ, ∀ᶠ k in Filter.atTop, ds k ≤ M := by
  constructor
  · rintro ⟨M, he⟩
    obtain ⟨N, hN⟩ := exists_nat_ge M
    refine ⟨N, ?_⟩
    filter_upwards [he, ht.eventually_gt_atTop M] with k hk htk
    have hd : (ds k : ℝ) ≤ M := by
      by_contra hn
      have hh := lt_min htk (lt_of_not_ge hn)
      exact (not_lt_of_ge hk) hh
    exact_mod_cast hd.trans hN
  · rintro ⟨M, he⟩
    refine ⟨M, he.mono ?_⟩
    intro k hk
    exact (min_le_right _ _).trans (by exact_mod_cast hk)

/-- Assume [the stated h condition](hyp:h) and [the stated ht condition](hyp:ht). [Along diverging resources, parametric order holds exactly for bounded dimensions](goal). -/
-- @node: rho_parametric_iff_bounded_dimension
lemma rho_parametric_iff_bounded_dimension (ns ds : ℕ → ℕ) (es : ℕ → ℝ)
    (h : ∀ k, Allowed (ns k) (ds k) (es k))
    (ht : Filter.Tendsto (fun k => (ns k : ℝ) * (es k) ^ 2) Filter.atTop Filter.atTop) :
    Comparable (fun k => rho (ns k*(es k)^2) (ds k)) (fun k => 1/(ns k*(es k)^2)) ↔
      ∃ M : ℕ, ∀ᶠ k in Filter.atTop, ds k ≤ M := by
  rw [rho_parametric_comparable_iff ns ds es h,
    bounded_min_iff_bounded_dimension _ ds ht]
  have ha : ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in Filter.atTop, a ≤ (ns k : ℝ)*(es k)^2 :=
    ⟨1, by norm_num, ht.eventually_ge_atTop 1⟩
  exact and_iff_right ha

/-- [The logarithmic dimension diverges with the number of cells](goal). -/
-- @node: logDim_tendsto_atTop
lemma logDim_tendsto_atTop :
    Filter.Tendsto logDim Filter.atTop Filter.atTop := by
  unfold logDim
  exact Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (Real.exp_pos 1))

/-- Assume [the stated ha condition](hyp:ha), [the stated hu condition](hyp:hu), [the stated l condition](hyp:hL), [the stated hb condition](hyp:hb), and [the stated ha l condition](hyp:haL). [At resources comparable to squared dimension, the shifted logarithm is comparable with the logarithm of the logarithmic dimension](goal). -/
-- @node: elbow_log_comparisons
lemma elbow_log_comparisons (a b L u : ℝ) (ha : 0 < a) (hu : u ∈ Set.Icc a b)
    (hL : 1 ≤ L) (hb : 2 * Real.log b ≤ Real.log L)
    (haL : Real.log (Real.exp 1 + 1 / a) ≤ Real.log L) :
    Real.log L / 2 ≤ Real.log (Real.exp 1 + L/u) ∧
      Real.log (Real.exp 1 + L/u) ≤ 2 * Real.log L := by
  have hu0 : 0 < u := ha.trans_le hu.1
  have hb0 : 0 < b := hu0.trans_le hu.2
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  constructor
  · have hdiv : L/b ≤ L/u := div_le_div_of_nonneg_left hL0.le hu0 hu.2
    have hh := Real.log_le_log (div_pos hL0 hb0)
      (show L/b ≤ Real.exp 1 + L/u by linarith [Real.exp_pos (1 : ℝ)])
    rw [Real.log_div hL0.ne' hb0.ne'] at hh
    linarith
  · have hdiv : L/u ≤ L/a := div_le_div_of_nonneg_left hL0.le ha hu.1
    have hexp : Real.exp 1 ≤ L * Real.exp 1 := by
      nlinarith [Real.exp_pos (1 : ℝ)]
    have hh := Real.log_le_log (show 0 < Real.exp 1 + L/u by positivity)
      (show Real.exp 1 + L/u ≤ L * (Real.exp 1 + 1/a) by
        rw [mul_add, mul_one_div]
        linarith)
    rw [Real.log_mul hL0.ne' (show Real.exp 1 + 1/a ≠ 0 by positivity)] at hh
    linarith

/-- Assume [the stated ha condition](hyp:ha) and [the stated  hab assumption](hyp:_hab). [The numerical rate at resources comparable to squared dimension has the squared log-log over log order, uniformly once the dimension is large enough](goal). -/
-- @node: rho_elbow_comparison
lemma rho_elbow_comparison (a b : ℝ) (ha : 0 < a) (_hab : a ≤ b) :
    ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧ ∃ D0 : ℕ,
      ∀ d : ℕ, D0 ≤ d → 2 ≤ d → ∀ t : ℝ,
        t/(d : ℝ)^2 ∈ Set.Icc a b →
        c * (Real.log (logDim d)/logDim d)^2 ≤ rho t d ∧
        rho t d ≤ C0 * (Real.log (logDim d)/logDim d)^2 := by
  have hlogL := Real.tendsto_log_atTop.comp logDim_tendsto_atTop
  have he : ∀ᶠ d : ℕ in Filter.atTop,
      b + 1 ≤ logDim d ∧ 2 * Real.log b ≤ Real.log (logDim d) ∧
      Real.log (Real.exp 1 + 1 / a) ≤ Real.log (logDim d) := by
    filter_upwards [logDim_tendsto_atTop.eventually_ge_atTop (b+1),
      hlogL.eventually_ge_atTop (2 * Real.log b),
      hlogL.eventually_ge_atTop (Real.log (Real.exp 1 + 1 / a))] with d h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨D0, hD0⟩ := Filter.eventually_atTop.mp he
  refine ⟨1/4, 4, by norm_num, by norm_num, D0, ?_⟩
  intro d hd0 hd t ht
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : 0 < (d : ℝ)^2 := sq_pos_of_pos hdpos
  have hL := (logDim_bounds d hd).1
  have hLp := logDim_pos d hd
  obtain ⟨hbL, hbLog, haLog⟩ := hD0 d hd0
  have htpos : 0 < t := (div_pos_iff_of_pos_right hd2).mp (ha.trans_le ht.1)
  have htupper : t ≤ b * (d : ℝ)^2 := (div_le_iff₀ hd2).mp ht.2
  have hbranch : ¬ (d : ℝ)^2 * logDim d ≤ t := by
    have hb : b < logDim d := by linarith
    have hh := mul_lt_mul_of_pos_left hb hd2
    nlinarith
  have heq : (d : ℝ)^2 * logDim d / t = logDim d / (t/(d : ℝ)^2) := by
    field_simp
  obtain ⟨hlo, hhi⟩ := elbow_log_comparisons a b (logDim d) (t/(d : ℝ)^2)
    ha ht hL hbLog haLog
  rw [rho, if_neg hbranch, heq]
  have hlog0 : 0 ≤ Real.log (logDim d) := Real.log_nonneg hL
  have hlogle : Real.log (logDim d) ≤ logDim d := by
    linarith [Real.log_le_sub_one_of_pos hLp]
  have hlo' : Real.log (logDim d) / logDim d / 2 ≤
      Real.log (Real.exp 1 + logDim d / (t/(d : ℝ)^2)) / logDim d := by
    simpa only [div_div, mul_comm] using div_le_div_of_nonneg_right hlo hLp.le
  have hhi' : Real.log (Real.exp 1 + logDim d / (t/(d : ℝ)^2)) / logDim d ≤
      2 * (Real.log (logDim d) / logDim d) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hhi hLp.le
  have hratio0 : 0 ≤ Real.log (logDim d) / logDim d := div_nonneg hlog0 hLp.le
  have hratio1 : Real.log (logDim d) / logDim d ≤ 1 := (div_le_one hLp).mpr hlogle
  have hmlo : Real.log (logDim d) / logDim d / 2 ≤
      min 1 (Real.log (Real.exp 1 + logDim d / (t/(d : ℝ)^2)) / logDim d) :=
    le_min (by linarith) hlo'
  have hmhi := (min_le_right (1 : ℝ)
    (Real.log (Real.exp 1 + logDim d / (t/(d : ℝ)^2)) / logDim d)).trans hhi'
  constructor <;> nlinarith

/-- Fix [the function risk and the function length](hyp:risk,length). [Resource conclusions transferred to actual finite minimax values](goal). -/
def ValueSequenceConclusions (risk length : (n d : ℕ) → ℝ → ℝ) : Prop :=
  (∀ (ns ds : ℕ → ℕ) (es : ℕ → ℝ), (∀ k, Allowed (ns k) (ds k) (es k)) →
    (Filter.Tendsto (fun k => risk (ns k) (ds k) (es k)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun k => (ns k : ℝ)*(es k)^2) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => Real.log (1+(ds k : ℝ)^2/(ns k*(es k)^2)) / logDim (ds k))
        Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto (fun k => length (ns k) (ds k) (es k)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun k => (ns k : ℝ)*(es k)^2) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => Real.log (1+(ds k : ℝ)^2/(ns k*(es k)^2)) / logDim (ds k))
        Filter.atTop (nhds 0)) ∧
    (Comparable (fun k => risk (ns k) (ds k) (es k)) (fun k => 1/(ns k*(es k)^2)) ↔
      (∃ a : ℝ, 0 < a ∧ ∀ᶠ k in Filter.atTop, a ≤ ns k*(es k)^2) ∧
      (∃ M : ℝ, ∀ᶠ k in Filter.atTop, min (ns k*(es k)^2) (ds k : ℝ) ≤ M)) ∧
    (Filter.Tendsto (fun k => (ns k : ℝ)*(es k)^2) Filter.atTop Filter.atTop →
      (Comparable (fun k => risk (ns k) (ds k) (es k)) (fun k => 1/(ns k*(es k)^2)) ↔
        ∃ M : ℕ, ∀ᶠ k in Filter.atTop, ds k ≤ M))) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b → ∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧
    ∃ D0 : ℕ, ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → D0 ≤ d →
      (n*eps^2)/(d : ℝ)^2 ∈ Set.Icc a b →
        c * (Real.log (logDim d)/logDim d)^2 ≤ risk n d eps ∧
        risk n d eps ≤ C0 * (Real.log (logDim d)/logDim d)^2 ∧
        Real.sqrt c * |Real.log (logDim d)/logDim d| ≤ length n d eps ∧
        length n d eps ≤ Real.sqrt C0 * |Real.log (logDim d)/logDim d|)


end CausalSmith.Stat.LdpOptvalueUniformFrontier
