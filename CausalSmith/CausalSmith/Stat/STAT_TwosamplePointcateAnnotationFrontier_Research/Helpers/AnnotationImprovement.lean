module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RateAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strict annotation improvement

The supervised-normalized frontier is a maximum of a vanishing oracle power
and a negative power of the total-to-labeled count ratio.
-/

public section

open Filter
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A negative power of an eventually positive sequence vanishes exactly when it diverges.  Given [the specified input f](hyp:f), [the specified input a](hyp:a), [the specified input ha](hyp:ha), [the specified input hf](hyp:hf), [the annotation negative power zero iff conclusion](goal) holds. -/
lemma annotation_negative_power_zero_iff (f : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hf : ∀ᶠ n in atTop, 0 < f n) :
    Tendsto (fun n => (f n)^(-a)) atTop (nhds 0) ↔ Tendsto f atTop atTop := by
  constructor
  · intro h
    apply tendsto_atTop.2
    intro b
    let x : ℝ := max 1 b
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have he : 0 < x^(-a) := Real.rpow_pos_of_pos hx _
    filter_upwards [hf, h.eventually (gt_mem_nhds he)] with n hn hsmall
    have hi : (x^(-a))^(-(1/a)) = x := by
      rw [← Real.rpow_mul hx.le]
      have hid : (-a)*(-(1/a)) = 1 := by field_simp
      rw [hid, Real.rpow_one]
    have hb := (decreasing_power_threshold (f n) (x^(-a)) 1 a hn he
      zero_lt_one ha).mp (by simpa using hsmall.le)
    rw [hi] at hb
    exact (le_max_right 1 b).trans hb
  · intro h
    exact (tendsto_rpow_neg_atTop ha).comp h

/-- In the rough regime the normalized frontier is exactly the two powers in the roadmap.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hs](hyp:hs), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the annotation supervised ratio formula conclusion](goal) holds. -/
lemma annotation_supervised_ratio_formula (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (hs : alpha + beta < sCrit d gamma)
    (n m : ℕ) (hn : 2 ≤ n) :
    sharpRate d alpha beta gamma n m / sharpRate d alpha beta gamma n 0 =
      max ((n:ℝ)^(-(gamma/(2*gamma+d)-2*gamma/bigDelta d alpha beta gamma)))
        ((((n:ℝ)+m)/(n:ℝ))^(-(gamma/bigDelta d alpha beta gamma))) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)+(m:ℝ) := by positivity
  rw [(supervised_rate_branches d alpha beta gamma L eps hdom n hn).1 hs]
  change max (oracleRate d gamma n)
    (((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) / _ = _
  rw [← max_div_div_right (Real.rpow_pos_of_pos hp _).le]
  congr 1
  · unfold oracleRate
    rw [← Real.rpow_sub hp]
    congr 1
    ring
  · rw [Real.mul_rpow hp.le hN.le, Real.div_rpow hN.le hp.le]
    have hid : -(2*gamma/bigDelta d alpha beta gamma) =
        -(gamma/bigDelta d alpha beta gamma) + -(gamma/bigDelta d alpha beta gamma) := by ring
    rw [hid, Real.rpow_add hp]
    field_simp

/-- The oracle-to-supervised decay exponent is positive precisely in the rough regime.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hs](hyp:hs), [the annotation improvement exponent pos conclusion](goal) holds. -/
lemma annotation_improvement_exponent_pos (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (hs : alpha + beta < sCrit d gamma) :
    0 < gamma/(2*gamma+d)-2*gamma/bigDelta d alpha beta gamma := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hA : 0 < 2*gamma+(d:ℝ) := by positivity
  have hq := qStar_gt_one d alpha beta gamma L eps hdom hs
  rw [(rate_exponent_identities d alpha beta gamma L eps hdom).2]
  have hD : 0 < (2*gamma+(d:ℝ))*(1+qStar d alpha beta gamma) := by positivity
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ hD hA).mpr
  have hh : 2*(2*gamma+(d:ℝ)) <
      (2*gamma+(d:ℝ))*(1+qStar d alpha beta gamma) := by nlinarith
  convert mul_lt_mul_of_pos_left hh hg using 1 <;> ring

/-- The total-to-labeled ratio diverges exactly when the auxiliary-to-labeled ratio does.  Given [the specified input mseq](hyp:mseq), [the annotation total ratio at top iff conclusion](goal) holds. -/
lemma annotation_total_ratio_atTop_iff (mseq : ℕ → ℕ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+mseq n)/(n:ℝ)) atTop atTop ↔
      Tendsto (fun n : ℕ => (mseq n:ℝ)/(n:ℝ)) atTop atTop := by
  have hid : ∀ᶠ n : ℕ in atTop,
      ((n:ℝ)+mseq n)/(n:ℝ) = 1+(mseq n:ℝ)/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [add_div, div_self hp]
  constructor
  · intro h
    apply tendsto_atTop.2
    intro b
    filter_upwards [hid, (tendsto_atTop.1 h) (b+1)] with n hn hb
    rw [hn] at hb
    linarith
  · intro h
    apply tendsto_atTop.2
    intro b
    filter_upwards [hid, (tendsto_atTop.1 h) (b-1)] with n hn hb
    rw [hn]
    linarith

/-- Strict numerical improvement requires rough smoothness and a divergent auxiliary ratio.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input mseq](hyp:mseq), [the annotation rate improvement iff conclusion](goal) holds. -/
lemma annotation_rate_improvement_iff (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (mseq : ℕ → ℕ) :
    Tendsto (fun n : ℕ => sharpRate d alpha beta gamma n (mseq n) /
      sharpRate d alpha beta gamma n 0) atTop (nhds 0) ↔
      alpha + beta < sCrit d gamma ∧
        Tendsto (fun n : ℕ => (mseq n:ℝ)/(n:ℝ)) atTop atTop := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha + beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hD : 0 < bigDelta d alpha beta gamma := by unfold bigDelta; positivity
  have ha : 0 < gamma/bigDelta d alpha beta gamma := div_pos hg hD
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n:ℝ)+mseq n)/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    positivity
  by_cases hs : alpha + beta < sCrit d gamma
  · rw [and_iff_right hs, ← annotation_total_ratio_atTop_iff,
      ← annotation_negative_power_zero_iff _ _ ha hpos]
    have hform : (fun n : ℕ => sharpRate d alpha beta gamma n (mseq n) /
        sharpRate d alpha beta gamma n 0) =ᶠ[atTop]
        (fun n : ℕ => max
          ((n:ℝ)^(-(gamma/(2*gamma+d)-2*gamma/bigDelta d alpha beta gamma)))
          ((((n:ℝ)+mseq n)/(n:ℝ))^(-(gamma/bigDelta d alpha beta gamma)))) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      exact annotation_supervised_ratio_formula d alpha beta gamma L eps hdom hs n (mseq n) hn
    rw [tendsto_congr' hform]
    constructor
    · intro h
      apply squeeze_zero (fun n => Real.rpow_nonneg (by positivity) _)
        (fun n => le_max_right _ _) h
    · intro h
      have horacle := (tendsto_rpow_neg_atTop
        (annotation_improvement_exponent_pos d alpha beta gamma L eps hdom hs)).comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
      simpa using horacle.max h
  · have heq : (fun n : ℕ => sharpRate d alpha beta gamma n (mseq n) /
        sharpRate d alpha beta gamma n 0) =ᶠ[atTop] (fun _ => (1:ℝ)) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      rw [(rate_branches d alpha beta gamma L eps hdom n (mseq n) hn).1 (le_of_not_gt hs),
        (rate_branches d alpha beta gamma L eps hdom n 0 hn).1 (le_of_not_gt hs)]
      have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact div_self (Real.rpow_pos_of_pos hp _).ne'
    constructor
    · intro h
      have h1 : Tendsto (fun n : ℕ => sharpRate d alpha beta gamma n (mseq n) /
          sharpRate d alpha beta gamma n 0) atTop (nhds 1) :=
        tendsto_const_nhds.congr' heq.symm
      have hh := tendsto_nhds_unique h h1
      norm_num at hh
    · intro h
      exact (hs h.1).elim

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
