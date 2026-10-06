module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FixedBudgetRealization
public import Causalean.Mathlib.Probability.LimitTheorems.Approximation.CharFunBound

/-! # Sensitivity of the clipped odds interval

The clipped logarithm is globally Lipschitz in its quotient argument. A positive
denominator floor then controls the width of the confidence rectangle on every
sample, including samples outside the coverage event.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Clipping contracts absolute differences.](goal) Under [the stated assumptions](hyp:l,x). -/
-- @node: clip_abs_sub_le
lemma clip_abs_sub_le (l u x y : ℝ) : |clip l u x - clip l u y| ≤ |x-y| := by
  unfold clip
  calc
    _ ≤ max |l-l| |min u x - min u y| := abs_max_sub_max_le_max _ _ _ _
    _ = |min u x - min u y| := by simp
    _ ≤ max |u-u| |x-y| := abs_min_sub_min_le_max _ _ _ _
    _ = |x-y| := by simp

/-- [On a positive half-line the logarithm has the reciprocal-floor Lipschitz bound.](goal) Under [the stated assumptions](hyp:x,ha,hx,hy). -/
-- @node: log_abs_sub_le_floor
lemma log_abs_sub_le_floor (a x y : ℝ) (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |Real.log x - Real.log y| ≤ |x-y|/a := by
  have hxp : 0 < x := ha.trans_le hx
  have hyp : 0 < y := ha.trans_le hy
  have hordered (v w : ℝ) (hv : a ≤ v) (hw : a ≤ w) (hvw : v ≤ w) :
      Real.log w - Real.log v ≤ (w-v)/a := by
    have hvp : 0 < v := ha.trans_le hv
    have hwp : 0 < w := ha.trans_le hw
    calc
      _ = Real.log (w/v) := (Real.log_div hwp.ne' hvp.ne').symm
      _ ≤ w/v-1 := Real.log_le_sub_one_of_pos (div_pos hwp hvp)
      _ = (w-v)/v := by field_simp
      _ ≤ (w-v)/a := div_le_div_of_nonneg_left (sub_nonneg.mpr hvw) ha hv
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hxp hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using hordered x y hx hy hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hyp hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hordered y x hy hx hyx

/-- [Effect clipping gives the exact global exponential Lipschitz constant in the roadmap. [the stated conclusion](goal) holds. -/
-- @node: inversion_abs_sub_le
lemma inversion_abs_sub_le (c d c' d' : ℝ) :
    |inversion c d - inversion c' d'| ≤ Real.exp (1/2) * |c/d-c'/d'| := by
  have h := log_abs_sub_le_floor (Real.exp (-1/2))
    (clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c/d))
    (clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c'/d'))
    (Real.exp_pos _) (le_max_left _ _) (le_max_left _ _)
  calc
    _ ≤ |clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c/d) -
        clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c'/d')| / Real.exp (-1/2) := h
    _ ≤ |(1+c/d)-(1+c'/d')| / Real.exp (-1/2) := by
      exact div_le_div_of_nonneg_right (clip_abs_sub_le _ _ _ _) (Real.exp_pos _).le
    _ = Real.exp (1/2) * |c/d-c'/d'| := by
      rw [show (1+c/d)-(1+c'/d') = c/d-c'/d' by ring, div_eq_mul_inv,
        show (Real.exp (-1/2 : ℝ))⁻¹ = Real.exp (1/2) by
          rw [← Real.exp_neg]; congr 1; ring]
      ring

/-- Inserting a cross quotient controls the two-coordinate perturbation. Under the stated assumptions. [The stated hypotheses](hyp:ha,hd,hd') hold, and [the stated conclusion follows](goal). -/
-- @node: quotient_abs_sub_le_floor
lemma quotient_abs_sub_le_floor (a c d c' d' : ℝ)
    (ha : 0 < a) (hd : a ≤ d) (hd' : a ≤ d') :
    |c/d-c'/d'| ≤ |c-c'|/a + |c'| *|d-d'|/a^2 := by
  have hdp : 0 < d := ha.trans_le hd
  have hd'p : 0 < d' := ha.trans_le hd'
  calc
    _ ≤ |c/d-c'/d| + |c'/d-c'/d'| := abs_sub_le _ _ _
    _ = |c-c'|/d + |c'| *|d-d'|/(d*d') := by
      rw [← sub_div, abs_div, abs_of_pos hdp]
      congr 1
      rw [show c'/d-c'/d' = c'*(d'-d)/(d*d') by field_simp,
        abs_div, abs_mul, abs_sub_comm d' d, abs_of_pos (mul_pos hdp hd'p)]
    _ ≤ |c-c'|/a + |c'| *|d-d'|/a^2 := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (abs_nonneg _) ha hd
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [mul_le_mul hd hd' ha.le hdp.le]

/-- [Any two corners of a confidence rectangle obey the same length envelope.](goal) Under [the stated assumptions](hyp:ha,hb,ht,hd₁,hd₂,hwidth). Under [the stated assumptions](hyp:hc₁,hc₂). -/
-- @node: inversion_rectangle_abs_sub_le
lemma inversion_rectangle_abs_sub_le (a c b t c₁ c₂ d₁ d₂ : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hc₁ : c₁ ∈ Set.Icc (c-b) (c+b)) (hc₂ : c₂ ∈ Set.Icc (c-b) (c+b))
    (hd₁ : a ≤ d₁) (hd₂ : a ≤ d₂) (hwidth : |d₁-d₂| ≤ 2*t) :
    |inversion c₁ d₁ - inversion c₂ d₂| ≤
      2*Real.exp (1/2)/a*b + 2*Real.exp (1/2)/a^2*t*(|c|+b) := by
  have hcd : |c₁-c₂| ≤ 2*b := by
    have := abs_sub_le_of_le_of_le hc₁.1 hc₁.2 hc₂.1 hc₂.2
    linarith
  have hcabs : |c₂| ≤ |c|+b := by
    have hdist : |c₂-c| ≤ b := abs_le.mpr ⟨by linarith [hc₂.1], by linarith [hc₂.2]⟩
    have := abs_sub_le c₂ c 0
    have htri : |c₂| ≤ |c₂-c| + |c| := by simpa using this
    linarith
  calc
    _ ≤ Real.exp (1/2) * (|c₁-c₂|/a + |c₂| *|d₁-d₂|/a^2) :=
      (inversion_abs_sub_le _ _ _ _).trans
        (mul_le_mul_of_nonneg_left (quotient_abs_sub_le_floor _ _ _ _ _ ha hd₁ hd₂)
          (Real.exp_pos _).le)
    _ ≤ Real.exp (1/2) * (2*b/a + (|c|+b)*(2*t)/a^2) := by gcongr
    _ = _ := by ring

/-- [Clipping the denominator preserves its floor and bounds the width by the input width.](goal) Under [the stated assumptions](hyp:ht). -/
-- @node: clipped_denominator_width
lemma clipped_denominator_width (s t : ℝ) (ht : 0 ≤ t) :
    denominatorFloor ≤ clip denominatorFloor 1 (s-t) ∧
    denominatorFloor ≤ clip denominatorFloor 1 (s+t) ∧
    |clip denominatorFloor 1 (s-t) - clip denominatorFloor 1 (s+t)| ≤ 2*t := by
  refine ⟨le_max_left _ _, le_max_left _ _, ?_⟩
  calc
    _ ≤ |(s-t)-(s+t)| := clip_abs_sub_le _ _ _ _
    _ = 2*t := by rw [show (s-t)-(s+t) = -(2*t) by ring, abs_neg, abs_of_nonneg (by positivity)]

/-- [The four-corner inversion width obeys an unconditional rectangle bound.](goal) Under [the stated assumptions](hyp:hb,ht). -/
-- @node: inversion_four_corner_width_le
lemma inversion_four_corner_width_le (c s b t : ℝ) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    max (inversion (c+b) (clip denominatorFloor 1 (s-t)))
        (inversion (c+b) (clip denominatorFloor 1 (s+t))) -
      min (inversion (c-b) (clip denominatorFloor 1 (s-t)))
        (inversion (c-b) (clip denominatorFloor 1 (s+t))) ≤
      2*Real.exp (1/2)/denominatorFloor*b +
        2*Real.exp (1/2)/denominatorFloor^2*t*(|c|+b) := by
  obtain ⟨hm, hp, hwidth⟩ := clipped_denominator_width s t ht
  have ha : 0 < denominatorFloor := by norm_num [denominatorFloor]
  have hlow : c-b ∈ Set.Icc (c-b) (c+b) := ⟨le_rfl, by linarith⟩
  have hhigh : c+b ∈ Set.Icc (c-b) (c+b) := ⟨by linarith, le_rfl⟩
  have hsame : |clip denominatorFloor 1 (s-t) - clip denominatorFloor 1 (s-t)| ≤ 2*t := by
    simpa using (show 0 ≤ 2*t by positivity)
  have hsame' : |clip denominatorFloor 1 (s+t) - clip denominatorFloor 1 (s+t)| ≤ 2*t := by
    simpa using (show 0 ≤ 2*t by positivity)
  have hrev : |clip denominatorFloor 1 (s+t) - clip denominatorFloor 1 (s-t)| ≤ 2*t := by
    simpa only [abs_sub_comm] using hwidth
  have h₁ := (le_abs_self _).trans
    (inversion_rectangle_abs_sub_le _ _ _ _ _ _ _ _ ha hb ht hhigh hlow hm hm hsame)
  have h₂ := (le_abs_self _).trans
    (inversion_rectangle_abs_sub_le _ _ _ _ _ _ _ _ ha hb ht hhigh hlow hm hp hwidth)
  have h₃ := (le_abs_self _).trans
    (inversion_rectangle_abs_sub_le _ _ _ _ _ _ _ _ ha hb ht hhigh hlow hp hm hrev)
  have h₄ := (le_abs_self _).trans
    (inversion_rectangle_abs_sub_le _ _ _ _ _ _ _ _ ha hb ht hhigh hlow hp hp hsame')
  rcases le_total (inversion (c+b) (clip denominatorFloor 1 (s-t)))
      (inversion (c+b) (clip denominatorFloor 1 (s+t))) with h | h
  · rw [max_eq_right h]
    rcases le_total (inversion (c-b) (clip denominatorFloor 1 (s-t)))
        (inversion (c-b) (clip denominatorFloor 1 (s+t))) with h' | h'
    · rw [min_eq_left h']; exact h₃
    · rw [min_eq_right h']; exact h₄
  · rw [max_eq_left h]
    rcases le_total (inversion (c-b) (clip denominatorFloor 1 (s-t)))
        (inversion (c-b) (clip denominatorFloor 1 (s+t))) with h' | h'
    · rw [min_eq_left h']; exact h₁
    · rw [min_eq_right h']; exact h₂

/-- [Exact ideal endpoints satisfy the unconditional bound on every original sample. [the stated conclusion](goal) holds. -/
-- @node: idealEndpoints_length_le
lemma idealEndpoints_length_le (E : ArithmeticEngine) (N : NamingPolicy)
    (n : ℕ) (α β : ℝ) (o : Fin n → Record) :
    let k := resolutions E N n α β
    let bC := 8*(k.1 : ℝ)^(-(α+β)) + Real.sqrt (20*varianceRadius n k.1)
    let bS := 25*(k.2 : ℝ)^(-2*β) + Real.sqrt (20*varianceRadius n k.2)
    (idealEndpoints E N n α β o).2 - (idealEndpoints E N n α β o).1 ≤
      2*Real.exp (1/2)/denominatorFloor*bC +
        2*Real.exp (1/2)/denominatorFloor^2*bS*(|cHat n k.1 o|+bC) := by
  dsimp only
  exact inversion_four_corner_width_le _ _ _ _ (by positivity) (by positivity)

/-- Outward rounding adds only the prescribed two-over-n excess to the samplewise bound. Under the stated assumptions. [The stated hypotheses](hyp:hE,hN,hn,hab) hold, and [the stated conclusion follows](goal). -/
-- @node: upperOutput_length_le
lemma upperOutput_length_le (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) (o : Fin n → Record) :
    let k := resolutions E N n α β
    let bC := 8*(k.1 : ℝ)^(-(α+β)) + Real.sqrt (20*varianceRadius n k.1)
    let bS := 25*(k.2 : ℝ)^(-2*β) + Real.sqrt (20*varianceRadius n k.2)
    intervalLength (upperOutput E N n α β o) ≤
      2*Real.exp (1/2)/denominatorFloor*bC +
        2*Real.exp (1/2)/denominatorFloor^2*bS*(|cHat n k.1 o|+bC) + 2/(n : ℝ) := by
  obtain ⟨c, s, L, R, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLength, _⟩ :=
    fixed_budget_realization.2 E hE N hN n hn α β hab o
  dsimp only
  have hIdeal := idealEndpoints_length_le E N n α β o
  dsimp only at hIdeal
  linarith

/-- [A square-integrable coordinate is controlled in absolute mean by its bias and variance.](goal) Under [the stated assumptions](hyp:μ,hX,hvar). Under [the stated assumptions](hyp:hbias). -/
-- @node: integral_abs_le_bias_sqrt_variance
lemma integral_abs_le_bias_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (c b V : ℝ) (hbias : |(∫ ω, X ω ∂μ)-c| ≤ b) (hvar : variance X μ ≤ V) :
    (∫ ω, |X ω| ∂μ) ≤ |c|+b+Real.sqrt V := by
  have hcenter : MemLp (fun ω => X ω - ∫ ω, X ω ∂μ) 2 μ := hX.sub (memLp_const _)
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hic := hcenter.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcs := Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
    μ _ hcenter
  simp only [Real.norm_eq_abs, sq_abs] at hcs
  rw [← variance_eq_integral hX.aemeasurable] at hcs
  have hmean : |∫ ω, X ω ∂μ| ≤ |c|+b := by
    have h := abs_sub_le (∫ ω, X ω ∂μ) c 0
    simp only [sub_zero] at h
    linarith
  calc
    _ ≤ ∫ ω, (|X ω - ∫ ω, X ω ∂μ| + |∫ ω, X ω ∂μ|) ∂μ :=
      integral_mono hi.abs (hic.abs.add (integrable_const _)) (fun ω => by
        simpa only [sub_zero] using abs_sub_le (X ω) (∫ ω, X ω ∂μ) 0)
    _ = (∫ ω, |X ω - ∫ ω, X ω ∂μ| ∂μ) + |∫ ω, X ω ∂μ| := by
      rw [integral_add hic.abs (integrable_const _)]
      simp
    _ ≤ Real.sqrt V + (|c|+b) := add_le_add (hcs.trans (Real.sqrt_le_sqrt hvar)) hmean
    _ = _ := by ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier
