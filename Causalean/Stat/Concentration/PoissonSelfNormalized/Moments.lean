import Causalean.Stat.Concentration.PoissonSelfNormalized.Chernoff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Scalar weighted and unconditioned Poisson moments

This module integrates the Poisson tail estimate.  It supplies first, second,
and fourth moments at the local scale and their exponentially truncated
counterparts on the universal self-normalized bad event.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

/-- Given [a moment order](hyp:t), the [uniform scalar bad-event moment constant](goal) is a fixed
power of ten large enough for all orders through four. -/
def scalarBadMomentConstant (t : ℕ) : ℝ := 10 ^ (8 * t + 8)

/-- Given [a moment order](hyp:t), the [uniform unconditioned scalar moment constant](goal) is a
fixed power of ten large enough for all orders through four. -/
def scalarMomentConstant (t : ℕ) : ℝ := 10 ^ (4 * t + 4)

/-- For [a moment order](hyp:t), the [scalar bad-event moment constant is strictly positive](goal). -/
theorem scalarBadMomentConstant_pos (t : ℕ) : 0 < scalarBadMomentConstant t := by
  exact pow_pos (by norm_num) _

/-- For [a moment order](hyp:t), the [unconditioned scalar moment constant is strictly
positive](goal). -/
theorem scalarMomentConstant_pos (t : ℕ) : 0 < scalarMomentConstant t := by
  exact pow_pos (by norm_num) _

/-- Given [a radius multiplier and logarithmic level](hyp:H,L), [a nonnegative Poisson
mean](hyp:lambda), and [a natural-valued count](hyp:w), the [scalar deviation-plus-radius
score](goal) adds the absolute deviation to the multiplied self-normalizing radius. -/
noncomputable def score (H L : ℝ) (lambda : ℝ≥0) (w : ℕ) : ℝ :=
  deviation lambda w + H * radius L w

private theorem localScale_one_le (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    1 ≤ localScale lambda L := by
  unfold localScale
  nlinarith [Real.sqrt_nonneg ((lambda : ℝ) * L)]

private theorem score_nonneg (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) (w : ℕ) :
    0 ≤ score universalH L lambda w := by
  unfold score deviation radius universalH
  positivity

private theorem measurable_score (lambda : ℝ≥0) (L : ℝ) :
    Measurable (score universalH L lambda) := by
  unfold score
  fun_prop

private theorem score_le_scale_add_deviation
    (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) (w : ℕ) :
    score universalH L lambda w ≤
      1536 * (localScale lambda L + deviation lambda w) := by
  have hL0 : 0 ≤ L := by linarith
  have hw0 : 0 ≤ (w : ℝ) := Nat.cast_nonneg w
  have hlambda0 : 0 ≤ (lambda : ℝ) := lambda.coe_nonneg
  have hd0 : 0 ≤ deviation lambda w := by simp [deviation]
  have hw_le : (w : ℝ) ≤ (lambda : ℝ) + deviation lambda w := by
    simp only [deviation]
    nlinarith [le_abs_self ((w : ℝ) - (lambda : ℝ))]
  have hmul : (w : ℝ) * L ≤
      (lambda : ℝ) * L + deviation lambda w * L := by
    nlinarith
  have hsqrt_add : Real.sqrt ((w : ℝ) * L) ≤
      Real.sqrt ((lambda : ℝ) * L) + Real.sqrt (deviation lambda w * L) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsq_lambda : (Real.sqrt ((lambda : ℝ) * L)) ^ 2 =
          (lambda : ℝ) * L := by rw [Real.sq_sqrt] <;> positivity
      have hsq_dev : (Real.sqrt (deviation lambda w * L)) ^ 2 =
          deviation lambda w * L := by rw [Real.sq_sqrt] <;> positivity
      nlinarith [Real.sqrt_nonneg ((lambda : ℝ) * L),
        Real.sqrt_nonneg (deviation lambda w * L)]
  have hsqrt_dev : Real.sqrt (deviation lambda w * L) ≤
      (deviation lambda w + L) / 2 := by
    have hsquare : (Real.sqrt (deviation lambda w * L)) ^ 2 =
        deviation lambda w * L := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (deviation lambda w * L),
      sq_nonneg (deviation lambda w - L)]
  unfold score radius universalH localScale
  nlinarith [Real.sqrt_nonneg ((lambda : ℝ) * L)]

private theorem integrable_exp_score_div_scale
    (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    Integrable (fun w : ℕ =>
      Real.exp (score universalH L lambda w / (4096 * localScale lambda L)))
      (poissonMeasure lambda) := by
  let S := localScale lambda L
  have hS : 1 ≤ S := localScale_one_le lambda hL
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  let theta : ℝ := 1 / (2 * S)
  have htheta0 : 0 ≤ theta := by positivity
  have hdom (w : ℕ) :
      Real.exp (score universalH L lambda w / (4096 * S)) ≤
        Real.exp (1 / 2) *
          (Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) +
            Real.exp (-theta * ((w : ℝ) - (lambda : ℝ)))) := by
    have hd0 : 0 ≤ deviation lambda w := by simp [deviation]
    have hs := score_le_scale_add_deviation lambda hL w
    have hfrac : score universalH L lambda w / (4096 * S) ≤
        1 / 2 + deviation lambda w / (2 * S) := by
      dsimp [S] at hs ⊢
      have hscale0 : 0 < localScale lambda L := by simpa [S] using hS0
      apply (div_le_iff₀ (by positivity : 0 < 4096 * localScale lambda L)).2
      field_simp
      nlinarith
    calc
      Real.exp (score universalH L lambda w / (4096 * S)) ≤
          Real.exp (1 / 2 + deviation lambda w / (2 * S)) :=
        Real.exp_le_exp.mpr hfrac
      _ = Real.exp (1 / 2) * Real.exp (deviation lambda w / (2 * S)) :=
        Real.exp_add _ _
      _ ≤ Real.exp (1 / 2) *
          (Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) +
            Real.exp (-theta * ((w : ℝ) - (lambda : ℝ)))) := by
        gcongr
        have habs := Real.exp_abs_le (theta * ((w : ℝ) - (lambda : ℝ)))
        rw [abs_mul, abs_of_nonneg htheta0] at habs
        simpa [deviation, theta, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
          using habs
  have hint : Integrable (fun w : ℕ =>
      Real.exp (1 / 2) *
        (Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) +
          Real.exp (-theta * ((w : ℝ) - (lambda : ℝ)))))
      (poissonMeasure lambda) :=
    ((integrable_exp_centered_poisson lambda theta).add
      (by simpa only [neg_mul] using integrable_exp_centered_poisson lambda (-theta))).const_mul _
  exact hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (by positivity : 0 ≤ Real.exp (1 / 2) *
        (Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) +
          Real.exp (-theta * ((w : ℝ) - (lambda : ℝ)))))] using hdom w)

private theorem integral_exp_score_div_scale_le
    (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    ∫ w : ℕ, Real.exp
        (score universalH L lambda w / (4096 * localScale lambda L))
        ∂poissonMeasure lambda ≤ 8 := by
  let S := localScale lambda L
  let theta : ℝ := 1 / (2 * S)
  have hS : 1 ≤ S := localScale_one_le lambda hL
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have htheta_abs : |theta| ≤ 1 := by
    dsimp [theta]
    rw [abs_of_nonneg (by positivity)]
    have : 1 / (2 * S) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * S) (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    linarith
  have hlambda_le_S_sq : (lambda : ℝ) ≤ S ^ 2 := by
    have hL0 : 0 ≤ L := by linarith
    have hsqrt_sq : (Real.sqrt ((lambda : ℝ) * L)) ^ 2 =
        (lambda : ℝ) * L := by rw [Real.sq_sqrt] <;> positivity
    dsimp [S, localScale]
    nlinarith [Real.sqrt_nonneg ((lambda : ℝ) * L), lambda.coe_nonneg]
  have htheta_sq : (lambda : ℝ) * theta ^ 2 ≤ 1 / 4 := by
    dsimp [theta]
    rw [div_pow]
    rw [one_pow]
    calc
      (lambda : ℝ) * (1 / (2 * S) ^ 2) =
          (lambda : ℝ) / (2 * S) ^ 2 := by ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < (2 * S) ^ 2)).2
        nlinarith
  have hexp_bound (u : ℝ) (hu : u = theta ∨ u = -theta) :
      Real.exp ((lambda : ℝ) * (Real.exp u - 1 - u)) ≤ Real.exp (1 / 4) := by
    have huabs : |u| ≤ 1 := by rcases hu with rfl | rfl <;> simpa using htheta_abs
    have hrem := Real.abs_exp_sub_one_sub_id_le huabs
    have hsq : u ^ 2 = theta ^ 2 := by rcases hu with rfl | rfl <;> ring
    apply Real.exp_le_exp.mpr
    calc
      (lambda : ℝ) * (Real.exp u - 1 - u) ≤
          (lambda : ℝ) * |Real.exp u - 1 - u| := by
        gcongr
        exact le_abs_self _
      _ ≤ (lambda : ℝ) * u ^ 2 := by gcongr
      _ = (lambda : ℝ) * theta ^ 2 := by rw [hsq]
      _ ≤ 1 / 4 := htheta_sq
  have hpoint (w : ℕ) :
      Real.exp (score universalH L lambda w / (4096 * S)) ≤
        Real.exp (1 / 2) *
          (Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) +
            Real.exp (-theta * ((w : ℝ) - (lambda : ℝ)))) := by
    have hd0 : 0 ≤ deviation lambda w := by simp [deviation]
    have hs := score_le_scale_add_deviation lambda hL w
    have hfrac : score universalH L lambda w / (4096 * S) ≤
        1 / 2 + deviation lambda w / (2 * S) := by
      dsimp [S] at hs ⊢
      have hscale0 : 0 < localScale lambda L := by simpa [S] using hS0
      apply (div_le_iff₀ (by positivity : 0 < 4096 * localScale lambda L)).2
      field_simp
      nlinarith
    calc
      _ ≤ Real.exp (1 / 2 + deviation lambda w / (2 * S)) := Real.exp_le_exp.mpr hfrac
      _ = Real.exp (1 / 2) * Real.exp (deviation lambda w / (2 * S)) := Real.exp_add _ _
      _ ≤ _ := by
        gcongr
        have habs := Real.exp_abs_le (theta * ((w : ℝ) - (lambda : ℝ)))
        have htheta0 : 0 ≤ theta := by positivity
        rw [abs_mul, abs_of_nonneg htheta0] at habs
        simpa [deviation, theta, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
          using habs
  calc
    ∫ w : ℕ, Real.exp (score universalH L lambda w / (4096 * S))
        ∂poissonMeasure lambda ≤
      ∫ w : ℕ, Real.exp (1 / 2) *
          (Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) +
            Real.exp (-theta * ((w : ℝ) - (lambda : ℝ))))
        ∂poissonMeasure lambda := by
      exact integral_mono (integrable_exp_score_div_scale lambda hL)
        (((integrable_exp_centered_poisson lambda theta).add
          (by simpa only [neg_mul] using integrable_exp_centered_poisson lambda (-theta))).const_mul _)
        hpoint
    _ = Real.exp (1 / 2) *
        (Real.exp ((lambda : ℝ) * (Real.exp theta - 1 - theta)) +
          Real.exp ((lambda : ℝ) * (Real.exp (-theta) - 1 - (-theta)))) := by
      have hpos := integral_exp_centered_poisson lambda theta
      have hneg : ∫ w : ℕ, Real.exp (-theta * ((w : ℝ) - (lambda : ℝ)))
          ∂poissonMeasure lambda =
          Real.exp ((lambda : ℝ) * (Real.exp (-theta) - 1 - (-theta))) := by
        convert integral_exp_centered_poisson lambda (-theta) using 1 <;> ring
      rw [integral_const_mul, integral_add,
        hpos, hneg]
      · exact integrable_exp_centered_poisson lambda theta
      · simpa only [neg_mul] using integrable_exp_centered_poisson lambda (-theta)
    _ ≤ Real.exp (1 / 2) * (Real.exp (1 / 4) + Real.exp (1 / 4)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (hexp_bound theta (Or.inl rfl))
          (hexp_bound (-theta) (Or.inr rfl))) (Real.exp_nonneg _)
    _ ≤ 8 := by
      calc
        Real.exp (1 / 2) * (Real.exp (1 / 4) + Real.exp (1 / 4)) =
            2 * (Real.exp (1 / 2) * Real.exp (1 / 4)) := by ring
        _ = 2 * Real.exp (3 / 4) := by rw [← Real.exp_add]; norm_num
        _ ≤ 2 * Real.exp 1 := by gcongr <;> norm_num
        _ ≤ 2 * 3 := by gcongr; exact Real.exp_one_lt_three.le
        _ ≤ 8 := by norm_num

private theorem integrable_score_pow_aux (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L)
    (t : ℕ) :
    Integrable (fun w : ℕ => (score universalH L lambda w) ^ t)
      (poissonMeasure lambda) := by
  have hS : 0 < localScale lambda L :=
    lt_of_lt_of_le zero_lt_one (localScale_one_le lambda hL)
  have hpoint (w : ℕ) :
      (score universalH L lambda w) ^ t ≤
        (t.factorial : ℝ) * (4096 * localScale lambda L) ^ t *
          Real.exp (score universalH L lambda w / (4096 * localScale lambda L)) := by
    let x := score universalH L lambda w / (4096 * localScale lambda L)
    have hx0 : 0 ≤ x := by positivity [score_nonneg lambda hL w]
    have he := Real.pow_div_factorial_le_exp x hx0 t
    have hfac : (0 : ℝ) < t.factorial := by positivity
    have he' : x ^ t ≤ (t.factorial : ℝ) * Real.exp x :=
      by simpa [mul_comm] using (div_le_iff₀ hfac).mp he
    have hbase : score universalH L lambda w =
        (4096 * localScale lambda L) * x := by
      dsimp [x]
      field_simp
    calc
      (score universalH L lambda w) ^ t =
          (4096 * localScale lambda L) ^ t * x ^ t := by rw [hbase, mul_pow]
      _ ≤ (4096 * localScale lambda L) ^ t *
          ((t.factorial : ℝ) * Real.exp x) := by gcongr
      _ = _ := by ring
  have hint := integrable_exp_score_div_scale lambda hL
  exact (hint.const_mul ((t.factorial : ℝ) *
      (4096 * localScale lambda L) ^ t)).mono'
    ((measurable_score lambda L).pow_const t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (score_nonneg lambda hL w) t),
        abs_of_nonneg (by positivity : 0 ≤ (t.factorial : ℝ) *
          (4096 * localScale lambda L) ^ t *
            Real.exp (score universalH L lambda w /
              (4096 * localScale lambda L)))] using hpoint w)

private theorem poisson_score_moment_aux (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L)
    {t : ℕ} (ht : t ≤ 8) :
    ∫ w : ℕ, (score universalH L lambda w) ^ t ∂poissonMeasure lambda ≤
      10 ^ (4 * t + 4) * (localScale lambda L) ^ t := by
  have hS : 0 < localScale lambda L :=
    lt_of_lt_of_le zero_lt_one (localScale_one_le lambda hL)
  have hpoint (w : ℕ) :
      (score universalH L lambda w) ^ t ≤
        (t.factorial : ℝ) * (4096 * localScale lambda L) ^ t *
          Real.exp (score universalH L lambda w / (4096 * localScale lambda L)) := by
    let x := score universalH L lambda w / (4096 * localScale lambda L)
    have hx0 : 0 ≤ x := by positivity [score_nonneg lambda hL w]
    have he := Real.pow_div_factorial_le_exp x hx0 t
    have hfac : (0 : ℝ) < t.factorial := by positivity
    have he' : x ^ t ≤ (t.factorial : ℝ) * Real.exp x :=
      by simpa [mul_comm] using (div_le_iff₀ hfac).mp he
    have hbase : score universalH L lambda w =
        (4096 * localScale lambda L) * x := by
      dsimp [x]
      field_simp
    calc
      (score universalH L lambda w) ^ t =
          (4096 * localScale lambda L) ^ t * x ^ t := by rw [hbase, mul_pow]
      _ ≤ (4096 * localScale lambda L) ^ t *
          ((t.factorial : ℝ) * Real.exp x) := by gcongr
      _ = _ := by ring
  have hint := integrable_exp_score_div_scale lambda hL
  have hpow := integrable_score_pow_aux lambda hL t
  calc
    ∫ w : ℕ, (score universalH L lambda w) ^ t ∂poissonMeasure lambda ≤
        ∫ w : ℕ, (t.factorial : ℝ) * (4096 * localScale lambda L) ^ t *
          Real.exp (score universalH L lambda w / (4096 * localScale lambda L))
          ∂poissonMeasure lambda := by
      exact integral_mono hpow
        (hint.const_mul ((t.factorial : ℝ) * (4096 * localScale lambda L) ^ t)) hpoint
    _ = ((t.factorial : ℝ) * 4096 ^ t) * (localScale lambda L) ^ t *
        ∫ w : ℕ, Real.exp
          (score universalH L lambda w / (4096 * localScale lambda L))
          ∂poissonMeasure lambda := by
      rw [integral_const_mul]
      ring
    _ ≤ ((t.factorial : ℝ) * 4096 ^ t) * (localScale lambda L) ^ t * 8 := by
      gcongr
      exact integral_exp_score_div_scale_le lambda hL
    _ ≤ 10 ^ (4 * t + 4) * (localScale lambda L) ^ t := by
      have hcoeff : ((t.factorial : ℝ) * 4096 ^ t) * 8 ≤ 10 ^ (4 * t + 4) := by
        interval_cases t <;> norm_num [Nat.factorial]
      calc
        ((t.factorial : ℝ) * 4096 ^ t) * (localScale lambda L) ^ t * 8 =
            (((t.factorial : ℝ) * 4096 ^ t) * 8) *
              (localScale lambda L) ^ t := by ring
        _ ≤ 10 ^ (4 * t + 4) * (localScale lambda L) ^ t :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by positivity) t)

/-- Under [a Poisson law with a nonnegative mean](hyp:lambda), at [a logarithmic level of at least
one](hyp:L,hL), every [moment order through four](hyp:t,ht) gives an [integrable power of the
universal score](goal). -/
-- Reduce `score` to a polynomial envelope in the count: for `L ≥ 1`,
-- `sqrt (w*L) ≤ w*L + 1`, so every power through four is bounded by a
-- constant multiple of `(w+1)^4`.  After `integrable_poissonMeasure_iff`,
-- summability follows from `Real.summable_pow_div_factorial` after shifting
-- the series finitely many times (as in `integrable_natCast_poisson`).
theorem integrable_score_pow (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L)
    {t : ℕ} (ht : t ≤ 4) :
    Integrable (fun w : ℕ => (score universalH L lambda w) ^ t)
      (poissonMeasure lambda) := by
  exact integrable_score_pow_aux lambda hL t

private theorem badEvent_subset_bernstein_eighty
    (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    badEvent universalH L lambda ⊆
      {w : ℕ | (w : ℝ) - (lambda : ℝ) >
          Real.sqrt (2 * (lambda : ℝ) * (80 * L)) + 2 * (80 * L)} ∪
        {w : ℕ | (lambda : ℝ) - (w : ℝ) >
          Real.sqrt (2 * (lambda : ℝ) * (80 * L))} := by
  intro w hw
  simp only [badEvent, Set.mem_setOf_eq, score, universalH] at hw ⊢
  have hL0 : 0 ≤ L := by linarith
  have hw0 : 0 ≤ (w : ℝ) := Nat.cast_nonneg w
  have hlambda0 : 0 ≤ (lambda : ℝ) := lambda.coe_nonneg
  let a := Real.sqrt ((w : ℝ) * L)
  let q := Real.sqrt (2 * (lambda : ℝ) * (80 * L))
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have ha_sq : a ^ 2 = (w : ℝ) * L := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have hq_sq : q ^ 2 = 160 * (lambda : ℝ) * L := by
    dsimp [q]
    rw [Real.sq_sqrt]
    · ring
    · positivity
  change deviation lambda w > (1024 / 4) * (a + L) at hw
  norm_num at hw
  by_cases hup : (lambda : ℝ) ≤ (w : ℝ)
  · left
    have hd : deviation lambda w = (w : ℝ) - (lambda : ℝ) := by
      simp [deviation, abs_of_nonneg (sub_nonneg.mpr hup)]
    have hq_le : q ≤ 16 * a := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [ha_sq]
    rw [hd] at hw
    change (w : ℝ) - (lambda : ℝ) > q + 2 * (80 * L)
    nlinarith
  · right
    have hwl : (w : ℝ) < (lambda : ℝ) := lt_of_not_ge hup
    let d := (lambda : ℝ) - (w : ℝ)
    have hd0 : 0 < d := sub_pos.mpr hwl
    have hd : deviation lambda w = d := by
      simp [deviation, d, abs_of_nonpos (sub_nonpos.mpr hwl.le)]
    rw [hd] at hw
    have hb : 256 * (a + L) < d := hw
    have hd80 : 160 * L < d := by nlinarith
    have hmono : 0 < (d - 256 * (a + L)) *
        (d + 256 * (a + L) - 160 * L) := by
      apply mul_pos
      · linarith
      · nlinarith
    have hbase : 0 < (256 * (a + L)) ^ 2 -
        160 * L * (256 * (a + L)) - 160 * a ^ 2 := by
      nlinarith [sq_nonneg (a - L)]
    have hquad : 0 < d ^ 2 - 160 * L * d - 160 * a ^ 2 := by
      nlinarith
    change d > q
    nlinarith [hq_sq]

private theorem poisson_badEvent_probability_eighty
    (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    poissonMeasure lambda (badEvent universalH L lambda) ≤
      2 * ENNReal.ofReal (Real.exp (-(80 * L))) := by
  have hz : 0 ≤ 80 * L := by positivity
  calc
    poissonMeasure lambda (badEvent universalH L lambda) ≤
        poissonMeasure lambda
          ({w : ℕ | (w : ℝ) - (lambda : ℝ) >
              Real.sqrt (2 * (lambda : ℝ) * (80 * L)) + 2 * (80 * L)} ∪
            {w : ℕ | (lambda : ℝ) - (w : ℝ) >
              Real.sqrt (2 * (lambda : ℝ) * (80 * L))}) :=
      measure_mono (badEvent_subset_bernstein_eighty lambda hL)
    _ ≤ poissonMeasure lambda
          {w : ℕ | (w : ℝ) - (lambda : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * (80 * L)) + 2 * (80 * L)} +
        poissonMeasure lambda
          {w : ℕ | (lambda : ℝ) - (w : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * (80 * L))} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(80 * L))) +
        ENNReal.ofReal (Real.exp (-(80 * L))) :=
      add_le_add (poisson_upper_bernstein lambda hz)
        (poisson_lower_bernstein lambda hz)
    _ = 2 * ENNReal.ofReal (Real.exp (-(80 * L))) := by ring

/-- Under [a Poisson law with a nonnegative mean](hyp:lambda), at [a logarithmic level of at least
one](hyp:L,hL), each [moment order one, two, or four](hyp:t,ht) has [its universal score truncated
to the bad event bounded by an exponentially decaying multiple of the matching local-scale
power](goal). -/
-- A convenient discrete-tail route is to partition by integer Bernstein
-- levels `z = 40*L+n`.  On each shell, the deterministic inequalities used
-- in `badEvent_subset_remote_bernstein` bound `score^t` by a fixed multiple
-- of `(localScale + n)^t`; `poisson_abs_bernstein` bounds the shell by
-- `2*exp (-(40*L+n))`.  Sum the resulting degree-at-most-four polynomial
-- times geometric series, absorb its `L^t` factor into `localScale^t`
-- (`localScale ≥ L`), and discharge the three allowed values of `t`
-- separately.  The very large declared constant leaves ample slack.
theorem poisson_weighted_bad_moment (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    ∫ w : ℕ, (badEvent universalH L lambda).indicator
        (fun w => (score universalH L lambda w) ^ t) w ∂poissonMeasure lambda ≤
      scalarBadMomentConstant t * Real.exp (-(scalarDecay * L)) *
        (localScale lambda L) ^ t := by
  let B := badEvent universalH L lambda
  let S := localScale lambda L
  let X : ℕ → ℝ := fun w => (score universalH L lambda w) ^ t
  let a : ℝ := Real.exp (-(40 * L)) * (S ^ t)⁻¹
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (localScale_one_le lambda hL)
  have ha : 0 < a := by positivity
  have ht8 : 2 * t ≤ 8 := by rcases ht with rfl | rfl | rfl <;> norm_num
  have hX : Integrable X (poissonMeasure lambda) := by
    exact integrable_score_pow_aux lambda hL t
  have hXsq : Integrable (fun w => (X w) ^ 2) (poissonMeasure lambda) := by
    simpa only [X, ← pow_mul, mul_comm] using
      integrable_score_pow_aux lambda hL (2 * t)
  have hB : MeasurableSet B := by
    exact measurableSet_badEvent universalH L lambda
  have hprobReal : (poissonMeasure lambda).real B ≤
      2 * Real.exp (-(80 * L)) := by
    have hp := poisson_badEvent_probability_eighty lambda hL
    have hto := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hp
    simpa [B, measureReal_def, ENNReal.toReal_mul, Real.exp_nonneg] using hto
  have hmoment : ∫ w : ℕ, (X w) ^ 2 ∂poissonMeasure lambda ≤
      10 ^ (8 * t + 4) * S ^ (2 * t) := by
    have heq : 4 * (2 * t) + 4 = 8 * t + 4 := by omega
    rw [← heq]
    simpa only [X, S, pow_two, ← pow_add, two_mul] using
      poisson_score_moment_aux lambda hL ht8
  have hyoung (w : ℕ) :
      B.indicator X w ≤
        (a * (X w) ^ 2 + a⁻¹ * B.indicator (fun _ => (1 : ℝ)) w) / 2 := by
    by_cases hw : w ∈ B
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have hsquare := sq_nonneg (a * X w - 1)
      have ha0 : a ≠ 0 := ne_of_gt ha
      field_simp [ha0]
      nlinarith
    · simp [Set.indicator_of_notMem hw]
      positivity
  have hleft : Integrable (B.indicator X) (poissonMeasure lambda) := hX.indicator hB
  have hright : Integrable (fun w =>
      (a * (X w) ^ 2 + a⁻¹ * B.indicator (fun _ => (1 : ℝ)) w) / 2)
      (poissonMeasure lambda) := by
    apply Integrable.div_const
    apply Integrable.add
    · exact hXsq.const_mul a
    · exact (integrable_const (1 : ℝ)).indicator hB |>.const_mul a⁻¹
  have hintegral : ∫ w : ℕ, B.indicator X w ∂poissonMeasure lambda ≤
      (a * ∫ w : ℕ, (X w) ^ 2 ∂poissonMeasure lambda +
        a⁻¹ * (poissonMeasure lambda).real B) / 2 := by
    calc
      ∫ w : ℕ, B.indicator X w ∂poissonMeasure lambda ≤
          ∫ w : ℕ,
            (a * (X w) ^ 2 + a⁻¹ * B.indicator (fun _ => (1 : ℝ)) w) / 2
            ∂poissonMeasure lambda := integral_mono hleft hright hyoung
      _ = (a * ∫ w : ℕ, (X w) ^ 2 ∂poissonMeasure lambda +
          a⁻¹ * (poissonMeasure lambda).real B) / 2 := by
        rw [integral_div, integral_add, integral_const_mul, integral_const_mul,
          integral_indicator_const (1 : ℝ) hB]
        simp
        · exact hXsq.const_mul a
        · exact (integrable_const (1 : ℝ)).indicator hB |>.const_mul a⁻¹
  have hterm1 : a * ∫ w : ℕ, (X w) ^ 2 ∂poissonMeasure lambda ≤
      10 ^ (8 * t + 4) * Real.exp (-(40 * L)) * S ^ t := by
    calc
      a * ∫ w : ℕ, (X w) ^ 2 ∂poissonMeasure lambda ≤
          a * (10 ^ (8 * t + 4) * S ^ (2 * t)) :=
        mul_le_mul_of_nonneg_left hmoment ha.le
      _ = 10 ^ (8 * t + 4) * Real.exp (-(40 * L)) * S ^ t := by
        dsimp [a]
        rw [pow_mul]
        field_simp
        ring
  have hterm2 : a⁻¹ * (poissonMeasure lambda).real B ≤
      2 * Real.exp (-(40 * L)) * S ^ t := by
    calc
      a⁻¹ * (poissonMeasure lambda).real B ≤
          a⁻¹ * (2 * Real.exp (-(80 * L))) :=
        mul_le_mul_of_nonneg_left hprobReal (inv_nonneg.mpr ha.le)
      _ = 2 * Real.exp (-(40 * L)) * S ^ t := by
        dsimp [a]
        rw [mul_inv_rev, inv_inv, ← Real.exp_neg]
        field_simp [Real.exp_ne_zero, ne_of_gt hS]
        rw [← Real.exp_add]
        ring_nf
  calc
    ∫ w : ℕ, (badEvent universalH L lambda).indicator
        (fun w => (score universalH L lambda w) ^ t) w ∂poissonMeasure lambda =
        ∫ w : ℕ, B.indicator X w ∂poissonMeasure lambda := by rfl
    _ ≤ (a * ∫ w : ℕ, (X w) ^ 2 ∂poissonMeasure lambda +
        a⁻¹ * (poissonMeasure lambda).real B) / 2 := hintegral
    _ ≤ (10 ^ (8 * t + 4) * Real.exp (-(40 * L)) * S ^ t +
        2 * Real.exp (-(40 * L)) * S ^ t) / 2 := by gcongr
    _ ≤ scalarBadMomentConstant t * Real.exp (-(scalarDecay * L)) *
        (localScale lambda L) ^ t := by
      dsimp [scalarBadMomentConstant, scalarDecay, S]
      have hcoeff : (10 ^ (8 * t + 4) + 2 : ℝ) / 2 ≤ 10 ^ (8 * t + 8) := by
        rcases ht with rfl | rfl | rfl <;> norm_num
      calc
        (10 ^ (8 * t + 4) * Real.exp (-(40 * L)) *
              localScale lambda L ^ t +
            2 * Real.exp (-(40 * L)) * localScale lambda L ^ t) / 2 =
            ((10 ^ (8 * t + 4) + 2 : ℝ) / 2) *
              (Real.exp (-(40 * L)) * localScale lambda L ^ t) := by ring
        _ ≤ 10 ^ (8 * t + 8) *
              (Real.exp (-(40 * L)) * localScale lambda L ^ t) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = 10 ^ (8 * t + 8) * Real.exp (-(40 * L)) *
              localScale lambda L ^ t := by ring

/-- Under [a Poisson law with a nonnegative mean](hyp:lambda), at [a logarithmic level of at least
one](hyp:L,hL), every [moment order through four](hyp:t,ht) has [its universal score moment bounded
by a constant times the matching local-scale power](goal). -/
-- Split at a constant Bernstein level and use the same integer-shell sum as
-- above without the initial `40*L` offset.  Equivalently use Mathlib's
-- layer-cake formula after deriving a tail bound for `score/localScale`.
-- Treat `t = 0,1,2,3,4` explicitly; `localScale ≥ L ≥ 1` absorbs constants.
theorem poisson_score_moment (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L)
    {t : ℕ} (ht : t ≤ 4) :
    ∫ w : ℕ, (score universalH L lambda w) ^ t ∂poissonMeasure lambda ≤
      scalarMomentConstant t * (localScale lambda L) ^ t := by
  simpa only [scalarMomentConstant] using
    poisson_score_moment_aux lambda hL (le_trans ht (by norm_num))

end Causalean.Stat.Concentration.PoissonSelfNormalized
