import Causalean.Stat.Concentration.PoissonSelfNormalized.Moments
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Independence.Integration

/-!
# Finite independent-product aggregation

This module aggregates self-normalized Poisson scores without losing the local
scale determined by the sum of the coordinate means.  Constants may depend on
the fixed cardinality cap and moment order, but not on the means or level.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

/-- Given [a finite coordinate index and sample space](hyp:ι,Ω), [natural-valued coordinate
counts](hyp:W), [a multiplier and logarithmic level](hyp:H,L), and [nonnegative coordinate
means](hyp:lambda), the [aggregate bad event](goal) occurs when at least one coordinate lies in its
self-normalized bad event. -/
def badAny {ι Ω : Type*} [Fintype ι] (W : ι → Ω → ℕ)
    (H L : ℝ) (lambda : ι → ℝ≥0) : Set Ω :=
  {ω | ∃ i, W i ω ∈ badEvent H L (lambda i)}

/-- Given [a finite coordinate index and sample space](hyp:ι,Ω), [natural-valued coordinate
counts](hyp:W), [a multiplier and logarithmic level](hyp:H,L), [nonnegative coordinate
means](hyp:lambda), and [a sample point](hyp:ω), the [aggregate score](goal) is the sum of all
coordinate deviation-plus-radius scores. -/
noncomputable def aggregateScore {ι Ω : Type*} [Fintype ι]
    (W : ι → Ω → ℕ) (H L : ℝ) (lambda : ι → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, score H L (lambda i) (W i ω)

/-- Given [a coordinate-cardinality cap](hyp:r) and [a moment order](hyp:t), the [finite-product
moment constant](goal) is a fixed power of ten depending only on those two quantities. -/
def productMomentConstant (r t : ℕ) : ℝ := 10 ^ (16 * (r + 1) * (t + 1))

/-- For [a coordinate-cardinality cap and moment order](hyp:r,t), the [finite-product moment
constant is strictly positive](goal). -/
theorem productMomentConstant_pos (r t : ℕ) : 0 < productMomentConstant r t := by
  exact pow_pos (by norm_num) _

private theorem measurable_score_pow (lambda : ℝ≥0) (L : ℝ) (t : ℕ) :
    Measurable (fun w : ℕ => (score universalH L lambda w) ^ t) := by
  unfold score
  fun_prop

private theorem score_nonneg_product (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) (w : ℕ) :
    0 ≤ score universalH L lambda w := by
  unfold score deviation radius universalH
  positivity

private theorem integrable_score_pow_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℕ) (lambda : ℝ≥0) (hWlaw : HasLaw W (poissonMeasure lambda) μ)
    {L : ℝ} (hL : 1 ≤ L) {t : ℕ} (ht : t ≤ 4) :
    Integrable (fun ω => (score universalH L lambda (W ω)) ^ t) μ := by
  have hbase := integrable_score_pow lambda hL ht
  have hmap : μ.map W = poissonMeasure lambda := hWlaw.map_eq
  have hbase' : Integrable (fun w : ℕ => (score universalH L lambda w) ^ t) (μ.map W) := by
    rwa [hmap]
  change Integrable ((fun w : ℕ => (score universalH L lambda w) ^ t) ∘ W) μ
  exact hbase'.comp_aemeasurable hWlaw.aemeasurable

private theorem integral_score_pow_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℕ) (lambda : ℝ≥0) (hWlaw : HasLaw W (poissonMeasure lambda) μ)
    (L : ℝ) (t : ℕ) :
    ∫ ω, (score universalH L lambda (W ω)) ^ t ∂μ =
      ∫ w : ℕ, (score universalH L lambda w) ^ t ∂poissonMeasure lambda := by
  simpa only [Function.comp_apply] using
    hWlaw.integral_comp (measurable_score_pow lambda L t).aestronglyMeasurable

private theorem poisson_badEvent_probability_real
    (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    (poissonMeasure lambda).real (badEvent universalH L lambda) ≤
      2 * Real.exp (-(40 * L)) := by
  have hp := poisson_badEvent_probability lambda hL
  have hto := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hp
  simpa [scalarDecay, measureReal_def, ENNReal.toReal_mul, Real.exp_nonneg] using hto

private theorem integral_badEvent_indicator_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℕ) (lambda : ℝ≥0) (hWlaw : HasLaw W (poissonMeasure lambda) μ)
    {L : ℝ} (hL : 1 ≤ L) :
    ∫ ω, (badEvent universalH L lambda).indicator (fun _ => (1 : ℝ)) (W ω) ∂μ ≤
      2 * Real.exp (-(40 * L)) := by
  have hB := measurableSet_badEvent universalH L lambda
  calc
    ∫ ω, (badEvent universalH L lambda).indicator (fun _ => (1 : ℝ)) (W ω) ∂μ =
        ∫ w : ℕ, (badEvent universalH L lambda).indicator (fun _ => (1 : ℝ)) w
          ∂poissonMeasure lambda := by
      simpa only [Function.comp_apply] using
        hWlaw.integral_comp (measurable_const.indicator hB).aestronglyMeasurable
    _ = (poissonMeasure lambda).real (badEvent universalH L lambda) := by
      rw [integral_indicator_const (1 : ℝ) hB]
      simp
    _ ≤ 2 * Real.exp (-(40 * L)) := poisson_badEvent_probability_real lambda hL

private theorem coordinate_cross_moment
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ι → Ω → ℕ) (lambda : ι → ℝ≥0)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (lambda i)) μ)
    (hWindep : iIndepFun W μ) {L : ℝ} (hL : 1 ≤ L)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) (i j : ι) :
    ∫ ω, (badEvent universalH L (lambda j)).indicator
        (fun _ => (score universalH L (lambda i) (W i ω)) ^ t) (W j ω) ∂μ ≤
      (scalarBadMomentConstant t + 2 * scalarMomentConstant t) *
        Real.exp (-(40 * L)) * (localScale (lambda i) L) ^ t := by
  have ht4 : t ≤ 4 := by rcases ht with rfl | rfl | rfl <;> norm_num
  by_cases hij : i = j
  · subst j
    have hmeas : Measurable (fun w : ℕ =>
        (badEvent universalH L (lambda i)).indicator
          (fun w => (score universalH L (lambda i) w) ^ t) w) :=
      (measurable_score_pow (lambda i) L t).indicator
        (measurableSet_badEvent universalH L (lambda i))
    have htransfer :
        ∫ ω, (badEvent universalH L (lambda i)).indicator
            (fun _ => (score universalH L (lambda i) (W i ω)) ^ t) (W i ω) ∂μ =
          ∫ w : ℕ, (badEvent universalH L (lambda i)).indicator
            (fun w => (score universalH L (lambda i) w) ^ t) w
            ∂poissonMeasure (lambda i) := by
      have hlaw := (hWlaw i).integral_comp hmeas.aestronglyMeasurable
      calc
        _ = ∫ ω, (fun w => (badEvent universalH L (lambda i)).indicator
              (fun w => (score universalH L (lambda i) w) ^ t) w) (W i ω) ∂μ := by
          congr 1
        _ = _ := hlaw
    rw [htransfer]
    calc
      _ ≤ scalarBadMomentConstant t * Real.exp (-(scalarDecay * L)) *
          (localScale (lambda i) L) ^ t :=
        poisson_weighted_bad_moment (lambda i) hL ht
      _ ≤ (scalarBadMomentConstant t + 2 * scalarMomentConstant t) *
          Real.exp (-(40 * L)) * (localScale (lambda i) L) ^ t := by
        simp only [scalarDecay]
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · linarith [scalarMomentConstant_pos t]
          · exact Real.exp_nonneg _
        · exact pow_nonneg (by
            unfold localScale
            positivity) t
  · let X : Ω → ℝ := fun ω => (score universalH L (lambda i) (W i ω)) ^ t
    let Y : Ω → ℝ := fun ω =>
      (badEvent universalH L (lambda j)).indicator (fun _ => (1 : ℝ)) (W j ω)
    have hXm : Measurable X :=
      (measurable_score_pow (lambda i) L t).comp (hWmeas i)
    have hYm : Measurable Y :=
      (measurable_const.indicator (measurableSet_badEvent universalH L (lambda j))).comp
        (hWmeas j)
    have hXY : X ⟂ᵢ[μ] Y := (hWindep.indepFun hij).comp
      (measurable_score_pow (lambda i) L t) (measurable_const.indicator
        (measurableSet_badEvent universalH L (lambda j)))
    have hfactor : ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ :=
      hXY.integral_fun_mul_eq_mul_integral hXm.aestronglyMeasurable hYm.aestronglyMeasurable
    have hrewrite : (fun ω =>
        (badEvent universalH L (lambda j)).indicator
          (fun _ => (score universalH L (lambda i) (W i ω)) ^ t) (W j ω)) =
        fun ω => X ω * Y ω := by
      funext ω
      by_cases hω : W j ω ∈ badEvent universalH L (lambda j)
      · simp [X, Y, hω]
      · simp [X, Y, hω]
    rw [hrewrite, hfactor]
    have hX0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg (fun ω => by
      exact pow_nonneg (score_nonneg_product (lambda i) hL (W i ω)) t)
    have hY0 : 0 ≤ ∫ ω, Y ω ∂μ := integral_nonneg (fun ω => by
      dsimp [Y]
      by_cases hω : W j ω ∈ badEvent universalH L (lambda j) <;> simp [hω])
    have hXbound : ∫ ω, X ω ∂μ ≤
        scalarMomentConstant t * (localScale (lambda i) L) ^ t := by
      dsimp [X]
      rw [integral_score_pow_comp μ (W i) (lambda i) (hWlaw i) L t]
      exact poisson_score_moment (lambda i) hL ht4
    have hYbound : ∫ ω, Y ω ∂μ ≤ 2 * Real.exp (-(40 * L)) := by
      exact integral_badEvent_indicator_comp μ (W j) (lambda j) (hWlaw j) hL
    calc
      (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ ≤
          (scalarMomentConstant t * (localScale (lambda i) L) ^ t) *
            (2 * Real.exp (-(40 * L))) :=
        mul_le_mul hXbound hYbound hY0 (mul_nonneg
          (scalarMomentConstant_pos t).le (pow_nonneg (by
            unfold localScale
            positivity) t))
      _ ≤ (scalarBadMomentConstant t + 2 * scalarMomentConstant t) *
          Real.exp (-(40 * L)) * (localScale (lambda i) L) ^ t := by
        have hbad : 0 ≤ scalarBadMomentConstant t := (scalarBadMomentConstant_pos t).le
        have hcoef : 2 * scalarMomentConstant t ≤
            scalarBadMomentConstant t + 2 * scalarMomentConstant t := by linarith
        calc
          (scalarMomentConstant t * localScale (lambda i) L ^ t) *
                (2 * Real.exp (-(40 * L))) =
              (2 * scalarMomentConstant t) *
                (Real.exp (-(40 * L)) * localScale (lambda i) L ^ t) := by ring
          _ ≤ (scalarBadMomentConstant t + 2 * scalarMomentConstant t) *
                (Real.exp (-(40 * L)) * localScale (lambda i) L ^ t) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.exp_nonneg _)
              (pow_nonneg (by unfold localScale; positivity) t))
          _ = _ := by ring

private theorem natCast_le_ten_pow (n : ℕ) : (n : ℝ) ≤ 10 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        rw [pow_succ]
        norm_num at ih ⊢
        nlinarith

private theorem product_coefficient_bound {r t : ℕ} :
    (r : ℝ) ^ (2 * t + 1) *
        (scalarBadMomentConstant t + 2 * scalarMomentConstant t) ≤
      productMomentConstant r t := by
  have hr := natCast_le_ten_pow r
  have hpow : (r : ℝ) ^ (2 * t + 1) ≤ 10 ^ (r * (2 * t + 1)) := by
    calc
      (r : ℝ) ^ (2 * t + 1) ≤ (10 ^ r) ^ (2 * t + 1) := by gcongr
      _ = 10 ^ (r * (2 * t + 1)) := by rw [pow_mul]
  have hexp : 4 * t + 4 ≤ 8 * t + 8 := by omega
  have hsmall : (10 : ℝ) ^ (4 * t + 4) ≤ 10 ^ (8 * t + 8) := by
    exact pow_le_pow_right₀ (by norm_num) hexp
  have hconst : scalarBadMomentConstant t + 2 * scalarMomentConstant t ≤
      10 ^ (8 * t + 9) := by
    dsimp [scalarBadMomentConstant, scalarMomentConstant]
    calc
      (10 : ℝ) ^ (8 * t + 8) + 2 * 10 ^ (4 * t + 4) ≤
          10 ^ (8 * t + 8) + 2 * 10 ^ (8 * t + 8) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 2 by norm_num))
      _ ≤ (10 : ℝ) * 10 ^ (8 * t + 8) := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 10) (8 * t + 8)]
      _ = (10 : ℝ) ^ (8 * t + 9) := by
        rw [show 8 * t + 9 = (8 * t + 8) + 1 by omega, pow_succ]
        ring
  have hexponents : r * (2 * t + 1) + (8 * t + 9) ≤
      16 * (r + 1) * (t + 1) := by nlinarith [Nat.zero_le (r * t)]
  calc
    (r : ℝ) ^ (2 * t + 1) *
        (scalarBadMomentConstant t + 2 * scalarMomentConstant t) ≤
        10 ^ (r * (2 * t + 1)) * 10 ^ (8 * t + 9) :=
      mul_le_mul hpow hconst
        (add_nonneg (scalarBadMomentConstant_pos t).le
          (mul_nonneg (by norm_num) (scalarMomentConstant_pos t).le))
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _)
    _ = 10 ^ (r * (2 * t + 1) + (8 * t + 9)) := by rw [← pow_add]
    _ ≤ 10 ^ (16 * (r + 1) * (t + 1)) :=
      pow_le_pow_right₀ (by norm_num) hexponents
    _ = productMomentConstant r t := rfl

private theorem sum_localScale_le_card_mul
    {ι : Type*} [Fintype ι] [Nonempty ι] (lambda : ι → ℝ≥0)
    {L : ℝ} (hL : 1 ≤ L) :
    ∑ i, localScale (lambda i) L ≤
      (Fintype.card ι : ℝ) *
        (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) := by
  have hL0 : 0 ≤ L := by linarith
  have hcard1 : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset ι)
    (f := fun i => (lambda i : ℝ) * L) (g := fun _ => (1 : ℝ))
    (fun i => mul_nonneg (lambda i).coe_nonneg hL0) (fun _ => by norm_num)
  have hcs' : ∑ i, Real.sqrt ((lambda i : ℝ) * L) ≤
      Real.sqrt ((∑ i, (lambda i : ℝ)) * L) *
        Real.sqrt (Fintype.card ι : ℝ) := by
    simpa [Finset.sum_mul, nsmul_eq_mul] using hcs
  have hsqrt_card : Real.sqrt (Fintype.card ι : ℝ) ≤ Fintype.card ι := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg ((Fintype.card ι : ℝ) - 1)]
  unfold localScale
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (∑ i, Real.sqrt ((lambda i : ℝ) * L)) + (Fintype.card ι : ℝ) * L ≤
        Real.sqrt ((∑ i, (lambda i : ℝ)) * L) * (Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) * L := by
      gcongr
      exact hcs'.trans (mul_le_mul_of_nonneg_left hsqrt_card (Real.sqrt_nonneg _))
    _ = (Fintype.card ι : ℝ) *
        (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) := by ring

private theorem sum_localScale_pow_le_card_mul_pow_sum
    {ι : Type*} [Fintype ι] (lambda : ι → ℝ≥0) {L : ℝ} (hL : 1 ≤ L) (t : ℕ) :
    ∑ i, (localScale (lambda i) L) ^ t ≤
      (Fintype.card ι : ℝ) * (∑ i, localScale (lambda i) L) ^ t := by
  have hS0 (i : ι) : 0 ≤ localScale (lambda i) L := by
    unfold localScale
    positivity
  have hsingle (i : ι) : localScale (lambda i) L ≤ ∑ k, localScale (lambda k) L := by
    exact Finset.single_le_sum (fun k _ => hS0 k) (Finset.mem_univ i)
  calc
    ∑ i, (localScale (lambda i) L) ^ t ≤
        ∑ _i : ι, (∑ k, localScale (lambda k) L) ^ t := by
      exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hS0 i) (hsingle i) t
    _ = (Fintype.card ι : ℝ) * (∑ i, localScale (lambda i) L) ^ t := by
      simp [nsmul_eq_mul]

/-- On [a measurable sample space with a finite coordinate index](hyp:Ω,ι), let [a probability
law](hyp:μ) carry [natural-valued coordinate counts](hyp:W) with [nonnegative coordinate
means](hyp:lambda). If [the counts are measurable](hyp:hWmeas), [each count has its stated Poisson
law](hyp:hWlaw), and [the counts are mutually independent](hyp:hWindep), then under [a fixed
coordinate-cardinality cap](hyp:r,hcard), for [moment order one, two, or four](hyp:t,ht) and [a
logarithmic level of at least one](hyp:L,hL), [the aggregate score moment on the union of bad
coordinates decays exponentially while retaining the local scale determined by the sum of the
means](goal). -/
-- Proof route: dominate `1_{BadAny}` by the sum of coordinate bad-event
-- indicators and use `pow_sum_le_card_mul_sum_pow` on the nonnegative scores.
-- This reduces the integral to terms `E[score_i^t 1_{Bad_j}]`.  For `i = j`,
-- transfer `poisson_weighted_bad_moment` through `HasLaw.integral_comp`.  For
-- `i != j`, use `hWindep.indepFun` (followed by measurable composition) and
-- `IndepFun.integral_mul` to factor the term into an untruncated score moment
-- and a bad-event probability.  Transfer `poisson_score_moment` and
-- `poisson_badEvent_probability_eighty` through the coordinate laws.  Finally
-- bound `sum_i localScale (lambda i) L` by a cardinality-dependent multiple of
-- `sqrt ((sum_i lambda_i) * L) + L` using Cauchy--Schwarz for the square-root
-- sum, and absorb all powers of `r` and scalar constants into
-- `productMomentConstant`.  Split off the empty-index/r=0 case before using
-- positive cardinality inequalities, and eliminate the three values of `t`
-- from `ht` explicitly.
theorem independent_poisson_badAny_moment
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ι → Ω → ℕ) (lambda : ι → ℝ≥0)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (lambda i)) μ)
    (hWindep : iIndepFun W μ)
    {r t : ℕ} (hcard : Fintype.card ι ≤ r)
    (ht : t = 1 ∨ t = 2 ∨ t = 4) {L : ℝ} (hL : 1 ≤ L) :
    ∫ ω, (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ ≤
      productMomentConstant r t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) ^ t := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    have ht4 : t ≤ 4 := by rcases ht with rfl | rfl | rfl <;> norm_num
    let K : ℝ := scalarBadMomentConstant t + 2 * scalarMomentConstant t
    let A : ℝ := Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L
    let n : ℝ := Fintype.card ι
    let F : ι → ι → Ω → ℝ := fun j i ω =>
      (badEvent universalH L (lambda j)).indicator
        (fun _ => (score universalH L (lambda i) (W i ω)) ^ t) (W j ω)
    have hn0 : 0 ≤ n := by dsimp [n]; positivity
    have hn1 : 1 ≤ n := by
      dsimp [n]
      exact_mod_cast Fintype.card_pos
    have hK0 : 0 ≤ K := by
      dsimp [K]
      exact add_nonneg (scalarBadMomentConstant_pos t).le
        (mul_nonneg (by norm_num) (scalarMomentConstant_pos t).le)
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg (Real.sqrt_nonneg _) (by linarith)
    have hscore0 (i : ι) (ω : Ω) :
        0 ≤ score universalH L (lambda i) (W i ω) :=
      score_nonneg_product (lambda i) hL (W i ω)
    have hF0 (j i : ι) (ω : Ω) : 0 ≤ F j i ω := by
      dsimp [F]
      by_cases hω : W j ω ∈ badEvent universalH L (lambda j)
      · simp [hω, pow_nonneg (hscore0 i ω) t]
      · simp [hω]
    have hFint (j i : ι) : Integrable (F j i) μ := by
      have hi := (integrable_score_pow_comp μ (W i) (lambda i) (hWlaw i) hL ht4).indicator
        ((measurableSet_badEvent universalH L (lambda j)).preimage (hWmeas j))
      change Integrable ((W j ⁻¹' badEvent universalH L (lambda j)).indicator
        (fun ω => (score universalH L (lambda i) (W i ω)) ^ t)) μ at hi
      have heq : F j i = (W j ⁻¹' badEvent universalH L (lambda j)).indicator
          (fun ω => (score universalH L (lambda i) (W i ω)) ^ t) := by
        funext ω
        by_cases hω : W j ω ∈ badEvent universalH L (lambda j) <;> simp [F, hω]
      rw [heq]
      exact hi
    have haggregate_pow (ω : Ω) :
        (aggregateScore W universalH L lambda ω) ^ t ≤
          n ^ (t - 1) * ∑ i, (score universalH L (lambda i) (W i ω)) ^ t := by
      unfold aggregateScore
      rcases ht with rfl | rfl | rfl
      · simpa [n] using
          (pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
            (f := fun i => score universalH L (lambda i) (W i ω))
            (fun i _ => hscore0 i ω) 0)
      · simpa [n] using
          (pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
            (f := fun i => score universalH L (lambda i) (W i ω))
            (fun i _ => hscore0 i ω) 1)
      · simpa [n] using
          (pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
            (f := fun i => score universalH L (lambda i) (W i ω))
            (fun i _ => hscore0 i ω) 3)
    have hpoint (ω : Ω) :
        (badAny W universalH L lambda).indicator
            (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ≤
          n ^ (t - 1) * ∑ j, ∑ i, F j i ω := by
      by_cases hbad : ω ∈ badAny W universalH L lambda
      · rw [Set.indicator_of_mem hbad]
        rcases hbad with ⟨j, hj⟩
        have hselected :
            ∑ i, (score universalH L (lambda i) (W i ω)) ^ t = ∑ i, F j i ω := by
          apply Finset.sum_congr rfl
          intro i _
          simp [F, hj]
        have hinner :
            ∑ i, (score universalH L (lambda i) (W i ω)) ^ t ≤
              ∑ j, ∑ i, F j i ω := by
          rw [hselected]
          exact Finset.single_le_sum
            (fun k _ => Finset.sum_nonneg fun i _ => hF0 k i ω) (Finset.mem_univ j)
        exact haggregate_pow ω |>.trans
          (mul_le_mul_of_nonneg_left hinner (pow_nonneg hn0 _))
      · rw [Set.indicator_of_notMem hbad]
        exact mul_nonneg (pow_nonneg hn0 _) (Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun i _ => hF0 j i ω)
    have hlhs0 : 0 ≤ᵐ[μ] fun ω =>
        (badAny W universalH L lambda).indicator
          (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω := by
      filter_upwards [] with ω
      by_cases hbad : ω ∈ badAny W universalH L lambda
      · rw [Set.indicator_of_mem hbad]
        apply pow_nonneg
        unfold aggregateScore
        exact Finset.sum_nonneg fun i _ => hscore0 i ω
      · simp [hbad]
    have hsumInt : Integrable (fun ω => ∑ j, ∑ i, F j i ω) μ :=
      integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun i _ => hFint j i
    have hdomInt : Integrable (fun ω => n ^ (t - 1) * ∑ j, ∑ i, F j i ω) μ :=
      hsumInt.const_mul _
    have hintegral :
        ∫ ω, (badAny W universalH L lambda).indicator
            (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ ≤
          n ^ (t - 1) * ∑ j, ∑ i, ∫ ω, F j i ω ∂μ := by
      calc
        _ ≤ ∫ ω, n ^ (t - 1) * ∑ j, ∑ i, F j i ω ∂μ :=
          integral_mono_of_nonneg hlhs0 hdomInt (Filter.Eventually.of_forall hpoint)
        _ = n ^ (t - 1) * ∫ ω, ∑ j, ∑ i, F j i ω ∂μ :=
          integral_const_mul _ _
        _ = n ^ (t - 1) * ∑ j, ∫ ω, ∑ i, F j i ω ∂μ := by
          congr 1
          exact integral_finsetSum Finset.univ fun j _ =>
            integrable_finsetSum _ fun i _ => hFint j i
        _ = n ^ (t - 1) * ∑ j, ∑ i, ∫ ω, F j i ω ∂μ := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          exact integral_finsetSum Finset.univ fun i _ => hFint j i
    have hcross (j i : ι) : ∫ ω, F j i ω ∂μ ≤
        K * Real.exp (-(40 * L)) * (localScale (lambda i) L) ^ t := by
      exact coordinate_cross_moment μ W lambda hWmeas hWlaw hWindep hL ht i j
    have hcrossSum : ∑ j, ∑ i, ∫ ω, F j i ω ∂μ ≤
        n * (K * Real.exp (-(40 * L)) *
          ∑ i, (localScale (lambda i) L) ^ t) := by
      calc
        _ ≤ ∑ _j : ι, ∑ i, K * Real.exp (-(40 * L)) *
              (localScale (lambda i) L) ^ t := by
          exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hcross j i
        _ = n * (K * Real.exp (-(40 * L)) *
              ∑ i, (localScale (lambda i) L) ^ t) := by
          simp [n, Finset.mul_sum]
    have hpowSum := sum_localScale_pow_le_card_mul_pow_sum lambda hL t
    have hscale := sum_localScale_le_card_mul lambda hL
    have hscalePow : (∑ i, localScale (lambda i) L) ^ t ≤ (n * A) ^ t := by
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => by
        unfold localScale
        positivity) (by simpa [n, A] using hscale) t
    have hncard : n ≤ (r : ℝ) := by
      dsimp [n]
      exact_mod_cast hcard
    have hcoeff : n ^ (2 * t + 1) * K ≤ productMomentConstant r t := by
      calc
        n ^ (2 * t + 1) * K ≤ (r : ℝ) ^ (2 * t + 1) * K := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn0 hncard _) hK0
        _ ≤ productMomentConstant r t := product_coefficient_bound
    calc
      ∫ ω, (badAny W universalH L lambda).indicator
          (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ ≤
          n ^ (t - 1) * ∑ j, ∑ i, ∫ ω, F j i ω ∂μ := hintegral
      _ ≤ n ^ (t - 1) *
          (n * (K * Real.exp (-(40 * L)) *
            ∑ i, (localScale (lambda i) L) ^ t)) :=
        mul_le_mul_of_nonneg_left hcrossSum (pow_nonneg hn0 _)
      _ ≤ n ^ (t - 1) *
          (n * (K * Real.exp (-(40 * L)) *
            (n * (∑ i, localScale (lambda i) L) ^ t))) := by
        gcongr
      _ ≤ n ^ (t - 1) *
          (n * (K * Real.exp (-(40 * L)) * (n * (n * A) ^ t))) := by
        gcongr
      _ = (n ^ (2 * t + 1) * K) * Real.exp (-(40 * L)) * A ^ t := by
        rcases ht with rfl | rfl | rfl <;> ring
      _ ≤ productMomentConstant r t * Real.exp (-(40 * L)) * A ^ t := by
        gcongr
      _ ≤ productMomentConstant r t * Real.exp (-20 * L) * A ^ t := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
            (productMomentConstant_pos r t).le
        · exact pow_nonneg hA0 t
      _ = productMomentConstant r t * Real.exp (-20 * L) *
          (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) ^ t := rfl
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    simp [badAny, aggregateScore]
    exact mul_nonneg (mul_nonneg (productMomentConstant_pos r t).le (Real.exp_nonneg _))
      (pow_nonneg (by linarith) t)

/-- On [a measurable sample space](hyp:Ω), let [a probability law](hyp:μ) carry [four
natural-valued coordinate counts](hyp:W) with [nonnegative coordinate means](hyp:lambda). If [the
counts are measurable](hyp:hWmeas), [each count has its stated Poisson law](hyp:hWlaw), and [the
counts are mutually independent](hyp:hWindep), then for [moment order one, two, or
four](hyp:t,ht) and [a logarithmic level of at least one](hyp:L,hL), [the four-coordinate aggregate
score moment on the union of bad coordinates has the corresponding exponentially decaying local
scale bound](goal). -/
-- Apply `independent_poisson_badAny_moment` with `r = 4`; the cardinality side
-- condition is `Fintype.card_fin 4`.
theorem independent_poisson_badAny_moment_four
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (lambda : Fin 4 → ℝ≥0)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (lambda i)) μ)
    (hWindep : iIndepFun W μ)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) {L : ℝ} (hL : 1 ≤ L) :
    ∫ ω, (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ ≤
      productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) ^ t := by
  exact independent_poisson_badAny_moment μ W lambda hWmeas hWlaw hWindep
    (r := 4) (by simp) ht hL

end Causalean.Stat.Concentration.PoissonSelfNormalized
