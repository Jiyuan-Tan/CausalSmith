module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonInverseCount
public import CausalSmith.Substrate.NestedPairedPoissonProductMoments

/-! Product-measure identities used to assemble the inverse-count risk bound. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open CausalSmith.Substrate.NestedPairedPoissonProductMoments

-- @node: poissonCountLaw_eq_nestedPairedPoissonMeasure
/-- The paper-facing count law is definitionally the nested paired-Poisson
product used by the tensorized Poincare and factorization lemmas.  [the stated conclusion](goal). -/
lemma poissonCountLaw_eq_nestedPairedPoissonMeasure {d : Nat}
    (P : DiscreteLaw d) (u t : Real) :
    poissonCountLaw P u t =
      nestedPairedPoissonMeasure
        (fun x a => Real.toNNReal (u * markedMass P x a))
        (fun x a => Real.toNNReal (t * armMass P x a)) := by
  rfl

-- @node: varianceUnder_eq_variance
/-- The local centered-second-moment wrapper agrees with Mathlib's variance
for measurable real statistics.  [the stated conditions](hyp:hf) [the stated conclusion](goal). -/
lemma varianceUnder_eq_variance {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (f : alpha -> Real) (hf : AEMeasurable f mu) :
    varianceUnder mu f = variance f mu := by
  rw [variance_eq_integral hf]
  rfl

-- @node: poissonCountLaw_integral_cell
/-- An integrand depending on one covariate cell can be integrated against
the corresponding inner arm-product law.  [the stated conclusion](goal). -/
lemma poissonCountLaw_integral_cell {d : Nat} (P : DiscreteLaw d)
    (u t : Real) (x : Fin d) (F : (Bool -> Nat × Nat) -> Real) :
    (∫ K, F (K x) ∂poissonCountLaw P u t) =
      ∫ k, F k ∂Measure.pi (fun a : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
          (poissonMeasure (Real.toNNReal (t * armMass P x a))) ) := by
  rw [poissonCountLaw_eq_nestedPairedPoissonMeasure]
  exact integral_comp_eval (measurable_of_countable _).aestronglyMeasurable

-- @node: poissonCountLaw_integral_arm
/-- A one-arm integrand further reduces to the scalar pair of independent
outcome and marginal Poisson counts.  [the stated conclusion](goal). -/
lemma poissonCountLaw_integral_arm {d : Nat} (P : DiscreteLaw d)
    (u t : Real) (x : Fin d) (a : Bool) (F : Nat × Nat -> Real) :
    (∫ K, F (K x a) ∂poissonCountLaw P u t) =
      ∫ z, F z ∂
        (poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
          (poissonMeasure (Real.toNNReal (t * armMass P x a))) := by
  calc
    _ = ∫ k, F (k a) ∂Measure.pi (fun b : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x b))).prod
          (poissonMeasure (Real.toNNReal (t * armMass P x b)))) :=
      poissonCountLaw_integral_cell P u t x (fun k => F (k a))
    _ = _ := integral_comp_eval (measurable_of_countable _).aestronglyMeasurable

-- @node: poisson_inverse_cross_moment_true
/-- Factorization of the three independent scalar counts in the treated-arm
cross term of an inverse-count weight.  [the stated conclusion](goal). -/
lemma poisson_inverse_cross_moment_true (lambdaS lambdaK : Bool -> NNReal)
    (u : Real) :
    (∫ k : Bool -> Nat × Nat,
      ((k true).1 : Real) / u * ((k false).2 : Real) *
        (((k true).2 + 1 : Nat) : Real)⁻¹
      ∂Measure.pi (fun a : Bool =>
        (poissonMeasure (lambdaS a)).prod (poissonMeasure (lambdaK a)))) =
      ((lambdaS true : Real) / u) * (lambdaK false : Real) *
        (∫ n : Nat, (((n + 1 : Nat) : Real))⁻¹
          ∂poissonMeasure (lambdaK true)) := by
  let f : Bool -> (Nat × Nat) -> Real := fun b z =>
    if b then ((z.1 : Real) / u) * (((z.2 + 1 : Nat) : Real))⁻¹
    else (z.2 : Real)
  have hfun : (fun k : Bool -> Nat × Nat =>
      ((k true).1 : Real) / u * ((k false).2 : Real) *
        (((k true).2 + 1 : Nat) : Real)⁻¹) =
      fun k => ∏ b, f b (k b) := by
    funext k
    simp [f, mul_assoc, mul_comm]
  rw [hfun, integral_fintype_prod_eq_prod]
  simp only [Fintype.prod_bool, f, Bool.false_eq_true, ↓reduceIte]
  rw [show (∫ x : Nat × Nat, ((x.1 : Real) / u) *
      (((x.2 + 1 : Nat) : Real))⁻¹ ∂(poissonMeasure (lambdaS true)).prod
        (poissonMeasure (lambdaK true))) =
      (∫ n : Nat, (n : Real) / u ∂poissonMeasure (lambdaS true)) *
        ∫ n : Nat, (((n + 1 : Nat) : Real))⁻¹
          ∂poissonMeasure (lambdaK true) by
        exact integral_prod_mul
          (μ := poissonMeasure (lambdaS true))
          (ν := poissonMeasure (lambdaK true))
          (fun n : Nat => (n : Real) / u)
          (fun n : Nat => (((n + 1 : Nat) : Real))⁻¹),
    show (∫ x : Nat × Nat, (x.2 : Real)
        ∂(poissonMeasure (lambdaS false)).prod (poissonMeasure (lambdaK false))) =
      (∫ _n : Nat, (1 : Real) ∂poissonMeasure (lambdaS false)) *
        ∫ n : Nat, (n : Real) ∂poissonMeasure (lambdaK false) by
        simpa using integral_prod_mul
          (μ := poissonMeasure (lambdaS false))
          (ν := poissonMeasure (lambdaK false))
          (fun _n : Nat => (1 : Real)) (fun n : Nat => (n : Real)), integral_div]
  rw [Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment,
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  simp
  ring

-- @node: poisson_inverse_cross_moment_false
/-- Control-arm counterpart of `poisson_inverse_cross_moment_true`.  [the stated conclusion](goal). -/
lemma poisson_inverse_cross_moment_false (lambdaS lambdaK : Bool -> NNReal)
    (u : Real) :
    (∫ k : Bool -> Nat × Nat,
      ((k false).1 : Real) / u * ((k true).2 : Real) *
        (((k false).2 + 1 : Nat) : Real)⁻¹
      ∂Measure.pi (fun a : Bool =>
        (poissonMeasure (lambdaS a)).prod (poissonMeasure (lambdaK a)))) =
      ((lambdaS false : Real) / u) * (lambdaK true : Real) *
        (∫ n : Nat, (((n + 1 : Nat) : Real))⁻¹
          ∂poissonMeasure (lambdaK false)) := by
  let f : Bool -> (Nat × Nat) -> Real := fun b z =>
    if b then (z.2 : Real)
    else ((z.1 : Real) / u) * (((z.2 + 1 : Nat) : Real))⁻¹
  have hfun : (fun k : Bool -> Nat × Nat =>
      ((k false).1 : Real) / u * ((k true).2 : Real) *
        (((k false).2 + 1 : Nat) : Real)⁻¹) =
      fun k => ∏ b, f b (k b) := by
    funext k
    simp [f]
    ring
  rw [hfun, integral_fintype_prod_eq_prod]
  simp only [Fintype.prod_bool, f, Bool.false_eq_true, ↓reduceIte]
  rw [show (∫ x : Nat × Nat, ((x.1 : Real) / u) *
      (((x.2 + 1 : Nat) : Real))⁻¹ ∂(poissonMeasure (lambdaS false)).prod
        (poissonMeasure (lambdaK false))) =
      (∫ n : Nat, (n : Real) / u ∂poissonMeasure (lambdaS false)) *
        ∫ n : Nat, (((n + 1 : Nat) : Real))⁻¹
          ∂poissonMeasure (lambdaK false) by
        exact integral_prod_mul
          (μ := poissonMeasure (lambdaS false))
          (ν := poissonMeasure (lambdaK false))
          (fun n : Nat => (n : Real) / u)
          (fun n : Nat => (((n + 1 : Nat) : Real))⁻¹),
    show (∫ x : Nat × Nat, (x.2 : Real)
        ∂(poissonMeasure (lambdaS true)).prod (poissonMeasure (lambdaK true))) =
      (∫ _n : Nat, (1 : Real) ∂poissonMeasure (lambdaS true)) *
        ∫ n : Nat, (n : Real) ∂poissonMeasure (lambdaK true) by
        simpa using integral_prod_mul
          (μ := poissonMeasure (lambdaS true))
          (ν := poissonMeasure (lambdaK true))
          (fun _n : Nat => (1 : Real)) (fun n : Nat => (n : Real)), integral_div]
  rw [Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment,
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  simp
  ring

-- @node: poisson_inverse_cross_moment
/-- Uniform arm-indexed form of the inverse-count cross-moment identity.  [the stated conclusion](goal). -/
lemma poisson_inverse_cross_moment (lambdaS lambdaK : Bool -> NNReal)
    (u : Real) (a : Bool) :
    (∫ k : Bool -> Nat × Nat,
      ((k a).1 : Real) / u * ((k (!a)).2 : Real) *
        (((k a).2 + 1 : Nat) : Real)⁻¹
      ∂Measure.pi (fun b : Bool =>
        (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))) =
      ((lambdaS a : Real) / u) * (lambdaK (!a) : Real) *
        (∫ n : Nat, (((n + 1 : Nat) : Real))⁻¹
          ∂poissonMeasure (lambdaK a)) := by
  cases a
  · simpa using poisson_inverse_cross_moment_false lambdaS lambdaK u
  · simpa using poisson_inverse_cross_moment_true lambdaS lambdaK u

-- @node: poisson_inverse_outcome_mean
/-- The outcome-count part of one arm's inverse-count summand has its Poisson
mean divided by the outcome intensity.  [the stated conclusion](goal). -/
lemma poisson_inverse_outcome_mean (lambdaS lambdaK : Bool -> NNReal)
    (u : Real) (a : Bool) :
    (∫ k : Bool -> Nat × Nat, ((k a).1 : Real) / u
      ∂Measure.pi (fun b : Bool =>
        (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))) =
      (lambdaS a : Real) / u := by
  calc
    _ = ∫ z : Nat × Nat, (z.1 : Real) / u
        ∂(poissonMeasure (lambdaS a)).prod (poissonMeasure (lambdaK a)) :=
      integral_comp_eval
        (μ := fun b : Bool =>
          (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))
        (i := a) (f := fun z : Nat × Nat => (z.1 : Real) / u)
        (measurable_of_countable _).aestronglyMeasurable
    _ = (∫ n : Nat, (n : Real) / u ∂poissonMeasure (lambdaS a)) *
        ∫ _n : Nat, (1 : Real) ∂poissonMeasure (lambdaK a) := by
      simpa using integral_prod_mul
        (μ := poissonMeasure (lambdaS a)) (ν := poissonMeasure (lambdaK a))
        (fun n : Nat => (n : Real) / u) (fun _n : Nat => (1 : Real))
    _ = _ := by
      rw [integral_div, Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
      simp

-- @node: inverse_count_outcome_addOne
/-- Adding one outcome-success count changes only its arm's summand, by the
corresponding inverse-count weight.  [the stated conditions](hyp:hu) [the stated conclusion](goal). -/
lemma inverse_count_outcome_addOne {d : Nat} (u : Real) (hu : u ≠ 0)
    (x : Fin d) (a : Bool) (K : PoissonCounts d) :
    nestedPairAddOneFst x a (inverseCountStatistic u) K =
      (if a then 1 else -1) / u *
        (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
          (((K x a).2 + 1 : Nat) : Real) := by
  classical
  simp only [nestedPairAddOneFst, inverseCountStatistic]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · cases a <;> simp [Function.update, hu] <;> field_simp <;> ring
  · intro y _ hy
    simp [Function.update, hy]
  · simp

-- @node: inverse_count_marginal_addOne
/-- Adding one marginal count has the two reciprocal increments displayed in
the Poincare calculation.  [the stated conditions](hyp:hu) [the stated conclusion](goal). -/
lemma inverse_count_marginal_addOne {d : Nat} (u : Real) (hu : u ≠ 0)
    (x : Fin d) (a : Bool) (K : PoissonCounts d) :
    nestedPairAddOneSnd x a (inverseCountStatistic u) K =
      if a then
        -((K x true).1 : Real) / u * ((K x false).2 : Real) /
            ((((K x true).2 + 1 : Nat) : Real) *
              (((K x true).2 + 2 : Nat) : Real)) -
          ((K x false).1 : Real) / u /
            (((K x false).2 + 1 : Nat) : Real)
      else
        ((K x true).1 : Real) / u /
            (((K x true).2 + 1 : Nat) : Real) +
          ((K x false).1 : Real) / u * ((K x true).2 : Real) /
            ((((K x false).2 + 1 : Nat) : Real) *
              (((K x false).2 + 2 : Nat) : Real)) := by
  classical
  simp only [nestedPairAddOneSnd, inverseCountStatistic]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · cases a <;> simp [Function.update, hu] <;> field_simp <;> ring
  · intro y _ hy
    simp [Function.update, hy]
  · simp

-- @node: poisson_inverse_weight_mean_mul_rate
/-- The exact mean of `1 + V / (K + 1)`, in a multiplied form that remains
valid when the denominator-count rate is zero.  [the stated conclusion](goal). -/
lemma poisson_inverse_weight_mean_mul_rate (lambda nu : NNReal) :
    (lambda : Real) *
      (∫ z : Nat × Nat,
        (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
          ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
      (lambda : Real) + (nu : Real) * (1 - Real.exp (-(lambda : Real))) := by
  let r : Nat → Real := fun k ↦ (((k + 1 : Nat) : Real))⁻¹
  have hr : Integrable r (poissonMeasure lambda) :=
    (Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two lambda).integrable (by norm_num)
  have hk : Integrable (fun k : Nat ↦ (k : Real)) (poissonMeasure nu) :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two nu).integrable (by norm_num)
  have hmean : (∫ k : Nat, (k : Real) ∂poissonMeasure nu) = (nu : Real) :=
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment nu
  have hprod :
      (∫ z : Nat × Nat, (z.2 : Real) * r z.1
        ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
        (∫ k : Nat, r k ∂poissonMeasure lambda) *
          ∫ v : Nat, (v : Real) ∂poissonMeasure nu := by
    simpa [mul_comm] using
      (integral_prod_mul (μ := poissonMeasure lambda) (ν := poissonMeasure nu)
        r (fun v : Nat ↦ (v : Real)))
  have hcross : Integrable (fun z : Nat × Nat ↦ (z.2 : Real) * r z.1)
      ((poissonMeasure lambda).prod (poissonMeasure nu)) := by
    apply (hr.mul_prod hk).congr
    filter_upwards with z
    simp [mul_comm]
  rw [integral_add (integrable_const 1) hcross]
  rw [hprod, hmean]
  simp only [integral_const]
  have huniv : ((poissonMeasure lambda).prod (poissonMeasure nu)).real Set.univ = 1 := by
    simp [Measure.real]
  rw [huniv]
  norm_num
  rw [mul_add, mul_one]
  congr 1
  calc
    (lambda : Real) * ((∫ k : Nat, r k ∂poissonMeasure lambda) * (nu : Real)) =
        (nu : Real) * ((lambda : Real) *
          ∫ k : Nat, r k ∂poissonMeasure lambda) := by ring
    _ = (nu : Real) * (1 - Real.exp (-(lambda : Real))) := by
      rw [Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_first_moment]

-- @node: poisson_inverse_arm_expectation_scalar
/-- Algebraic form of the per-arm expectation calculation.  The multiplied
reciprocal identity is enough even when the arm mass `s` vanishes.  [the stated conditions](hyp:ht,hmean) [the stated conclusion](goal). -/
lemma poisson_inverse_arm_expectation_scalar
    {p s mu t w : Real} (ht : 0 < t)
    (hmean : (t * s) * w = t * s + t * (p - s) *
      (1 - Real.exp (-(t * s)))) :
    (s * mu) * w = p * mu - (p - s) * mu * Real.exp (-(t * s)) := by
  have hscaled : s * w = s + (p - s) *
      (1 - Real.exp (-(t * s))) := by
    apply (mul_left_cancel₀ ht.ne')
    nlinarith
  calc
    (s * mu) * w = mu * (s * w) := by ring
    _ = mu * (s + (p - s) * (1 - Real.exp (-(t * s)))) := by rw [hscaled]
    _ = p * mu - (p - s) * mu * Real.exp (-(t * s)) := by ring

-- @node: poisson_inverse_arm_bias_envelope
/-- Overlap turns the exact missing-cell term for one arm into the exponential
cell-mass envelope used by `inverse_count_bias_aggregate`.  [the stated conditions](hyp:ht,hp,hs_nonneg,hs_le,hmu,hlower,hmean) [the stated conclusion](goal). -/
lemma poisson_inverse_arm_bias_envelope
    {p s mu eps t mean : Real} (ht : 0 < t) (hp : 0 ≤ p)
    (hs_nonneg : 0 ≤ s) (hs_le : s ≤ p) (hmu : mu ∈ Set.Icc (0 : Real) 1)
    (hlower : eps * p ≤ s)
    (hmean : mean = p * mu - (p - s) * mu * Real.exp (-(t * s))) :
    |mean - p * mu| ≤ p * Real.exp (-eps * t * p) := by
  have hexp : Real.exp (-(t * s)) ≤ Real.exp (-eps * t * p) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlower ht.le]
  rw [hmean]
  have hnonneg : 0 ≤ (p - s) * mu * Real.exp (-(t * s)) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hs_le) hmu.1) (Real.exp_pos _).le
  rw [show p * mu - (p - s) * mu * Real.exp (-(t * s)) - p * mu =
      -((p - s) * mu * Real.exp (-(t * s))) by ring,
    abs_neg, abs_of_nonneg hnonneg]
  calc
    (p - s) * mu * Real.exp (-(t * s)) ≤
        (p - s) * 1 * Real.exp (-(t * s)) := by
          gcongr
          exact hmu.2
    _ ≤ p * 1 * Real.exp (-(t * s)) := by nlinarith [Real.exp_pos (-(t * s))]
    _ ≤ p * 1 * Real.exp (-eps * t * p) := by gcongr
    _ = p * Real.exp (-eps * t * p) := by ring

-- @node: poisson_cell_variance_sum_bound
/-- The cellwise variance remainder sums at the marginal-information rate,
without any minimum-cell-mass assumption.  [the stated conditions](hyp:ht,hp,hsum) [the stated conclusion](goal). -/
lemma poisson_cell_variance_sum_bound {d : Nat} (p : Fin d → Real)
    {t : Real} (ht : 0 < t) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    (∑ x, p x ^ 2 / (1 + t * p x)) ≤ t⁻¹ := by
  calc
    (∑ x, p x ^ 2 / (1 + t * p x)) ≤ ∑ x, p x / t := by
      apply Finset.sum_le_sum
      intro x _
      have htp : 0 ≤ t * p x := mul_nonneg ht.le (hp x)
      have hden : 0 < 1 + t * p x := by linarith
      apply (div_le_div_iff₀ hden ht).2
      nlinarith [hp x]
    _ = t⁻¹ := by
      rw [← Finset.sum_div, hsum]
      simp [one_div]

-- @node: inverse_count_variance_aggregate
/-- Aggregate the two armwise cell variance bounds after the product-measure
calculation.  The marked masses consume the outcome-information budget, while
the squared cell masses consume the marginal-information budget.  [the stated conditions](hyp:hu,ht,hA,hB,hp,hsump,hq0,hq1,hsumq,hv,hV) [the stated conclusion](goal). -/
lemma inverse_count_variance_aggregate {d : Nat}
    (p q0 q1 v0 v1 : Fin d → Real) {u t A B V : Real}
    (hu : 0 < u) (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : ∀ x, 0 ≤ p x) (hsump : ∑ x, p x = 1)
    (hq0 : ∀ x, 0 ≤ q0 x) (hq1 : ∀ x, 0 ≤ q1 x)
    (hsumq : ∑ x, (q0 x + q1 x) ≤ 1)
    (hv : ∀ x (a : Bool),
      (if a then v1 x else v0 x) ≤
        A * (if a then q1 x else q0 x) * u⁻¹ +
          B * p x ^ 2 / (1 + t * p x))
    (hV : V ≤ 2 * ∑ x, (v0 x + v1 x)) :
    V ≤ 4 * max A B * (u⁻¹ + t⁻¹) := by
  have hcell := poisson_cell_variance_sum_bound p ht hp hsump
  have hsumarms :
      (∑ x, (v0 x + v1 x)) ≤
        A * u⁻¹ * (∑ x, (q0 x + q1 x)) +
          2 * B * (∑ x, p x ^ 2 / (1 + t * p x)) := by
    calc
      (∑ x, (v0 x + v1 x)) ≤
          ∑ x, ((A * q0 x * u⁻¹ + B * p x ^ 2 / (1 + t * p x)) +
            (A * q1 x * u⁻¹ + B * p x ^ 2 / (1 + t * p x))) := by
        apply Finset.sum_le_sum
        intro x _
        exact add_le_add (by simpa using hv x false) (by simpa using hv x true)
      _ = A * u⁻¹ * (∑ x, (q0 x + q1 x)) +
          2 * B * (∑ x, p x ^ 2 / (1 + t * p x)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hAu : 0 ≤ A * u⁻¹ := mul_nonneg hA (inv_nonneg.mpr hu.le)
  have hBt : 0 ≤ 2 * B := by positivity
  have hsumarms' :
      (∑ x, (v0 x + v1 x)) ≤ A * u⁻¹ + 2 * B * t⁻¹ := by
    calc
      _ ≤ A * u⁻¹ * (∑ x, (q0 x + q1 x)) +
          2 * B * (∑ x, p x ^ 2 / (1 + t * p x)) := hsumarms
      _ ≤ A * u⁻¹ * 1 + 2 * B * t⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left hsumq hAu)
          (mul_le_mul_of_nonneg_left hcell hBt)
      _ = A * u⁻¹ + 2 * B * t⁻¹ := by ring
  have hAle : A ≤ max A B := le_max_left _ _
  have hBle : B ≤ max A B := le_max_right _ _
  have huinv : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.le
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  calc
    V ≤ 2 * ∑ x, (v0 x + v1 x) := hV
    _ ≤ 2 * (A * u⁻¹ + 2 * B * t⁻¹) := by gcongr
    _ ≤ 4 * max A B * (u⁻¹ + t⁻¹) := by
      nlinarith [mul_le_mul_of_nonneg_right hAle huinv,
        mul_le_mul_of_nonneg_right hBle htinv]

-- @node: inverseCountStatistic_memLp_and_addOne
/-- The inverse-count statistic and all of its coordinate add-one increments
are square-integrable under the nested Poisson law.  This packages the
polynomial-growth side conditions needed by the tensorized Poincare theorem.  [the stated conditions](hyp:hu) [the stated conclusion](goal). -/
lemma inverseCountStatistic_memLp_and_addOne {d : Nat} (P : DiscreteLaw d)
    {u t : Real} (hu : 0 < u) :
    let lambda₁ : Fin d → Bool → NNReal := fun x a ↦
      Real.toNNReal (u * markedMass P x a)
    let lambda₂ : Fin d → Bool → NNReal := fun x a ↦
      Real.toNNReal (t * armMass P x a)
    MemLp (inverseCountStatistic u) 2
        (nestedPairedPoissonMeasure lambda₁ lambda₂) ∧
      (∀ x a, MemLp (nestedPairAddOneFst x a (inverseCountStatistic u)) 2
        (nestedPairedPoissonMeasure lambda₁ lambda₂)) ∧
      (∀ x a, MemLp (nestedPairAddOneSnd x a (inverseCountStatistic u)) 2
        (nestedPairedPoissonMeasure lambda₁ lambda₂)) := by
  classical
  dsimp only
  let total : PoissonCounts d → Real := fun K ↦
    (nestedPairedTotalCount K : Real)
  have hcoord (K : PoissonCounts d) (x : Fin d) (a : Bool) :
      ((K x a).1 : Real) ≤ total K := by
    dsimp [total, nestedPairedTotalCount]
    have hnat : (K x a).1 ≤ ∑ i, ∑ b, ((K i b).1 + (K i b).2) := by
      calc
        (K x a).1 ≤ (K x a).1 + (K x a).2 := Nat.le_add_right _ _
        _ ≤ ∑ b, ((K x b).1 + (K x b).2) := by
          exact Finset.single_le_sum
            (f := fun b : Bool ↦ (K x b).1 + (K x b).2)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        _ ≤ ∑ i, ∑ b, ((K i b).1 + (K i b).2) := by
          exact Finset.single_le_sum
            (f := fun i : Fin d ↦ ∑ b, ((K i b).1 + (K i b).2))
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ x)
    exact_mod_cast hnat
  have hmarg (K : PoissonCounts d) (x : Fin d) (a : Bool) :
      ((K x a).2 : Real) ≤ total K := by
    dsimp [total, nestedPairedTotalCount]
    have hnat : (K x a).2 ≤ ∑ i, ∑ b, ((K i b).1 + (K i b).2) := by
      calc
        (K x a).2 ≤ (K x a).1 + (K x a).2 := Nat.le_add_left _ _
        _ ≤ ∑ b, ((K x b).1 + (K x b).2) := by
          exact Finset.single_le_sum
            (f := fun b : Bool ↦ (K x b).1 + (K x b).2)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        _ ≤ ∑ i, ∑ b, ((K i b).1 + (K i b).2) :=
          by exact Finset.single_le_sum
              (f := fun i : Fin d ↦ ∑ b, ((K i b).1 + (K i b).2))
              (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.zero_le _)
              (Finset.mem_univ x)
    exact_mod_cast hnat
  have hbound (K : PoissonCounts d) :
      |inverseCountStatistic u K| ≤
        ((4 * d : Nat) : Real) * |u⁻¹| * (1 + total K) ^ 2 := by
    rw [inverseCountStatistic]
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply le_trans (Finset.sum_le_sum fun x _ ↦ abs_sub _ _)
    have htotal : 0 ≤ total K := by dsimp [total]; positivity
    have hone : 0 ≤ 1 + total K := by positivity
    have harm (x : Fin d) (a : Bool) :
        |((K x a).1 : Real) / u *
            (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
              (((K x a).2 + 1 : Nat) : Real)| ≤
          2 * |u⁻¹| * (1 + total K) ^ 2 := by
      have hden : (1 : Real) ≤ (((K x a).2 + 1 : Nat) : Real) := by
        exact_mod_cast Nat.le_add_left 1 (K x a).2
      have hnum : (((K x false).2 + (K x true).2 + 1 : Nat) : Real) ≤
          1 + 2 * total K := by
        norm_num [Nat.cast_add]
        nlinarith [hmarg K x false, hmarg K x true]
      simp only [div_eq_mul_inv, abs_mul]
      rw [abs_of_nonneg (show 0 ≤ ((K x a).1 : Real) by positivity),
        abs_of_nonneg (show 0 ≤
          (((K x false).2 + (K x true).2 + 1 : Nat) : Real) by positivity)]
      have hdinv : ((((K x a).2 + 1 : Nat) : Real))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ hden
      have hdinvAbs : |((((K x a).2 + 1 : Nat) : Real))⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        exact hdinv
      have hfirst : ((K x a).1 : Real) ≤ total K := hcoord K x a
      have hinv0 : 0 ≤ |u⁻¹| := abs_nonneg _
      have hcast0 : 0 ≤ ((K x a).1 : Real) := by positivity
      have hnum0 : 0 ≤ (((K x false).2 + (K x true).2 + 1 : Nat) : Real) := by
        positivity
      have hdinv0 : 0 ≤ ((((K x a).2 + 1 : Nat) : Real))⁻¹ := by positivity
      calc
        ((K x a).1 : Real) * |u⁻¹| *
              (((K x false).2 + (K x true).2 + 1 : Nat) : Real) *
              |((((K x a).2 + 1 : Nat) : Real))⁻¹| ≤
            total K * |u⁻¹| * (1 + 2 * total K) * 1 := by
              gcongr
        _ ≤ 2 * |u⁻¹| * (1 + total K) ^ 2 := by
          have hpoly : total K * (1 + 2 * total K) ≤
              2 * (1 + total K) ^ 2 := by nlinarith [sq_nonneg (total K)]
          nlinarith [mul_le_mul_of_nonneg_left hpoly hinv0]
    calc
      ∑ x, (|((K x true).1 : Real) / u *
              (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
                (((K x true).2 + 1 : Nat) : Real)| +
            |((K x false).1 : Real) / u *
              (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
                (((K x false).2 + 1 : Nat) : Real)|) ≤
          ∑ _x : Fin d, (4 * |u⁻¹| * (1 + total K) ^ 2) := by
            apply Finset.sum_le_sum
            intro x _
            nlinarith [harm x true, harm x false]
      _ = ((4 * d : Nat) : Real) * |u⁻¹| * (1 + total K) ^ 2 := by
        simp
        push_cast
        ring
  exact memLp_nestedPairedPoisson_and_addOne_of_polynomial_bound
    (fun x a ↦ Real.toNNReal (u * markedMass P x a))
    (fun x a ↦ Real.toNNReal (t * armMass P x a))
    (inverseCountStatistic u) (measurable_of_countable _)
    (((4 * d : Nat) : Real) * |u⁻¹|) 2 (by positivity) (by
      intro K
      simpa [total] using hbound K)

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
