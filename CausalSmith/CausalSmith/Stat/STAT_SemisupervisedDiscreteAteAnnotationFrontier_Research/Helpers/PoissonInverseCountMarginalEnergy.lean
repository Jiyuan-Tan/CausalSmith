module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonInverseCountRiskAssembly

/-! Marginal-count energy and final Poincare assembly for the inverse-count statistic. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open CausalSmith.Substrate.NestedPairedPoissonProductMoments

-- @node: poisson_inverse_marginal_cross_square_moment
/-- Factor the squared three-coordinate term in a marginal-count add-one increment.  [the stated conclusion](goal). -/
lemma poisson_inverse_marginal_cross_square_moment
    (lambdaS lambdaK : Bool → NNReal) (u : Real) (a : Bool) :
    (∫ k : Bool → Nat × Nat,
      ((((k a).1 : Real) / u * ((k (!a)).2 : Real) /
        ((((k a).2 + 1 : Nat) : Real) * (((k a).2 + 2 : Nat) : Real))) ^ 2)
      ∂Measure.pi (fun b : Bool ↦
        (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))) =
      ((∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lambdaS a)) *
        ∫ n : Nat, (((((n + 1 : Nat) : Real) *
          ((n + 2 : Nat) : Real)))⁻¹) ^ 2 ∂poissonMeasure (lambdaK a)) *
        ∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lambdaK (!a)) := by
  let f : Bool → (Nat × Nat) → Real := fun b z ↦
    if b = a then ((z.1 : Real) / u) ^ 2 *
      (((((z.2 + 1 : Nat) : Real) * ((z.2 + 2 : Nat) : Real)))⁻¹) ^ 2
    else (z.2 : Real) ^ 2
  have hpair (b : Bool) :
      (∫ z : Nat × Nat, ((z.1 : Real) / u) ^ 2 *
          (((((z.2 + 1 : Nat) : Real) * ((z.2 + 2 : Nat) : Real)))⁻¹) ^ 2
          ∂(poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b))) =
        (∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lambdaS b)) *
          ∫ n : Nat, (((((n + 1 : Nat) : Real) *
            ((n + 2 : Nat) : Real)))⁻¹) ^ 2 ∂poissonMeasure (lambdaK b) := by
    exact integral_prod_mul
      (μ := poissonMeasure (lambdaS b)) (ν := poissonMeasure (lambdaK b))
      (fun n : Nat ↦ ((n : Real) / u) ^ 2)
      (fun n : Nat ↦ (((((n + 1 : Nat) : Real) *
        ((n + 2 : Nat) : Real)))⁻¹) ^ 2)
  have hop (b : Bool) :
      (∫ z : Nat × Nat, (z.2 : Real) ^ 2
          ∂(poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b))) =
        ∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lambdaK b) := by
    calc
      _ = (∫ _n : Nat, (1 : Real) ∂poissonMeasure (lambdaS b)) *
          ∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lambdaK b) := by
            simpa using integral_prod_mul
              (μ := poissonMeasure (lambdaS b)) (ν := poissonMeasure (lambdaK b))
              (fun _n : Nat ↦ (1 : Real)) (fun n : Nat ↦ (n : Real) ^ 2)
      _ = _ := by simp
  rw [show (fun k : Bool → Nat × Nat ↦
      (((k a).1 : Real) / u * ((k (!a)).2 : Real) /
        ((((k a).2 + 1 : Nat) : Real) * (((k a).2 + 2 : Nat) : Real))) ^ 2) =
      fun k ↦ ∏ b, f b (k b) by
        funext k
        cases a <;> simp [f, div_eq_mul_inv] <;> ring,
    integral_fintype_prod_eq_prod]
  cases a
  · rw [Fintype.prod_bool]
    change (∫ z : Nat × Nat, (z.2 : Real) ^ 2
        ∂(poissonMeasure (lambdaS true)).prod (poissonMeasure (lambdaK true))) *
      (∫ z : Nat × Nat, ((z.1 : Real) / u) ^ 2 *
        (((((z.2 + 1 : Nat) : Real) * ((z.2 + 2 : Nat) : Real)))⁻¹) ^ 2
        ∂(poissonMeasure (lambdaS false)).prod (poissonMeasure (lambdaK false))) = _
    rw [hpair false, hop true]
    simp only [Bool.not_false]
    ring
  · rw [Fintype.prod_bool]
    change (∫ z : Nat × Nat, ((z.1 : Real) / u) ^ 2 *
        (((((z.2 + 1 : Nat) : Real) * ((z.2 + 2 : Nat) : Real)))⁻¹) ^ 2
        ∂(poissonMeasure (lambdaS true)).prod (poissonMeasure (lambdaK true))) *
      (∫ z : Nat × Nat, (z.2 : Real) ^ 2
        ∂(poissonMeasure (lambdaS false)).prod (poissonMeasure (lambdaK false))) = _
    rw [hop false, hpair true]
    simp only [Bool.not_true]

-- @node: poisson_inverse_marginal_reciprocal_square_moment
/-- Factor the one-arm reciprocal term in a marginal-count add-one increment.  [the stated conclusion](goal). -/
lemma poisson_inverse_marginal_reciprocal_square_moment
    (lambdaS lambdaK : Bool → NNReal) (u : Real) (a : Bool) :
    (∫ k : Bool → Nat × Nat,
      ((((k a).1 : Real) / u /
        (((k a).2 + 1 : Nat) : Real)) ^ 2)
      ∂Measure.pi (fun b : Bool ↦
        (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))) =
      (∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lambdaS a)) *
        ∫ n : Nat, (((n + 1 : Nat) : Real)⁻¹) ^ 2
          ∂poissonMeasure (lambdaK a) := by
  calc
    _ = ∫ z : Nat × Nat, (((z.1 : Real) / u /
          (((z.2 + 1 : Nat) : Real))) ^ 2)
        ∂(poissonMeasure (lambdaS a)).prod (poissonMeasure (lambdaK a)) :=
      integral_comp_eval
        (μ := fun b : Bool ↦
          (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))
        (i := a) (f := fun z : Nat × Nat ↦
          (((z.1 : Real) / u / (((z.2 + 1 : Nat) : Real))) ^ 2))
        (measurable_of_countable _).aestronglyMeasurable
    _ = _ := by
      rw [show (fun z : Nat × Nat ↦
          (((z.1 : Real) / u / (((z.2 + 1 : Nat) : Real))) ^ 2)) =
          fun z ↦ ((z.1 : Real) / u) ^ 2 *
            ((((z.2 + 1 : Nat) : Real)⁻¹) ^ 2) by
            funext z
            simp only [div_eq_mul_inv, mul_pow]]
      exact integral_prod_mul
        (μ := poissonMeasure (lambdaS a)) (ν := poissonMeasure (lambdaK a))
        (fun n : Nat ↦ ((n : Real) / u) ^ 2)
        (fun n : Nat ↦ ((((n + 1 : Nat) : Real)⁻¹) ^ 2))

-- @node: poisson_inverse_bidirectional_poincare_energy_scalar
/-- Add the two arm orientations of the scalar marginal-count energy bound.  [the stated conditions](hyp:heps,heps1,hw,hlambda,hnu,hllower,hnlower,hlupper,hnupper,hr2l,hr2lrate,hr2n,hr2nrate,hr4l,hr4lrate,hr4n,hr4nrate) [the stated conclusion](goal). -/
lemma poisson_inverse_bidirectional_poincare_energy_scalar
    {eps w lambda nu r2l r2n r4l r4n : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hw : 0 ≤ w)
    (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (hllower : eps * w ≤ lambda) (hnlower : eps * w ≤ nu)
    (hlupper : lambda ≤ w) (hnupper : nu ≤ w)
    (hr2l : 0 ≤ r2l) (hr2lrate : (1 + lambda) ^ 2 * r2l ≤ 8)
    (hr2n : 0 ≤ r2n) (hr2nrate : (1 + nu) ^ 2 * r2n ≤ 8)
    (hr4l : 0 ≤ r4l) (hr4lrate : (1 + lambda) ^ 4 * r4l ≤ 96)
    (hr4n : 0 ≤ r4n) (hr4nrate : (1 + nu) ^ 4 * r4n ≤ 96) :
    (lambda * (nu + nu ^ 2) * r4l + nu * r2l) +
        (nu * (lambda + lambda ^ 2) * r4n + lambda * r2n) ≤
      2 * (8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3)) / (1 + w) := by
  let C := 8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3)
  have h₁ := Causalean.Mathlib.Probability.Poisson.poisson_inverse_weight_poincare_energy_scalar
    heps heps1 hw hlambda hnu hllower hnupper hr2l hr2lrate hr4l hr4lrate
  have h₂ := Causalean.Mathlib.Probability.Poisson.poisson_inverse_weight_poincare_energy_scalar
    heps heps1 hw hnu hlambda hnlower hlupper hr2n hr2nrate hr4n hr4nrate
  have hden : 0 < 1 + w := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

-- @node: poisson_inverse_marginal_energy_with_outcome_rates
/-- Insert outcome moments into the bidirectional marginal energy estimate.  [the stated conditions](hyp:hu,hp,hql,hqn,hqlp,hqnp,heps,heps1,hw,hlambda,hnu,hllower,hnlower,hlupper,hnupper,hr2l,hr2lrate,hr2n,hr2nrate,hr4l,hr4lrate,hr4n,hr4nrate) [the stated conclusion](goal). -/
lemma poisson_inverse_marginal_energy_with_outcome_rates
    {eps p u w lambda nu ql qn r2l r2n r4l r4n : Real}
    (hu : 0 < u) (hp : 0 ≤ p) (hql : 0 ≤ ql) (hqn : 0 ≤ qn)
    (hqlp : ql ≤ p) (hqnp : qn ≤ p)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hw : 0 ≤ w)
    (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (hllower : eps * w ≤ lambda) (hnlower : eps * w ≤ nu)
    (hlupper : lambda ≤ w) (hnupper : nu ≤ w)
    (hr2l : 0 ≤ r2l) (hr2lrate : (1 + lambda) ^ 2 * r2l ≤ 8)
    (hr2n : 0 ≤ r2n) (hr2nrate : (1 + nu) ^ 2 * r2n ≤ 8)
    (hr4l : 0 ≤ r4l) (hr4lrate : (1 + lambda) ^ 4 * r4l ≤ 96)
    (hr4n : 0 ≤ r4n) (hr4nrate : (1 + nu) ^ 4 * r4n ≤ 96) :
    lambda * ((ql * u⁻¹ + ql ^ 2) * (nu + nu ^ 2) * r4l +
        (qn * u⁻¹ + qn ^ 2) * r2n) +
      nu * ((qn * u⁻¹ + qn ^ 2) * (lambda + lambda ^ 2) * r4n +
        (ql * u⁻¹ + ql ^ 2) * r2l) ≤
      (p * u⁻¹ + p ^ 2) *
        (2 * (8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3)) /
          (1 + w)) := by
  have huinv : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.le
  have hMl : ql * u⁻¹ + ql ^ 2 ≤ p * u⁻¹ + p ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqlp huinv,
      sq_nonneg (p - ql)]
  have hMn : qn * u⁻¹ + qn ^ 2 ≤ p * u⁻¹ + p ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqnp huinv,
      sq_nonneg (p - qn)]
  have hM0 : 0 ≤ p * u⁻¹ + p ^ 2 := by positivity
  have hbase := poisson_inverse_bidirectional_poincare_energy_scalar
    heps heps1 hw hlambda hnu hllower hnlower hlupper hnupper
    hr2l hr2lrate hr2n hr2nrate hr4l hr4lrate hr4n hr4nrate
  calc
    _ ≤ (p * u⁻¹ + p ^ 2) *
        ((lambda * (nu + nu ^ 2) * r4l + nu * r2l) +
          (nu * (lambda + lambda ^ 2) * r4n + lambda * r2n)) := by
      have hnu2 : 0 ≤ nu + nu ^ 2 := by positivity
      have hlambda2 : 0 ≤ lambda + lambda ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hMl
          (mul_nonneg (mul_nonneg hlambda hnu2) hr4l),
        mul_le_mul_of_nonneg_right hMn (mul_nonneg hlambda hr2n),
        mul_le_mul_of_nonneg_right hMn
          (mul_nonneg (mul_nonneg hnu hlambda2) hr4n),
        mul_le_mul_of_nonneg_right hMl (mul_nonneg hnu hr2l)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase hM0

-- @node: poisson_inverse_marginal_cell_energy_bound
/-- Rate-weighted marginal-count energy in one covariate cell.  [the stated conditions](hyp:hP,hu,ht,heps,heps1) [the stated conclusion](goal). -/
lemma poisson_inverse_marginal_cell_energy_bound {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (heps1 : eps ≤ 1) (x : Fin d) :
    (∑ a : Bool, ((Real.toNNReal (t * armMass P x a) : NNReal) : Real) *
      ∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
        ∂poissonCountLaw P u t) ≤
      4 * (8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3)) *
        (cellMass P x * u⁻¹ + cellMass P x ^ 2) /
          (1 + t * cellMass P x) := by
  classical
  let lS : Bool → NNReal := fun a ↦ Real.toNNReal (u * markedMass P x a)
  let lK : Bool → NNReal := fun a ↦ Real.toNNReal (t * armMass P x a)
  let r2 : Bool → Real := fun a ↦
    ∫ n : Nat, ((((n + 1 : Nat) : Real)⁻¹) ^ 2) ∂poissonMeasure (lK a)
  let r4 : Bool → Real := fun a ↦
    ∫ n : Nat, (((((n + 1 : Nat) : Real) *
      ((n + 2 : Nat) : Real)))⁻¹) ^ 2 ∂poissonMeasure (lK a)
  have hp0 : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
  have hs0 (a : Bool) : 0 ≤ armMass P x a :=
    Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1
  have hsle (a : Bool) : armMass P x a ≤ cellMass P x := by
    have hsplit : armMass P x a + armMass P x (!a) = cellMass P x := by
      cases a <;> simp [armMass, cellMass] <;> ring
    linarith [hs0 (!a)]
  have hq0 (a : Bool) : 0 ≤ markedMass P x a :=
    (jointMass_mem_unitInterval P x a true).1
  have hqle (a : Bool) : markedMass P x a ≤ cellMass P x := by
    calc
      markedMass P x a ≤ armMass P x a := by
        simp [markedMass, armMass]
        exact (jointMass_mem_unitInterval P x a false).1
      _ ≤ cellMass P x := hsle a
  have hlS (a : Bool) : ((lS a : NNReal) : Real) =
      u * markedMass P x a := by
    rw [Real.coe_toNNReal]
    exact mul_nonneg hu.le (hq0 a)
  have hlK (a : Bool) : ((lK a : NNReal) : Real) =
      t * armMass P x a := by
    rw [Real.coe_toNNReal]
    exact mul_nonneg ht.le (hs0 a)
  have hw : 0 ≤ t * cellMass P x := mul_nonneg ht.le hp0
  have hKl (a : Bool) : eps * (t * cellMass P x) ≤ (lK a : Real) := by
    rw [hlK]
    have h := (overlap_armMass_bounds P hP.overlap x a).1
    nlinarith [mul_le_mul_of_nonneg_left h ht.le]
  have hKu (a : Bool) : (lK a : Real) ≤ t * cellMass P x := by
    rw [hlK]
    exact mul_le_mul_of_nonneg_left (hsle a) ht.le
  have hr20 (a : Bool) : 0 ≤ r2 a := integral_nonneg fun _ ↦ sq_nonneg _
  have hr40 (a : Bool) : 0 ≤ r4 a := integral_nonneg fun _ ↦ sq_nonneg _
  have hr2rate (a : Bool) : (1 + (lK a : Real)) ^ 2 * r2 a ≤ 8 := by
    simpa [r2] using Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_sq_bound (lK a)
  have hr4rate (a : Bool) : (1 + (lK a : Real)) ^ 4 * r4 a ≤ 96 := by
    simpa [r4] using Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_pair_sq_bound (lK a)
  have hscalar := poisson_inverse_marginal_energy_with_outcome_rates
    (p := cellMass P x) (u := u) (w := t * cellMass P x)
    (lambda := (lK true : Real)) (nu := (lK false : Real))
    (ql := markedMass P x true) (qn := markedMass P x false)
    (r2l := r2 true) (r2n := r2 false) (r4l := r4 true) (r4n := r4 false)
    hu hp0 (hq0 true) (hq0 false) (hqle true) (hqle false)
    heps heps1 hw (lK true).coe_nonneg (lK false).coe_nonneg
    (hKl true) (hKl false) (hKu true) (hKu false)
    (hr20 true) (hr2rate true) (hr20 false) (hr2rate false)
    (hr40 true) (hr4rate true) (hr40 false) (hr4rate false)
  have hmem := inverseCountStatistic_memLp_and_addOne P (t := t) hu
  have hD (a : Bool) : MemLp
      (nestedPairAddOneSnd x a (inverseCountStatistic u)) 2
      (poissonCountLaw P u t) := by
    rw [poissonCountLaw_eq_nestedPairedPoissonMeasure]
    exact hmem.2.2 x a
  let cross : Bool → PoissonCounts d → Real := fun a K ↦
    ((K x a).1 : Real) / u * ((K x (!a)).2 : Real) /
      ((((K x a).2 + 1 : Nat) : Real) * (((K x a).2 + 2 : Nat) : Real))
  let recip : Bool → PoissonCounts d → Real := fun a K ↦
    ((K x a).1 : Real) / u / (((K x a).2 + 1 : Nat) : Real)
  have hparts (a : Bool) (K : PoissonCounts d) :
      nestedPairAddOneSnd x a (inverseCountStatistic u) K =
        if a then -(cross true K + recip false K)
        else cross false K + recip true K := by
    rw [inverse_count_marginal_addOne u hu.ne' x a K]
    cases a <;> simp [cross, recip] <;> ring
  have hcross0 (a : Bool) (K : PoissonCounts d) : 0 ≤ cross a K := by
    dsimp [cross]
    positivity
  have hrecip0 (a : Bool) (K : PoissonCounts d) : 0 ≤ recip a K := by
    dsimp [recip]
    positivity
  have hcrossLp (a : Bool) : MemLp (cross a) 2 (poissonCountLaw P u t) := by
    refine (hD a).mono (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards with K
    rw [hparts]
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false,
      norm_neg, Real.norm_eq_abs]
    · rw [abs_of_nonneg (hcross0 false K), abs_of_nonneg
          (add_nonneg (hcross0 false K) (hrecip0 true K))]
      linarith [hrecip0 true K]
    · rw [abs_of_nonneg (hcross0 true K), abs_of_nonneg
          (add_nonneg (hcross0 true K) (hrecip0 false K))]
      linarith [hrecip0 false K]
  have hrecipLp (a : Bool) : MemLp (recip a) 2 (poissonCountLaw P u t) := by
    refine (hD (!a)).mono (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards with K
    rw [hparts]
    cases a <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Bool.true_eq_false, norm_neg, Real.norm_eq_abs]
    · rw [abs_of_nonneg (hrecip0 false K), abs_of_nonneg
          (add_nonneg (hcross0 true K) (hrecip0 false K))]
      linarith [hcross0 true K]
    · rw [abs_of_nonneg (hrecip0 true K), abs_of_nonneg
          (add_nonneg (hcross0 false K) (hrecip0 true K))]
      linarith [hcross0 false K]
  have hE (a : Bool) :
      (∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
          ∂poissonCountLaw P u t) ≤
        2 * ((∫ K, (cross a K) ^ 2 ∂poissonCountLaw P u t) +
          ∫ K, (recip (!a) K) ^ 2 ∂poissonCountLaw P u t) := by
    calc
      _ ≤ ∫ K, 2 * ((cross a K) ^ 2 + (recip (!a) K) ^ 2)
          ∂poissonCountLaw P u t := by
        apply integral_mono_ae (hD a).integrable_sq
          (((hcrossLp a).integrable_sq.add (hrecipLp (!a)).integrable_sq).const_mul 2)
        filter_upwards with K
        rw [hparts]
        cases a <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, Bool.true_eq_false, neg_sq]
        · exact add_sq_le
        · exact add_sq_le
      _ = _ := by
        rw [integral_const_mul, integral_add (hcrossLp a).integrable_sq
          (hrecipLp (!a)).integrable_sq]
  have hMS (a : Bool) :
      (∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lS a)) ≤
        markedMass P x a * u⁻¹ + markedMass P x a ^ 2 := by
    have hm := poisson_natCast_second_moment_le (lS a)
    rw [show (fun n : Nat ↦ ((n : Real) / u) ^ 2) =
        fun n : Nat ↦ u⁻¹ ^ 2 * (n : Real) ^ 2 by
          funext n
          simp only [div_eq_mul_inv, mul_pow, inv_pow]
          ring,
      integral_const_mul]
    rw [hlS] at hm
    have huinv2 : 0 ≤ u⁻¹ ^ 2 := sq_nonneg _
    calc
      u⁻¹ ^ 2 * ∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lS a) ≤
          u⁻¹ ^ 2 * (u * markedMass P x a +
            (u * markedMass P x a) ^ 2) := mul_le_mul_of_nonneg_left hm huinv2
      _ = markedMass P x a * u⁻¹ + markedMass P x a ^ 2 := by
        field_simp
  have hcrossMoment (a : Bool) :
      (∫ K, (cross a K) ^ 2 ∂poissonCountLaw P u t) =
        (∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lS a)) *
          (∫ n : Nat, (((((n + 1 : Nat) : Real) *
            ((n + 2 : Nat) : Real)))⁻¹) ^ 2 ∂poissonMeasure (lK a)) *
          ∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lK (!a)) := by
    calc
      _ = ∫ k : Bool → Nat × Nat,
          ((((k a).1 : Real) / u * ((k (!a)).2 : Real) /
            ((((k a).2 + 1 : Nat) : Real) *
              (((k a).2 + 2 : Nat) : Real))) ^ 2)
          ∂Measure.pi (fun b : Bool ↦
            (poissonMeasure (lS b)).prod (poissonMeasure (lK b))) := by
              simpa [cross, lS, lK] using poissonCountLaw_integral_cell P u t x
                (fun k : Bool → Nat × Nat ↦
                  ((((k a).1 : Real) / u * ((k (!a)).2 : Real) /
                    ((((k a).2 + 1 : Nat) : Real) *
                      (((k a).2 + 2 : Nat) : Real))) ^ 2))
      _ = _ := poisson_inverse_marginal_cross_square_moment lS lK u a
  have hrecipMoment (a : Bool) :
      (∫ K, (recip a K) ^ 2 ∂poissonCountLaw P u t) =
        (∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lS a)) * r2 a := by
    calc
      _ = ∫ k : Bool → Nat × Nat,
          ((((k a).1 : Real) / u / (((k a).2 + 1 : Nat) : Real)) ^ 2)
          ∂Measure.pi (fun b : Bool ↦
            (poissonMeasure (lS b)).prod (poissonMeasure (lK b))) := by
              simpa [recip, lS, lK] using poissonCountLaw_integral_cell P u t x
                (fun k : Bool → Nat × Nat ↦
                  ((((k a).1 : Real) / u /
                    (((k a).2 + 1 : Nat) : Real)) ^ 2))
      _ = _ := by
        simpa [r2] using
          poisson_inverse_marginal_reciprocal_square_moment lS lK u a
  have hK2 (a : Bool) :
      (∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lK a)) ≤
        (lK a : Real) + (lK a : Real) ^ 2 := poisson_natCast_second_moment_le (lK a)
  have hEa (a : Bool) :
      (∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
          ∂poissonCountLaw P u t) ≤
        2 * (((markedMass P x a * u⁻¹ + markedMass P x a ^ 2) *
            ((lK (!a) : Real) + (lK (!a) : Real) ^ 2) * r4 a) +
          (markedMass P x (!a) * u⁻¹ + markedMass P x (!a) ^ 2) * r2 (!a)) := by
    refine hE a |>.trans ?_
    rw [hcrossMoment, hrecipMoment]
    have hMS0 (b : Bool) : 0 ≤
        ∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lS b) :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hK20 (b : Bool) : 0 ≤
        ∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lK b) :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hM0 (b : Bool) : 0 ≤
        markedMass P x b * u⁻¹ + markedMass P x b ^ 2 := by
      exact add_nonneg (mul_nonneg (hq0 b) (inv_nonneg.mpr hu.le)) (sq_nonneg _)
    have hcross₁ :
        ((∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lS a)) * r4 a) *
            (∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lK (!a))) ≤
          ((markedMass P x a * u⁻¹ + markedMass P x a ^ 2) * r4 a) *
            ((lK (!a) : Real) + (lK (!a) : Real) ^ 2) := by
      calc
        _ ≤ ((markedMass P x a * u⁻¹ + markedMass P x a ^ 2) * r4 a) *
            (∫ n : Nat, (n : Real) ^ 2 ∂poissonMeasure (lK (!a))) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hMS a) (hr40 a)) (hK20 (!a))
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left (hK2 (!a))
            (mul_nonneg (hM0 a) (hr40 a))
    have hrecip₁ :
        (∫ n : Nat, ((n : Real) / u) ^ 2 ∂poissonMeasure (lS (!a))) * r2 (!a) ≤
          (markedMass P x (!a) * u⁻¹ + markedMass P x (!a) ^ 2) * r2 (!a) := by
      exact mul_le_mul_of_nonneg_right (hMS (!a)) (hr20 (!a))
    nlinarith [hcross₁, hrecip₁]
  change (∑ a : Bool, (lK a : Real) *
      ∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
        ∂poissonCountLaw P u t) ≤ _
  rw [Fintype.sum_bool]
  have hrate0 (a : Bool) : 0 ≤ (lK a : Real) := (lK a).coe_nonneg
  calc
    (lK true : Real) *
          (∫ K, (nestedPairAddOneSnd x true (inverseCountStatistic u) K) ^ 2
            ∂poissonCountLaw P u t) +
        (lK false : Real) *
          (∫ K, (nestedPairAddOneSnd x false (inverseCountStatistic u) K) ^ 2
            ∂poissonCountLaw P u t) ≤
        (lK true : Real) * (2 *
          (((markedMass P x true * u⁻¹ + markedMass P x true ^ 2) *
              ((lK false : Real) + (lK false : Real) ^ 2) * r4 true) +
            (markedMass P x false * u⁻¹ + markedMass P x false ^ 2) * r2 false)) +
        (lK false : Real) * (2 *
          (((markedMass P x false * u⁻¹ + markedMass P x false ^ 2) *
              ((lK true : Real) + (lK true : Real) ^ 2) * r4 false) +
            (markedMass P x true * u⁻¹ + markedMass P x true ^ 2) * r2 true)) := by
      gcongr
      · exact hEa true
      · exact hEa false
    _ ≤ 2 * ((cellMass P x * u⁻¹ + cellMass P x ^ 2) *
        (2 * (8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3)) /
          (1 + t * cellMass P x))) := by
      nlinarith [hscalar]
    _ = _ := by ring

-- @node: lem:poisson-inverse-count-risk
/-- Uniform bias and variance bounds for the independent Poisson inverse-count statistic.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma poisson_inverse_count_risk {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧
    ∀ (d : Nat) (u t : Real), 0 < u → 0 < t →
    ∀ (P : DiscreteLaw d), ModelClass d eps P →
      |expectationUnder (poissonCountLaw P u t) (inverseCountStatistic u) -
          ateFunctional P| ≤ C * min 1 (d / t) ∧
      varianceUnder (poissonCountLaw P u t) (inverseCountStatistic u) ≤
        C * (u⁻¹ + t⁻¹) := by
  let A : Real := 1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2
  let B : Real := 8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3)
  let D : Real := 2 * max 1 (eps * Real.exp 1)⁻¹
  let C : Real := D + A + 4 * B + 1
  have heps1 : eps ≤ 1 := by linarith
  have hepsinv : 0 < eps⁻¹ := inv_pos.mpr heps
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < max 1 (eps * Real.exp 1)⁻¹ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro d u t hu ht P hP
  constructor
  · calc
      |expectationUnder (poissonCountLaw P u t) (inverseCountStatistic u) -
          ateFunctional P| ≤ 2 * min 1 (d / (eps * Real.exp 1 * t)) :=
        poisson_inverse_count_bias_of_expectation_eq P hP hu ht heps
          (poisson_inverse_count_expectation_eq_arm_means P hu)
      _ ≤ D * min 1 (d / t) := by
        exact poisson_bias_min_rescale d heps ht
      _ ≤ C * min 1 (d / t) := by
        have hmin : 0 ≤ min 1 ((d : Real) / t) := by positivity
        apply mul_le_mul_of_nonneg_right _ hmin
        dsimp [C]
        nlinarith [hA, hB]
  · let lambdaS : Fin d → Bool → NNReal := fun x a ↦
      Real.toNNReal (u * markedMass P x a)
    let lambdaK : Fin d → Bool → NNReal := fun x a ↦
      Real.toNNReal (t * armMass P x a)
    have hmem := inverseCountStatistic_memLp_and_addOne P (t := t) hu
    have hpoinc := nestedPairedPoisson_addOne_poincare lambdaS lambdaK
      (inverseCountStatistic u) hmem.1 hmem.2.1 hmem.2.2
    have hF : MemLp (inverseCountStatistic u) 2 (poissonCountLaw P u t) := by
      rw [poissonCountLaw_eq_nestedPairedPoissonMeasure]
      exact hmem.1
    have hvar : varianceUnder (poissonCountLaw P u t) (inverseCountStatistic u) ≤
        ∑ x : Fin d, ∑ a : Bool,
          (((lambdaS x a : NNReal) : Real) *
              ∫ K, (nestedPairAddOneFst x a (inverseCountStatistic u) K) ^ 2
                ∂poissonCountLaw P u t +
            ((lambdaK x a : NNReal) : Real) *
              ∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
                ∂poissonCountLaw P u t) := by
      rw [varianceUnder_eq_variance _ _ hF.aemeasurable,
        poissonCountLaw_eq_nestedPairedPoissonMeasure]
      simpa [lambdaS, lambdaK] using hpoinc
    have hmarkedCell (x : Fin d) :
        (∑ a : Bool, markedMass P x a) ≤ cellMass P x := by
      simp [markedMass, cellMass]
      nlinarith [show 0 ≤ jointMass P x false false from
          (jointMass_mem_unitInterval P x false false).1,
        show 0 ≤ jointMass P x true false from
          (jointMass_mem_unitInterval P x true false).1]
    have hmarkedSum : (∑ x : Fin d, ∑ a : Bool, markedMass P x a) ≤ 1 := by
      calc
        _ ≤ ∑ x : Fin d, cellMass P x :=
          Finset.sum_le_sum fun x _ ↦ hmarkedCell x
        _ = 1 := cellMass_sum_eq_one_annotation P
    have houtcome :
        (∑ x : Fin d, ∑ a : Bool,
          ((lambdaS x a : NNReal) : Real) *
            ∫ K, (nestedPairAddOneFst x a (inverseCountStatistic u) K) ^ 2
              ∂poissonCountLaw P u t) ≤ A * u⁻¹ := by
      calc
        _ ≤ ∑ x : Fin d, ∑ a : Bool, A * markedMass P x a * u⁻¹ := by
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro a _
          exact poisson_inverse_outcome_coordinate_energy_bound P hP hu ht heps x a
        _ = A * u⁻¹ * (∑ x : Fin d, ∑ a : Bool, markedMass P x a) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ ≤ A * u⁻¹ := by
          have hAu : 0 ≤ A * u⁻¹ := mul_nonneg hA.le (inv_nonneg.mpr hu.le)
          nlinarith [mul_le_mul_of_nonneg_left hmarkedSum hAu]
    have hmarginalCell (x : Fin d) :
        (∑ a : Bool, ((lambdaK x a : NNReal) : Real) *
          ∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
            ∂poissonCountLaw P u t) ≤
          4 * B * (cellMass P x * u⁻¹ + cellMass P x ^ 2) /
            (1 + t * cellMass P x) := by
      simpa [lambdaK, B] using
        poisson_inverse_marginal_cell_energy_bound P hP hu ht heps heps1 x
    have hp (x : Fin d) : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
    have hcell := poisson_cell_variance_sum_bound
      (fun x : Fin d ↦ cellMass P x) ht hp (cellMass_sum_eq_one_annotation P)
    have hmarginal :
        (∑ x : Fin d, ∑ a : Bool, ((lambdaK x a : NNReal) : Real) *
          ∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
            ∂poissonCountLaw P u t) ≤ 4 * B * (u⁻¹ + t⁻¹) := by
      calc
        _ ≤ ∑ x : Fin d,
            4 * B * (cellMass P x * u⁻¹ + cellMass P x ^ 2) /
              (1 + t * cellMass P x) :=
          Finset.sum_le_sum fun x _ ↦ hmarginalCell x
        _ ≤ ∑ x : Fin d, 4 * B *
            (cellMass P x * u⁻¹ +
              cellMass P x ^ 2 / (1 + t * cellMass P x)) := by
          apply Finset.sum_le_sum
          intro x _
          have hden : 1 ≤ 1 + t * cellMass P x := by
            nlinarith [mul_nonneg ht.le (hp x)]
          have hpu : 0 ≤ cellMass P x * u⁻¹ :=
            mul_nonneg (hp x) (inv_nonneg.mpr hu.le)
          have hfrac : (cellMass P x * u⁻¹ + cellMass P x ^ 2) /
                (1 + t * cellMass P x) ≤
              cellMass P x * u⁻¹ +
                cellMass P x ^ 2 / (1 + t * cellMass P x) := by
            rw [add_div]
            have := div_le_self hpu hden
            linarith
          calc
            4 * B * (cellMass P x * u⁻¹ + cellMass P x ^ 2) /
                (1 + t * cellMass P x) =
              4 * B * ((cellMass P x * u⁻¹ + cellMass P x ^ 2) /
                (1 + t * cellMass P x)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = 4 * B * (u⁻¹ * (∑ x : Fin d, cellMass P x) +
            ∑ x : Fin d, cellMass P x ^ 2 / (1 + t * cellMass P x)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          congr 2
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ ≤ 4 * B * (u⁻¹ + t⁻¹) := by
          rw [cellMass_sum_eq_one_annotation P, mul_one]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa [add_comm] using add_le_add_left hcell u⁻¹
    calc
      varianceUnder (poissonCountLaw P u t) (inverseCountStatistic u) ≤
          (∑ x : Fin d, ∑ a : Bool,
            ((lambdaS x a : NNReal) : Real) *
              ∫ K, (nestedPairAddOneFst x a (inverseCountStatistic u) K) ^ 2
                ∂poissonCountLaw P u t) +
          (∑ x : Fin d, ∑ a : Bool,
            ((lambdaK x a : NNReal) : Real) *
              ∫ K, (nestedPairAddOneSnd x a (inverseCountStatistic u) K) ^ 2
                ∂poissonCountLaw P u t) := by
        refine hvar.trans_eq ?_
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib]
      _ ≤ A * u⁻¹ + 4 * B * (u⁻¹ + t⁻¹) := add_le_add houtcome hmarginal
      _ ≤ C * (u⁻¹ + t⁻¹) := by
        have huinv : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.le
        have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
        dsimp [C]
        nlinarith [hD, hA, hB]

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
