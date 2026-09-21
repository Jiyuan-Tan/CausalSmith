module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonInverseCountAssembly

/-! Final expectation and variance assembly for the inverse-count statistic. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open CausalSmith.Substrate.NestedPairedPoissonProductMoments

-- @node: poisson_inverse_arm_mean_formula
/-- Exact model-specific mean of one arm's inverse-count contribution.  [the stated conditions](hyp:hu,ht) [the stated conclusion](goal). -/
lemma poisson_inverse_arm_mean_formula {d : Nat} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) {u t : Real} (hu : 0 < u) (ht : 0 < t) :
    let lambdaS : Bool → NNReal := fun b ↦
      Real.toNNReal (u * markedMass P x b)
    let lambdaK : Bool → NNReal := fun b ↦
      Real.toNNReal (t * armMass P x b)
    ((lambdaS a : Real) / u) *
      (∫ z : Nat × Nat,
        (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
          ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a)))) =
      cellMass P x * outcomeMean P a x -
        (cellMass P x - armMass P x a) * outcomeMean P a x *
          Real.exp (-(t * armMass P x a)) := by
  dsimp only
  have hs0 : 0 ≤ armMass P x a := by
    exact Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1
  have hso0 : 0 ≤ armMass P x (!a) := by
    exact Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x (!a) y).1
  have hq0 : 0 ≤ markedMass P x a := (jointMass_mem_unitInterval P x a true).1
  have hp_split : armMass P x a + armMass P x (!a) = cellMass P x := by
    cases a <;> simp [armMass, cellMass] <;> ring
  have hrateS : ((Real.toNNReal (u * markedMass P x a) : NNReal) : Real) =
      u * markedMass P x a := by
    rw [Real.coe_toNNReal]
    positivity
  have hrateK : ((Real.toNNReal (t * armMass P x a) : NNReal) : Real) =
      t * armMass P x a := by
    rw [Real.coe_toNNReal]
    positivity
  have hrateKo : ((Real.toNNReal (t * armMass P x (!a)) : NNReal) : Real) =
      t * armMass P x (!a) := by
    rw [Real.coe_toNNReal]
    positivity
  let w : Real := ∫ z : Nat × Nat,
    (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
      ∂(poissonMeasure (Real.toNNReal (t * armMass P x a))).prod
        (poissonMeasure (Real.toNNReal (t * armMass P x (!a))))
  have hw : (t * armMass P x a) * w =
      t * armMass P x a + t * (cellMass P x - armMass P x a) *
        (1 - Real.exp (-(t * armMass P x a))) := by
    have h := poisson_inverse_weight_mean_mul_rate
      (Real.toNNReal (t * armMass P x a))
      (Real.toNNReal (t * armMass P x (!a)))
    rw [hrateK, hrateKo] at h
    dsimp [w]
    rw [← hp_split]
    convert h using 1 <;> ring
  rw [hrateS]
  rw [markedMass_eq_armMass_mul_outcomeMean]
  change (u * (armMass P x a * outcomeMean P a x) / u) * w = _
  rw [mul_div_cancel_left₀ _ hu.ne']
  exact poisson_inverse_arm_expectation_scalar ht hw

-- @node: poisson_inverse_arm_mean_envelope
/-- The exact arm mean has the exponential missing-cell envelope under overlap.  [the stated conditions](hyp:hP,hu,ht,heps) [the stated conclusion](goal). -/
lemma poisson_inverse_arm_mean_envelope {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P) (x : Fin d) (a : Bool)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps) :
    let lambdaS : Bool → NNReal := fun b ↦
      Real.toNNReal (u * markedMass P x b)
    let lambdaK : Bool → NNReal := fun b ↦
      Real.toNNReal (t * armMass P x b)
    |((lambdaS a : Real) / u) *
        (∫ z : Nat × Nat,
          (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
            ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a)))) -
        cellMass P x * outcomeMean P a x| ≤
      cellMass P x * Real.exp (-eps * t * cellMass P x) := by
  dsimp only
  have hb := overlap_armMass_bounds P hP.overlap x a
  have hp0 := (cellMass_mem_unitInterval P x).1
  have hs0 : 0 ≤ armMass P x a := by
    exact Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1
  have hsle : armMass P x a ≤ cellMass P x := by
    nlinarith [hb.2]
  apply poisson_inverse_arm_bias_envelope ht hp0 hs0 hsle
    (outcomeMean_mem_unitInterval P a x) hb.1
  exact poisson_inverse_arm_mean_formula P x a hu ht

-- @node: poisson_inverse_arm_means_bias_aggregate
/-- Summing the exact arm means gives the paper's uniform inverse-count bias
bound before the overlap-dependent factor is absorbed into the final constant.  [the stated conditions](hyp:hP,hu,ht,heps) [the stated conclusion](goal). -/
lemma poisson_inverse_arm_means_bias_aggregate {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps) :
    let armMean : Fin d → Bool → Real := fun x a ↦
      let lambdaS : Bool → NNReal := fun b ↦
        Real.toNNReal (u * markedMass P x b)
      let lambdaK : Bool → NNReal := fun b ↦
        Real.toNNReal (t * armMass P x b)
      ((lambdaS a : Real) / u) *
        (∫ z : Nat × Nat,
          (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
            ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a))))
    |∑ x, (armMean x true - armMean x false) - ateFunctional P| ≤
      2 * min 1 (d / (eps * Real.exp 1 * t)) := by
  dsimp only
  let g : Fin d → Bool → Real := fun x a ↦
    ((Real.toNNReal (u * markedMass P x a) : NNReal) : Real) / u *
      (∫ z : Nat × Nat,
        (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
          ∂(poissonMeasure (Real.toNNReal (t * armMass P x a))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x (!a)))))
  have hg : ∀ x a,
      |g x a - cellMass P x * outcomeMean P a x| ≤
        cellMass P x * Real.exp (-eps * t * cellMass P x) := by
    intro x a
    exact poisson_inverse_arm_mean_envelope P hP x a hu ht heps
  simpa [g] using inverse_count_bias_aggregate P heps ht g hg

-- @node: poissonInverseArmMean
/-- The scalar arm contribution appearing in the exact expectation assembly.  [the stated conditions](hyp:P,u,t,x,a) [the stated conclusion](goal). -/
noncomputable def poissonInverseArmMean {d : Nat} (P : DiscreteLaw d)
    (u t : Real) (x : Fin d) (a : Bool) : Real :=
  let lambdaS : Bool → NNReal := fun b ↦
    Real.toNNReal (u * markedMass P x b)
  let lambdaK : Bool → NNReal := fun b ↦
    Real.toNNReal (t * armMass P x b)
  ((lambdaS a : Real) / u) *
    (∫ z : Nat × Nat,
      (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
        ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a))))

-- @node: nestedPaired_count_fst_le_total_annotation
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma nestedPaired_count_fst_le_total_annotation {d : Nat}
    (K : PoissonCounts d) (x : Fin d) (a : Bool) :
    (K x a).1 ≤ nestedPairedTotalCount K := by
  dsimp [nestedPairedTotalCount]
  calc
    (K x a).1 ≤ (K x a).1 + (K x a).2 := Nat.le_add_right _ _
    _ ≤ ∑ b, ((K x b).1 + (K x b).2) :=
      Finset.single_le_sum
        (f := fun b : Bool ↦ (K x b).1 + (K x b).2)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    _ ≤ ∑ i, ∑ b, ((K i b).1 + (K i b).2) :=
      Finset.single_le_sum
        (f := fun i : Fin d ↦ ∑ b, ((K i b).1 + (K i b).2))
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)

-- @node: nestedPaired_count_snd_le_total_annotation
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma nestedPaired_count_snd_le_total_annotation {d : Nat}
    (K : PoissonCounts d) (x : Fin d) (a : Bool) :
    (K x a).2 ≤ nestedPairedTotalCount K := by
  dsimp [nestedPairedTotalCount]
  calc
    (K x a).2 ≤ (K x a).1 + (K x a).2 := Nat.le_add_left _ _
    _ ≤ ∑ b, ((K x b).1 + (K x b).2) :=
      Finset.single_le_sum
        (f := fun b : Bool ↦ (K x b).1 + (K x b).2)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    _ ≤ ∑ i, ∑ b, ((K i b).1 + (K i b).2) :=
      Finset.single_le_sum
        (f := fun i : Fin d ↦ ∑ b, ((K i b).1 + (K i b).2))
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)

-- @node: poisson_inverse_weight_mean
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma poisson_inverse_weight_mean (lambda nu : NNReal) :
    (∫ z : Nat × Nat,
      (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹)
        ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
      1 + (nu : Real) *
        ∫ k : Nat, (((k + 1 : Nat) : Real))⁻¹ ∂poissonMeasure lambda := by
  let r : Nat → Real := fun k ↦ (((k + 1 : Nat) : Real))⁻¹
  have hr : Integrable r (poissonMeasure lambda) :=
    (Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two lambda).integrable (by norm_num)
  have hk : Integrable (fun k : Nat ↦ (k : Real)) (poissonMeasure nu) :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two nu).integrable (by norm_num)
  have hcross : Integrable (fun z : Nat × Nat ↦ (z.2 : Real) * r z.1)
      ((poissonMeasure lambda).prod (poissonMeasure nu)) := by
    apply (hr.mul_prod hk).congr
    filter_upwards with z
    simp [mul_comm]
  rw [integral_add (integrable_const 1) hcross]
  rw [show (∫ z : Nat × Nat, (z.2 : Real) * r z.1
      ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
      (∫ k, r k ∂poissonMeasure lambda) *
        ∫ k : Nat, (k : Real) ∂poissonMeasure nu by
        simpa [mul_comm] using integral_prod_mul r (fun k : Nat ↦ (k : Real))]
  rw [Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  simp
  simpa [r, Nat.cast_add, Nat.cast_one] using
    mul_comm (∫ k : Nat, (((k : Real) + 1))⁻¹ ∂poissonMeasure lambda) (nu : Real)

/-- Product-measure factorization identifies the expectation of the full
inverse-count statistic with the sum of its scalar arm means. [the stated conditions](hyp:hu) establishes [the stated conclusion](goal). -/
-- @node: poisson_inverse_count_expectation_eq_arm_means
lemma poisson_inverse_count_expectation_eq_arm_means {d : Nat}
    (P : DiscreteLaw d) {u t : Real} (hu : 0 < u) :
    expectationUnder (poissonCountLaw P u t) (inverseCountStatistic u) =
      ∑ x, (poissonInverseArmMean P u t x true -
        poissonInverseArmMean P u t x false) := by
  classical
  let lambdaS : Fin d → Bool → NNReal := fun x a ↦
    Real.toNNReal (u * markedMass P x a)
  let lambdaK : Fin d → Bool → NNReal := fun x a ↦
    Real.toNNReal (t * armMass P x a)
  have hbaseInt (x : Fin d) (a : Bool) :
      Integrable (fun K : PoissonCounts d ↦ ((K x a).1 : Real) / u)
        (poissonCountLaw P u t) := by
    rw [poissonCountLaw_eq_nestedPairedPoissonMeasure]
    letI : IsProbabilityMeasure (nestedPairedPoissonMeasure
        (fun x a ↦ Real.toNNReal (u * markedMass P x a))
        (fun x a ↦ Real.toNNReal (t * armMass P x a))) := by
      unfold nestedPairedPoissonMeasure
      infer_instance
    apply (memLp_nestedPairedPoisson_of_polynomial_bound
      (fun x a ↦ Real.toNNReal (u * markedMass P x a))
      (fun x a ↦ Real.toNNReal (t * armMass P x a))
      (fun K : PoissonCounts d ↦ ((K x a).1 : Real) / u)
      (measurable_of_countable _) |u⁻¹| 2 (abs_nonneg _) ?_).integrable (by norm_num)
    intro K
    have hcoord : ((K x a).1 : Real) ≤ nestedPairedTotalCount K := by
      exact_mod_cast nestedPaired_count_fst_le_total_annotation K x a
    have htotal : 0 ≤ (nestedPairedTotalCount K : Real) := by positivity
    rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((K x a).1 : Real))]
    have hpoly : (nestedPairedTotalCount K : Real) ≤
        (1 + (nestedPairedTotalCount K : Real)) ^ 2 := by
      nlinarith [sq_nonneg (nestedPairedTotalCount K : Real)]
    calc
      ((K x a).1 : Real) * |u⁻¹| ≤
          (nestedPairedTotalCount K : Real) * |u⁻¹| := by gcongr
      _ ≤ |u⁻¹| * (1 + (nestedPairedTotalCount K : Real)) ^ 2 := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hpoly (abs_nonneg _)
  have hcrossInt (x : Fin d) (a : Bool) :
      Integrable (fun K : PoissonCounts d ↦
        ((K x a).1 : Real) / u * ((K x (!a)).2 : Real) *
          (((K x a).2 + 1 : Nat) : Real)⁻¹) (poissonCountLaw P u t) := by
    rw [poissonCountLaw_eq_nestedPairedPoissonMeasure]
    letI : IsProbabilityMeasure (nestedPairedPoissonMeasure
        (fun x a ↦ Real.toNNReal (u * markedMass P x a))
        (fun x a ↦ Real.toNNReal (t * armMass P x a))) := by
      unfold nestedPairedPoissonMeasure
      infer_instance
    apply (memLp_nestedPairedPoisson_of_polynomial_bound
      (fun x a ↦ Real.toNNReal (u * markedMass P x a))
      (fun x a ↦ Real.toNNReal (t * armMass P x a))
      (fun K : PoissonCounts d ↦ ((K x a).1 : Real) / u *
        ((K x (!a)).2 : Real) * (((K x a).2 + 1 : Nat) : Real)⁻¹)
      (measurable_of_countable _) |u⁻¹| 2 (abs_nonneg _) ?_).integrable (by norm_num)
    intro K
    have hfst : ((K x a).1 : Real) ≤ nestedPairedTotalCount K := by
      exact_mod_cast nestedPaired_count_fst_le_total_annotation K x a
    have hsnd : ((K x (!a)).2 : Real) ≤ nestedPairedTotalCount K := by
      exact_mod_cast nestedPaired_count_snd_le_total_annotation K x (!a)
    have htotal : 0 ≤ (nestedPairedTotalCount K : Real) := by positivity
    have hinv : |((((K x a).2 + 1 : Nat) : Real))⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 (K x a).2)
    simp only [div_eq_mul_inv, abs_mul]
    rw [abs_of_nonneg (by positivity : 0 ≤ ((K x a).1 : Real)),
      abs_of_nonneg (by positivity : 0 ≤ ((K x (!a)).2 : Real))]
    calc
      ((K x a).1 : Real) * |u⁻¹| * ((K x (!a)).2 : Real) *
          |((((K x a).2 + 1 : Nat) : Real))⁻¹| ≤
          (nestedPairedTotalCount K : Real) * |u⁻¹| *
            (nestedPairedTotalCount K : Real) * 1 := by gcongr
      _ ≤ |u⁻¹| * (1 + (nestedPairedTotalCount K : Real)) ^ 2 := by
        have hsq : (nestedPairedTotalCount K : Real) ^ 2 ≤
            (1 + (nestedPairedTotalCount K : Real)) ^ 2 := by nlinarith
        rw [mul_one]
        calc
          (nestedPairedTotalCount K : Real) * |u⁻¹| *
              (nestedPairedTotalCount K : Real) =
              |u⁻¹| * (nestedPairedTotalCount K : Real) ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have harmInt (x : Fin d) (a : Bool) : Integrable (fun K : PoissonCounts d ↦
      ((K x a).1 : Real) / u *
        (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
          (((K x a).2 + 1 : Nat) : Real)) (poissonCountLaw P u t) := by
    refine ((hbaseInt x a).add (hcrossInt x a)).congr ?_
    filter_upwards with K
    cases a <;> simp only [Bool.not_false, Bool.not_true]
    all_goals
      change ((K x _).1 : Real) / u +
          ((K x _).1 : Real) / u * ((K x _).2 : Real) *
            (((K x _).2 + 1 : Nat) : Real)⁻¹ = _
      push_cast
      field_simp [hu.ne']
      ring
  have harm (x : Fin d) (a : Bool) :
      (∫ K, ((K x a).1 : Real) / u *
          (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
            (((K x a).2 + 1 : Nat) : Real)
          ∂poissonCountLaw P u t) = poissonInverseArmMean P u t x a := by
    have hout := poisson_inverse_outcome_mean (lambdaS x) (lambdaK x) u a
    have hcross := poisson_inverse_cross_moment (lambdaS x) (lambdaK x) u a
    simp only [lambdaS, lambdaK] at hout hcross
    rw [poissonInverseArmMean]
    calc
      (∫ K, ((K x a).1 : Real) / u *
          (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
            (((K x a).2 + 1 : Nat) : Real) ∂poissonCountLaw P u t) =
          (∫ K, ((K x a).1 : Real) / u ∂poissonCountLaw P u t) +
          ∫ K, ((K x a).1 : Real) / u * ((K x (!a)).2 : Real) *
              (((K x a).2 + 1 : Nat) : Real)⁻¹ ∂poissonCountLaw P u t := by
            rw [← integral_add (hbaseInt x a) (hcrossInt x a)]
            apply integral_congr_ae
            filter_upwards with K
            cases a <;> simp only [Bool.not_false, Bool.not_true]
            all_goals push_cast; field_simp <;> ring
      _ = _ := by
        have hb := poissonCountLaw_integral_cell P u t x
          (fun k : Bool → Nat × Nat ↦ ((k a).1 : Real) / u)
        have hc := poissonCountLaw_integral_cell P u t x
          (fun k : Bool → Nat × Nat ↦ ((k a).1 : Real) / u *
            ((k (!a)).2 : Real) * (((k a).2 + 1 : Nat) : Real)⁻¹)
        rw [hb, hc, hout, hcross, poisson_inverse_weight_mean]
        ring
  change (∫ K, ∑ x : Fin d,
    (((K x true).1 : Real) / u *
      (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
        (((K x true).2 + 1 : Nat) : Real) -
    ((K x false).1 : Real) / u *
      (((K x false).2 + (K x true).2 + 1 : Nat) : Real) /
        (((K x false).2 + 1 : Nat) : Real)) ∂poissonCountLaw P u t) = _
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun x _ ↦ by
      rw [integral_sub (harmInt x true) (harmInt x false), harm x true, harm x false]
  · intro x _
    exact (harmInt x true).sub (harmInt x false)

-- @node: poisson_inverse_count_bias_of_expectation_eq
/-- Once product-measure factorization identifies the statistic's expectation
with its scalar arm means, the already-proved cell envelopes give the complete
uniform bias bound.  [the stated conditions](hyp:hP,hu,ht,heps,hmean) [the stated conclusion](goal). -/
lemma poisson_inverse_count_bias_of_expectation_eq {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (hmean : expectationUnder (poissonCountLaw P u t) (inverseCountStatistic u) =
      ∑ x, (poissonInverseArmMean P u t x true -
        poissonInverseArmMean P u t x false)) :
    |expectationUnder (poissonCountLaw P u t) (inverseCountStatistic u) -
        ateFunctional P| ≤
      2 * min 1 (d / (eps * Real.exp 1 * t)) := by
  rw [hmean]
  simpa [poissonInverseArmMean] using
    poisson_inverse_arm_means_bias_aggregate P hP hu ht heps

-- @node: poisson_natCast_second_moment_le
/-- The scalar Poisson second moment bound used in the inverse-weight
calculation.  It follows directly from the add-one Poincare inequality.  [the stated conclusion](goal). -/
lemma poisson_natCast_second_moment_le (lambda : NNReal) :
    (∫ k : Nat, (k : Real) ^ 2 ∂poissonMeasure lambda) ≤
      (lambda : Real) + (lambda : Real) ^ 2 := by
  let f : Nat → Real := fun k ↦ (k : Real)
  have hf : MemLp f 2 (poissonMeasure lambda) :=
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two lambda
  have hdf : MemLp (addOne f) 2 (poissonMeasure lambda) := by
    apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards with k
    simp [addOne, f]
  have hp := poisson_addOne_poincare lambda f hf hdf
  have hvar : variance f (poissonMeasure lambda) ≤ (lambda : Real) := by
    simpa [addOne, f] using hp
  rw [variance_eq_sub hf,
    show (∫ k : Nat, f k ∂poissonMeasure lambda) = (lambda : Real) by
      simpa [f] using Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment lambda] at hvar
  simpa [f] using hvar

-- @node: poisson_inverse_weight_second_moment_bound
/-- Under the arm-overlap rate comparison, the inverse-count weight has a
uniform second moment.  [the stated conditions](hyp:heps,hoverlap) [the stated conclusion](goal). -/
lemma poisson_inverse_weight_second_moment_bound {eps : Real}
    (heps : 0 < eps) (lambda nu : NNReal)
    (hoverlap : eps * (nu : Real) ≤ (lambda : Real)) :
    (∫ z : Nat × Nat,
      (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹) ^ 2
        ∂(poissonMeasure lambda).prod (poissonMeasure nu)) ≤
      1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2 := by
  let r : Nat → Real := fun k ↦ (((k + 1 : Nat) : Real))⁻¹
  let r1 : Real := ∫ k, r k ∂poissonMeasure lambda
  let r2 : Real := ∫ k, (r k) ^ 2 ∂poissonMeasure lambda
  have hr : MemLp r 2 (poissonMeasure lambda) := by
    simpa [r] using Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two lambda
  have hv : MemLp (fun k : Nat ↦ (k : Real)) 2 (poissonMeasure nu) :=
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two nu
  have hcross : Integrable (fun z : Nat × Nat ↦
      2 * ((z.2 : Real) * r z.1))
      ((poissonMeasure lambda).prod (poissonMeasure nu)) := by
    exact ((hr.integrable (by norm_num)).mul_prod
      (hv.integrable (by norm_num))).const_mul 2 |>.congr (by
        filter_upwards with z
        ring)
  have hsq : Integrable (fun z : Nat × Nat ↦
      (z.2 : Real) ^ 2 * (r z.1) ^ 2)
      ((poissonMeasure lambda).prod (poissonMeasure nu)) := by
    exact (hr.integrable_sq.mul_prod hv.integrable_sq).congr (by
      filter_upwards with z
      ring)
  have hr1_nonneg : 0 ≤ r1 := by
    exact integral_nonneg fun k ↦ inv_nonneg.mpr (by positivity)
  have hr1rate : (lambda : Real) * r1 ≤ 1 := by
    have h := Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_first_moment lambda
    dsimp [r1, r] at *
    rw [h]
    linarith [Real.exp_pos (-(lambda : Real))]
  have hr2_nonneg : 0 ≤ r2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hr2rate : (1 + (lambda : Real)) ^ 2 * r2 ≤ 8 := by
    simpa [r2, r] using Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_sq_bound lambda
  have hscalar := Causalean.Mathlib.Probability.Poisson.poisson_inverse_weight_second_moment_scalar heps
    lambda.coe_nonneg nu.coe_nonneg hoverlap hr1_nonneg hr1rate
    hr2_nonneg hr2rate
  have hmeanNu : (∫ k : Nat, (k : Real) ∂poissonMeasure nu) = (nu : Real) :=
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment nu
  have hsecondNu : (∫ k : Nat, (k : Real) ^ 2 ∂poissonMeasure nu) ≤
      (nu : Real) + (nu : Real) ^ 2 := poisson_natCast_second_moment_le nu
  calc
    (∫ z : Nat × Nat,
        (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹) ^ 2
          ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
        1 + 2 * r1 * (nu : Real) + r2 *
          (∫ k : Nat, (k : Real) ^ 2 ∂poissonMeasure nu) := by
      rw [show (fun z : Nat × Nat ↦
          (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹) ^ 2) =
          fun z ↦ 1 + 2 * ((z.2 : Real) * r z.1) +
            (z.2 : Real) ^ 2 * (r z.1) ^ 2 by
          funext z
          simp only [r]
          ring]
      have hsplit :
          (∫ z : Nat × Nat, 1 + 2 * ((z.2 : Real) * r z.1) +
              (z.2 : Real) ^ 2 * (r z.1) ^ 2
              ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
            (∫ z : Nat × Nat, 1 + 2 * ((z.2 : Real) * r z.1)
              ∂(poissonMeasure lambda).prod (poissonMeasure nu)) +
            ∫ z : Nat × Nat, (z.2 : Real) ^ 2 * (r z.1) ^ 2
              ∂(poissonMeasure lambda).prod (poissonMeasure nu) :=
        integral_add ((integrable_const 1).add hcross) hsq
      have hsplit' :
          (∫ z : Nat × Nat, 1 + 2 * ((z.2 : Real) * r z.1)
              ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
            (∫ _z : Nat × Nat, (1 : Real)
              ∂(poissonMeasure lambda).prod (poissonMeasure nu)) +
            ∫ z : Nat × Nat, 2 * ((z.2 : Real) * r z.1)
              ∂(poissonMeasure lambda).prod (poissonMeasure nu) :=
        integral_add (integrable_const 1) hcross
      rw [hsplit, hsplit']
      rw [show (∫ z : Nat × Nat, 2 * ((z.2 : Real) * r z.1)
          ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
          2 * (r1 * (nu : Real)) by
            rw [integral_const_mul]
            rw [show (∫ z : Nat × Nat, (z.2 : Real) * r z.1
                ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
                r1 * ∫ k : Nat, (k : Real) ∂poissonMeasure nu by
                  simpa [mul_comm] using integral_prod_mul
                    (μ := poissonMeasure lambda) (ν := poissonMeasure nu) r
                    (fun k : Nat ↦ (k : Real))]
            rw [hmeanNu],
        show (∫ z : Nat × Nat, (z.2 : Real) ^ 2 * (r z.1) ^ 2
            ∂(poissonMeasure lambda).prod (poissonMeasure nu)) =
            r2 * ∫ k : Nat, (k : Real) ^ 2 ∂poissonMeasure nu by
              calc
                _ = ∫ z : Nat × Nat, (r z.1) ^ 2 * (z.2 : Real) ^ 2
                    ∂(poissonMeasure lambda).prod (poissonMeasure nu) := by
                      apply integral_congr_ae
                      filter_upwards with z
                      ring
                _ = (∫ k : Nat, (r k) ^ 2 ∂poissonMeasure lambda) *
                    ∫ k : Nat, (k : Real) ^ 2 ∂poissonMeasure nu :=
                      integral_prod_mul
                        (μ := poissonMeasure lambda) (ν := poissonMeasure nu)
                        (fun k : Nat ↦ (r k) ^ 2) (fun k : Nat ↦ (k : Real) ^ 2)
                _ = _ := by rfl]
      simp [r1]
      ring
    _ ≤ 1 + 2 * (nu : Real) * r1 +
        ((nu : Real) + (nu : Real) ^ 2) * r2 := by
      have hr20 : 0 ≤ r2 := hr2_nonneg
      nlinarith [mul_le_mul_of_nonneg_left hsecondNu hr20]
    _ ≤ 1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2 := by
      simpa [mul_comm] using hscalar

-- @node: poisson_inverse_weight_second_moment_cell
/-- Integrating out the outcome-count coordinates leaves exactly the two marginal
Poisson counts in the inverse weight.  [the stated conclusion](goal). -/
lemma poisson_inverse_weight_second_moment_cell
    (lambdaS lambdaK : Bool → NNReal) (a : Bool) :
    (∫ k : Bool → Nat × Nat,
      (1 + ((k (!a)).2 : Real) * ((((k a).2 + 1 : Nat) : Real))⁻¹) ^ 2
        ∂Measure.pi (fun b : Bool ↦
          (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b)))) =
      ∫ z : Nat × Nat,
        (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹) ^ 2
          ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a))) := by
  let mu : Bool → Measure (Nat × Nat) := fun b ↦
    (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b))
  let e := MeasurableEquiv.piCongrLeft (fun _ : Bool ↦ Nat × Nat) finTwoEquiv
  have hmp₁ : MeasurePreserving e
      (Measure.pi fun i : Fin 2 ↦ mu (finTwoEquiv i)) (Measure.pi mu) :=
    measurePreserving_piCongrLeft mu finTwoEquiv
  have hmp₂ := measurePreserving_piFinTwo
    (fun i : Fin 2 ↦ mu (finTwoEquiv i))
  let eTotal := e.symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ Nat × Nat))
  have hmp : MeasurePreserving eTotal
      (Measure.pi mu) ((mu false).prod (mu true)) := hmp₂.comp hmp₁.symm
  have hmpK : MeasurePreserving (fun z : (Nat × Nat) × (Nat × Nat) ↦
      (z.1.2, z.2.2)) ((mu false).prod (mu true))
      ((poissonMeasure (lambdaK false)).prod (poissonMeasure (lambdaK true))) :=
    (measurePreserving_snd (μ := poissonMeasure (lambdaS false))
      (ν := poissonMeasure (lambdaK false))).prod
      (measurePreserving_snd (μ := poissonMeasure (lambdaS true))
        (ν := poissonMeasure (lambdaK true)))
  have hmpKswap : MeasurePreserving (fun z : (Nat × Nat) × (Nat × Nat) ↦
      (z.2.2, z.1.2)) ((mu false).prod (mu true))
      ((poissonMeasure (lambdaK true)).prod (poissonMeasure (lambdaK false))) :=
    (Measure.measurePreserving_swap (μ := poissonMeasure (lambdaK false))
      (ν := poissonMeasure (lambdaK true))).comp hmpK
  cases a
  · calc
      _ = ∫ y : (Nat × Nat) × (Nat × Nat),
          (1 + (y.2.2 : Real) * (((y.1.2 + 1 : Nat) : Real))⁻¹) ^ 2
            ∂((mu false).prod (mu true)) := by
              rw [← hmp.integral_comp']
              apply integral_congr_ae
              filter_upwards with k
              change _ = (1 + ((e.symm k 1).2 : Real) *
                ((((e.symm k 0).2 + 1 : Nat) : Real))⁻¹) ^ 2
              congr 3 <;> rfl
      _ = _ := by
        simp only [Bool.not_false]
        dsimp [mu] at hmpK ⊢
        rw [← hmpK.map_eq, integral_map hmpK.measurable.aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]
  · calc
      _ = ∫ y : (Nat × Nat) × (Nat × Nat),
          (1 + (y.1.2 : Real) * (((y.2.2 + 1 : Nat) : Real))⁻¹) ^ 2
            ∂((mu false).prod (mu true)) := by
              rw [← hmp.integral_comp']
              apply integral_congr_ae
              filter_upwards with k
              change _ = (1 + ((e.symm k 0).2 : Real) *
                ((((e.symm k 1).2 + 1 : Nat) : Real))⁻¹) ^ 2
              congr 3 <;> rfl
      _ = _ := by
        simp only [Bool.not_true]
        dsimp [mu] at hmpKswap ⊢
        rw [← hmpKswap.map_eq, integral_map hmpKswap.measurable.aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]

-- @node: poisson_inverse_outcome_coordinate_energy_bound
/-- Each outcome-count add-one energy is controlled by its marked mass and the
outcome-information scale.  [the stated conditions](hyp:hP,hu,ht,heps) [the stated conclusion](goal). -/
lemma poisson_inverse_outcome_coordinate_energy_bound {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (x : Fin d) (a : Bool) :
    ((Real.toNNReal (u * markedMass P x a) : NNReal) : Real) *
        (∫ K, (nestedPairAddOneFst x a (inverseCountStatistic u) K) ^ 2
          ∂poissonCountLaw P u t) ≤
      (1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2) * markedMass P x a * u⁻¹ := by
  let lambdaS : Bool → NNReal := fun b ↦ Real.toNNReal (u * markedMass P x b)
  let lambdaK : Bool → NNReal := fun b ↦ Real.toNNReal (t * armMass P x b)
  have hrateS : ((lambdaS a : NNReal) : Real) = u * markedMass P x a := by
    rw [Real.coe_toNNReal]
    exact mul_nonneg hu.le (jointMass_mem_unitInterval P x a true).1
  have hrateKa : ((lambdaK a : NNReal) : Real) = t * armMass P x a := by
    rw [Real.coe_toNNReal]
    exact mul_nonneg ht.le
      (Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1)
  have hrateKo : ((lambdaK (!a) : NNReal) : Real) = t * armMass P x (!a) := by
    rw [Real.coe_toNNReal]
    exact mul_nonneg ht.le
      (Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x (!a) y).1)
  have hoverlap : eps * ((lambdaK (!a) : NNReal) : Real) ≤
      ((lambdaK a : NNReal) : Real) := by
    rw [hrateKa, hrateKo]
    have ha := (overlap_armMass_bounds P hP.overlap x a).1
    have ho0 : 0 ≤ armMass P x a :=
      Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1
    have hsplit : armMass P x a + armMass P x (!a) = cellMass P x := by
      cases a <;> simp [armMass, cellMass] <;> ring
    have ho : armMass P x (!a) ≤ cellMass P x := by linarith
    calc
      eps * (t * armMass P x (!a)) = t * (eps * armMass P x (!a)) := by ring
      _ ≤ t * (eps * cellMass P x) := by gcongr
      _ ≤ t * armMass P x a := by gcongr
  have hw := poisson_inverse_weight_second_moment_bound heps
    (lambdaK a) (lambdaK (!a)) hoverlap
  have hcell :
      (∫ K, (nestedPairAddOneFst x a (inverseCountStatistic u) K) ^ 2
          ∂poissonCountLaw P u t) =
        u⁻¹ ^ 2 *
          (∫ z : Nat × Nat,
            (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹) ^ 2
              ∂(poissonMeasure (lambdaK a)).prod
                (poissonMeasure (lambdaK (!a)))) := by
    rw [show (fun K : PoissonCounts d ↦
        (nestedPairAddOneFst x a (inverseCountStatistic u) K) ^ 2) =
        fun K ↦ u⁻¹ ^ 2 *
          (1 + ((K x (!a)).2 : Real) * ((((K x a).2 + 1 : Nat) : Real))⁻¹) ^ 2 by
      funext K
      rw [inverse_count_outcome_addOne u hu.ne' x a K]
      cases a <;> simp <;> field_simp <;> ring]
    rw [integral_const_mul]
    congr 1
    calc
      _ = ∫ k, (1 + ((k (!a)).2 : Real) *
          ((((k a).2 + 1 : Nat) : Real))⁻¹) ^ 2
          ∂Measure.pi (fun b : Bool ↦
            (poissonMeasure (Real.toNNReal (u * markedMass P x b))).prod
              (poissonMeasure (Real.toNNReal (t * armMass P x b)))) :=
        poissonCountLaw_integral_cell P u t x _
      _ = _ := poisson_inverse_weight_second_moment_cell lambdaS lambdaK a
  rw [hcell, hrateS]
  have hmark : 0 ≤ markedMass P x a :=
    (jointMass_mem_unitInterval P x a true).1
  have huinv : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.le
  let W2 : Real := ∫ z : Nat × Nat,
    (1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹) ^ 2
      ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a)))
  change (u * markedMass P x a) * (u⁻¹ ^ 2 * W2) ≤ _
  have hw' : W2 ≤ 1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2 := hw
  calc
    (u * markedMass P x a) * (u⁻¹ ^ 2 * W2) =
        markedMass P x a * u⁻¹ * W2 := by
          rw [inv_pow]
          field_simp
    _ ≤ markedMass P x a * u⁻¹ *
        (1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2) := by gcongr
    _ = _ := by ring


end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
