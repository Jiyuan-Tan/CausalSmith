module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ChebyshevCalibration
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonFallingFactorial

/-! Exact one-cell identities for the light factorial branch. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Polynomial ProbabilityTheory MeasureTheory

private lemma memLp_mul_prod_nat {mu0 mu1 : Measure Nat}
    {f g : Nat → Real} (hf : MemLp f 2 mu0) (hg : MemLp g 2 mu1) :
    MemLp (fun K : Nat × Nat ↦ f K.1 * g K.2) 2 (mu0.prod mu1) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_of_countable _).aestronglyMeasurable).2
  apply (hf.integrable_sq.mul_prod hg.integrable_sq).congr
  filter_upwards [] with K
  ring

/-- The finite factorial polynomial has a finite second moment under two
independent Poisson counts.  [the stated conclusion](goal). -/
lemma factorialLift_memLp (a : Bool) (L : Nat) (B t s0 s1 : Real) :
    MemLp (fun K : Nat × Nat ↦ factorialLift a L B t K.1 K.2) 2
      ((poissonMeasure (Real.toNNReal (t * s0))).prod
        (poissonMeasure (Real.toNNReal (t * s1)))) := by
  unfold factorialLift
  apply memLp_finsetSum
  intro j hj
  let mu0 := poissonMeasure (Real.toNNReal (t * s0))
  let mu1 := poissonMeasure (Real.toNNReal (t * s1))
  cases a
  · have hmain := memLp_mul_prod_nat
      (memLp_descFactorial_poisson (Real.toNNReal (t * s0)) (j + 1))
      (memLp_const (1 : Real) : MemLp (fun _ : Nat ↦ (1 : Real)) 2 mu1)
    have hcross := memLp_mul_prod_nat
      (memLp_descFactorial_poisson (Real.toNNReal (t * s0)) j)
      (memLp_descFactorial_poisson (Real.toNNReal (t * s1)) 1)
    convert (hmain.add hcross).const_mul
      ((chebG L).coeff j / (t * B) ^ (j + 1)) using 1
    funext K
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.descFactorial_one,
      Pi.add_apply, Nat.add_comm]
    ring
  · have hmain := memLp_mul_prod_nat
      (memLp_const (1 : Real) : MemLp (fun _ : Nat ↦ (1 : Real)) 2 mu0)
      (memLp_descFactorial_poisson (Real.toNNReal (t * s1)) (j + 1))
    have hcross := memLp_mul_prod_nat
      (memLp_descFactorial_poisson (Real.toNNReal (t * s0)) 1)
      (memLp_descFactorial_poisson (Real.toNNReal (t * s1)) j)
    convert (hmain.add hcross).const_mul
      ((chebG L).coeff j / (t * B) ^ (j + 1)) using 1
    funext K
    simp only [↓reduceIte, Nat.descFactorial_one, Pi.add_apply, Nat.add_comm]
    ring

private lemma factorialLift_term_integrable (a : Bool) (j : Nat)
    {L : Nat} {B t s0 s1 : Real} (ht : 0 < t) (hB : 0 < B) :
    Integrable (fun K : Nat × Nat ↦
      (chebG L).coeff j *
        ((((if a then K.2 else K.1).descFactorial (j + 1) : Nat) : Real) +
          (if a then (K.1 : Real) else (K.2 : Real)) *
            (((if a then K.2 else K.1).descFactorial j : Nat) : Real)) /
          (t * B) ^ (j + 1))
      ((poissonMeasure (Real.toNNReal (t * s0))).prod
        (poissonMeasure (Real.toNNReal (t * s1)))) := by
  have htB : t * B ≠ 0 := ne_of_gt (mul_pos ht hB)
  cases a
  · have hs := (integrable_descFactorial_poisson
        (Real.toNNReal (t * s0)) (j + 1)).mul_prod
        (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real))
          (poissonMeasure (Real.toNNReal (t * s1))))
    have hc := (integrable_descFactorial_poisson
        (Real.toNNReal (t * s0)) j).mul_prod
      (integrable_descFactorial_poisson (Real.toNNReal (t * s1)) 1)
    apply ((hs.add hc).const_mul ((chebG L).coeff j / (t * B) ^ (j + 1))).congr
    filter_upwards with K
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.descFactorial_one, Pi.add_apply]
    field_simp
  · have hs :=
      (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real))
        (poissonMeasure (Real.toNNReal (t * s0)))).mul_prod
        (integrable_descFactorial_poisson (Real.toNNReal (t * s1)) (j + 1))
    have hc := (integrable_descFactorial_poisson
        (Real.toNNReal (t * s0)) 1).mul_prod
      (integrable_descFactorial_poisson (Real.toNNReal (t * s1)) j)
    apply ((hs.add hc).const_mul ((chebG L).coeff j / (t * B) ^ (j + 1))).congr
    filter_upwards with K
    simp only [↓reduceIte, Nat.descFactorial_one, Pi.add_apply]
    field_simp

private lemma integral_factorialLift_term (a : Bool) (j : Nat)
    {B t s0 s1 : Real} (ht : 0 < t) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) :
    (∫ K : Nat × Nat,
      ((((if a then K.2 else K.1).descFactorial (j + 1) : Nat) : Real) +
        (if a then (K.1 : Real) else (K.2 : Real)) *
          (((if a then K.2 else K.1).descFactorial j : Nat) : Real)) /
        (t * B) ^ (j + 1) ∂
      (poissonMeasure (Real.toNNReal (t * s0))).prod
        (poissonMeasure (Real.toNNReal (t * s1)))) =
      (((t * (if a then s1 else s0)) ^ (j + 1) +
        (t * (if a then s0 else s1)) *
          (t * (if a then s1 else s0)) ^ j) / (t * B) ^ (j + 1)) := by
  rw [integral_div, integral_add]
  · cases a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show (∫ K : Nat × Nat, (K.1.descFactorial (j + 1) : Real) ∂
          (poissonMeasure (Real.toNNReal (t * s0))).prod
            (poissonMeasure (Real.toNNReal (t * s1)))) =
          ∫ n : Nat, (n.descFactorial (j + 1) : Real) ∂
            poissonMeasure (Real.toNNReal (t * s0)) by
        simpa using integral_prod_mul
          (μ := poissonMeasure (Real.toNNReal (t * s0)))
          (ν := poissonMeasure (Real.toNNReal (t * s1)))
          (fun n : Nat ↦ (n.descFactorial (j + 1) : Real))
          (fun _ : Nat ↦ (1 : Real))]
      rw [show (∫ K : Nat × Nat, (K.2 : Real) * K.1.descFactorial j ∂
          (poissonMeasure (Real.toNNReal (t * s0))).prod
            (poissonMeasure (Real.toNNReal (t * s1)))) =
          (∫ n : Nat, (n.descFactorial j : Real) ∂
            poissonMeasure (Real.toNNReal (t * s0))) *
          ∫ n : Nat, (n.descFactorial 1 : Real) ∂
            poissonMeasure (Real.toNNReal (t * s1)) by
        simpa [mul_comm] using integral_prod_mul
          (μ := poissonMeasure (Real.toNNReal (t * s0)))
          (ν := poissonMeasure (Real.toNNReal (t * s1)))
          (fun n : Nat ↦ (n.descFactorial j : Real))
          (fun n : Nat ↦ (n.descFactorial 1 : Real))]
      rw [integral_descFactorial_poisson, integral_descFactorial_poisson,
        integral_descFactorial_poisson]
      simp [Real.coe_toNNReal, mul_nonneg ht.le hs0, mul_nonneg ht.le hs1]
      ring
    · simp only [↓reduceIte]
      rw [show (∫ K : Nat × Nat, (K.2.descFactorial (j + 1) : Real) ∂
          (poissonMeasure (Real.toNNReal (t * s0))).prod
            (poissonMeasure (Real.toNNReal (t * s1)))) =
          ∫ n : Nat, (n.descFactorial (j + 1) : Real) ∂
            poissonMeasure (Real.toNNReal (t * s1)) by
        simpa using integral_prod_mul
          (μ := poissonMeasure (Real.toNNReal (t * s0)))
          (ν := poissonMeasure (Real.toNNReal (t * s1)))
          (fun _ : Nat ↦ (1 : Real))
          (fun n : Nat ↦ (n.descFactorial (j + 1) : Real))]
      rw [show (∫ K : Nat × Nat, (K.1 : Real) * K.2.descFactorial j ∂
          (poissonMeasure (Real.toNNReal (t * s0))).prod
            (poissonMeasure (Real.toNNReal (t * s1)))) =
          (∫ n : Nat, (n.descFactorial 1 : Real) ∂
            poissonMeasure (Real.toNNReal (t * s0))) *
          ∫ n : Nat, (n.descFactorial j : Real) ∂
            poissonMeasure (Real.toNNReal (t * s1)) by
        simpa using integral_prod_mul
          (μ := poissonMeasure (Real.toNNReal (t * s0)))
          (ν := poissonMeasure (Real.toNNReal (t * s1)))
          (fun n : Nat ↦ (n.descFactorial 1 : Real))
          (fun n : Nat ↦ (n.descFactorial j : Real))]
      rw [integral_descFactorial_poisson, integral_descFactorial_poisson,
        integral_descFactorial_poisson]
      simp [Real.coe_toNNReal, mul_nonneg ht.le hs0, mul_nonneg ht.le hs1]
  · cases a
    · simpa using (integrable_descFactorial_poisson
        (Real.toNNReal (t * s0)) (j + 1)).mul_prod
          (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real))
            (poissonMeasure (Real.toNNReal (t * s1))))
    · simpa using
        (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real))
          (poissonMeasure (Real.toNNReal (t * s0)))).mul_prod
          (integrable_descFactorial_poisson (Real.toNNReal (t * s1)) (j + 1))
  · cases a
    · exact ((integrable_descFactorial_poisson
        (Real.toNNReal (t * s0)) j).mul_prod
          (integrable_descFactorial_poisson (Real.toNNReal (t * s1)) 1)).congr
            (Filter.Eventually.of_forall fun K ↦ by simp [mul_comm])
    · simpa using (integrable_descFactorial_poisson
        (Real.toNNReal (t * s0)) 1).mul_prod
          (integrable_descFactorial_poisson (Real.toNNReal (t * s1)) j)

/-- The factorial lift is unbiased for the polynomial light-cell continuation.  [the stated conditions](hyp:ht,hB,hs0,hs1) [the stated conclusion](goal). -/
lemma integral_factorialLift (a : Bool) (L : Nat) {B t s0 s1 : Real}
    (ht : 0 < t) (hB : 0 < B) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) :
    (∫ K : Nat × Nat, factorialLift a L B t K.1 K.2 ∂
      (poissonMeasure (Real.toNNReal (t * s0))).prod
        (poissonMeasure (Real.toNNReal (t * s1)))) =
      (s0 + s1) / B * (chebG L).eval ((if a then s1 else s0) / B) := by
  unfold factorialLift
  rw [integral_finset_sum]
  · rw [eval_eq_sum]
    simp only [Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul]
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hterm := integral_factorialLift_term (B := B) false j ht hs0 hs1
      simp only [Bool.false_eq_true, ↓reduceIte] at hterm
      rw [hterm]
      simp only [div_pow]
      rw [pow_succ]
      field_simp [ne_of_gt ht, ne_of_gt hB]
      ring
    · simp only [↓reduceIte]
      have hterm := integral_factorialLift_term (B := B) true j ht hs0 hs1
      simp only [↓reduceIte] at hterm
      rw [hterm]
      simp only [div_pow]
      rw [pow_succ]
      field_simp [ne_of_gt ht, ne_of_gt hB]
      ring
  · intro j hj
    cases a
    · apply (factorialLift_term_integrable (L := L) (s0 := s0) (s1 := s1)
          false j ht hB).congr
      filter_upwards with K
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · apply (factorialLift_term_integrable (L := L) (s0 := s0) (s1 := s1)
          true j ht hB).congr
      filter_upwards with K
      simp only [↓reduceIte]
      ring

/-- One arm's light contribution, separating its marked count from the two
factorial arm counts.  [the stated conditions](hyp:a,L,B,u,t,Z) [the stated conclusion](goal). -/
noncomputable def lightArmCell (a : Bool) (L : Nat) (B u t : Real)
    (Z : Nat × (Nat × Nat)) : Real :=
  (Z.1 : Real) / u * factorialLift a L B t Z.2.1 Z.2.2

/-- Exact mean of one light arm contribution.  [the stated conditions](hyp:hu,ht,hB,hmarked,hs0,hs1) [the stated conclusion](goal). -/
lemma integral_lightArmCell (a : Bool) (L : Nat) {B u t marked s0 s1 : Real}
    (hu : 0 < u) (ht : 0 < t) (hB : 0 < B)
    (hmarked : 0 ≤ marked) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) :
    (∫ Z : Nat × (Nat × Nat), lightArmCell a L B u t Z ∂
      (poissonMeasure (Real.toNNReal (u * marked))).prod
        ((poissonMeasure (Real.toNNReal (t * s0))).prod
          (poissonMeasure (Real.toNNReal (t * s1))))) =
      marked * ((s0 + s1) / B) *
        (chebG L).eval ((if a then s1 else s0) / B) := by
  rw [show (∫ Z : Nat × (Nat × Nat), lightArmCell a L B u t Z ∂
      (poissonMeasure (Real.toNNReal (u * marked))).prod
        ((poissonMeasure (Real.toNNReal (t * s0))).prod
          (poissonMeasure (Real.toNNReal (t * s1))))) =
      (∫ S : Nat, (S : Real) / u ∂poissonMeasure (Real.toNNReal (u * marked))) *
        ∫ K : Nat × Nat, factorialLift a L B t K.1 K.2 ∂
          (poissonMeasure (Real.toNNReal (t * s0))).prod
            (poissonMeasure (Real.toNNReal (t * s1))) by
    exact integral_prod_mul (fun S : Nat ↦ (S : Real) / u)
      (fun K : Nat × Nat ↦ factorialLift a L B t K.1 K.2)]
  rw [integral_div]
  have hfirst : (∫ S : Nat, (S : Real) ∂poissonMeasure
      (Real.toNNReal (u * marked))) = (Real.toNNReal (u * marked) : Real) := by
    simpa using integral_descFactorial_poisson (Real.toNNReal (u * marked)) 1
  rw [hfirst, integral_factorialLift a L ht hB hs0 hs1]
  rw [Real.coe_toNNReal _ (mul_nonneg hu.le hmarked)]
  field_simp

/-- Exact second-moment factorization for one light arm contribution.  [the stated conditions](hyp:hu,hmarked) [the stated conclusion](goal). -/
lemma integral_lightArmCell_sq (a : Bool) (L : Nat) {B u t marked s0 s1 : Real}
    (hu : 0 < u) (hmarked : 0 ≤ marked) :
    (∫ Z : Nat × (Nat × Nat), lightArmCell a L B u t Z ^ 2 ∂
      (poissonMeasure (Real.toNNReal (u * marked))).prod
        ((poissonMeasure (Real.toNNReal (t * s0))).prod
          (poissonMeasure (Real.toNNReal (t * s1))))) =
      (marked / u + marked ^ 2) * factorialLiftSecondMoment a L B t s0 s1 := by
  rw [show (∫ Z : Nat × (Nat × Nat), lightArmCell a L B u t Z ^ 2 ∂
      (poissonMeasure (Real.toNNReal (u * marked))).prod
        ((poissonMeasure (Real.toNNReal (t * s0))).prod
          (poissonMeasure (Real.toNNReal (t * s1))))) =
      (∫ S : Nat, ((S : Real) / u) ^ 2 ∂
        poissonMeasure (Real.toNNReal (u * marked))) *
      ∫ K : Nat × Nat, factorialLift a L B t K.1 K.2 ^ 2 ∂
        (poissonMeasure (Real.toNNReal (t * s0))).prod
          (poissonMeasure (Real.toNNReal (t * s1))) by
    simpa [lightArmCell, mul_pow] using integral_prod_mul
      (fun S : Nat ↦ ((S : Real) / u) ^ 2)
      (fun K : Nat × Nat ↦ factorialLift a L B t K.1 K.2 ^ 2)]
  rw [show (∫ S : Nat, ((S : Real) / u) ^ 2 ∂
      poissonMeasure (Real.toNNReal (u * marked))) =
      ∫ S : Nat, (S : Real) ^ 2 / u ^ 2 ∂
        poissonMeasure (Real.toNNReal (u * marked)) by
    congr 1
    funext S
    ring]
  rw [integral_div, integral_natCast_sq_poisson]
  unfold factorialLiftSecondMoment
  rw [Real.coe_toNNReal _ (mul_nonneg hu.le hmarked)]
  field_simp

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
