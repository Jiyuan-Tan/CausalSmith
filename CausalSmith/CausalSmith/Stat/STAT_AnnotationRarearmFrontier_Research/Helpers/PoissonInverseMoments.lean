module
public import Causalean.Mathlib.Probability.Poisson.InverseMoments
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Causalean.Mathlib.Probability.Poisson.Poincare.Scalar

/-!
First moment, squared moment, and variance of a shifted reciprocal Poisson count.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


-- @node: lem:poisson-inverse-moments
/--
[The shifted reciprocal Poisson count has its exact first moment and the displayed universal
squared-moment and variance bounds](goal).
-/
lemma poisson_inverse_moments (lam : NNReal) :
    let g : Nat → Real := fun k => ((k : Real) + 1)⁻¹
    (∫ k, g k ∂poissonMeasure lam) =
      (if (lam : Real) = 0 then 1 else (1 - Real.exp (-(lam : Real))) / (lam : Real)) ∧
    (∫ k, g k ^ 2 ∂poissonMeasure lam) ≤ 2 ^ 16 / (1 + (lam : Real)) ^ 2 ∧
    ProbabilityTheory.variance g (poissonMeasure lam) ≤ 2 ^ 16 * (lam : Real) / (1 + (lam :
      Real)) ^ 4 :=
  by
    dsimp only
    let g : Nat → Real := fun k => ((k : Real) + 1)⁻¹
    let r : Nat → Real := fun k =>
      ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
    have hg : MemLp g 2 (poissonMeasure lam) := by
      simpa only [g, Nat.cast_add, Nat.cast_one] using
        Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two lam
    have hr := Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_pair_memLp_two lam
    have hdiff : Causalean.Mathlib.Probability.PoissonAddOnePoincare.addOne g =
        fun k => -r k := by
      funext k
      dsimp [Causalean.Mathlib.Probability.PoissonAddOnePoincare.addOne, g, r]
      push_cast
      field_simp
      ring
    have hd : MemLp
        (Causalean.Mathlib.Probability.PoissonAddOnePoincare.addOne g) 2
        (poissonMeasure lam) := by
      rw [hdiff]
      exact hr.neg
    have hvar := Causalean.Mathlib.Probability.PoissonAddOnePoincare.poisson_addOne_poincare
      lam g hg hd
    rw [hdiff] at hvar
    simp only [neg_sq] at hvar
    have hsecond := Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_sq_bound lam
    have hfourth := Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_pair_sq_bound lam
    simp only [Nat.cast_add, Nat.cast_one] at hsecond
    have hden : 0 < 1 + (lam : Real) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · by_cases hz : (lam : Real) = 0
      · have hl : lam = 0 := NNReal.coe_eq_zero.mp hz
        subst lam
        rw [integral_poissonMeasure]
        simp only [NNReal.coe_zero, neg_zero, Real.exp_zero, one_mul, smul_eq_mul]
        rw [tsum_eq_single 0]
        · norm_num
        · intro k hk
          simp [zero_pow hk]
      · rw [if_neg hz]
        apply (eq_div_iff hz).2
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
          Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_first_moment lam
    · apply (le_div_iff₀ (pow_pos hden 2)).2
      nlinarith [hsecond]
    · apply (le_div_iff₀ (pow_pos hden 4)).2
      have hscaled := mul_le_mul_of_nonneg_right hvar (le_of_lt (pow_pos hden 4))
      have hmoment := mul_le_mul_of_nonneg_left hfourth lam.coe_nonneg
      change variance g (poissonMeasure lam) * (1 + (lam : Real)) ^ 4 ≤ _
      dsimp only [r] at hscaled
      nlinarith [hscaled, hmoment, lam.coe_nonneg]

end CausalSmith.Stat.AnnotationRarearmFrontier
