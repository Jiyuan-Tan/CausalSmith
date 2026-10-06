module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ChebyshevAlgebra
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FactorialCertificate
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.Calibration
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PoissonInverseMoments

/-!
Canonical Poisson branch statistics and their exact polynomial and inverse-count means.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Canonical independent outcome-success, own-arm, and opposite-arm counts](goal).
-/
noncomputable def cellPoissonLaw (u t q s v : Real) : Measure (Nat × Nat × Nat) :=
  (poissonMeasure (Real.toNNReal (u * q))).prod
    ((poissonMeasure (Real.toNNReal (t * s))).prod (poissonMeasure (Real.toNNReal (t * v))))
/--
[For the polynomial degree](hyp:L), [the scale bound](hyp:B), [the marked-count intensity](hyp:u), [the arm-count intensity](hyp:t), and [a triple of observed counts](hyp:z),
[the polynomial cell branch](goal) is the factorial-polynomial estimator used for the light-cell branch.
-/
noncomputable def polynomialCellBranch (L : Nat) (B u t : Real) (z : Nat × Nat × Nat) : Real :=
  (z.1 : Real) / u * (1 + (z.2.2 : Real) / (t * B) *
    ∑ h ∈ Finset.range (L - 1), (chebG L).coeff h * (z.2.1.descFactorial h : Real) / (t * B) ^ h)
/--
[For the marked-count intensity](hyp:u) and [a triple of observed counts](hyp:z),
[the inverse-count cell branch](goal) is the reciprocal-count estimator used for the heavy-cell branch.
-/
noncomputable def inverseCellBranch (u : Real) (z : Nat × Nat × Nat) : Real :=
  (z.1 : Real) / u * (1 + (z.2.2 : Real) / ((z.2.1 : Real) + 1))
/-- [Under the stated inputs and conditions](hyp:p,J,hJ,hD,hz,D,z), A finite factorial lift has the same mean as its ordinary polynomial.  This gives [the stated result](goal).-/
-- @node: poisson_factorial_polynomial_mean
lemma poisson_factorial_polynomial_mean (p : Polynomial Real) (J : Nat)
    (hJ : p.natDegree < J) (D z : Real) (hD : 0 < D) (hz : 0 ≤ z) :
    (∫ K : Nat, (∑ h ∈ Finset.range J,
      p.coeff h * (K.descFactorial h : Real) / D ^ h)
      ∂poissonMeasure (Real.toNNReal (D * z))) = p.eval z := by
  rw [integral_finsetSum]
  · rw [p.eval_eq_sum_range' hJ z]
    apply Finset.sum_congr rfl
    intro h _
    rw [integral_div, integral_const_mul,
      Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment]
    simp only [Real.coe_toNNReal _ (mul_nonneg hD.le hz), mul_pow]
    field_simp
  · intro h _
    exact ((Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      _ h).const_mul _).div_const _

/-- [Under the stated inputs and conditions](hyp:hu,hq,hv,ht,F,hF,u,t,q,s,v), Independent Poisson counts factor the outcome and opposite-arm multiplier means.  This gives [the stated result](goal).-/
-- @node: poisson_cell_multiplier_mean
lemma poisson_cell_multiplier_mean (u t q s v : Real) (hu : 0 < u)
    (hq : 0 ≤ q) (hv : 0 ≤ v) (ht : 0 < t) (F : Nat → Real)
    (hF : Integrable F (poissonMeasure (Real.toNNReal (t * s)))) :
    (∫ z : Nat × Nat × Nat, (z.1 : Real) / u *
      (1 + (z.2.2 : Real) * F z.2.1) ∂cellPoissonLaw u t q s v) =
      q * (1 + t * v * ∫ K, F K ∂poissonMeasure (Real.toNNReal (t * s))) := by
  have hW := (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
    (Real.toNNReal (t * v))).integrable (by norm_num)
  have hm (r : Real) (hr : 0 ≤ r) :
      (∫ K : Nat, (K : Real) ∂poissonMeasure (Real.toNNReal r)) = r := by
    have hh := Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment
      (Real.toNNReal r) 1
    simpa [Real.coe_toNNReal _ hr] using hh
  have hprod := hF.mul_prod hW
  simp only [cellPoissonLaw]
  rw [integral_prod_mul (fun Z : Nat => (Z : Real) / u)
    (fun z : Nat × Nat => 1 + (z.2 : Real) * F z.1),
    integral_div, hm (u * q) (mul_nonneg hu.le hq)]
  have heq : (fun z : Nat × Nat => 1 + (z.2 : Real) * F z.1) =
      (fun z : Nat × Nat => 1 + F z.1 * (z.2 : Real)) := by
    funext z; ring
  rw [heq, integral_add (integrable_const 1) hprod, integral_prod_mul F (fun W : Nat => (W : Real)),
    hm (t * v) (mul_nonneg ht.le hv)]
  simp only [integral_const, smul_eq_mul, probReal_univ]
  field_simp

/--
[Under the stated inputs and conditions](hyp:L,hL,hB,hu,ht,hs,hv,hmu,B,u,t,s,v,mu), [Both branch means equal the arm target minus their explicit bias terms](goal).
-/
-- @node: hybrid_branch_means
lemma hybrid_branch_means (L : Nat) (B u t s v mu : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t)
    (hs : 0 < s) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1) :
    (∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s * mu) s v) =
      (s + v) * mu - v * mu * (chebE L).eval (s / B) ∧
    (∫ z, inverseCellBranch u z ∂cellPoissonLaw u t (s * mu) s v) =
      (s + v) * mu - v * mu * Real.exp (-t * s) := by
  let G : Nat → Real := fun K => ∑ h ∈ Finset.range (L - 1),
    (chebG L).coeff h * (K.descFactorial h : Real) / (t * B) ^ h
  have hG : Integrable G (poissonMeasure (Real.toNNReal (t * s))) := by
    apply integrable_finsetSum
    intro h _
    exact ((Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      _ h).const_mul _).div_const _
  have hdeg := chebG_natDegree_le L
  have hmean : (∫ K, G K ∂poissonMeasure (Real.toNNReal (t * s))) =
      (chebG L).eval (s / B) := by
    have hr : t * B * (s / B) = t * s := by field_simp
    simpa only [hr] using poisson_factorial_polynomial_mean (chebG L) (L - 1)
      (by omega) (t * B) (s / B) (mul_pos ht hB) (by positivity)
  have hq : 0 ≤ s * mu := mul_nonneg hs.le hmu.1
  constructor
  · have hh := poisson_cell_multiplier_mean u t (s * mu) s v hu hq hv ht
      (fun K => G K / (t * B)) (hG.div_const _)
    have heq : polynomialCellBranch L B u t =
        (fun z : Nat × Nat × Nat => (z.1 : Real) / u *
          (1 + (z.2.2 : Real) * (G z.2.1 / (t * B)))) := by
      funext z; dsimp [polynomialCellBranch, G]; ring
    rw [heq, hh, integral_div, hmean]
    rw [(cheb_continuation_eval L (by omega) (s / B) (by positivity)).2]
    field_simp
    ring
  · let F : Nat → Real := fun K => ((K : Real) + 1)⁻¹
    have hF : Integrable F (poissonMeasure (Real.toNNReal (t * s))) := by
      simpa only [F, Nat.cast_add, Nat.cast_one] using
        (Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two
          (Real.toNNReal (t * s))).integrable (by norm_num)
    have hh := poisson_cell_multiplier_mean u t (s * mu) s v hu hq hv ht F hF
    have heq : inverseCellBranch u =
        (fun z : Nat × Nat × Nat => (z.1 : Real) / u *
          (1 + (z.2.2 : Real) * F z.2.1)) := by
      funext z; simp [inverseCellBranch, F, div_eq_mul_inv]
    rw [heq, hh]
    have hrec := (poisson_inverse_moments (Real.toNNReal (t * s))).1
    simp only [Real.coe_toNNReal _ (mul_nonneg ht.le hs.le),
      if_neg (ne_of_gt (mul_pos ht hs))] at hrec
    rw [show (∫ K, F K ∂poissonMeasure (Real.toNNReal (t * s))) =
      (1 - Real.exp (-(t * s))) / (t * s) from hrec]
    field_simp
    ring

end CausalSmith.Stat.AnnotationRarearmFrontier
