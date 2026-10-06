module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.BranchMeans

/-!
Factorial branch light-cell moments, upstream of the aggregate variance bound.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- Under the stated inputs and conditions, Every finite normalized falling-factorial polynomial is square-integrable under a
Poisson law, so its second-moment estimates can be integrated.  This gives [the stated result](goal). -/
-- @node: poisson_factorial_polynomial_memLp
lemma poisson_factorial_polynomial_memLp (rate : NNReal) (J : Nat)
    (c : Nat → Real) (D : Real) :
    MemLp (fun K : Nat => ∑ h ∈ Finset.range J,
      c h * (K.descFactorial h : Real) / D ^ h) 2 (poissonMeasure rate) := by
  apply memLp_finsetSum
  intro h _
  have hh : MemLp (fun K : Nat => (K.descFactorial h : Real)) 2
      (poissonMeasure rate) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have hi := integrable_finsetSum (Finset.range (min h h + 1))
      (fun r _ => (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
        rate (h + h - r)).const_mul
        ((h.choose r : Real) * (h.choose r : Real) * (r.factorial : Real)))
    exact hi.congr (Filter.Eventually.of_forall (fun K => by
      simpa only [pow_two] using
        (Causalean.Stat.Concentration.Poisson.descFactorial_mul K h h).symm))
  simpa only [div_eq_mul_inv] using (hh.const_mul (c h)).mul_const ((D ^ h)⁻¹)

/-- Under the stated inputs and conditions, The factorial multiplier has a universal light-cell squared-moment bound. This gives [the stated conclusion](goal). -/
-- @node: light_multiplier_second_moment
lemma light_multiplier_second_moment :
    ∃ C : Real, 0 < C ∧ ∀ (L : Nat) (B t s v : Real),
      4 ≤ L → 0 < B → 0 < t → 0 ≤ s → s ≤ B → 0 ≤ v → (L : Real) ≤ t * B →
      (∫ z : Nat × Nat,
        (1 + (z.2 : Real) / (t * B) * (∑ h ∈ Finset.range (L - 1),
          (chebG L).coeff h * (z.1.descFactorial h : Real) / (t * B) ^ h)) ^ 2 ∂
        (poissonMeasure (Real.toNNReal (t * s))).prod (poissonMeasure (Real.toNNReal (t * v)))) ≤
      C * ((2 : Real) ^ 24) ^ L * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro L B t s v hL hB ht hs hsB hv hD
  let G : Nat → Real := fun K => ∑ h ∈ Finset.range (L - 1),
    (chebG L).coeff h * (K.descFactorial h : Real) / (t * B) ^ h
  let mu := poissonMeasure (Real.toNNReal (t * s))
  let nu := poissonMeasure (Real.toNNReal (t * v))
  have hG : MemLp G 2 mu := poisson_factorial_polynomial_memLp _ _ _ _
  have hW := Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
    (Real.toNNReal (t * v))
  have hprod : Integrable (fun z : Nat × Nat => G z.1 ^ 2 *
      ((z.2 : Real) / (t * B)) ^ 2) (mu.prod nu) :=
    hG.integrable_sq.mul_prod (by
      simpa only [div_eq_mul_inv] using (hW.mul_const ((t * B)⁻¹)).integrable_sq)
  have hbound : (∫ z : Nat × Nat, (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2
      ∂mu.prod nu) ≤ 2 + 2 * ((∫ K, G K ^ 2 ∂mu) *
        (∫ W : Nat, ((W : Real) / (t * B)) ^ 2 ∂nu)) := by
    calc
      _ ≤ ∫ z : Nat × Nat, 2 + 2 * (G z.1 ^ 2 * ((z.2 : Real) / (t * B)) ^ 2)
          ∂mu.prod nu := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          ((integrable_const 2).add (hprod.const_mul 2))
        exact Filter.Eventually.of_forall (fun z => by
          have hh : (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2 ≤
              2 + 2 * ((z.2 : Real) / (t * B) * G z.1) ^ 2 := by
            nlinarith only [sq_nonneg (1 - (z.2 : Real) / (t * B) * G z.1)]
          change (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2 ≤
            2 + 2 * (G z.1 ^ 2 * ((z.2 : Real) / (t * B)) ^ 2)
          calc
            _ ≤ 2 + 2 * ((z.2 : Real) / (t * B) * G z.1) ^ 2 := hh
            _ = _ := by ring)
      _ = _ := by
        rw [integral_add (integrable_const 2) (hprod.const_mul 2), integral_const_mul,
          integral_prod_mul (fun K => G K ^ 2) (fun W : Nat => ((W : Real) / (t * B)) ^ 2)]
        simp
  have hsratio : 0 ≤ s / B := div_nonneg hs hB.le
  have hratio : s / B ≤ 1 := (div_le_one hB).2 hsB
  have hcert := (chebyshev_factorial_certificate L (by omega)).2.2.2.2.2
    t B (s / B) ht hB hsratio hD
  have hrate : t * (s / B) * B = t * s := by field_simp
  have hGs : (∫ K, G K ^ 2 ∂mu) ≤ ((2 : Real) ^ 24) ^ L := by
    have hg := hcert.2
    rw [hrate] at hg
    have hp : (1 + s / B) ^ (2 * L) ≤ (2 : Real) ^ (2 * L) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ 392 ^ L * (1 + s / B) ^ (2 * L) := hg
      _ ≤ 392 ^ L * (2 : Real) ^ (2 * L) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (1568 : Real) ^ L := by rw [pow_mul, ← mul_pow]; norm_num
      _ ≤ ((2 : Real) ^ 24) ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hWmoment : (∫ W : Nat, ((W : Real) / (t * B)) ^ 2 ∂nu) =
      v ^ 2 / B ^ 2 + v / (t * B ^ 2) := by
    have hm := Causalean.Stat.Concentration.Poisson.poisson_descFactorial_mixed
      (Real.toNNReal (t * v)) 1 1
    norm_num [Finset.sum_range_succ,
      Real.toNNReal_of_nonneg (mul_nonneg ht.le hv)] at hm
    simp_rw [div_pow]
    rw [integral_div]
    simp only [nu]
    simp_rw [pow_two]
    simp only [Real.toNNReal_of_nonneg (mul_nonneg ht.le hv)]
    rw [hm]
    field_simp
  have hF : 1 ≤ ((2 : Real) ^ 24) ^ L := one_le_pow₀ (by norm_num)
  have hV : 0 ≤ v ^ 2 / B ^ 2 + v / (t * B ^ 2) := by positivity
  change (∫ z : Nat × Nat, (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2
    ∂mu.prod nu) ≤ _
  rw [hWmoment] at hbound
  calc
    _ ≤ 2 + 2 * ((∫ K, G K ^ 2 ∂mu) * (v ^ 2 / B ^ 2 + v / (t * B ^ 2))) := hbound
    _ ≤ 2 * ((2 : Real) ^ 24) ^ L * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) := by
      have hh := mul_le_mul_of_nonneg_right hGs hV
      calc
        _ ≤ 2 * ((2 : Real) ^ 24) ^ L +
            2 * (((2 : Real) ^ 24) ^ L * (v ^ 2 / B ^ 2 + v / (t * B ^ 2))) :=
          add_le_add (by linarith only [hF]) (mul_le_mul_of_nonneg_left hh (by norm_num))
        _ = _ := by ring

end CausalSmith.Stat.AnnotationRarearmFrontier
