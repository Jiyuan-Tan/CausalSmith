module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.CoefficientBounds

/-!
Chebyshev continuation and factorial-lift mean and second-moment certificate.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- Under the stated inputs and conditions, Products of falling factorials have finite Poisson expectation.  This gives [the stated result](goal). -/
-- @node: factorial_product_integrable
lemma factorial_product_integrable (rate : NNReal) (h v : Nat) :
    Integrable (fun K : Nat => (K.descFactorial h : Real) *
      (K.descFactorial v : Real)) (poissonMeasure rate) := by
  have hi := integrable_finsetSum (Finset.range (min h v + 1))
    (fun r _ => (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      rate (h + v - r)).const_mul
      ((h.choose r : Real) * (v.choose r : Real) * (r.factorial : Real)))
  exact hi.congr (Filter.Eventually.of_forall (fun K =>
    (Causalean.Stat.Concentration.Poisson.descFactorial_mul K h v).symm))

/-- [Under the stated inputs and conditions](hyp:hD,hz,D,z,h,v), Normalize the exact overlap formula by the factorial-pool intensity.  This gives [the stated result](goal).-/
-- @node: normalized_factorial_mixed_moment
lemma normalized_factorial_mixed_moment (D z : Real) (h v : Nat)
    (hD : 0 < D) (hz : 0 ≤ z) :
    (∫ K : Nat, ((K.descFactorial h : Real) / D ^ h) *
      ((K.descFactorial v : Real) / D ^ v)
      ∂poissonMeasure (Real.toNNReal (D * z))) =
    ∑ r ∈ Finset.range (min h v + 1),
      (h.choose r : Real) * ((v.choose r : Real) * (r.factorial : Real) / D ^ r) *
        z ^ (h + v - r) := by
  simp_rw [div_mul_div_comm]
  rw [integral_div, Causalean.Stat.Concentration.Poisson.poisson_descFactorial_mixed,
    Real.coe_toNNReal _ (mul_nonneg hD.le hz), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hrhv : r ≤ h + v := by
    have := Finset.mem_range.mp hr
    have := Nat.min_le_left h v
    omega
  rw [mul_pow, show D ^ h * D ^ v = D ^ (h + v) by rw [pow_add],
    show D ^ (h + v) = D ^ r * D ^ (h + v - r) by
      rw [← pow_add, Nat.add_sub_of_le hrhv]]
  field_simp

/-- [Under the stated inputs and conditions](hyp:D,hD,hv,v,r), Each overlap factor is at most one when the order is below the intensity.  This gives [the stated result](goal).-/
-- @node: factorial_overlap_factor_le_one
lemma factorial_overlap_factor_le_one (D : Real) (v r : Nat)
    (hD : 0 < D) (hv : (v : Real) ≤ D) :
    (v.choose r : Real) * (r.factorial : Real) / D ^ r ≤ 1 := by
  have hc : (v.choose r : Real) * (r.factorial : Real) =
      (v.descFactorial r : Real) := by
    exact_mod_cast (Nat.mul_comm (v.choose r) r.factorial).trans
      (Nat.descFactorial_eq_factorial_mul_choose v r).symm
  rw [hc, div_le_one (pow_pos hD r)]
  have hb : (v.descFactorial r : Real) ≤ (v : Real) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow v r
  exact hb.trans (pow_le_pow_left₀ (Nat.cast_nonneg v) hv r)

/-- [Under the stated inputs and conditions](hyp:hh,hv,hD,hLD,L,hz,h,v,D,z), The binomial overlap sum gives the uniform mixed-moment envelope.  This gives [the stated result](goal).-/
-- @node: normalized_factorial_mixed_bound
lemma normalized_factorial_mixed_bound (L h v : Nat) (D z : Real)
    (hh : h ≤ L) (hv : v ≤ L) (hD : 0 < D) (hLD : (L : Real) ≤ D)
    (hz : 0 ≤ z) :
    (∫ K : Nat, ((K.descFactorial h : Real) / D ^ h) *
      ((K.descFactorial v : Real) / D ^ v)
      ∂poissonMeasure (Real.toNNReal (D * z))) ≤
      2 ^ L * (1 + z) ^ (2 * L) := by
  rw [normalized_factorial_mixed_moment D z h v hD hz]
  have hbase : 1 ≤ 1 + z := by linarith
  have hpower (r : Nat) : z ^ (h + v - r) ≤ (1 + z) ^ (2 * L) :=
    (pow_le_pow_left₀ hz (by linarith) _).trans
      (pow_le_pow_right₀ hbase (by omega))
  calc
    _ ≤ ∑ r ∈ Finset.range (min h v + 1),
        (h.choose r : Real) * (1 + z) ^ (2 * L) := by
      apply Finset.sum_le_sum
      intro r _
      have hf := factorial_overlap_factor_le_one D v r hD
        ((by exact_mod_cast hv : (v : Real) ≤ (L : Real)).trans hLD)
      have hn : 0 ≤ (v.choose r : Real) * (r.factorial : Real) / D ^ r := by positivity
      apply mul_le_mul
      · simpa using mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (h.choose r))
      · exact hpower r
      · positivity
      · positivity
    _ ≤ ∑ r ∈ Finset.range (h + 1),
        (h.choose r : Real) * (1 + z) ^ (2 * L) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega : min h v + 1 ≤ h + 1)
      · intros; positivity
    _ = 2 ^ h * (1 + z) ^ (2 * L) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose h
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hh) (by positivity)

/-- [Under the stated inputs and conditions](hyp:c,hJ,hD,hLD,L,hz,J,D,z), Finite assembly of the mixed-moment envelope against absolute coefficients.  This gives [the stated result](goal).-/
-- @node: factorial_polynomial_second_moment_bound
lemma factorial_polynomial_second_moment_bound (L J : Nat) (c : Nat → Real)
    (D z : Real) (hJ : J ≤ L + 1) (hD : 0 < D) (hLD : (L : Real) ≤ D)
    (hz : 0 ≤ z) :
    (∫ K : Nat, (∑ h ∈ Finset.range J,
      c h * (K.descFactorial h : Real) / D ^ h) ^ 2
      ∂poissonMeasure (Real.toNNReal (D * z))) ≤
    (∑ h ∈ Finset.range J, |c h|) ^ 2 *
      (2 ^ L * (1 + z) ^ (2 * L)) := by
  let mu := poissonMeasure (Real.toNNReal (D * z))
  let A := fun (h K : Nat) => (K.descFactorial h : Real) / D ^ h
  let M := fun h v => ∫ K, A h K * A v K ∂mu
  have hi (h v : Nat) : Integrable (fun K => (c h * A h K) * (c v * A v K)) mu := by
    have hh := ((factorial_product_integrable (Real.toNNReal (D * z)) h v).div_const
      (D ^ h * D ^ v)).const_mul (c h * c v)
    convert hh using 1
    funext K
    dsimp [A]
    ring
  have heq : (∫ K : Nat, (∑ h ∈ Finset.range J,
      c h * (K.descFactorial h : Real) / D ^ h) ^ 2 ∂mu) =
      ∑ h ∈ Finset.range J, ∑ v ∈ Finset.range J, c h * c v * M h v := by
    have halg (K : Nat) : (∑ h ∈ Finset.range J,
        c h * (K.descFactorial h : Real) / D ^ h) ^ 2 =
        ∑ h ∈ Finset.range J, ∑ v ∈ Finset.range J,
          (c h * A h K) * (c v * A v K) := by
      simp only [A, pow_two, Finset.sum_mul, Finset.mul_sum, mul_div_assoc]
      rw [Finset.sum_comm]
    simp_rw [halg]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro h _
      rw [integral_finsetSum (Finset.range J) (fun v _ => hi h v)]
      apply Finset.sum_congr rfl
      intro v _
      have ht (K : Nat) : (c h * A h K) * (c v * A v K) =
          (c h * c v) * (A h K * A v K) := by ring
      simp_rw [ht]
      exact integral_const_mul _ _
    · intro h _
      exact integrable_finsetSum _ (fun v _ => hi h v)
  rw [heq]
  calc
    _ ≤ ∑ h ∈ Finset.range J, ∑ v ∈ Finset.range J,
        |c h| * |c v| * (2 ^ L * (1 + z) ^ (2 * L)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro v hv
      have hm0 : 0 ≤ M h v := by
        apply integral_nonneg
        intro K
        dsimp [A]
        positivity
      have hm := normalized_factorial_mixed_bound L h v D z
        (by have := Finset.mem_range.mp hh; omega)
        (by have := Finset.mem_range.mp hv; omega) hD hLD hz
      have hc : c h * c v ≤ |c h| * |c v| := by
        rw [← abs_mul]
        exact le_abs_self _
      exact mul_le_mul hc hm hm0 (by positivity)
    _ = _ := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- [Under the stated inputs and conditions](hyp:L,hL,ht,hBb,hz,hD,t,Bb,z), The coefficient certificate and the mixed-moment envelope give the stated constant.  This gives [the stated result](goal).-/
-- @node: chebG_factorial_second_moment
lemma chebG_factorial_second_moment (L : Nat) (hL : 2 ≤ L) (t Bb z : Real)
    (ht : 0 < t) (hBb : 0 < Bb) (hz : 0 ≤ z) (hD : (L : Real) ≤ t * Bb) :
    (∫ K : Nat, (∑ h ∈ Finset.range (L - 1),
      (chebG L).coeff h * (K.descFactorial h : Real) / (t * Bb) ^ h) ^ 2
      ∂poissonMeasure (Real.toNNReal (t * z * Bb))) ≤
      392 ^ L * (1 + z) ^ (2 * L) := by
  have hrate : t * z * Bb = (t * Bb) * z := by ring
  rw [hrate]
  have hc := chebG_coeff_sum_le L hL
  have hs0 : 0 ≤ ∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h|) ^ 2 *
        (2 ^ L * (1 + z) ^ (2 * L)) :=
      factorial_polynomial_second_moment_bound L (L - 1) _ (t * Bb) z
        (by omega) (mul_pos ht hBb) hD hz
    _ ≤ (14 ^ L) ^ 2 * (2 ^ L * (1 + z) ^ (2 * L)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hc 2) (by positivity)
    _ = _ := by
      rw [← pow_mul, Nat.mul_comm L 2, pow_mul, ← mul_assoc, ← mul_pow]
      norm_num

/-- [Under the stated inputs and conditions](hyp:L,hL,ht,hBb,hz,t,Bb,z), The factorial lift of the second continuation is unbiased under its Poisson law.  This gives [the stated result](goal).-/
-- @node: chebG_factorial_unbiased
lemma chebG_factorial_unbiased (L : Nat) (hL : 2 ≤ L) (t Bb z : Real)
    (ht : 0 < t) (hBb : 0 < Bb) (hz : 0 ≤ z) :
    (∫ K, (∑ h ∈ Finset.range (L - 1),
      (chebG L).coeff h * (K.descFactorial h : Real) / (t * Bb) ^ h)
      ∂poissonMeasure (Real.toNNReal (t * z * Bb))) = (chebG L).eval z := by
  have hrate : 0 ≤ t * z * Bb := by positivity
  have hD : t * Bb ≠ 0 := ne_of_gt (mul_pos ht hBb)
  have hterm (h : Nat) :
      (∫ K, ((chebG L).coeff h / (t * Bb) ^ h) * (K.descFactorial h : Real)
        ∂poissonMeasure (Real.toNNReal (t * z * Bb))) =
      (chebG L).coeff h * z ^ h := by
    rw [integral_const_mul, Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment,
      Real.coe_toNNReal _ hrate]
    have heq : t * z * Bb = (t * Bb) * z := by ring
    rw [heq, mul_pow]
    field_simp
    simp only [mul_pow, mul_assoc]
  calc
    _ = ∫ K, ∑ h ∈ Finset.range (L - 1),
        ((chebG L).coeff h / (t * Bb) ^ h) * (K.descFactorial h : Real)
        ∂poissonMeasure (Real.toNNReal (t * z * Bb)) := by
      congr 1
      funext K
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = ∑ h ∈ Finset.range (L - 1), (chebG L).coeff h * z ^ h := by
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun h _ => hterm h)
      · intro h _
        exact (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
          (Real.toNNReal (t * z * Bb)) h).const_mul _
    _ = (chebG L).eval z := by
      exact (Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (chebG_natDegree_le L)
        (by omega : L - 2 < L - 1)) z).symm

-- @node: lem:chebyshev-factorial-certificate
/-- [Under the stated hypotheses](hyp:hL), The Chebyshev continuations obey the stated approximation, coefficient, unbiasedness, and
factorial second-moment bounds. This gives [the stated conclusion](goal). -/
lemma chebyshev_factorial_certificate (L : Nat) (hL : 2 ≤ L) :
    (∀ z : Real, 0 < z → z ≤ 1 → 0 ≤ (chebE L).eval z ∧
      (chebE L).eval z ≤ min 1 ((L : Real) ^ 2 * z)⁻¹) ∧
    (chebE L).eval 0 = 1 ∧
    (∀ z : Real, z ≠ 0 →
      (chebE L).eval z = (1 - (Polynomial.Chebyshev.T Real L).eval (1 - 2 * z)) /
        (2 * (L : Real) ^ 2 * z) ∧ (chebG L).eval z = (1 - (chebE L).eval z) / z) ∧
    (chebG L).natDegree ≤ L - 2 ∧
    (∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h|) ≤ 14 ^ L ∧
    ∀ (t Bb z : Real), 0 < t → 0 < Bb → 0 ≤ z → (L : Real) ≤ t * Bb →
      let Ghat : Nat → Real := fun K => ∑ h ∈ Finset.range (L - 1),
        (chebG L).coeff h * (K.descFactorial h : Real) / (t * Bb) ^ h
      (∫ K, Ghat K ∂poissonMeasure (Real.toNNReal (t * z * Bb))) = (chebG L).eval z ∧
      (∫ K, Ghat K ^ 2 ∂poissonMeasure (Real.toNNReal (t * z * Bb))) ≤
        392 ^ L * (1 + z) ^ (2 * L) := by
  have hLp : 0 < L := by omega
  refine ⟨fun z hz hz' => chebE_approximation_bounds L hLp z hz hz',
    chebE_eval_zero L hLp, cheb_continuation_eval L hLp, chebG_natDegree_le L, ?_, ?_⟩
  · exact chebG_coeff_sum_le L hL
  · intro t Bb z ht hBb hz hD
    exact ⟨chebG_factorial_unbiased L hL t Bb z ht hBb hz,
      chebG_factorial_second_moment L hL t Bb z ht hBb hz hD⟩

end CausalSmith.Stat.AnnotationRarearmFrontier
