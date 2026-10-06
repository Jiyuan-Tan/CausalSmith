module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.CountSummation

/-!
Exchange of the count-summed coefficient envelope with the positive exponential
series. The total-degree cutoff reads back the one-cell Taylor tail without a
bound on the common control baseline.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open scoped BigOperators

set_option maxHeartbeats 800000 in
-- Elaborating the nested series and their finite convolutions requires a larger budget.
/-- [Under the stated hypotheses](hyp:hz), The positive two-series envelope is absolutely summable even after the
matching-degree cutoff is imposed.  This gives [the stated result](goal). -/
-- @node: affine_filtered_exponential_product_summable
lemma affine_filtered_exponential_product_summable (z : Real) (hz : 0 ≤ z) (L : Nat) :
    Summable (fun k : Nat × Nat =>
      if L < k.1 + k.2 then
        z ^ k.1 / (k.1.factorial : Real) * z ^ k.2 / (k.2.factorial : Real)
      else 0) := by
  have hs := summable_mul_of_summable_norm
    (summable_norm_iff.mpr (Real.summable_pow_div_factorial z))
    (summable_norm_iff.mpr (Real.summable_pow_div_factorial z))
  apply hs.of_nonneg_of_le
  · intro k; split_ifs <;> positivity
  · intro k
    split_ifs
    · simp only [mul_div_assoc]
      exact le_rfl
    · positivity

set_option maxHeartbeats 800000 in
-- Elaborating the nested series and their finite convolutions requires a larger budget.
/-- [Under the stated inputs and conditions](hyp:z,hz,L), Regrouping the two positive exponential series by total degree gives the
Taylor tail of exp(2z), retaining precisely the degrees above L.  This gives [the stated result](goal).-/
-- @node: affine_exponential_total_degree_tail_eq
lemma affine_exponential_total_degree_tail_eq (z : Real) (hz : 0 ≤ z) (L : Nat) :
    (∑' j : Nat, ∑' k : Nat, if L < j + k then
      z ^ j / (j.factorial : Real) * z ^ k / (k.factorial : Real) else 0) =
    ∑' h : Nat, if L < h then (2 * z) ^ h / (h.factorial : Real) else 0 := by
  let f : Nat × Nat → Real := fun k => if L < k.1 + k.2 then
    z ^ k.1 / (k.1.factorial : Real) * z ^ k.2 / (k.2.factorial : Real) else 0
  have hf : Summable f := affine_filtered_exponential_product_summable z hz L
  rw [← hf.tsum_prod' hf.prod_factor]
  have hs : Summable (fun k : Σ h : Nat, Finset.antidiagonal h => f k.2) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [hs.tsum_sigma' (fun h => (hasSum_fintype _).summable)]
  apply tsum_congr
  intro h
  rw [tsum_fintype, Finset.sum_coe_sort]
  by_cases hh : L < h
  · calc
      _ = ∑ k ∈ Finset.antidiagonal h,
          z ^ k.1 / (k.1.factorial : Real) * z ^ k.2 / (k.2.factorial : Real) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [f, Finset.mem_antidiagonal.mp hk, if_pos hh]
      _ = _ := by
        simpa only [if_pos hh, mul_div_assoc, show z + z = 2 * z by ring] using
          affine_exponential_coeff_convolution z z h
  · simp only [if_neg hh]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [f, Finset.mem_antidiagonal.mp hk, if_neg hh]

set_option maxHeartbeats 800000 in
-- Elaborating the nested series and their finite convolutions requires a larger budget.
/-- [Under the stated inputs and conditions](hyp:A,L,hM,hB,hA,hle,M,B), Any nonnegative coefficient envelope dominated by the baseline-canceled
Poisson coefficients has total-degree tail at most that of exp(2MB).  This gives [the stated result](goal).-/
-- @node: affine_dominated_coeff_total_degree_tail_le
lemma affine_dominated_coeff_total_degree_tail_le (A : Nat → Real) (M B : Real)
    (L : Nat) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ j, 0 ≤ A j) (hle : ∀ j, A j ≤ M ^ j / (j.factorial : Real)) :
    (∑' j : Nat, A j * B ^ j *
      ∑' k : Nat, if L < k + j then (M * B) ^ k / (k.factorial : Real) else 0) ≤
    ∑' h : Nat, if L < h then (2 * M * B) ^ h / (h.factorial : Real) else 0 := by
  let F : Nat × Nat → Real := fun v => if L < v.1 + v.2 then
    A v.1 * B ^ v.1 * (M * B) ^ v.2 / (v.2.factorial : Real) else 0
  let G : Nat × Nat → Real := fun v => if L < v.1 + v.2 then
    (M * B) ^ v.1 / (v.1.factorial : Real) *
      (M * B) ^ v.2 / (v.2.factorial : Real) else 0
  have hn (v : Nat × Nat) : 0 ≤ F v := by
    have hAv := hA v.1
    dsimp [F]; split_ifs <;> positivity
  have hFG (v : Nat × Nat) : F v ≤ G v := by
    dsimp [F, G]
    split_ifs
    · have h := mul_le_mul_of_nonneg_right (hle v.1)
        (show 0 ≤ B ^ v.1 * ((M * B) ^ v.2 / (v.2.factorial : Real)) by positivity)
      convert h using 1 <;> first | rfl | (try simp only [mul_pow]; ring)
    · exact le_rfl
  have hG : Summable G :=
    affine_filtered_exponential_product_summable (M * B) (mul_nonneg hM hB) L
  have hF : Summable F := hG.of_nonneg_of_le hn hFG
  have heq : (∑' j : Nat, A j * B ^ j *
      ∑' k : Nat, if L < k + j then (M * B) ^ k / (k.factorial : Real) else 0) =
      ∑' j : Nat, ∑' k : Nat, F (j, k) := by
    apply tsum_congr
    intro j
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [F]
    rw [Nat.add_comm j k]
    split_ifs <;> simp [mul_div_assoc]
  rw [heq, ← hF.tsum_prod' hF.prod_factor]
  calc
    _ ≤ ∑' v, G v := hF.tsum_le_tsum hFG hG
    _ = ∑' j : Nat, ∑' k : Nat, G (j, k) := hG.tsum_prod' hG.prod_factor
    _ = _ := by
      simpa only [G, mul_assoc] using
        affine_exponential_total_degree_tail_eq (M * B) (mul_nonneg hM hB) L

/-- [Under the stated inputs and conditions](hyp:L,hb,he,he',hu,hw,hM,hB,b0,eps,u,w,M,B), Equation (7)'s count-summed Taylor envelope is bounded by the one-cell
exponential tail. Both treated channels and all control counts are retained.  This gives [the stated result](goal).-/
-- @node: affine_three_count_total_degree_tail_le
lemma affine_three_count_total_degree_tail_le (b0 eps u w M B : Real) (L : Nat)
    (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hM : M = u + w) (hB : 0 ≤ B) :
    (∑' j : Nat, (Real.exp (-M * b0) *
      (∑' c : Nat, M ^ c / (c.factorial : Real) *
        (∑' r : Nat, ∑' g : Nat, u ^ r / ((r + 1).factorial : Real) *
          (w ^ g / (g.factorial : Real)) *
          (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ (r + g)) *
            ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j))) *
      B ^ j * ∑' k : Nat, if L < k + j then
        (M * B) ^ k / (k.factorial : Real) else 0) ≤
    ∑' h : Nat, if L < h then (2 * M * B) ^ h / (h.factorial : Real) else 0 := by
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  apply affine_dominated_coeff_total_degree_tail_le _ M B L hM0 hB
  · intro j
    apply mul_nonneg (Real.exp_pos _).le
    apply tsum_nonneg
    intro c
    apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro r
    apply tsum_nonneg
    intro g
    exact mul_nonneg (by positivity)
      (affine_arm_power_coeff_nonneg (eps * b0) b0 eps (r + g) c j
        (mul_nonneg he hb) hb he he')
  · intro j
    exact affine_three_count_coeff_baseline_le b0 eps u w M j hb he he' hu hw hM

end CausalSmith.Stat.AnnotationRarearmFrontier
