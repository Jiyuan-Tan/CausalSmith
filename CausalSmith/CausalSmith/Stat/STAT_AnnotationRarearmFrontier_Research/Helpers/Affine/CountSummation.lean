module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.CountEnvelope

/-!
Absolutely convergent count sums and the Palm-shifted coefficient envelope for
one rare cell. These bounds retain the common control baseline exactly.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open scoped BigOperators

set_option maxHeartbeats 800000 in
-- Elaborating the finite coefficient convolution requires a larger local budget.
/-- Under the stated inputs and conditions, Absolute convergence justifies regrouping the two count indices at any
fixed Taylor coefficient.  This gives [the stated result](goal). -/
-- @node: affine_two_arm_coeff_series_summable
lemma affine_two_arm_coeff_series_summable (a b c d t s : Real) (j : Nat) :
    Summable (fun k : Nat × Nat => t ^ k.1 / (k.1.factorial : Real) *
      (s ^ k.2 / (k.2.factorial : Real)) *
      (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k.1) *
        ((Polynomial.C c + Polynomial.C d * Polynomial.X) ^ k.2)).coeff j) := by
  have hs (v : Nat × Nat) (_ : v ∈ Finset.antidiagonal j) :
      Summable (fun k : Nat × Nat =>
        (t ^ k.1 / (k.1.factorial : Real) *
          ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k.1).coeff v.1) *
        (s ^ k.2 / (k.2.factorial : Real) *
          ((Polynomial.C c + Polynomial.C d * Polynomial.X) ^ k.2).coeff v.2)) := by
    exact summable_mul_of_summable_norm
      (summable_norm_iff.mpr (affine_linear_coeff_series_summable a b t v.1))
      (summable_norm_iff.mpr (affine_linear_coeff_series_summable c d s v.2))
  convert summable_sum hs using 1
  ext k
  rw [Polynomial.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- [Under the stated hypotheses](hyp:ha,hb,he,he',hu,hM), The labeled Palm shift preserves absolute convergence of the joint count sum.  This gives [the stated result](goal). -/
-- @node: affine_labeled_two_arm_coeff_series_summable
lemma affine_labeled_two_arm_coeff_series_summable (alpha b0 eps u M : Real) (j : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hM : 0 ≤ M) :
    Summable (fun k : Nat × Nat => u ^ k.1 / ((k.1 + 1).factorial : Real) *
      (M ^ k.2 / (k.2.factorial : Real)) *
      (((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ k.1) *
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ k.2)).coeff j) := by
  apply (affine_two_arm_coeff_series_summable alpha (1 - eps)
    ((1 - eps) * b0) eps u M j).of_nonneg_of_le
  · intro k
    exact mul_nonneg (by positivity)
      (affine_arm_power_coeff_nonneg alpha b0 eps k.1 k.2 j ha hb he he')
  · intro k
    have h := affine_labeled_count_coeff_le alpha b0 eps u k.1 k.2 j ha hb he he' hu
    have hc : 0 ≤ M ^ k.2 / (k.2.factorial : Real) := by positivity
    convert mul_le_mul_of_nonneg_right h hc using 1 <;> first | rfl | ring

/-- [Under the stated inputs and conditions](hyp:j,ha,hb,he,he',hu,hM,alpha,b0,eps,u,M), After summing both counts, the Palm-shifted coefficients are dominated by
those of the ordinary two-arm exponential.  This gives [the stated result](goal).-/
-- @node: affine_labeled_two_arm_coeff_series_le
lemma affine_labeled_two_arm_coeff_series_le (alpha b0 eps u M : Real) (j : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hM : 0 ≤ M) :
    (∑' r : Nat, ∑' c : Nat, u ^ r / ((r + 1).factorial : Real) *
      (M ^ c / (c.factorial : Real)) *
      (((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j) ≤
    Real.exp (u * alpha + M * ((1 - eps) * b0)) *
      (u * (1 - eps) + M * eps) ^ j / (j.factorial : Real) := by
  rw [← affine_two_arm_coeff_series_eq alpha (1 - eps) ((1 - eps) * b0) eps u M j]
  have hl := affine_labeled_two_arm_coeff_series_summable alpha b0 eps u M j
    ha hb he he' hu hM
  have hr := affine_two_arm_coeff_series_summable alpha (1 - eps) ((1 - eps) * b0) eps u M j
  rw [← hl.tsum_prod' hl.prod_factor, ← hr.tsum_prod' hr.prod_factor]
  apply hl.tsum_le_tsum _ hr
  intro k
  have h := affine_labeled_count_coeff_le alpha b0 eps u k.1 k.2 j ha hb he he' hu
  have hc : 0 ≤ M ^ k.2 / (k.2.factorial : Real) := by positivity
  convert mul_le_mul_of_nonneg_right h hc using 1 <;> first | rfl | ring

/-- [Under the stated inputs and conditions](hyp:j,hb,he,he',hM,b0,eps,M), When treated channels have been combined, the Palm envelope cancels the
common baseline, coefficient by coefficient.  This gives [the stated result](goal).-/
-- @node: affine_labeled_count_coeff_baseline_le
lemma affine_labeled_count_coeff_baseline_le (b0 eps M : Real) (j : Nat)
    (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1) (hM : 0 ≤ M) :
    Real.exp (-M * b0) *
      (∑' r : Nat, ∑' c : Nat, M ^ r / ((r + 1).factorial : Real) *
        (M ^ c / (c.factorial : Real)) *
        (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
          ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j) ≤
    M ^ j / (j.factorial : Real) := by
  have h := mul_le_mul_of_nonneg_left
    (affine_labeled_two_arm_coeff_series_le (eps * b0) b0 eps M M j
      (mul_nonneg he hb) hb he he' hM hM) (Real.exp_pos (-M * b0)).le
  have hbase : M * (eps * b0) + M * ((1 - eps) * b0) = M * b0 := by ring
  have hslope : M * (1 - eps) + M * eps = M := by ring
  rw [hbase, hslope, ← mul_div_assoc, ← mul_assoc, ← Real.exp_add] at h
  simpa using h

set_option maxHeartbeats 800000 in
-- Elaborating the finite coefficient convolution requires a larger local budget.
/-- Under the stated inputs and conditions, Absolute convergence of both treated channels remains valid after multiplying
by a fixed control-count polynomial.  This gives [the stated result](goal). -/
-- @node: affine_treated_count_series_summable
lemma affine_treated_count_series_summable (a b u w : Real)
    (q : Polynomial Real) (j : Nat) :
    Summable (fun k : Nat × Nat => u ^ k.1 / (k.1.factorial : Real) *
      (w ^ k.2 / (k.2.factorial : Real)) *
      (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ (k.1 + k.2)) * q).coeff j) := by
  have hs (v : Nat × Nat) (_ : v ∈ Finset.antidiagonal j) :
      Summable (fun k : Nat × Nat =>
        (u ^ k.1 / (k.1.factorial : Real) * (w ^ k.2 / (k.2.factorial : Real)) *
          (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k.1) *
            ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k.2)).coeff v.1) *
          q.coeff v.2) :=
    (affine_two_arm_coeff_series_summable a b a b u w v.1).mul_right _
  convert summable_sum hs using 1
  ext k
  rw [pow_add, Polynomial.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- [Under the stated inputs and conditions](hyp:q,j,a,b,u,w), Regrouping the complete and auxiliary treated counts gives intensity u+w,
with every fixed control count retained.  This gives [the stated result](goal).-/
-- @node: affine_treated_count_series_eq
lemma affine_treated_count_series_eq (a b u w : Real)
    (q : Polynomial Real) (j : Nat) :
    (∑' r : Nat, ∑' g : Nat, u ^ r / (r.factorial : Real) *
      (w ^ g / (g.factorial : Real)) *
      (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ (r + g)) * q).coeff j) =
    ∑' R : Nat, (u + w) ^ R / (R.factorial : Real) *
      (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ R) * q).coeff j := by
  let p : Polynomial Real := Polynomial.C a + Polynomial.C b * Polynomial.X
  let f : Nat × Nat → Real := fun k => u ^ k.1 / (k.1.factorial : Real) *
    (w ^ k.2 / (k.2.factorial : Real)) * ((p ^ (k.1 + k.2)) * q).coeff j
  have hf : Summable f := affine_treated_count_series_summable a b u w q j
  rw [← hf.tsum_prod' hf.prod_factor]
  have hs : Summable (fun k : Σ R : Nat, Finset.antidiagonal R => f k.2) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [hs.tsum_sigma' (fun R => (hasSum_fintype _).summable)]
  apply tsum_congr
  intro R
  rw [tsum_fintype]
  change (∑ k : Finset.antidiagonal R, f k) = _
  rw [Finset.sum_coe_sort]
  calc
    _ = (∑ k ∈ Finset.antidiagonal R,
        u ^ k.1 / (k.1.factorial : Real) * (w ^ k.2 / (k.2.factorial : Real))) *
        ((p ^ R) * q).coeff j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [f, Finset.mem_antidiagonal.mp hk]
    _ = _ := by
      have hc : (∑ k ∈ Finset.antidiagonal R,
          u ^ k.1 / (k.1.factorial : Real) * (w ^ k.2 / (k.2.factorial : Real))) =
          (u + w) ^ R / (R.factorial : Real) := by
        simpa only [mul_div_assoc] using affine_exponential_coeff_convolution u w R
      rw [← hc]

/-- [Under the stated inputs and conditions](hyp:ha,hb,he,he',hu,hw,alpha,b0,eps,u,w,c,j), The labeled factorial shift decreases the joint treated-channel coefficient
sum, while retaining the entire control-count polynomial.  This gives [the stated result](goal).-/
-- @node: affine_labeled_treated_series_le
lemma affine_labeled_treated_series_le (alpha b0 eps u w : Real) (c j : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) :
    (∑' r : Nat, ∑' g : Nat, u ^ r / ((r + 1).factorial : Real) *
      (w ^ g / (g.factorial : Real)) *
      (((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ (r + g)) *
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j) ≤
    ∑' R : Nat, (u + w) ^ R / (R.factorial : Real) *
      (((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ R) *
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j := by
  let p : Polynomial Real := Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X
  let q : Polynomial Real := Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X
  let f : Nat × Nat → Real := fun k => u ^ k.1 / (k.1.factorial : Real) *
    (w ^ k.2 / (k.2.factorial : Real)) * ((p ^ (k.1 + k.2)) * q ^ c).coeff j
  let g : Nat × Nat → Real := fun k => u ^ k.1 / ((k.1 + 1).factorial : Real) *
    (w ^ k.2 / (k.2.factorial : Real)) * ((p ^ (k.1 + k.2)) * q ^ c).coeff j
  have hcoeff (k : Nat × Nat) : 0 ≤ ((p ^ (k.1 + k.2)) * q ^ c).coeff j :=
    affine_arm_power_coeff_nonneg alpha b0 eps (k.1 + k.2) c j ha hb he he'
  have hnonneg (k : Nat × Nat) : 0 ≤ g k := mul_nonneg (by positivity) (hcoeff k)
  have hle (k : Nat × Nat) : g k ≤ f k := by
    have h := mul_le_mul_of_nonneg_right (affine_labeled_factorial_term_le u hu k.1)
      (mul_nonneg (show 0 ≤ w ^ k.2 / (k.2.factorial : Real) by positivity) (hcoeff k))
    simpa only [g, f, mul_assoc] using h
  have hf : Summable f := affine_treated_count_series_summable alpha (1 - eps) u w (q ^ c) j
  have hg : Summable g := hf.of_nonneg_of_le hnonneg hle
  rw [← affine_treated_count_series_eq alpha (1 - eps) u w (q ^ c) j]
  change (∑' r, ∑' g', g (r, g')) ≤ ∑' r, ∑' g', f (r, g')
  rw [← hg.tsum_prod' hg.prod_factor, ← hf.tsum_prod' hf.prod_factor]
  exact hg.tsum_le_tsum hle hf

set_option maxHeartbeats 800000 in
-- The three nested count series require elaborating two finite coefficient convolutions.
/-- [Under the stated inputs and conditions](hyp:j,hb,he,he',hu,hw,hM,b0,eps,u,w,M), The three count indices have the coefficient envelope asserted in equation
(7): the two treated intensities combine, and the baseline cancels exactly.  This gives [the stated result](goal).-/
-- @node: affine_three_count_coeff_baseline_le
lemma affine_three_count_coeff_baseline_le (b0 eps u w M : Real) (j : Nat)
    (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hM : M = u + w) :
    Real.exp (-M * b0) *
      (∑' c : Nat, M ^ c / (c.factorial : Real) *
        (∑' r : Nat, ∑' g : Nat, u ^ r / ((r + 1).factorial : Real) *
          (w ^ g / (g.factorial : Real)) *
          (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ (r + g)) *
            ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j)) ≤
    M ^ j / (j.factorial : Real) := by
  let p : Polynomial Real := Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X
  let q : Polynomial Real := Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X
  let F : Nat → Real := fun c => M ^ c / (c.factorial : Real) *
    (∑' r : Nat, ∑' g : Nat, u ^ r / ((r + 1).factorial : Real) *
      (w ^ g / (g.factorial : Real)) * ((p ^ (r + g)) * q ^ c).coeff j)
  let G : Nat → Real := fun c => M ^ c / (c.factorial : Real) *
    (∑' R : Nat, M ^ R / (R.factorial : Real) * ((p ^ R) * q ^ c).coeff j)
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hle (c : Nat) : F c ≤ G c := by
    have h := affine_labeled_treated_series_le (eps * b0) b0 eps u w c j
      (mul_nonneg he hb) hb he he' hu hw
    rw [← hM] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hn (c : Nat) : 0 ≤ F c := by
    apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro r
    apply tsum_nonneg
    intro g
    exact mul_nonneg (by positivity)
      (affine_arm_power_coeff_nonneg (eps * b0) b0 eps (r + g) c j
        (mul_nonneg he hb) hb he he')
  have hr : Summable (fun k : Nat × Nat => M ^ k.1 / (k.1.factorial : Real) *
      (M ^ k.2 / (k.2.factorial : Real)) * ((p ^ k.1) * q ^ k.2).coeff j) :=
    affine_two_arm_coeff_series_summable (eps * b0) (1 - eps)
      ((1 - eps) * b0) eps M M j
  have hG : Summable G := by
    apply hr.prod_symm.prod.congr
    intro c
    simp only [G, Prod.swap_prod_mk, ← tsum_mul_left]
    apply tsum_congr
    intro R
    ring
  have hF : Summable F := hG.of_nonneg_of_le hn hle
  have heq : Real.exp (-M * b0) * (∑' c, G c) = M ^ j / (j.factorial : Real) := by
    have hc := Summable.tsum_comm (f := fun R c : Nat =>
      M ^ R / (R.factorial : Real) * (M ^ c / (c.factorial : Real)) *
        ((p ^ R) * q ^ c).coeff j) hr
    have hsum : (∑' c, G c) = ∑' R : Nat, ∑' c : Nat, M ^ R / (R.factorial : Real) *
        (M ^ c / (c.factorial : Real)) * ((p ^ R) * q ^ c).coeff j := by
      rw [← hc]
      simp only [G, ← tsum_mul_left]
      apply tsum_congr
      intro c
      apply tsum_congr
      intro R
      ring
    rw [hsum]
    exact affine_arm_count_coeff_baseline_cancel b0 eps M j
  change Real.exp (-M * b0) * (∑' c, F c) ≤ _
  rw [← heq]
  exact mul_le_mul_of_nonneg_left (hF.tsum_le_tsum hle hG) (Real.exp_pos _).le

end CausalSmith.Stat.AnnotationRarearmFrontier
