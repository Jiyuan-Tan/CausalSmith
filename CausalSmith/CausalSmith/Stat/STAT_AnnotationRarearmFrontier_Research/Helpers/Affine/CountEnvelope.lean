module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.RawPoissonTV

/-!
Countwise nonnegative polynomial envelopes for equation (6), the shifted labeled
factorial comparison, absolutely convergent coefficientwise count sums, and exact
cancellation of the common control baseline.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open scoped BigOperators

/-- [Under the stated inputs and conditions](hyp:ha,hb,he,he',alpha,b0,eps,r,c,j), Products of nonnegative affine powers have nonnegative Taylor coefficients.  This gives [the stated result](goal).-/
-- @node: affine_arm_power_coeff_nonneg
lemma affine_arm_power_coeff_nonneg (alpha b0 eps : Real) (r c j : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1) :
    0 ≤ ((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r *
      (Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c).coeff j := by
  have hmul (p q : Polynomial Real) (hp : ∀ j, 0 ≤ p.coeff j)
      (hq : ∀ j, 0 ≤ q.coeff j) (j : Nat) : 0 ≤ (p * q).coeff j := by
    rw [Polynomial.coeff_mul]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k.1) (hq k.2)
  have hpow (p : Polynomial Real) (hp : ∀ j, 0 ≤ p.coeff j) (n j : Nat) :
      0 ≤ (p ^ n).coeff j := by
    induction n generalizing j with
    | zero => simp only [pow_zero, Polynomial.coeff_one]; split_ifs <;> norm_num
    | succ n ih =>
      rw [pow_succ]
      exact hmul (p ^ n) p ih hp j
  have hlin (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Nat) :
      0 ≤ (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff j := by
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X]
    split_ifs <;> positivity
  exact hmul _ _ (hpow _ (hlin _ _ ha (by linarith)) r)
    (hpow _ (hlin _ _ (mul_nonneg (by linarith) hb) he) c) j

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,hb,he,he',hM,B,eps,alpha,b0,M,r,c), Each count kernel is bounded by positive coefficients with only total degrees
above the matching degree retained, including counts exceeding that degree.  This gives [the stated result](goal).-/
-- @node: affine_signed_count_polynomial_bound
lemma affine_signed_count_polynomial_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (alpha b0 M : Real) (r c : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hM : 0 ≤ M) :
    let p : Polynomial Real :=
      (Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r *
      (Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c
    |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) *
      (alpha + (1 - eps) * sigma.nodes i) ^ r *
      ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)| ≤
    ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * B ^ j *
      ∑' k : Nat, (M * B) ^ (k + (if j ≤ L then L - j + 1 else 0)) /
        ((k + (if j ≤ L then L - j + 1 else 0)).factorial : Real) := by
  intro p
  have h := affine_signed_exp_polynomial_bound sigma M hM p
  have hcoeff (j : Nat) : |p.coeff j| = p.coeff j :=
    abs_of_nonneg (affine_arm_power_coeff_nonneg alpha b0 eps r c j ha hb he he')
  simpa only [hcoeff, p, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, mul_assoc] using h

/-- [Under the stated inputs and conditions](hyp:z,hz,L,j), The shifted exponential tail is exactly the series filtered by total degree.
This form retains the cancellation cutoff when polynomial and count sums are exchanged.  This gives [the stated result](goal).-/
-- @node: affine_total_degree_tail_eq
lemma affine_total_degree_tail_eq (z : Real) (hz : 0 ≤ z) (L j : Nat) :
    (∑' k : Nat, z ^ (k + (if j ≤ L then L - j + 1 else 0)) /
      ((k + (if j ≤ L then L - j + 1 else 0)).factorial : Real)) =
    ∑' k : Nat, if L < k + j then z ^ k / (k.factorial : Real) else 0 := by
  by_cases hj : j ≤ L
  · simp only [if_pos hj]
    have hs : Summable (fun k : Nat =>
        if L < k + j then z ^ k / (k.factorial : Real) else 0) := by
      apply (Real.summable_pow_div_factorial z).of_nonneg_of_le
      · intro k; split_ifs <;> positivity
      · intro k; split_ifs <;> first | exact le_rfl | positivity
    have hzero : (∑ k ∈ Finset.range (L - j + 1),
        if L < k + j then z ^ k / (k.factorial : Real) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
    have hshift (k : Nat) : L < k + (L - j + 1) + j := by omega
    simpa only [hzero, zero_add, hshift, if_true] using
      hs.sum_add_tsum_nat_add (L - j + 1)
  · simp only [if_neg hj, Nat.add_zero,
      show ∀ k : Nat, L < k + j by omega, if_true]

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,hb,he,he',hM,B,eps,alpha,b0,M,r,c), The signed count kernel has a nonnegative envelope filtered by total degree,
ready for exchanging the polynomial, exponential, and count sums.  This gives [the stated result](goal).-/
-- @node: affine_signed_count_total_degree_bound
lemma affine_signed_count_total_degree_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (alpha b0 M : Real) (r c : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hM : 0 ≤ M) :
    let p : Polynomial Real :=
      (Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r *
      (Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c
    |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) *
      (alpha + (1 - eps) * sigma.nodes i) ^ r *
      ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)| ≤
    ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * B ^ j *
      ∑' k : Nat, if L < k + j then (M * B) ^ k / (k.factorial : Real) else 0 := by
  intro p
  have hB : 0 ≤ B := (sigma.mem 0).1.trans (sigma.mem 0).2
  have h := affine_signed_count_polynomial_bound sigma alpha b0 M r c ha hb he he' hM
  simpa only [affine_total_degree_tail_eq (M * B) (mul_nonneg hM hB)] using h

/-- [Under the stated inputs and conditions](hyp:z,hz,h), Shifting the labeled count by one decreases every nonnegative factorial term.  This gives [the stated result](goal).-/
-- @node: affine_labeled_factorial_term_le
lemma affine_labeled_factorial_term_le (z : Real) (hz : 0 ≤ z) (h : Nat) :
    z ^ h / ((h + 1).factorial : Real) ≤ z ^ h / (h.factorial : Real) := by
  apply div_le_div_of_nonneg_left (pow_nonneg hz h) (by positivity)
  exact_mod_cast Nat.factorial_le (Nat.le_succ h)

/-- [Under the stated inputs and conditions](hyp:z,hz), The labeled Palm count series is dominated by the ordinary exponential series.  This gives [the stated result](goal).-/
-- @node: affine_labeled_factorial_series_le
lemma affine_labeled_factorial_series_le (z : Real) (hz : 0 ≤ z) :
    (∑' h : Nat, z ^ h / ((h + 1).factorial : Real)) ≤ Real.exp z := by
  have hs := Real.summable_pow_div_factorial z
  have ht : Summable (fun h : Nat => z ^ h / ((h + 1).factorial : Real)) :=
    hs.of_nonneg_of_le (fun h => by positivity)
      (affine_labeled_factorial_term_le z hz)
  calc
    _ ≤ ∑' h : Nat, z ^ h / (h.factorial : Real) :=
      Summable.tsum_le_tsum (affine_labeled_factorial_term_le z hz) ht hs
    _ = Real.exp z := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- [The positive count generating functions cancel the entire common baseline,
so their envelope contains only twice the latent intensity. ](goal)-/
-- @node: affine_count_exp_baseline_cancel
lemma affine_count_exp_baseline_cancel (u w b0 eps v : Real) :
    Real.exp ((u + w) * v - (u + w) * b0) *
      Real.exp (u * (eps * b0 + (1 - eps) * v)) *
      Real.exp (w * (eps * b0 + (1 - eps) * v)) *
      Real.exp ((u + w) * ((1 - eps) * b0 + eps * v)) =
    Real.exp (2 * (u + w) * v) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- [The binomial coefficient of an affine arm power, including zero slopes. ](goal)-/
-- @node: affine_linear_pow_coeff
lemma affine_linear_pow_coeff (a b : Real) (r j : Nat) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff j =
      b ^ j * a ^ (r - j) * (r.choose j : Real) := by
  rw [add_comm (Polynomial.C a), add_pow, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, mul_pow, ← Polynomial.C_pow,
    ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single j, Polynomial.coeff_X_pow_self]
  · ring
  · intro k hk hkj
    simp [Polynomial.coeff_X_pow, hkj.symm]
  · intro hj
    have hrj : r < j := by simp only [Finset.mem_range] at hj; omega
    simp [Nat.choose_eq_zero_of_lt hrj]

/-- [After shifting by the coefficient degree, a count term separates into a
fixed slope coefficient and an ordinary exponential term. ](goal)-/
-- @node: affine_linear_coeff_factorial_shift
lemma affine_linear_coeff_factorial_shift (a b t : Real) (k j : Nat) :
    t ^ (k + j) / ((k + j).factorial : Real) *
      ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ (k + j)).coeff j =
    ((t * b) ^ j / (j.factorial : Real)) *
      ((t * a) ^ k / (k.factorial : Real)) := by
  rw [affine_linear_pow_coeff, Nat.add_sub_cancel, pow_add, mul_pow, mul_pow]
  have hfact : ((k + j).choose j : Real) * (j.factorial : Real) *
      (k.factorial : Real) = ((k + j).factorial : Real) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (show ((k + j).choose j : Real) * (k.factorial : Real) *
        (j.factorial : Real) = ((k + j).factorial : Real) by
        exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k j)
  have hk : (k.factorial : Real) ≠ 0 := by positivity
  have hj : (j.factorial : Real) ≠ 0 := by positivity
  have hkj : ((k + j).factorial : Real) ≠ 0 := by positivity
  field_simp
  calc
    _ = (t ^ k * t ^ j * b ^ j * a ^ k) *
        (((k + j).choose j : Real) * (j.factorial : Real) * (k.factorial : Real)) := by ring
    _ = _ := by rw [hfact]; ring

/-- Under the stated inputs and conditions, Each fixed affine Taylor coefficient is absolutely summable over the Poisson count.  This gives [the stated result](goal). -/
-- @node: affine_linear_coeff_series_summable
lemma affine_linear_coeff_series_summable (a b t : Real) (j : Nat) :
    Summable (fun r : Nat => t ^ r / (r.factorial : Real) *
      ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff j) := by
  apply Summable.comp_nat_add (k := j)
  simp_rw [affine_linear_coeff_factorial_shift]
  exact (Real.summable_pow_div_factorial (t * a)).mul_left _

/-- [Under the stated inputs and conditions](hyp:j,a,b,t), Summing a fixed Taylor coefficient over all counts reads back the affine
exponential exactly; the common constant is retained rather than bounded.  This gives [the stated result](goal).-/
-- @node: affine_linear_coeff_series_eq
lemma affine_linear_coeff_series_eq (a b t : Real) (j : Nat) :
    (∑' r : Nat, t ^ r / (r.factorial : Real) *
      ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff j) =
    Real.exp (t * a) * (t * b) ^ j / (j.factorial : Real) := by
  have hs := affine_linear_coeff_series_summable a b t j
  have hzero : (∑ r ∈ Finset.range j, t ^ r / (r.factorial : Real) *
      ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff j) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [affine_linear_pow_coeff, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hr)]
    simp
  rw [← hs.sum_add_tsum_nat_add j, hzero, zero_add]
  simp_rw [affine_linear_coeff_factorial_shift]
  have he : (∑' k : Nat, (t * a) ^ k / (k.factorial : Real)) = Real.exp (t * a) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [tsum_mul_left, he]
  ring

/-- [Under the stated inputs and conditions](hyp:j,x,y), The finite convolution of two exponential Taylor coefficients is the
coefficient for the sum of their slopes.  This gives [the stated result](goal).-/
-- @node: affine_exponential_coeff_convolution
lemma affine_exponential_coeff_convolution (x y : Real) (j : Nat) :
    (∑ k ∈ Finset.antidiagonal j,
      x ^ k.1 / (k.1.factorial : Real) * y ^ k.2 / (k.2.factorial : Real)) =
      (x + y) ^ j / (j.factorial : Real) := by
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k.1 + k.2 = j := Finset.mem_antidiagonal.mp hk
  have hfact : (j.choose k.1 : Real) * (k.1.factorial : Real) *
      (k.2.factorial : Real) = (j.factorial : Real) := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show k.1 ≤ j by omega)
    have hsub : j - k.1 = k.2 := by omega
    rw [hsub] at h
    exact_mod_cast h
  simp only [nsmul_eq_mul]
  field_simp
  calc
    _ = (x ^ k.1 * y ^ k.2) * (j.factorial : Real) := by ring
    _ = _ := by rw [← hfact]; ring

/-- [Under the stated inputs and conditions](hyp:j,a,b,c,d,t,s), The two independent arm-count sums exchange with the finite coefficient
convolution and retain their common constant exactly.  This gives [the stated result](goal).-/
-- @node: affine_two_arm_coeff_series_eq
lemma affine_two_arm_coeff_series_eq (a b c d t s : Real) (j : Nat) :
    (∑' r : Nat, ∑' q : Nat, t ^ r / (r.factorial : Real) *
      (s ^ q / (q.factorial : Real)) *
      (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r) *
        ((Polynomial.C c + Polynomial.C d * Polynomial.X) ^ q)).coeff j) =
    Real.exp (t * a + s * c) * (t * b + s * d) ^ j / (j.factorial : Real) := by
  have hinner (r : Nat) :
      (∑' q : Nat, t ^ r / (r.factorial : Real) * (s ^ q / (q.factorial : Real)) *
        (((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r) *
          ((Polynomial.C c + Polynomial.C d * Polynomial.X) ^ q)).coeff j) =
      ∑ k ∈ Finset.antidiagonal j,
        (t ^ r / (r.factorial : Real) *
          ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff k.1) *
        (Real.exp (s * c) * (s * d) ^ k.2 / (k.2.factorial : Real)) := by
    calc
      _ = ∑' q : Nat, ∑ k ∈ Finset.antidiagonal j,
          (t ^ r / (r.factorial : Real) *
            ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff k.1) *
          (s ^ q / (q.factorial : Real) *
            ((Polynomial.C c + Polynomial.C d * Polynomial.X) ^ q).coeff k.2) := by
        apply tsum_congr
        intro q
        rw [Polynomial.coeff_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        have hsum (k : Nat × Nat) (_ : k ∈ Finset.antidiagonal j) :
            Summable (fun q : Nat =>
              (t ^ r / (r.factorial : Real) *
                ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff k.1) *
              (s ^ q / (q.factorial : Real) *
                ((Polynomial.C c + Polynomial.C d * Polynomial.X) ^ q).coeff k.2)) :=
          (affine_linear_coeff_series_summable c d s k.2).mul_left _
        rw [Summable.tsum_finsetSum hsum]
        simp_rw [tsum_mul_left, affine_linear_coeff_series_eq]
  simp_rw [hinner]
  have hsum (k : Nat × Nat) (_ : k ∈ Finset.antidiagonal j) :
      Summable (fun r : Nat =>
        (t ^ r / (r.factorial : Real) *
          ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ r).coeff k.1) *
        (Real.exp (s * c) * (s * d) ^ k.2 / (k.2.factorial : Real))) :=
    (affine_linear_coeff_series_summable a b t k.1).mul_right _
  rw [Summable.tsum_finsetSum hsum]
  simp_rw [tsum_mul_right, affine_linear_coeff_series_eq]
  calc
    _ = Real.exp (t * a + s * c) *
        ∑ k ∈ Finset.antidiagonal j,
          (t * b) ^ k.1 / (k.1.factorial : Real) *
            (s * d) ^ k.2 / (k.2.factorial : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.exp_add]
      ring
    _ = _ := by rw [affine_exponential_coeff_convolution]; ring

/-- [Under the stated inputs and conditions](hyp:ha,hb,he,he',hu,alpha,b0,eps,u,r,c,j), The Palm shift in the labeled count decreases each coefficient of the
nonnegative two-arm polynomial envelope.  This gives [the stated result](goal).-/
-- @node: affine_labeled_count_coeff_le
lemma affine_labeled_count_coeff_le (alpha b0 eps u : Real) (r c j : Nat)
    (ha : 0 ≤ alpha) (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) :
    u ^ r / ((r + 1).factorial : Real) *
      (((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j ≤
    u ^ r / (r.factorial : Real) *
      (((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j := by
  exact mul_le_mul_of_nonneg_right (affine_labeled_factorial_term_le u hu r)
    (affine_arm_power_coeff_nonneg alpha b0 eps r c j ha hb he he')

/-- [Under the stated inputs and conditions](hyp:j,b0,eps,M), Summing the combined treated and control counts cancels the common baseline
at every coefficient, without any bound on its size.  This gives [the stated result](goal).-/
-- @node: affine_arm_count_coeff_baseline_cancel
lemma affine_arm_count_coeff_baseline_cancel (b0 eps M : Real) (j : Nat) :
    Real.exp (-M * b0) *
      (∑' r : Nat, ∑' c : Nat, M ^ r / (r.factorial : Real) *
        (M ^ c / (c.factorial : Real)) *
        (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
          ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff j) =
    M ^ j / (j.factorial : Real) := by
  rw [affine_two_arm_coeff_series_eq]
  have hbase : M * (eps * b0) + M * ((1 - eps) * b0) = M * b0 := by ring
  have hslope : M * (1 - eps) + M * eps = M := by ring
  rw [hbase, hslope]
  rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add]
  simp

/-- [Under the stated inputs and conditions](hyp:h,b0,eps,M), Convolving the coefficientwise count sum with the positive Taylor series
of exp(Mv) leaves exactly the coefficients of exp(2Mv).  This gives [the stated result](goal).-/
-- @node: affine_full_count_envelope_coeff_eq
lemma affine_full_count_envelope_coeff_eq (b0 eps M : Real) (h : Nat) :
    (∑ k ∈ Finset.antidiagonal h, M ^ k.1 / (k.1.factorial : Real) *
      (Real.exp (-M * b0) *
        (∑' r : Nat, ∑' c : Nat, M ^ r / (r.factorial : Real) *
          (M ^ c / (c.factorial : Real)) *
          (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
            ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff k.2))) =
    (2 * M) ^ h / (h.factorial : Real) := by
  simp_rw [affine_arm_count_coeff_baseline_cancel]
  have hc := affine_exponential_coeff_convolution M M h
  simpa only [mul_div_assoc, show M + M = 2 * M by ring] using hc

/-- [Under the stated inputs and conditions](hyp:p,u,w,R,j), Grouping the labeled and auxiliary treated counts by their sum gives the
ordinary combined-intensity coefficient; the polynomial power is unchanged.  This gives [the stated result](goal).-/
-- @node: affine_treated_count_antidiagonal
lemma affine_treated_count_antidiagonal (u w : Real) (p : Polynomial Real) (R j : Nat) :
    (∑ k ∈ Finset.antidiagonal R, u ^ k.1 / (k.1.factorial : Real) *
      w ^ k.2 / (k.2.factorial : Real) * (p ^ (k.1 + k.2)).coeff j) =
    (u + w) ^ R / (R.factorial : Real) * (p ^ R).coeff j := by
  calc
    _ = (∑ k ∈ Finset.antidiagonal R,
        u ^ k.1 / (k.1.factorial : Real) * w ^ k.2 / (k.2.factorial : Real)) *
        (p ^ R).coeff j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_antidiagonal.mp hk]
    _ = _ := by rw [affine_exponential_coeff_convolution]

/-- [Under the stated inputs and conditions](hyp:L,b0,eps,M,B), At the support endpoint, the full coefficientwise count envelope has exactly
the Taylor tail used in equation (7). No common baseline enters the bound.  This gives [the stated result](goal).-/
-- @node: affine_full_count_endpoint_tail_eq
lemma affine_full_count_endpoint_tail_eq (b0 eps M B : Real) (L : Nat) :
    (∑' h : Nat, if L < h then B ^ h *
      (∑ k ∈ Finset.antidiagonal h, M ^ k.1 / (k.1.factorial : Real) *
        (Real.exp (-M * b0) *
          (∑' r : Nat, ∑' c : Nat, M ^ r / (r.factorial : Real) *
            (M ^ c / (c.factorial : Real)) *
            (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ r) *
              ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c)).coeff k.2)))
      else 0) =
    ∑' h : Nat, if L < h then (2 * M * B) ^ h / (h.factorial : Real) else 0 := by
  apply tsum_congr
  intro h
  rw [affine_full_count_envelope_coeff_eq]
  split_ifs
  · rw [mul_pow]
    ring
  · rfl

end CausalSmith.Stat.AnnotationRarearmFrontier
