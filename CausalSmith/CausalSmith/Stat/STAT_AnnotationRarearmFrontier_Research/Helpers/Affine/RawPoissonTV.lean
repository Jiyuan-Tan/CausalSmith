module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Separation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.TVBound
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
Moment cancellation and exact Taylor-remainder readback for the affine one-cell
marked-Poisson kernel, together with its calibrated exponential tail bound.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:L,hL), [The Taylor remainder at 2MB=L/500 is geometrically small in the degree](goal).
-/
-- @node: affine_poisson_taylor_tail
lemma affine_poisson_taylor_tail (L : Nat) (hL : 2 ≤ L) :
    (∑' h : Nat, if L < h then ((L : Real) / 500) ^ h / (h.factorial : Real) else 0) ≤
      2 * Real.exp (-5 * (L : Real)) := by
  have he6 : Real.exp (6 : Real) ≤ 500 := by
    have he : Real.exp 1 ≤ (11 / 4 : Real) := by linarith [Real.exp_one_lt_d9]
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 6
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hq : Real.exp 1 / 500 ≤ Real.exp (-5) := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 500)).2
    have h := mul_le_mul_of_nonneg_left he6 (Real.exp_pos (-5)).le
    rw [← Real.exp_add] at h
    norm_num at h
    simpa [mul_comm] using h
  have hterm (h : Nat) (hh : L < h) :
      ((L : Real) / 500) ^ h / (h.factorial : Real) ≤ Real.exp (-5) ^ h := by
    have hLh : (L : Real) ≤ h := by exact_mod_cast hh.le
    have hbound := Real.pow_div_factorial_le_exp (h : Real) (Nat.cast_nonneg h) h
    calc
      ((L : Real) / 500) ^ h / (h.factorial : Real) ≤
          ((h : Real) / 500) ^ h / (h.factorial : Real) := by gcongr
      _ = (1 / 500 : Real) ^ h * ((h : Real) ^ h / (h.factorial : Real)) := by
        simp only [div_pow]; norm_num; ring
      _ ≤ (1 / 500 : Real) ^ h * Real.exp (h : Real) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (Real.exp 1 / 500) ^ h := by
        rw [show (h : Real) = (h : Real) * 1 by ring, Real.exp_nat_mul]
        simp only [div_pow, one_pow]; ring
      _ ≤ Real.exp (-5) ^ h := pow_le_pow_left₀ (by positivity) hq h
  have hqhalf : Real.exp (-5) ≤ (1 / 2 : Real) := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos 5)).2
    have h := Real.exp_le_exp.mpr (show (1 : Real) ≤ 5 by norm_num)
    linarith [Real.exp_one_gt_two]
  have hqs : Summable (fun h : Nat => Real.exp (-5) ^ h) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; linarith)
  have hgs : Summable (fun h : Nat => if L < h then Real.exp (-5) ^ h else 0) := by
    apply hqs.of_nonneg_of_le
    · intro h; positivity
    · intro h; split_ifs
      · rfl
      · positivity
  have hfs : Summable (fun h : Nat =>
      if L < h then ((L : Real) / 500) ^ h / (h.factorial : Real) else 0) := by
    apply hgs.of_nonneg_of_le
    · intro h; positivity
    · intro h; split_ifs with hh
      · exact hterm h hh
      · rfl
  have hzero : (∑ h ∈ Finset.range (L + 1),
      if L < h then Real.exp (-5) ^ h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    rw [if_neg (by have := Finset.mem_range.mp hh; omega)]
  calc
    _ ≤ ∑' h : Nat, if L < h then Real.exp (-5) ^ h else 0 := by
      apply Summable.tsum_le_tsum _ hfs hgs
      intro h; split_ifs with hh
      · exact hterm h hh
      · rfl
    _ = Real.exp (-5) ^ (L + 1) * (1 - Real.exp (-5))⁻¹ := by
      rw [← hgs.sum_add_tsum_nat_add (L + 1), hzero, zero_add]
      simp only [show ∀ h : Nat, L < h + (L + 1) by omega, if_true, pow_add]
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; linarith)]
      ring
    _ ≤ 2 * Real.exp (-5) ^ L := by
      have hi : (1 - Real.exp (-5))⁻¹ ≤ (2 : Real) := by
        rw [← one_div]
        apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-5))).2
        linarith
      rw [pow_succ]
      have hp : 0 ≤ Real.exp (-5) ^ L := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hi
        (show 0 ≤ Real.exp (-5) ^ L * Real.exp (-5) by positivity)]
    _ = 2 * Real.exp (-5 * (L : Real)) := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,p,hp,B,eps), Every polynomial through the matching degree cancels against the cone dual.  This gives [the stated result](goal).-/
-- @node: ConeDual.sum_polynomial_eq_zero
lemma ConeDual.sum_polynomial_eq_zero {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (p : Polynomial Real) (hp : p.natDegree ≤ L) :
    (∑ i, sigma.weights i * p.eval (sigma.nodes i)) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hkL : k ≤ L := by have := Finset.mem_range.mp hk; omega
  calc
    (∑ i, sigma.weights i * (p.coeff k * sigma.nodes i ^ k)) =
        p.coeff k * ∑ i, sigma.weights i * sigma.nodes i ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [sigma.moments k hkL, mul_zero]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hdegree,B,eps,alpha,b0,k,r,c), The low-degree terms of the exponential times the two affine arm powers cancel.  This gives [the stated result](goal).-/
-- @node: affine_signed_mixed_moment_zero
lemma affine_signed_mixed_moment_zero {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (alpha b0 : Real) (k r c : Nat)
    (hdegree : k + r + c ≤ L) :
    (∑ i, sigma.weights i * (sigma.nodes i ^ k *
      (alpha + (1 - eps) * sigma.nodes i) ^ r *
      ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)) = 0 := by
  let p : Polynomial Real := Polynomial.X ^ k *
    (Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r *
    (Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c
  have hlin (a b : Real) :
      (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  have hp : p.natDegree ≤ L := by
    apply le_trans (Polynomial.natDegree_mul_le)
    apply le_trans (Nat.add_le_add (Polynomial.natDegree_mul_le) le_rfl)
    have hk : (Polynomial.X ^ k : Polynomial Real).natDegree ≤ k := by
      simp
    have hr : ((Polynomial.C alpha + Polynomial.C (1 - eps) * Polynomial.X) ^ r).natDegree ≤ r :=
      Polynomial.natDegree_pow_le.trans (by
        simpa using Nat.mul_le_mul_left r (hlin alpha (1 - eps)))
    have hc :
        ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ c).natDegree ≤ c :=
      Polynomial.natDegree_pow_le.trans (by
        simpa using Nat.mul_le_mul_left c (hlin ((1 - eps) * b0) eps))
    exact (Nat.add_le_add (Nat.add_le_add hk hr) hc).trans hdegree
  simpa [p] using sigma.sum_polynomial_eq_zero p hp

/-- [Under the stated inputs and conditions](hyp:L,sigma,f,p,hp,R,hR,B,eps), Subtracting any canceled polynomial bounds the signed sum by its uniform remainder,
using the dual's variation mass one.  This gives [the stated result](goal).-/
-- @node: affine_signed_polynomial_remainder_bound
lemma affine_signed_polynomial_remainder_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (f : Real → Real) (p : Polynomial Real)
    (hp : p.natDegree ≤ L) (R : Real)
    (hR : ∀ i, |f (sigma.nodes i) - p.eval (sigma.nodes i)| ≤ R) :
    |∑ i, sigma.weights i * f (sigma.nodes i)| ≤ R := by
  have hcancel := sigma.sum_polynomial_eq_zero p hp
  calc
    |∑ i, sigma.weights i * f (sigma.nodes i)| =
        |∑ i, sigma.weights i * (f (sigma.nodes i) - p.eval (sigma.nodes i))| := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hcancel, sub_zero]
    _ ≤ ∑ i, |sigma.weights i * (f (sigma.nodes i) - p.eval (sigma.nodes i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |sigma.weights i| * R := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hR i) (abs_nonneg _)
    _ = R := by rw [← Finset.sum_mul, sigma.abs_sum, one_mul]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hdegree,B,eps,alpha,b0,M,r,c), Every retained Taylor term of the one-cell kernel has zero signed integral.  This gives [the stated result](goal).-/
-- @node: affine_signed_exp_truncation_zero
lemma affine_signed_exp_truncation_zero {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (alpha b0 M : Real) (r c : Nat)
    (hdegree : r + c ≤ L) :
    (∑ i, sigma.weights i *
      ((∑ k ∈ Finset.range (L - (r + c) + 1),
        (-M) ^ k / (k.factorial : Real) * sigma.nodes i ^ k) *
      (alpha + (1 - eps) * sigma.nodes i) ^ r *
      ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)) = 0 := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hkL : k + r + c ≤ L := by
    have := Finset.mem_range.mp hk
    omega
  calc
    (∑ i, sigma.weights i *
      ((-M) ^ k / (k.factorial : Real) * sigma.nodes i ^ k *
        (alpha + (1 - eps) * sigma.nodes i) ^ r *
        ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)) =
      ((-M) ^ k / (k.factorial : Real)) *
        ∑ i, sigma.weights i * (sigma.nodes i ^ k *
          (alpha + (1 - eps) * sigma.nodes i) ^ r *
          ((1 - eps) * b0 + eps * sigma.nodes i) ^ c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [affine_signed_mixed_moment_zero sigma alpha b0 k r c hkL, mul_zero]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hdegree,B,eps,alpha,b0,M,r,c), The signed one-cell exponential kernel equals its surviving Taylor remainder exactly.
This removes all terms of total degree at most L before bounding absolute coefficients.  This gives [the stated result](goal).-/
-- @node: affine_signed_exp_remainder_identity
lemma affine_signed_exp_remainder_identity {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (alpha b0 M : Real) (r c : Nat)
    (hdegree : r + c ≤ L) :
    (∑ i, sigma.weights i *
      (Real.exp (-M * sigma.nodes i) *
        (alpha + (1 - eps) * sigma.nodes i) ^ r *
        ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)) =
    ∑ i, sigma.weights i *
      ((Real.exp (-M * sigma.nodes i) -
        ∑ k ∈ Finset.range (L - (r + c) + 1),
          (-M) ^ k / (k.factorial : Real) * sigma.nodes i ^ k) *
        (alpha + (1 - eps) * sigma.nodes i) ^ r *
        ((1 - eps) * b0 + eps * sigma.nodes i) ^ c) := by
  have hc := affine_signed_exp_truncation_zero sigma alpha b0 M r c hdegree
  simp_rw [sub_mul, mul_sub] at hc ⊢
  rw [Finset.sum_sub_distrib, hc, sub_zero]

/-- [Under the stated inputs and conditions](hyp:s,hM,hv,hvB,M,B,v), The absolute exponential remainder on the cone is bounded by its positive
Taylor tail at the support endpoint; no bound on the common baseline is used.  This gives [the stated result](goal).-/
-- @node: affine_exp_remainder_abs_le
lemma affine_exp_remainder_abs_le (M B v : Real) (s : Nat)
    (hM : 0 ≤ M) (hv : 0 ≤ v) (hvB : v ≤ B) :
    |Real.exp (-M * v) - ∑ k ∈ Finset.range s,
      (-M) ^ k / (k.factorial : Real) * v ^ k| ≤
    ∑' k : Nat, (M * B) ^ (k + s) / ((k + s).factorial : Real) := by
  have hB : 0 ≤ B := hv.trans hvB
  have heq : Real.exp (-M * v) = ∑' k : Nat,
      (-M * v) ^ k / (k.factorial : Real) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsplit := (Real.summable_pow_div_factorial (-M * v)).sum_add_tsum_nat_add s
  have hfin : (∑ k ∈ Finset.range s, (-M * v) ^ k / (k.factorial : Real)) =
      ∑ k ∈ Finset.range s, (-M) ^ k / (k.factorial : Real) * v ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  rw [← heq, hfin] at hsplit
  rw [show Real.exp (-M * v) - ∑ k ∈ Finset.range s,
      (-M) ^ k / (k.factorial : Real) * v ^ k =
      ∑' k : Nat, (-M * v) ^ (k + s) / ((k + s).factorial : Real) by linarith [hsplit]]
  have hnorm (k : Nat) :
      ‖(-M * v) ^ (k + s) / ((k + s).factorial : Real)‖ =
      (M * v) ^ (k + s) / ((k + s).factorial : Real) := by
    simp [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, abs_of_nonneg hM,
      abs_of_nonneg hv]
  have hsum := (Real.summable_pow_div_factorial (M * v)).comp_injective
    (show Function.Injective (fun k : Nat => k + s) from fun _ _ h => Nat.add_right_cancel h)
  have hsumB := (Real.summable_pow_div_factorial (M * B)).comp_injective
    (show Function.Injective (fun k : Nat => k + s) from fun _ _ h => Nat.add_right_cancel h)
  change Summable (fun k : Nat => (M * v) ^ (k + s) / ((k + s).factorial : Real)) at hsum
  change Summable (fun k : Nat => (M * B) ^ (k + s) / ((k + s).factorial : Real)) at hsumB
  have hsumNorm : Summable (fun k : Nat =>
      ‖(-M * v) ^ (k + s) / ((k + s).factorial : Real)‖) := by
    simpa only [hnorm] using hsum
  calc
    _ ≤ ∑' k : Nat, ‖(-M * v) ^ (k + s) / ((k + s).factorial : Real)‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsumNorm
    _ = ∑' k : Nat, (M * v) ^ (k + s) / ((k + s).factorial : Real) := tsum_congr hnorm
    _ ≤ _ := by
      apply Summable.tsum_le_tsum _ hsum hsumB
      intro k
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hM hv) (mul_le_mul_of_nonneg_left hvB hM) _)
        (Nat.cast_nonneg _)

/-- [Under the stated inputs and conditions](hyp:L,sigma,M,j,hj,B,eps), Matching moments cancel the monomial times every retained exponential term.  This gives [the stated result](goal).-/
-- @node: affine_signed_monomial_exp_truncation_zero
lemma affine_signed_monomial_exp_truncation_zero {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (M : Real) (j : Nat) (hj : j ≤ L) :
    (∑ i, sigma.weights i *
      ((∑ k ∈ Finset.range (L - j + 1),
        (-M) ^ k / (k.factorial : Real) * sigma.nodes i ^ k) * sigma.nodes i ^ j)) = 0 := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hkj : k + j ≤ L := by have := Finset.mem_range.mp hk; omega
  calc
    _ = ((-M) ^ k / (k.factorial : Real)) *
        ∑ i, sigma.weights i * sigma.nodes i ^ (k + j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = 0 := by rw [sigma.moments (k + j) hkj, mul_zero]

/-- [Under the stated inputs and conditions](hyp:L,sigma,M,hM,j,hj,B,eps), A signed exponential monomial retains only terms above the matching total degree.
The variation mass one bounds the remainder by its positive endpoint tail.  This gives [the stated result](goal).-/
-- @node: affine_signed_exp_monomial_bound
lemma affine_signed_exp_monomial_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (M : Real) (hM : 0 ≤ M)
    (j : Nat) (hj : j ≤ L) :
    |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) * sigma.nodes i ^ j)| ≤
      B ^ j * ∑' k : Nat,
        (M * B) ^ (k + (L - j + 1)) / ((k + (L - j + 1)).factorial : Real) := by
  let R := ∑' k : Nat,
    (M * B) ^ (k + (L - j + 1)) / ((k + (L - j + 1)).factorial : Real)
  have hB : 0 ≤ B := (sigma.mem 0).1.trans (sigma.mem 0).2
  have hR : 0 ≤ R := tsum_nonneg (fun k => by positivity)
  have hc := affine_signed_monomial_exp_truncation_zero sigma M j hj
  have heq : (∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) * sigma.nodes i ^ j)) =
      ∑ i, sigma.weights i *
        ((Real.exp (-M * sigma.nodes i) - ∑ k ∈ Finset.range (L - j + 1),
          (-M) ^ k / (k.factorial : Real) * sigma.nodes i ^ k) * sigma.nodes i ^ j) := by
    simp_rw [sub_mul, mul_sub]
    rw [Finset.sum_sub_distrib, hc, sub_zero]
  rw [heq]
  calc
    _ ≤ ∑ i, |sigma.weights i *
        ((Real.exp (-M * sigma.nodes i) - ∑ k ∈ Finset.range (L - j + 1),
          (-M) ^ k / (k.factorial : Real) * sigma.nodes i ^ k) * sigma.nodes i ^ j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |sigma.weights i| * (R * B ^ j) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (sigma.mem i).1]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact mul_le_mul
        (affine_exp_remainder_abs_le M B (sigma.nodes i) (L - j + 1)
          hM (sigma.mem i).1 (sigma.mem i).2)
        (pow_le_pow_left₀ (sigma.mem i).1 (sigma.mem i).2 j)
        (pow_nonneg (sigma.mem i).1 j) hR
    _ = _ := by rw [← Finset.sum_mul, sigma.abs_sum, one_mul]; ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,M,hM,j,B,eps), Without a matching-degree restriction, the full positive Taylor series
still bounds the signed exponential monomial.  This gives [the stated result](goal).-/
-- @node: affine_signed_exp_monomial_full_bound
lemma affine_signed_exp_monomial_full_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (M : Real) (hM : 0 ≤ M) (j : Nat) :
    |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) * sigma.nodes i ^ j)| ≤
      B ^ j * ∑' k : Nat, (M * B) ^ k / (k.factorial : Real) := by
  let R := ∑' k : Nat, (M * B) ^ k / (k.factorial : Real)
  have hB : 0 ≤ B := (sigma.mem 0).1.trans (sigma.mem 0).2
  have hR : 0 ≤ R := tsum_nonneg (fun k => by positivity)
  calc
    _ ≤ ∑ i, |sigma.weights i *
        (Real.exp (-M * sigma.nodes i) * sigma.nodes i ^ j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |sigma.weights i| * (R * B ^ j) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (sigma.mem i).1]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul _ (pow_le_pow_left₀ (sigma.mem i).1 (sigma.mem i).2 j)
        (pow_nonneg (sigma.mem i).1 j) hR
      simpa [R] using affine_exp_remainder_abs_le M B (sigma.nodes i) 0
        hM (sigma.mem i).1 (sigma.mem i).2
    _ = _ := by rw [← Finset.sum_mul, sigma.abs_sum, one_mul]; ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,M,hM,p,B,eps), Polynomial coefficients give a total-degree Taylor envelope for the signed kernel.
This preserves each monomial's cancellation degree before the count sums are exchanged.  This gives [the stated result](goal).-/
-- @node: affine_signed_exp_polynomial_bound
lemma affine_signed_exp_polynomial_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (M : Real) (hM : 0 ≤ M)
    (p : Polynomial Real) :
    |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) * p.eval (sigma.nodes i))| ≤
      ∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j| * B ^ j *
        ∑' k : Nat, (M * B) ^ (k + (if j ≤ L then L - j + 1 else 0)) /
          ((k + (if j ≤ L then L - j + 1 else 0)).factorial : Real) := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = |∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j *
        ∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) * sigma.nodes i ^ j)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j *
        ∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) * sigma.nodes i ^ j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      by_cases hjL : j ≤ L
      · simpa only [if_pos hjL] using affine_signed_exp_monomial_bound sigma M hM j hjL
      · simpa only [if_neg hjL, Nat.add_zero] using affine_signed_exp_monomial_full_bound sigma M hM j

end CausalSmith.Stat.AnnotationRarearmFrontier
