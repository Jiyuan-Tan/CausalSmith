module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.CountTail

/-!
Absolute convergence and count-summed Taylor bounds for the signed rare-cell
kernel. These justify exchanging the count indices with the polynomial envelope.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open scoped BigOperators

/-- [Under the stated hypotheses](hyp:hM,hB), The coefficient majorant remains summable after attaching the matching-degree tail.  This gives [the stated result](goal). -/
-- @node: affine_coefficient_tail_majorant_summable
lemma affine_coefficient_tail_majorant_summable (M B : Real) (L : Nat)
    (hM : 0 ≤ M) (hB : 0 ≤ B) :
    Summable (fun j : Nat => M ^ j / (j.factorial : Real) * B ^ j *
      ∑' k : Nat, if L < k + j then (M * B) ^ k / (k.factorial : Real) else 0) := by
  have hs := (affine_filtered_exponential_product_summable (M * B)
    (mul_nonneg hM hB) L).prod
  apply hs.congr
  intro j
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [Nat.add_comm j k]
  split_ifs <;> simp [mul_pow, mul_div_assoc, mul_assoc] <;> ring

set_option maxHeartbeats 800000 in
-- The count/coefficient exchanges elaborate nested series and finite polynomial convolutions.
/-- [Under the stated inputs and conditions](hyp:I,L,sigma,M,hM,p,a,ha,hp,hc,hle,B,eps), A family of nonnegative polynomial coefficients with summable columns and
an exponential column bound has an absolutely summable signed-kernel envelope.
Moment cancellation is applied to each polynomial before the count exchange.  This gives [the stated result](goal).-/
-- @node: affine_signed_polynomial_family_tail_bound
lemma affine_signed_polynomial_family_tail_bound {I : Type*} {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (M : Real) (hM : 0 ≤ M)
    (p : I → Polynomial Real) (a : I → Real) (ha : ∀ i, 0 ≤ a i)
    (hp : ∀ i j, 0 ≤ (p i).coeff j)
    (hc : ∀ j, Summable (fun i => a i * (p i).coeff j))
    (hle : ∀ j, (∑' i, a i * (p i).coeff j) ≤ M ^ j / (j.factorial : Real)) :
    Summable (fun i => a i *
      |∑ t, sigma.weights t * (Real.exp (-M * sigma.nodes t) * (p i).eval (sigma.nodes t))|) ∧
    (∑' i, a i *
      |∑ t, sigma.weights t * (Real.exp (-M * sigma.nodes t) * (p i).eval (sigma.nodes t))|) ≤
      ∑' h : Nat, if L < h then (2 * M * B) ^ h / (h.factorial : Real) else 0 := by
  have hB : 0 ≤ B := (sigma.mem 0).1.trans (sigma.mem 0).2
  let T : Nat → Real := fun j => B ^ j *
    ∑' k : Nat, if L < k + j then (M * B) ^ k / (k.factorial : Real) else 0
  have hT (j : Nat) : 0 ≤ T j := by
    dsimp [T]; apply mul_nonneg (by positivity)
    exact tsum_nonneg fun k => by split_ifs <;> positivity
  let F : Nat × I → Real := fun v => (a v.2 * (p v.2).coeff v.1) * T v.1
  have hn (v : Nat × I) : 0 ≤ F v :=
    mul_nonneg (mul_nonneg (ha _) (hp _ _)) (hT _)
  have hcols (j : Nat) : Summable (fun i => F (j, i)) := (hc j).mul_right (T j)
  have hsum : Summable (fun j => ∑' i, F (j, i)) := by
    apply (affine_coefficient_tail_majorant_summable M B L hM hB).of_nonneg_of_le
    · intro j; exact tsum_nonneg fun i => hn (j, i)
    · intro j
      change (∑' i, (a i * (p i).coeff j) * T j) ≤ _
      rw [tsum_mul_right]
      simpa only [T, mul_assoc] using mul_le_mul_of_nonneg_right (hle j) (hT j)
  have hF : Summable F := (summable_prod_of_nonneg hn).2 ⟨hcols, hsum⟩
  let G : I → Real := fun i => a i *
    |∑ t, sigma.weights t * (Real.exp (-M * sigma.nodes t) * (p i).eval (sigma.nodes t))|
  have hG (i : I) : 0 ≤ G i := mul_nonneg (ha i) (abs_nonneg _)
  have hGF (i : I) : G i ≤ ∑' j, F (j, i) := by
    have h := affine_signed_exp_polynomial_bound sigma M hM (p i)
    simp_rw [abs_of_nonneg (hp i _),
      affine_total_degree_tail_eq (M * B) (mul_nonneg hM hB)] at h
    calc
      G i ≤ a i * ∑ j ∈ Finset.range ((p i).natDegree + 1), (p i).coeff j * T j :=
        mul_le_mul_of_nonneg_left (by simpa only [T, mul_assoc] using h) (ha i)
      _ = ∑ j ∈ Finset.range ((p i).natDegree + 1), F (j, i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; dsimp [F]; ring
      _ ≤ ∑' j, F (j, i) := (hF.prod_symm.prod_factor i).sum_le_tsum _
        (fun j _ => hn (j, i))
  have hGs : Summable G := hF.prod_symm.prod.of_nonneg_of_le hG hGF
  refine ⟨hGs, ?_⟩
  calc
    (∑' i, G i) ≤ ∑' i, ∑' j, F (j, i) :=
      hGs.tsum_le_tsum hGF hF.prod_symm.prod
    _ = ∑' j, ∑' i, F (j, i) := Summable.tsum_comm (f := fun j i => F (j, i)) hF
    _ = ∑' j, (∑' i, a i * (p i).coeff j) * B ^ j *
        ∑' k : Nat, if L < k + j then (M * B) ^ k / (k.factorial : Real) else 0 := by
      simp only [F, tsum_mul_right]
      apply tsum_congr
      intro j
      dsimp [T]
      ring
    _ ≤ _ := affine_dominated_coeff_total_degree_tail_le _ M B L hM hB
      (fun j => tsum_nonneg fun i => mul_nonneg (ha i) (hp i j)) hle

set_option maxHeartbeats 800000 in
-- The count/coefficient exchanges elaborate nested series and finite polynomial convolutions.
/-- [Under the stated hypotheses](hyp:hb,he,he',hu,hw,hM), The three original count indices are jointly absolutely summable at every
fixed Taylor coefficient, including the Palm factorial shift.  This gives [the stated result](goal). -/
-- @node: affine_three_count_coeff_series_summable
lemma affine_three_count_coeff_series_summable (b0 eps u w M : Real) (j : Nat)
    (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hM : M = u + w) :
    Summable (fun v : Nat × (Nat × Nat) => M ^ v.1 / (v.1.factorial : Real) *
      (u ^ v.2.1 / ((v.2.1 + 1).factorial : Real) *
        (w ^ v.2.2 / (v.2.2.factorial : Real)) *
        (((Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^
            (v.2.1 + v.2.2)) *
          ((Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ v.1)).coeff j)) := by
  let p : Polynomial Real := Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X
  let q : Polynomial Real := Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X
  let f (c : Nat) (k : Nat × Nat) : Real := u ^ k.1 / ((k.1 + 1).factorial : Real) *
    (w ^ k.2 / (k.2.factorial : Real)) * ((p ^ (k.1 + k.2)) * q ^ c).coeff j
  let g (c : Nat) (k : Nat × Nat) : Real := u ^ k.1 / (k.1.factorial : Real) *
    (w ^ k.2 / (k.2.factorial : Real)) * ((p ^ (k.1 + k.2)) * q ^ c).coeff j
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hcoeff (c : Nat) (k : Nat × Nat) : 0 ≤ ((p ^ (k.1 + k.2)) * q ^ c).coeff j :=
    affine_arm_power_coeff_nonneg (eps * b0) b0 eps (k.1 + k.2) c j
      (mul_nonneg he hb) hb he he'
  have hn (c : Nat) (k : Nat × Nat) : 0 ≤ f c k :=
    mul_nonneg (by positivity) (hcoeff c k)
  have hle (c : Nat) (k : Nat × Nat) : f c k ≤ g c k := by
    have h := mul_le_mul_of_nonneg_right (affine_labeled_factorial_term_le u hu k.1)
      (mul_nonneg (show 0 ≤ w ^ k.2 / (k.2.factorial : Real) by positivity) (hcoeff c k))
    simpa only [f, g, mul_assoc] using h
  have hs (c : Nat) : Summable (f c) :=
    (affine_treated_count_series_summable (eps * b0) (1 - eps) u w (q ^ c) j).of_nonneg_of_le
      (hn c) (hle c)
  let G : Nat → Real := fun c => M ^ c / (c.factorial : Real) *
    (∑' R : Nat, M ^ R / (R.factorial : Real) * ((p ^ R) * q ^ c).coeff j)
  have hr := affine_two_arm_coeff_series_summable (eps * b0) (1 - eps)
    ((1 - eps) * b0) eps M M j
  have hG : Summable G := by
    apply hr.prod_symm.prod.congr
    intro c
    simp only [G, Prod.swap_prod_mk, ← tsum_mul_left]
    apply tsum_congr
    intro R
    ring
  change Summable (fun v : Nat × (Nat × Nat) =>
    M ^ v.1 / (v.1.factorial : Real) * f v.1 v.2)
  apply (summable_prod_of_nonneg (fun v =>
    mul_nonneg (show 0 ≤ M ^ v.1 / (v.1.factorial : Real) by positivity) (hn v.1 v.2))).2
  constructor
  · intro c
    exact (hs c).mul_left (M ^ c / (c.factorial : Real))
  · apply hG.of_nonneg_of_le
    · intro c
      exact tsum_nonneg fun k => mul_nonneg (by positivity) (hn c k)
    · intro c
      change (∑' k, M ^ c / (c.factorial : Real) * f c k) ≤ G c
      rw [tsum_mul_left, (hs c).tsum_prod' (hs c).prod_factor]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := affine_labeled_treated_series_le (eps * b0) b0 eps u w c j
        (mul_nonneg he hb) hb he he' hu hw
      simpa only [← hM] using h

set_option maxHeartbeats 800000 in
-- The count/coefficient exchanges elaborate nested series and finite polynomial convolutions.
/-- [Under the stated inputs and conditions](hyp:L,sigma,hb,he,he',hu,hw,hM,B,eps,b0,u,w,M), The absolute signed equation (6) kernels, summed over all three counts,
have precisely the equation (7) tail bound. The common baseline cancels before
any bound is taken, and the convergence claim justifies the exchange.  This gives [the stated result](goal).-/
-- @node: affine_signed_three_count_tail_bound
lemma affine_signed_three_count_tail_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (b0 u w M : Real)
    (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hM : M = u + w) :
    let F : Nat × (Nat × Nat) → Real := fun v =>
      Real.exp (-M * b0) * (M ^ v.1 / (v.1.factorial : Real)) *
        (u ^ v.2.1 / ((v.2.1 + 1).factorial : Real)) *
        (w ^ v.2.2 / (v.2.2.factorial : Real)) *
        |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) *
          (eps * b0 + (1 - eps) * sigma.nodes i) ^ (v.2.1 + v.2.2) *
          ((1 - eps) * b0 + eps * sigma.nodes i) ^ v.1)|
    Summable F ∧ (∑' v, F v) ≤
      ∑' h : Nat, if L < h then (2 * M * B) ^ h / (h.factorial : Real) else 0 := by
  intro F
  let p : Nat × (Nat × Nat) → Polynomial Real := fun v =>
    (Polynomial.C (eps * b0) + Polynomial.C (1 - eps) * Polynomial.X) ^ (v.2.1 + v.2.2) *
      (Polynomial.C ((1 - eps) * b0) + Polynomial.C eps * Polynomial.X) ^ v.1
  let a : Nat × (Nat × Nat) → Real := fun v =>
    Real.exp (-M * b0) * (M ^ v.1 / (v.1.factorial : Real)) *
      (u ^ v.2.1 / ((v.2.1 + 1).factorial : Real)) *
      (w ^ v.2.2 / (v.2.2.factorial : Real))
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hs (j : Nat) := affine_three_count_coeff_series_summable b0 eps u w M j hb he he' hu hw hM
  have hc (j : Nat) : Summable (fun v => a v * (p v).coeff j) := by
    apply ((hs j).mul_left (Real.exp (-M * b0))).congr
    intro v
    dsimp [a, p]
    ring
  have hread (j : Nat) : (∑' v, a v * (p v).coeff j) =
      Real.exp (-M * b0) *
        (∑' c : Nat, M ^ c / (c.factorial : Real) *
          (∑' r : Nat, ∑' g : Nat, u ^ r / ((r + 1).factorial : Real) *
            (w ^ g / (g.factorial : Real)) * (p (c, (r, g))).coeff j)) := by
    rw [(hc j).tsum_prod' (hc j).prod_factor]
    simp_rw [← tsum_mul_left]
    apply tsum_congr
    intro c
    have hinner := (hc j).prod_factor c
    rw [hinner.tsum_prod' hinner.prod_factor]
    apply tsum_congr
    intro r
    apply tsum_congr
    intro g
    dsimp [a, p]
    ring
  have hle (j : Nat) : (∑' v, a v * (p v).coeff j) ≤ M ^ j / (j.factorial : Real) := by
    rw [hread]
    exact affine_three_count_coeff_baseline_le b0 eps u w M j hb he he' hu hw hM
  have h := affine_signed_polynomial_family_tail_bound sigma M hM0 p a
    (fun v => by dsimp [a]; positivity)
    (fun v j => affine_arm_power_coeff_nonneg (eps * b0) b0 eps
      (v.2.1 + v.2.2) v.1 j (mul_nonneg he hb) hb he he') hc hle
  simpa only [F, a, p, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, mul_assoc] using h

/-- [Under the stated inputs and conditions](hyp:L,sigma,hb,he,he',B,eps,b0,u,w,M,r,g,c), Factoring the original signed count difference in equation (6) gives the
Palm intensity times the kernel controlled by the count-summed Taylor bound.  This gives [the stated result](goal).-/
-- @node: affine_signed_raw_count_factorization
lemma affine_signed_raw_count_factorization {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (b0 u w M : Real) (r g c : Nat)
    (hb : 0 < b0) (he : 0 < eps) (he' : eps ≤ 1) :
    (∑ i, sigma.weights i * (Real.exp (-M * (b0 + sigma.nodes i)) *
      (u * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ (r + 1) *
      (w * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ g *
      (M * ((1 - eps) * b0 + eps * sigma.nodes i)) ^ c /
      (((r + 1).factorial : Real) * (g.factorial : Real) * (c.factorial : Real)) *
      (eps * b0 / (eps * b0 + (1 - eps) * sigma.nodes i)))) =
    u * (eps * b0) * Real.exp (-M * b0) *
      (M ^ c / (c.factorial : Real)) * (u ^ r / ((r + 1).factorial : Real)) *
      (w ^ g / (g.factorial : Real)) *
      (∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) *
        (eps * b0 + (1 - eps) * sigma.nodes i) ^ (r + g) *
        ((1 - eps) * b0 + eps * sigma.nodes i) ^ c)) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hS : eps * b0 + (1 - eps) * sigma.nodes i ≠ 0 := by
    apply ne_of_gt
    exact add_pos_of_pos_of_nonneg (mul_pos he hb)
      (mul_nonneg (sub_nonneg.mpr he') (sigma.mem i).1)
  rw [show -M * (b0 + sigma.nodes i) = -M * b0 + -M * sigma.nodes i by ring,
    Real.exp_add]
  generalize hsdef : eps * b0 + (1 - eps) * sigma.nodes i = s at hS ⊢
  simp only [mul_pow, pow_succ, pow_add]
  field_simp [hS]

set_option maxHeartbeats 800000 in
-- The count/coefficient exchanges elaborate nested series and finite polynomial convolutions.
/-- [Under the stated inputs and conditions](hyp:L,sigma,hb,he,he',hu,hw,hM,B,eps,b0,u,w,M), The equation (6) signed masses are absolutely summable and their absolute
sum obeys the equation (7) one-cell bound, with both channels retained.  This gives [the stated result](goal).-/
-- @node: affine_signed_raw_count_tail_bound
lemma affine_signed_raw_count_tail_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (b0 u w M : Real)
    (hb : 0 < b0) (he : 0 < eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hM : M = u + w) :
    let D : Nat × (Nat × Nat) → Real := fun v =>
      ∑ i, sigma.weights i * (Real.exp (-M * (b0 + sigma.nodes i)) *
        (u * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ (v.2.1 + 1) *
        (w * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ v.2.2 *
        (M * ((1 - eps) * b0 + eps * sigma.nodes i)) ^ v.1 /
        (((v.2.1 + 1).factorial : Real) * (v.2.2.factorial : Real) *
          (v.1.factorial : Real)) * (eps * b0 / (eps * b0 + (1 - eps) * sigma.nodes i)))
    Summable (fun v => |D v|) ∧ (∑' v, |D v|) ≤
      u * (eps * b0) *
        ∑' h : Nat, if L < h then (2 * M * B) ^ h / (h.factorial : Real) else 0 := by
  intro D
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  let F : Nat × (Nat × Nat) → Real := fun v =>
    Real.exp (-M * b0) * (M ^ v.1 / (v.1.factorial : Real)) *
      (u ^ v.2.1 / ((v.2.1 + 1).factorial : Real)) *
      (w ^ v.2.2 / (v.2.2.factorial : Real)) *
      |∑ i, sigma.weights i * (Real.exp (-M * sigma.nodes i) *
        (eps * b0 + (1 - eps) * sigma.nodes i) ^ (v.2.1 + v.2.2) *
        ((1 - eps) * b0 + eps * sigma.nodes i) ^ v.1)|
  obtain ⟨hs, ht⟩ := affine_signed_three_count_tail_bound sigma b0 u w M
    hb.le he.le he' hu hw hM
  have hread (v : Nat × (Nat × Nat)) : |D v| = u * (eps * b0) * F v := by
    dsimp only [D]
    rw [affine_signed_raw_count_factorization sigma b0 u w M v.2.1 v.2.2 v.1 hb he he']
    simp only [abs_mul, abs_of_nonneg hu, abs_of_nonneg he.le, abs_of_nonneg hb.le,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (pow_nonneg hM0 _),
      abs_of_nonneg (pow_nonneg hu _), abs_of_nonneg (pow_nonneg hw _),
      abs_div, abs_of_nonneg (Nat.cast_nonneg (α := Real) _)]
    dsimp only [F]
    ring
  simp_rw [hread]
  constructor
  · exact hs.mul_left (u * (eps * b0))
  · rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left ht (mul_nonneg hu (mul_nonneg he.le hb.le))

end CausalSmith.Stat.AnnotationRarearmFrontier
