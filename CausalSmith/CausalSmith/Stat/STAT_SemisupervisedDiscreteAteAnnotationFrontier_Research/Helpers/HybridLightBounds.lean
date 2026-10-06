module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.FactorialCertificate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLightMoments

/-! Deterministic and moment bounds for one polynomial (light-cell) branch. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- The exact algebraic form of (C16), separated from the probabilistic
factorial-moment calculation.  [the stated conditions](hyp:hp,h0,h1) [the stated conclusion](goal). -/
lemma light_mean_error_identity {p B s0 s1 mu0 mu1 e0 e1 g0 g1 : Real}
    (hp : p = s0 + s1)
    (h0 : s0 / B * g0 + e0 = 1)
    (h1 : s1 / B * g1 + e1 = 1) :
    s1 * mu1 * (p / B) * g1 - s0 * mu0 * (p / B) * g0 =
      p * (mu1 - mu0) - p * (mu1 * e1 - mu0 * e0) := by
  rw [hp]
  linear_combination
    (s0 + s1) * mu1 * h1 - (s0 + s1) * mu0 * h0

/-- One arm of the light-cell approximation error, after using overlap to
cancel the cell mass against the Chebyshev reciprocal bound.  [the stated conditions](hyp:heps,hp,hB,hL,hs,he,heInv) [the stated conclusion](goal). -/
lemma light_arm_bias_le {eps p B s e : Real} {L : Nat}
    (heps : 0 < eps) (hp : 0 ≤ p) (hB : 0 < B) (hL : 0 < L)
    (hs : eps * p ≤ s) (he : 0 ≤ e)
    (heInv : e ≤ (((L : Real) ^ 2 * (s / B))⁻¹)) :
    p * e ≤ B / (eps * (L : Real) ^ 2) := by
  by_cases hp0 : p = 0
  · simp [hp0, div_nonneg hB.le (mul_nonneg heps.le (sq_nonneg _))]
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hsPos : 0 < s := lt_of_lt_of_le (mul_pos heps hpPos) hs
  have hLReal : 0 < (L : Real) := by exact_mod_cast hL
  have hden : 0 < (L : Real) ^ 2 * (s / B) := by positivity
  have heScaled : e * ((L : Real) ^ 2 * (s / B)) ≤ 1 := by
    rw [inv_eq_one_div] at heInv
    exact (le_div_iff₀ hden).mp heInv
  have hraw : e * (L : Real) ^ 2 * s ≤ B := by
    calc
      e * (L : Real) ^ 2 * s =
          (e * ((L : Real) ^ 2 * (s / B))) * B := by
            field_simp
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right heScaled hB.le
      _ = B := one_mul B
  have hoverlap : e * (L : Real) ^ 2 * (eps * p) ≤
      e * (L : Real) ^ 2 * s := by
    gcongr
  apply (le_div_iff₀ (mul_pos heps (sq_pos_of_pos hLReal))).2
  nlinarith [hoverlap.trans hraw]

/-- Two-arm form of (C17).  [the stated conditions](hyp:heps,hp,hB,hL,hs0,hs1,hmu0,hmu1,he0,he1,heInv0,heInv1) [the stated conclusion](goal). -/
lemma light_cell_bias_abs_le {eps p B s0 s1 mu0 mu1 e0 e1 : Real}
    {L : Nat} (heps : 0 < eps) (hp : 0 ≤ p) (hB : 0 < B)
    (hL : 0 < L) (hs0 : eps * p ≤ s0) (hs1 : eps * p ≤ s1)
    (hmu0 : mu0 ∈ Set.Icc (0 : Real) 1)
    (hmu1 : mu1 ∈ Set.Icc (0 : Real) 1)
    (he0 : 0 ≤ e0) (he1 : 0 ≤ e1)
    (heInv0 : e0 ≤ (((L : Real) ^ 2 * (s0 / B))⁻¹))
    (heInv1 : e1 ≤ (((L : Real) ^ 2 * (s1 / B))⁻¹)) :
    |p * (mu1 * e1 - mu0 * e0)| ≤
      2 * B / (eps * (L : Real) ^ 2) := by
  have h0 := light_arm_bias_le heps hp hB hL hs0 he0 heInv0
  have h1 := light_arm_bias_le heps hp hB hL hs1 he1 heInv1
  let R := B / (eps * (L : Real) ^ 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hm0 : 0 ≤ p * (mu0 * e0) :=
    mul_nonneg hp (mul_nonneg hmu0.1 he0)
  have hm1 : 0 ≤ p * (mu1 * e1) :=
    mul_nonneg hp (mul_nonneg hmu1.1 he1)
  have hb0 : p * (mu0 * e0) ≤ R := by
    calc
      p * (mu0 * e0) = mu0 * (p * e0) := by ring
      _ ≤ 1 * R := mul_le_mul hmu0.2 h0 (mul_nonneg hp he0) (by norm_num)
      _ = R := one_mul R
  have hb1 : p * (mu1 * e1) ≤ R := by
    calc
      p * (mu1 * e1) = mu1 * (p * e1) := by ring
      _ ≤ 1 * R := mul_le_mul hmu1.2 h1 (mul_nonneg hp he1) (by norm_num)
      _ = R := one_mul R
  calc
    |p * (mu1 * e1 - mu0 * e0)| =
        |p * (mu1 * e1) - p * (mu0 * e0)| := by ring_nf
    _ ≤ |p * (mu1 * e1)| + |p * (mu0 * e0)| := abs_sub _ _
    _ = p * (mu1 * e1) + p * (mu0 * e0) := by
      rw [abs_of_nonneg hm1, abs_of_nonneg hm0]
    _ ≤ 2 * R := by linarith
    _ = 2 * B / (eps * (L : Real) ^ 2) := by dsimp [R]; ring

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
