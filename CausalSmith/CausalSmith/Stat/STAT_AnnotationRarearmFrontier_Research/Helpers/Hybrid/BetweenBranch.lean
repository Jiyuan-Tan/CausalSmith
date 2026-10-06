module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.AggregateBias
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountArmRisk

/-!
The light-cell between-branch contribution in equation (13), including null cells.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:hp,ht,heps,hov,p,s,t,eps), Overlap controls squared missing-cell bias by cell mass over twice the intensity.  This gives [the stated result](goal).-/
-- @node: hybrid_squared_missing_cell_bound
lemma hybrid_squared_missing_cell_bound (p s t eps : Real)
    (hp : 0 ≤ p) (ht : 0 < t) (heps : 0 < eps) (hov : eps * p ≤ s) :
    (p * Real.exp (-t * s)) ^ 2 ≤ p / (2 * Real.exp 1 * t * eps) := by
  have hexp : Real.exp (-2 * t * s) ≤ Real.exp (-(2 * t * eps * p)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have henv := inverse_count_exp_envelope p (2 * t) eps (by positivity) heps
  calc
    _ = p * (p * Real.exp (-2 * t * s)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
    _ ≤ p * (p * Real.exp (-(2 * t * eps * p))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hp) hp
    _ ≤ p * (1 / (Real.exp 1 * (2 * t) * eps)) :=
      mul_le_mul_of_nonneg_left henv hp
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:alpha,J,ht,heps,hcell,hmass,p,s,t,eps), Summing the squared inverse-branch biases costs no factor for the cell count.  This gives [the stated result](goal).-/
-- @node: hybrid_squared_missing_mass_sum
lemma hybrid_squared_missing_mass_sum {alpha : Type} (J : Finset alpha)
    (p s : alpha → Real) (t eps : Real) (ht : 0 < t) (heps : 0 < eps)
    (hcell : ∀ j ∈ J, 0 ≤ p j ∧ eps * p j ≤ s j)
    (hmass : (∑ j ∈ J, p j) ≤ 1) :
    (∑ j ∈ J, (p j * Real.exp (-t * s j)) ^ 2) ≤
      1 / (2 * Real.exp 1 * t * eps) := by
  calc
    _ ≤ ∑ j ∈ J, p j / (2 * Real.exp 1 * t * eps) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hybrid_squared_missing_cell_bound (p j) (s j) t eps
        (hcell j hj).1 ht heps (hcell j hj).2
    _ = (∑ j ∈ J, p j) / (2 * Real.exp 1 * t * eps) := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right hmass (by positivity)

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,hu,ht,hs,hsB,hv,hmu,heps,hov,B,u,t,s,v,mu,eps,pi), The light-cell branch separation bound extends to zero own-arm masses by overlap.  This gives [the stated result](goal).-/
-- @node: hybrid_light_between_branch_bound_nonneg
lemma hybrid_light_between_branch_bound_nonneg (L : Nat) (B u t s v mu eps pi : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t)
    (hs : 0 ≤ s) (hsB : s ≤ B) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1)
    (heps : 0 < eps) (hov : eps * (s + v) ≤ s) :
    pi * (1 - pi) *
      ((∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s * mu) s v) -
        ∫ z, inverseCellBranch u z ∂cellPoissonLaw u t (s * mu) s v) ^ 2 ≤
      2 * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        2 * ((s + v) * Real.exp (-t * s)) ^ 2 := by
  by_cases hs0 : s = 0
  · have hv0 : v = 0 := by rw [hs0] at hov; nlinarith
    subst s
    subst v
    obtain ⟨hp, hh⟩ := hybrid_zero_outcome_branch_means L B u t 0 0 hu ht (by norm_num)
    simpa only [zero_mul, hp, hh, sub_self, zero_pow, mul_zero, zero_add, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
      (show (0 : Real) ≤ 2 * (B / (eps * (L : Real) ^ 2)) ^ 2 from by positivity)
  · exact hybrid_light_between_branch_bound L B u t s v mu eps pi hL hB hu ht
      (lt_of_le_of_ne hs (Ne.symm hs0)) hsB hv hmu heps hov

/-- [Under the stated inputs and conditions](hyp:alpha,J,L,hL,hB,hu,ht,heps,hcell,hmass,s,v,mu,pi,B,u,t,eps), The light-cell part of equation (13) retains its squared approximation term
and absorbs all inverse-branch separation terms using total mass at most one.  This gives [the stated result](goal).-/
-- @node: hybrid_light_between_branch_sum
lemma hybrid_light_between_branch_sum {alpha : Type} (J : Finset alpha)
    (s v mu pi : alpha → Real) (L : Nat) (B u t eps : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (hcell : ∀ j ∈ J, 0 ≤ s j ∧ s j ≤ B ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
      eps * (s j + v j) ≤ s j)
    (hmass : (J.sum (fun j => s j + v j)) ≤ 1) :
    (∑ j ∈ J, pi j * (1 - pi j) *
      ((∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s j * mu j) (s j) (v j)) -
        ∫ z, inverseCellBranch u z ∂cellPoissonLaw u t (s j * mu j) (s j) (v j)) ^ 2) ≤
      2 * J.card * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        1 / (Real.exp 1 * t * eps) := by
  have hmissing := hybrid_squared_missing_mass_sum J (fun j => s j + v j) s t eps ht heps
    (fun j hj => ⟨add_nonneg (hcell j hj).1 (hcell j hj).2.2.1, (hcell j hj).2.2.2.2⟩)
    hmass
  calc
    _ ≤ ∑ j ∈ J, (2 * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        2 * ((s j + v j) * Real.exp (-t * s j)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hs, hsB, hv, hmu, hov⟩ := hcell j hj
      exact hybrid_light_between_branch_bound_nonneg L B u t (s j) (v j) (mu j)
        eps (pi j) hL hB hu ht hs hsB hv hmu heps hov
    _ = 2 * J.card * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        2 * (∑ j ∈ J, ((s j + v j) * Real.exp (-t * s j)) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hmissing (by norm_num : (0 : Real) ≤ 2)
      have heq : 2 * (1 / (2 * Real.exp 1 * t * eps)) = 1 / (Real.exp 1 * t * eps) := by ring
      rw [heq] at hh
      exact add_le_add_right hh _

end CausalSmith.Stat.AnnotationRarearmFrontier
