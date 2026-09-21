module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ChebyshevCalibration

/-! A universal-constant packaging of the Chebyshev factorial certificate. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Polynomial

-- @node: lem:chebyshev-factorial-certificate
/-- For every degree at least two, the continuations obey (C9), have the stated
degree, and use one universal factorial-lift moment constant.  [the stated conclusion](goal). -/
lemma chebyshev_factorial_certificate :
    ∃ A : Real, 1 < A ∧ ∀ L : Nat, 2 ≤ L →
      (chebG L).natDegree ≤ L - 2 ∧
      (∀ z : Real, z ∈ Set.Icc (0 : Real) 1 →
        0 ≤ (chebE L).eval z ∧
        (chebE L).eval z ≤ 1 ∧
        (0 < z → (chebE L).eval z ≤ ((L : Real) ^ 2 * z)⁻¹) ∧
        z * (chebG L).eval z + (chebE L).eval z = 1) ∧
      ∀ (a : Bool) (t B s0 s1 : Real),
        0 < t → 0 < B → 0 ≤ s0 → 0 ≤ s1 → (L : Real) ≤ t * B →
        factorialLiftSecondMoment a L B t s0 s1 ≤
          A ^ L * (1 + (s0 + s1) / B) ^ (2 * L) ∧
        (s0 + s1 ≤ B → factorialLiftSecondMoment a L B t s0 s1 ≤ A ^ L) := by
  refine ⟨7056, by norm_num, ?_⟩
  intro L hL
  have hcal := explicit_chebyshev_calibration L hL
  have hH : (chebH L).natDegree ≤ L := by
    unfold chebH chebQ
    calc
      ((2 * (L : Real) ^ 2)⁻¹ •
          (1 - (Chebyshev.T Real L).comp (1 - 2 * X))).natDegree
          ≤ (1 - (Chebyshev.T Real L).comp (1 - 2 * X)).natDegree :=
            natDegree_smul_le _ _
      _ ≤ max 0 ((Chebyshev.T Real L).comp (1 - 2 * X)).natDegree := by
        simpa using natDegree_sub_le (1 : Polynomial Real)
          ((Chebyshev.T Real L).comp (1 - 2 * X))
      _ ≤ L := by
        rw [max_le_iff]
        constructor
        · omega
        · calc
            ((Chebyshev.T Real L).comp (1 - 2 * X)).natDegree
                ≤ (Chebyshev.T Real L).natDegree *
                    (1 - 2 * X : Polynomial Real).natDegree :=
                  natDegree_comp_le
            _ ≤ L := by
              rw [Chebyshev.natDegree_T]
              have hlin : (1 - 2 * X : Polynomial Real).natDegree ≤ 1 := by
                exact (natDegree_sub_le (1 : Polynomial Real) (2 * X)).trans (by simp)
              simpa using Nat.mul_le_mul_left L hlin
  have hE : (chebE L).natDegree ≤ L - 1 := by
    rw [chebE, natDegree_divByMonic _ monic_X, natDegree_X]
    exact Nat.sub_le_sub_right hH 1
  have hnum : (1 - chebE L).natDegree ≤ L - 1 :=
    (natDegree_sub_le (1 : Polynomial Real) (chebE L)).trans
      (max_le (by simpa using hL) hE)
  have hdegree : (chebG L).natDegree ≤ L - 2 := by
    rw [chebG, natDegree_divByMonic _ monic_X, natDegree_X]
    simpa [Nat.sub_sub] using Nat.sub_le_sub_right hnum 1
  refine ⟨hdegree, hcal.2.2.2, ?_⟩
  intro a t B s0 s1 ht hB hs0 hs1 htB
  exact hcal.2.2.1 a t B s0 s1 ht hB hs0 hs1 htB

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
