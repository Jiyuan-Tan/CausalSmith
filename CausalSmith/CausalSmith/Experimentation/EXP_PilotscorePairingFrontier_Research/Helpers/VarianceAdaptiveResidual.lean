module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic

/-! # Algebra for adaptive matched-pair residuals

This module isolates the finite involution identities used when a matching is
allowed to depend on the observed covariates.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open scoped BigOperators

/-- Squared matched differences split into a score term, a residual term, and
their cross term whenever the original signal is twice the score plus the
residual. -/
lemma matched_square_decomposition (M : Match N) (s q r : Fin N → ℝ)
    (hs : ∀ i, s i = 2 * q i + r i) :
    ∑ i : Fin N, (s i - s (M.val i)) ^ 2 =
      4 * ∑ i : Fin N, (q i - q (M.val i)) ^ 2 +
      ∑ i : Fin N, (r i - r (M.val i)) ^ 2 +
      4 * ∑ i : Fin N,
        (q i - q (M.val i)) * (r i - r (M.val i)) := by
  calc
    ∑ i : Fin N, (s i - s (M.val i)) ^ 2 =
        ∑ i : Fin N, (4 * (q i - q (M.val i)) ^ 2 +
          (r i - r (M.val i)) ^ 2 +
          4 * (q i - q (M.val i)) * (r i - r (M.val i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i, hs (M.val i)]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hscoremul :
          (∑ i : Fin N, 4 * (q i - q (M.val i)) ^ 2) =
            4 * ∑ i : Fin N, (q i - q (M.val i)) ^ 2 := by
        simpa using (Finset.mul_sum Finset.univ
          (fun i : Fin N => (q i - q (M.val i)) ^ 2) 4).symm
      have hmul :
          (∑ i : Fin N,
            4 * (q i - q (M.val i)) * (r i - r (M.val i))) =
            4 * ∑ i : Fin N,
              (q i - q (M.val i)) * (r i - r (M.val i)) := by
        simpa only [mul_assoc] using (Finset.mul_sum Finset.univ
          (fun i : Fin N => (q i - q (M.val i)) * (r i - r (M.val i))) 4).symm
      rw [hscoremul, hmul]

/-- Under an involution, the sum of squared residual differences is twice the
sum of residual squares minus twice the matched cross-product sum. -/
lemma sum_sq_sub_match (M : Match N) (r : Fin N → ℝ) :
    ∑ i : Fin N, (r i - r (M.val i)) ^ 2 =
      2 * ∑ i : Fin N, (r i) ^ 2 -
      2 * ∑ i : Fin N, r i * r (M.val i) := by
  have hperm : (∑ i : Fin N, (r (M.val i)) ^ 2) = ∑ i : Fin N, (r i) ^ 2 := by
    exact Equiv.sum_comp M.val (fun i => (r i) ^ 2)
  calc
    ∑ i : Fin N, (r i - r (M.val i)) ^ 2 =
        ∑ i : Fin N, ((r i) ^ 2 + (r (M.val i)) ^ 2 -
          2 * (r i * r (M.val i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i : Fin N, (r i) ^ 2) +
        (∑ i : Fin N, (r (M.val i)) ^ 2) -
        2 * ∑ i : Fin N, r i * r (M.val i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hperm]; ring

/-- The score-residual cross term against matched differences reduces to twice
the same score difference times the residual at the first endpoint. -/
lemma sum_score_mul_residual_sub_match (M : Match N) (q r : Fin N → ℝ) :
    ∑ i : Fin N,
        (q i - q (M.val i)) * (r i - r (M.val i)) =
      2 * ∑ i : Fin N, (q i - q (M.val i)) * r i := by
  have hpartner :
      (∑ i : Fin N, (q i - q (M.val i)) * r (M.val i)) =
        -∑ i : Fin N, (q i - q (M.val i)) * r i := by
    calc
      ∑ i : Fin N, (q i - q (M.val i)) * r (M.val i) =
          ∑ i : Fin N,
            (q (M.val i) - q (M.val (M.val i))) * r (M.val (M.val i)) :=
        (Equiv.sum_comp M.val _).symm
      _ = ∑ i : Fin N, -((q i - q (M.val i)) * r i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [M.property.1]
        ring
      _ = _ := by rw [Finset.sum_neg_distrib]
  calc
    ∑ i : Fin N,
        (q i - q (M.val i)) * (r i - r (M.val i)) =
        (∑ i : Fin N, (q i - q (M.val i)) * r i) -
          ∑ i : Fin N, (q i - q (M.val i)) * r (M.val i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpartner]; ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
