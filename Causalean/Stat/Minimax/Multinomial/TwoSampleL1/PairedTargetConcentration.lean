module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedProductPrior

/-!
# Concentration of the paired product-prior target

The L1 target under a balanced product prior is an average of independent
bounded scalar absolute values. This module isolates its finite variance
bound before the fuzzy-hypothesis construction.
-/

public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open scoped BigOperators ENNReal

/-- Given [a scalar moment prior](hyp:P), [a positive balanced pair count](hyp:b,hb), [a bounded nonnegative tilt](hyp:t,ht,ht1), and [a prior side](hyp:side), [the paired-product L1 target has the stated variance bound](goal). -/
theorem pairedProductTarget_variance_le {L : ℕ} (P : ScalarMomentPriors L)
    (b : ℕ) (hb : 0 < b)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (side : Bool) :
    ∑ u : Fin b → Fin P.m,
        (pairedProductWeight P b side u).toReal *
          (simplexL1 (pairedBaseVector b hb)
              (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
                (pairedNodeVector_abs_le_one P u)) -
            t * ∑ i : Fin P.m, scalarPriorWeight P side i * |P.node i|) ^ 2 ≤
      t ^ 2 / (b : ℝ) := by
  classical
  let w : Fin P.m → ℝ := scalarPriorWeight P side
  let μ : ℝ := ∑ i : Fin P.m, w i * |P.node i|
  let c : Fin P.m → ℝ := fun i => |P.node i| - μ
  let W : (Fin b → Fin P.m) → ℝ := fun u => ∏ j : Fin b, w (u j)
  have hw (i : Fin P.m) : 0 ≤ w i := by
    dsimp [w]
    cases side <;> simp [scalarPriorWeight, P.w₀_nonneg, P.w₁_nonneg]
  have hwsum : ∑ i : Fin P.m, w i = 1 := by
    dsimp [w]
    cases side <;> simp [scalarPriorWeight, P.w₀_sum, P.w₁_sum]
  have hcenter : ∑ i : Fin P.m, w i * c i = 0 := by
    simp only [c, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp [μ, hwsum]
  have hW (u : Fin b → Fin P.m) : 0 ≤ W u := by
    exact Finset.prod_nonneg (by intro i hi; exact hw _)
  have hweight (u : Fin b → Fin P.m) :
      (pairedProductWeight P b side u).toReal = W u := by
    simp [pairedProductWeight, ENNReal.toReal_prod, ENNReal.toReal_ofReal (hw _), W, w]
  have hpair (j k : Fin b) (hjk : j ≠ k) :
      ∑ u : Fin b → Fin P.m, W u * c (u j) * c (u k) = 0 := by
    let f : Fin b → Fin P.m → ℝ := fun l i =>
      w i * (if l = j then c i else 1) * (if l = k then c i else 1)
    have hf (u : Fin b → Fin P.m) :
        W u * c (u j) * c (u k) = ∏ l : Fin b, f l (u l) := by
      simp only [f, Finset.prod_mul_distrib]
      simp [W, Finset.prod_ite_eq', mul_assoc]
    calc
      _ = ∑ u : Fin b → Fin P.m, ∏ l : Fin b, f l (u l) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hf u
      _ = ∏ l : Fin b, ∑ i : Fin P.m, f l i := by
        exact (Fintype.prod_sum f).symm
      _ = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [f, hjk, hcenter]
  have hdiag (j : Fin b) :
      ∑ u : Fin b → Fin P.m, W u * c (u j) ^ 2 ≤ 1 := by
    have hμlo : 0 ≤ μ := Finset.sum_nonneg (by
      intro i hi
      exact mul_nonneg (hw i) (abs_nonneg _))
    have hμhi : μ ≤ 1 := by
      calc
        μ ≤ ∑ i : Fin P.m, w i := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_of_le_one_right (hw i) (pairedNodeVector_abs_le_one P (fun _ => i) j)
        _ = 1 := hwsum
    have hc (i : Fin P.m) : c i ^ 2 ≤ 1 := by
      have hai : |P.node i| ≤ 1 := by
        exact abs_le.mpr (P.node_mem i)
      have hlow : 0 ≤ |P.node i| := abs_nonneg _
      nlinarith [sq_nonneg (c i - 1), sq_nonneg (c i + 1)]
    calc
      _ ≤ ∑ u : Fin b → Fin P.m, W u := by
        apply Finset.sum_le_sum
        intro u hu
        simpa [mul_comm] using mul_le_of_le_one_left (hW u) (hc (u j))
      _ = 1 := by
        calc
          _ = ∏ _j : Fin b, ∑ i : Fin P.m, w i := by
            simpa [W] using (Fintype.prod_sum (fun _j : Fin b => w)).symm
          _ = 1 := by simp [hwsum]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hscale (u : Fin b → Fin P.m) :
      simplexL1 (pairedBaseVector b hb)
          (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
            (pairedNodeVector_abs_le_one P u)) -
        t * ∑ i : Fin P.m, scalarPriorWeight P side i * |P.node i| =
      (t / (b : ℝ)) * ∑ j : Fin b, c (u j) := by
    rw [pairedBase_tilt_l1]
    simp only [pairedNodeVector]
    have hs : ∑ j : Fin b, c (u j) =
        (∑ j : Fin b, |P.node (u j)|) - (b : ℝ) * μ := by
      simp [c, Finset.sum_sub_distrib]
    rw [hs]
    dsimp [μ, w]
    field_simp
  have hvar :
      ∑ u : Fin b → Fin P.m, W u * (∑ j : Fin b, c (u j)) ^ 2 ≤ (b : ℝ) := by
    have hsplit :
        ∑ u : Fin b → Fin P.m, W u * (∑ j : Fin b, c (u j)) ^ 2 =
          ∑ j : Fin b, ∑ u : Fin b → Fin P.m, W u * c (u j) ^ 2 := by
      calc
        _ = ∑ j : Fin b, ∑ k : Fin b,
              ∑ u : Fin b → Fin P.m, W u * c (u j) * c (u k) := by
          simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            _ = ∑ k : Fin b, if k = j then
                  ∑ u : Fin b → Fin P.m, W u * c (u j) ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              split_ifs with h
              · subst k
                congr 1
                ext u
                ring
              · exact hpair j k (Ne.symm h)
            _ = _ := by simp
    rw [hsplit]
    calc
      _ ≤ ∑ _j : Fin b, (1 : ℝ) := Finset.sum_le_sum (by
        intro j hj
        exact hdiag j)
      _ = b := by simp
  simp_rw [hweight, hscale]
  calc
    _ = (t / (b : ℝ)) ^ 2 *
          ∑ u : Fin b → Fin P.m, W u * (∑ j : Fin b, c (u j)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (t / (b : ℝ)) ^ 2 * (b : ℝ) := by
      exact mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    _ = t ^ 2 / (b : ℝ) := by field_simp

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
