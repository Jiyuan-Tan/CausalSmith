/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Bandwidth

/-! # Elementary rates for the continuity-only frontier -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter

noncomputable section

/-- At the continuity elbow the two summands of the frontier have root-sample
size order. The result uses [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
lemma contFrontier_elbow_asymp (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    AsympSeq
      (fun n => contFrontier n
        ((n : ℝ) ^ (-(1 : ℝ) / (2 * (kappa + 1)))) kappa)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk1 : 0 < kappa + 1 := by linarith
  have hp :
      (((n : ℝ) ^ (-(1 : ℝ) / (2 * (kappa + 1)))) ^ (kappa + 1)) =
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_mul hnR.le]
    congr 1
    field_simp [hk1.ne']
  rw [contFrontier, hp]
  have hnonneg := Real.rpow_nonneg hnR.le (-(1 : ℝ) / 2)
  constructor <;> nlinarith

/-- At threshold zero the continuity-only frontier is exactly the regular
root-sample-size term. The result uses [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
lemma contFrontier_zero_asymp (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    AsympSeq (fun n => contFrontier n 0 kappa)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards with n
  have hk1 : kappa + 1 ≠ 0 := by linarith
  simp only [contFrontier, Real.zero_rpow hk1, add_zero, one_mul]
  have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 : ℝ) / 2)
  constructor <;> nlinarith

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
