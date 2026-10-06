module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedHolderBounds
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Global scalar moduli for the triangular fold -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma triangularFold_le_even_distance (t : ℝ) (z : ℤ) :
    triangularFold t ≤ |t - 2 * z| := by
  let n : ℤ := Int.floor ((t + 1) / 2)
  have hlo : (2 : ℝ) * n - 1 ≤ t := by
    have := Int.floor_le ((t + 1) / 2)
    dsimp [n]
    linarith
  have hhi : t < (2 : ℝ) * n + 1 := by
    have := Int.lt_floor_add_one ((t + 1) / 2)
    dsimp [n]
    linarith
  have hnabs : |t - 2 * (n : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  unfold triangularFold
  dsimp [n] at hnabs ⊢
  by_cases hzn : z = n
  · subst z
    simpa [n]
  rcases lt_or_gt_of_ne hzn with hz | hz
  · have hzleZ : z ≤ n - 1 := by omega
    have hzle : (z : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hzleZ
    have hpos : 1 ≤ t - 2 * (z : ℝ) := by linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ t - 2 * (z : ℝ))]
    exact hnabs.trans hpos
  · have hzle : (n : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hz)
    have hpos : 1 ≤ 2 * (z : ℝ) - t := by linarith
    rw [abs_of_nonpos (by linarith : t - 2 * (z : ℝ) ≤ 0)]
    exact hnabs.trans (by linarith)

@[no_expose]
noncomputable def evenIntegers : Set ℝ :=
  Set.range fun z : ℤ => 2 * (z : ℝ)

lemma triangularFold_eq_infDist (t : ℝ) :
    triangularFold t = Metric.infDist t evenIntegers := by
  let n : ℤ := Int.floor ((t + 1) / 2)
  apply le_antisymm
  · rw [Metric.infDist_eq_iInf]
    have hne : evenIntegers.Nonempty := by
      refine ⟨0, ?_⟩
      exact ⟨0, by simp [evenIntegers]⟩
    letI : Nonempty evenIntegers := hne.to_subtype
    apply le_ciInf
    rintro ⟨y, z, rfl⟩
    simpa [Real.dist_eq] using triangularFold_le_even_distance t z
  · refine Metric.infDist_le_dist_of_mem ?_
    exact ⟨n, rfl⟩

lemma triangularFold_diff_le (s t : ℝ) :
    |triangularFold s - triangularFold t| ≤ |s - t| := by
  rw [triangularFold_eq_infDist, triangularFold_eq_infDist]
  have h := (Metric.lipschitz_infDist_pt evenIntegers).dist_le_mul s t
  simpa [Real.dist_eq] using h

lemma triangularFold_add_two_int (t : ℝ) (z : ℤ) :
    triangularFold (t + 2 * z) = triangularFold t := by
  unfold triangularFold
  have harg : ((t + 2 * (z : ℝ)) + 1) / 2 = (t + 1) / 2 + z := by ring
  rw [harg, Int.floor_add_intCast]
  congr 1
  push_cast
  ring

lemma triangularWave_eq_fold (t : ℝ) :
    triangularWave t = 2 * triangularFold (2 * t + 1 / 2) - 1 := by
  let n : ℤ := Int.floor t
  let r : ℝ := t - n
  have hr0 : 0 ≤ r := by dsimp [r]; exact sub_nonneg.mpr (Int.floor_le t)
  have hr1 : r < 1 := by
    dsimp [r]
    linarith [Int.lt_floor_add_one t]
  have ht : t = r + n := by dsimp [r]; ring
  have hperiod : triangularFold (2 * t + 1 / 2) =
      triangularFold (2 * r + 1 / 2) := by
    rw [ht]
    convert triangularFold_add_two_int (2 * r + 1 / 2) n using 1 <;> ring
  rw [hperiod]
  unfold triangularWave
  change (if r ≤ 1 / 4 then 4 * r
    else if r ≤ 3 / 4 then 2 - 4 * r else 4 * r - 4) = _
  split
  next hfirst =>
    rw [triangularFold_eq_self]
    · ring
    · constructor <;> linarith
  next hfirst =>
    split
    next hmiddle =>
      rw [triangularFold_eq_two_sub]
      · ring
      · constructor <;> linarith
    next hlast =>
      have hp := triangularFold_add_two_int (2 * r - 3 / 2) 1
      have heq : triangularFold (2 * r + 1 / 2) = triangularFold (2 * r - 3 / 2) := by
        convert hp using 1 <;> norm_num <;> ring
      rw [heq, triangularFold_eq_self]
      · ring
      · constructor <;> linarith

lemma triangularWave_diff_le (s t : ℝ) :
    |triangularWave s - triangularWave t| ≤ 4 * |s - t| := by
  rw [triangularWave_eq_fold, triangularWave_eq_fold]
  calc
    |(2 * triangularFold (2 * s + 1 / 2) - 1) -
        (2 * triangularFold (2 * t + 1 / 2) - 1)| =
        2 * |triangularFold (2 * s + 1 / 2) -
          triangularFold (2 * t + 1 / 2)| := by
            rw [show (2 * triangularFold (2 * s + 1 / 2) - 1) -
              (2 * triangularFold (2 * t + 1 / 2) - 1) =
              2 * (triangularFold (2 * s + 1 / 2) -
                triangularFold (2 * t + 1 / 2)) by ring, abs_mul]
            norm_num
    _ ≤ 2 * |(2 * s + 1 / 2) - (2 * t + 1 / 2)| := by
      exact mul_le_mul_of_nonneg_left (triangularFold_diff_le _ _) (by norm_num)
    _ = 4 * |s - t| := by
      rw [show (2 * s + 1 / 2) - (2 * t + 1 / 2) = 2 * (s - t) by ring,
        abs_mul]
      norm_num
      ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
