module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedGeometryBounds
public import Mathlib.MeasureTheory.Function.Floor

/-! # Scalar algebra for the folded score -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

@[fun_prop]
lemma measurable_triangularFold : Measurable triangularFold := by
  unfold triangularFold
  have hfloor : Measurable fun t : ℝ => Int.floor ((t + 1) / 2) :=
    Int.measurable_floor.comp ((measurable_id.add_const 1).div_const 2)
  have hcast : Measurable fun t : ℝ => (Int.floor ((t + 1) / 2) : ℝ) :=
    (measurable_of_countable fun z : ℤ => (z : ℝ)).comp hfloor
  exact (measurable_id.sub (measurable_const.mul hcast)).abs

@[fun_prop]
lemma measurable_triangularWave : Measurable triangularWave := by
  unfold triangularWave
  let r : ℝ → ℝ := fun t => t - Int.floor t
  have hfloor : Measurable fun t : ℝ => Int.floor t := Int.measurable_floor
  have hcast : Measurable fun t : ℝ => (Int.floor t : ℝ) :=
    (measurable_of_countable fun z : ℤ => (z : ℝ)).comp hfloor
  have hr : Measurable r := measurable_id.sub hcast
  exact (measurable_const.mul hr).ite (measurableSet_le hr measurable_const)
    ((measurable_const.sub (measurable_const.mul hr)).ite
      (measurableSet_le hr measurable_const)
      ((measurable_const.mul hr).sub_const 4))

lemma triangularFold_eq_self {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    triangularFold t = t := by
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · have hf : Int.floor ((t + 1) / 2) = 0 := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith [ht.1]
    simp [triangularFold, hf, abs_of_nonneg ht.1]
  · norm_num [triangularFold, Int.floor_eq_iff]

lemma triangularFold_eq_neg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 0) :
    triangularFold t = -t := by
  have hf : Int.floor ((t + 1) / 2) = 0 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith [ht.1, ht.2]
  simp [triangularFold, hf, abs_of_nonpos ht.2]

lemma triangularFold_eq_two_sub {t : ℝ} (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    triangularFold t = 2 - t := by
  have hf : Int.floor ((t + 1) / 2) = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith [ht.1, ht.2]
  rw [triangularFold, hf]
  norm_num
  rw [abs_of_nonpos]
  · ring
  · linarith [ht.2]

lemma triangularWave_mem_Icc (t : ℝ) : triangularWave t ∈ Set.Icc (-1 : ℝ) 1 := by
  let r : ℝ := t - Int.floor t
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact sub_nonneg.mpr (Int.floor_le t)
  have hr1 : r < 1 := by
    dsimp only [r]
    have hf := Int.lt_floor_add_one t
    linarith
  change (if r ≤ 1 / 4 then 4 * r
    else if r ≤ 3 / 4 then 2 - 4 * r else 4 * r - 4) ∈ Set.Icc (-1 : ℝ) 1
  split
  next h => constructor <;> linarith
  next h =>
    split
    next h' => constructor <;> linarith
    next h' => constructor <;> linarith

lemma abs_localSign (b : Bool) : |localSign b| = 1 := by
  cases b <;> norm_num [localSign]

lemma signed_bump_sum_abs_le_one {K : ℕ}
    {Q : Fin K → Set (XSpace d)} {ψ : Fin K → XSpace d → ℝ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hψ : ∀ j x, 0 ≤ ψ j x ∧ ψ j x ≤ 1 ∧ (x ∉ Q j → ψ j x = 0))
    (θ : Fin K → Bool) (x : XSpace d) :
    |∑ j : Fin K, localSign (θ j) * ψ j x| ≤ 1 := by
  classical
  by_cases hex : ∃ j, ψ j x ≠ 0
  · obtain ⟨j, hj⟩ := hex
    have hxj : x ∈ Q j := by
      by_contra hx
      exact hj ((hψ j x).2.2 hx)
    have hzero (i : Fin K) (hij : i ≠ j) : ψ i x = 0 := by
      by_contra hi
      have hxi : x ∈ Q i := by
        by_contra hx
        exact hi ((hψ i x).2.2 hx)
      exact Set.disjoint_left.mp (hdisj i j hij) hxi hxj
    rw [Finset.sum_eq_single j]
    · rw [abs_mul, abs_localSign, one_mul, abs_of_nonneg (hψ j x).1]
      exact (hψ j x).2.1
    · intro i hi hij
      rw [hzero i hij, mul_zero]
    · simp
  · push Not at hex
    simp_rw [hex, mul_zero, Finset.sum_const_zero, abs_zero]
    norm_num

end CausalSmith.Experimentation.PilotscorePairingFrontier
