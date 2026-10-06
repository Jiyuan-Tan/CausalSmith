module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Schedule and bias rates for the upper bound

These are steps (7)–(8) of the upper-bound roadmap: the deletion schedule
eventually leaves its cap, and the uniform joint-tail bias and sampling scale
both have the stated risk power. The expected-regret peeling step is separate.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

/-- The public bias exponent is strictly positive. -/
-- @node: upperRates_sExp_pos
lemma upperRates_sExp_pos (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    0 < sExp α γ θ := by
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  have hs : 0 < sLoc α γ θ := by unfold sLoc; positivity
  exact lt_min hs hθ

/-- The uncapped deletion power tends to zero. -/
-- @node: upperRates_power_tendsto_zero
lemma upperRates_power_tendsto_zero (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / (sExp α γ θ + 1))))
      Filter.atTop (nhds 0) := by
  have hs := upperRates_sExp_pos α γ θ hα hγ hθ
  exact (tendsto_rpow_neg_atTop (by positivity : 0 < 1 / (sExp α γ θ + 1))).comp
    tendsto_natCast_atTop_atTop

/-- Eventually the schedule is its uncapped power, positive and below any
fixed positive bias radius. -/
-- @node: upperRates_schedule_eventually
lemma upperRates_schedule_eventually (α γ θ a0 : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (ha0 : 0 < a0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < n ∧
      deletionSchedule α γ θ n = (n : ℝ) ^ (-(1 / (sExp α γ θ + 1))) ∧
      0 < deletionSchedule α γ θ n ∧
      deletionSchedule α γ θ n ≤ min a0 (1/4) := by
  have hsmall := (upperRates_power_tendsto_zero α γ θ hα hγ hθ).eventually_lt_const
    (lt_min ha0 (by norm_num : (0 : ℝ) < 1/4))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with n hsmall hn
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hcap : (n : ℝ) ^ (-(1 / (sExp α γ θ + 1))) ≤ 1/4 :=
    hsmall.le.trans (min_le_right _ _)
  have he : deletionSchedule α γ θ n =
      (n : ℝ) ^ (-(1 / (sExp α γ θ + 1))) := min_eq_right hcap
  refine ⟨hn0, he, ?_, ?_⟩
  · rw [he]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  · rw [he]
    exact hsmall.le

/-- On the uncapped schedule the bias power equals the risk power exactly. -/
-- @node: upperRates_schedule_bias_power
lemma upperRates_schedule_bias_power (α γ θ : ℝ) (n : ℕ) (hn : 0 < n)
    (he : deletionSchedule α γ θ n = (n : ℝ) ^ (-(1 / (sExp α γ θ + 1)))) :
    deletionSchedule α γ θ n ^ sExp α γ θ = (n : ℝ) ^ (-rExp α γ θ) := by
  rw [he, ← Real.rpow_mul (Nat.cast_pos.mpr hn).le]
  congr 1
  unfold rExp
  ring

/-- On the uncapped schedule the inverse effective sample size equals the
same risk power. -/
-- @node: upperRates_schedule_sampling_power
lemma upperRates_schedule_sampling_power (α γ θ : ℝ) (n : ℕ)
    (hs : 0 < sExp α γ θ) (hn : 0 < n)
    (he : deletionSchedule α γ θ n = (n : ℝ) ^ (-(1 / (sExp α γ θ + 1)))) :
    ((n : ℝ) * deletionSchedule α γ θ n)⁻¹ = (n : ℝ) ^ (-rExp α γ θ) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hprod : (n : ℝ) * deletionSchedule α γ θ n =
      (n : ℝ) ^ (1 - 1 / (sExp α γ θ + 1)) := by
    rw [he, sub_eq_add_neg, Real.rpow_add hn', Real.rpow_one]
  rw [hprod, ← Real.rpow_neg hn'.le]
  congr 1
  unfold rExp
  field_simp
  ring

/-- For deletion levels at most one, both tail powers are bounded by the
minimum exponent's power. -/
-- @node: upperRates_bias_powers_le
lemma upperRates_bias_powers_le (α γ θ a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ sLoc α γ θ + a ^ θ ≤ 2 * a ^ sExp α γ θ := by
  have hl := Real.rpow_le_rpow_of_exponent_ge ha ha1
    (show sExp α γ θ ≤ sLoc α γ θ from min_le_left _ _)
  have hh := Real.rpow_le_rpow_of_exponent_ge ha ha1
    (show sExp α γ θ ≤ θ from min_le_right _ _)
  linarith

/-- The uniform joint-tail bias along the actual deletion schedule has the
claimed risk power, uniformly over every legal law and supplied logger. -/
-- @node: upperRates_uniform_schedule_bias
lemma upperRates_uniform_schedule_bias (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (P : RowLaw) (e : ℝ → ℝ), LawClass α γ θ n P e →
        biasFunctional P (deletionSchedule α γ θ n) ≤ C * (n : ℝ) ^ (-rExp α γ θ) := by
  obtain ⟨C, a0, hC, ha0, hb⟩ := (joint_tail_bias α γ θ hα hγ hθ).1
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [upperRates_schedule_eventually α γ θ a0 hα hγ hθ ha0]
    with n hn
  intro P e hP
  have ha0' := hn.2.2.2.trans (min_le_left _ _)
  have ha1 : deletionSchedule α γ θ n ≤ 1 :=
    (hn.2.2.2.trans (min_le_right _ _)).trans (by norm_num)
  calc
    _ ≤ C * (deletionSchedule α γ θ n ^ sLoc α γ θ +
        deletionSchedule α γ θ n ^ θ) := hb n P e _ hP hn.2.2.1 ha0'
    _ ≤ C * (2 * deletionSchedule α γ θ n ^ sExp α γ θ) :=
      mul_le_mul_of_nonneg_left (upperRates_bias_powers_le α γ θ _ hn.2.2.1 ha1) hC
    _ = _ := by rw [upperRates_schedule_bias_power α γ θ n hn.1 hn.2.1]; ring

/-- The entire bias-plus-sampling remainder in roadmap step (6) has the
uniform risk power under the chosen schedule. -/
-- @node: upperRates_uniform_remainder
lemma upperRates_uniform_remainder (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (P : RowLaw) (e : ℝ → ℝ), LawClass α γ θ n P e →
        biasFunctional P (deletionSchedule α γ θ n) +
          ((n : ℝ) * deletionSchedule α γ θ n)⁻¹ ≤ C * (n : ℝ) ^ (-rExp α γ θ) := by
  obtain ⟨C, hC, hb⟩ := upperRates_uniform_schedule_bias α γ θ hα hγ hθ
  refine ⟨C+1, by positivity, ?_⟩
  filter_upwards [hb, upperRates_schedule_eventually α γ θ 1 hα hγ hθ zero_lt_one]
    with n hbound hn
  intro P e hP
  rw [upperRates_schedule_sampling_power α γ θ n
    (upperRates_sExp_pos α γ θ hα hγ hθ) hn.1 hn.2.1]
  calc
    _ ≤ C * (n : ℝ) ^ (-rExp α γ θ) + (n : ℝ) ^ (-rExp α γ θ) :=
      add_le_add (hbound P e hP) le_rfl
    _ = _ := by ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
