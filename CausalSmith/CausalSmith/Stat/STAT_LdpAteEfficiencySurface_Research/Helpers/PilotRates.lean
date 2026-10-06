module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Sqrt

/-! # Square-root pilot sample size

The integer square-root pilot size diverges, remains asymptotically negligible,
and lies strictly between zero and the full sample size once `n ≥ 2`.
-/

@[expose] public section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter
open scoped Topology

/-- The integer square-root pilot sample size tends to infinity. [The stated result](goal) follows. -/
-- @node: natSqrt_pilotDiverges
lemma natSqrt_pilotDiverges : PilotDiverges Nat.sqrt := by
  rw [PilotDiverges, tendsto_atTop_atTop]
  intro b
  refine ⟨b * b, ?_⟩
  intro a ha
  exact Nat.le_sqrt.mpr ha

/-- The integer square-root pilot is sublinear and is a nonempty proper split
for every sample size at least two. [The stated result](goal) follows. -/
-- @node: natSqrt_pilotSublinear
lemma natSqrt_pilotSublinear : PilotSublinear Nat.sqrt := by
  constructor
  · have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    apply squeeze_zero'
      (Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      ?_ (tendsto_inv_atTop_zero.comp hsqrt)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnreal
    calc
      (Nat.sqrt n : ℝ) / n ≤ Real.sqrt (n : ℝ) / n :=
        div_le_div_of_nonneg_right Real.nat_sqrt_le_real_sqrt hnreal.le
      _ = (Real.sqrt (n : ℝ))⁻¹ := by
        nth_rewrite 2 [← Real.mul_self_sqrt hnreal.le]
        field_simp
  · intro n hn
    constructor
    · exact Nat.le_sqrt.mpr (by omega)
    · exact Nat.sqrt_lt_self (by omega)

end CausalSmith.Stat.LdpAteEfficiencySurface
