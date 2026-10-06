module
public import Causalean.Stat.Concentration.BoundedVariation.Variation

/-!
# Quantiles of a continuous variation control

A continuous nondecreasing control on the unit interval has a monotone
section over its range. Dyadic points in that range therefore have consistent
representatives even when the control has flat intervals.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- If a continuous control path on the unit interval is
[nondecreasing](hyp:hmono) and [zero at time zero](hyp:hzero), then [every
level between zero and its terminal value is attained at some time, and these
representative times can be chosen increasing in the level](goal).
-/
theorem exists_monotone_control_section (u : Path)
    (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0) :
    ∃ q : Set.Icc (0 : ℝ) (u timeOne) → Time,
      (∀ x, u (q x) = x.1) ∧ Monotone q := by
  /- The intermediate value theorem makes u surjective onto [0,u(1)].
  Choose one preimage for each level. Any choices at distinct levels are
  automatically ordered by monotonicity of u. A repeated dyadic level is
  literally the same argument of q, so plateaus cause no inconsistency. -/
  have h01 : timeZero ≤ timeOne := by
    change (0 : ℝ) ≤ 1
    norm_num
  have hpreimage (x : Set.Icc (0 : ℝ) (u timeOne)) :
      ∃ t : Time, u t = x.1 := by
    have hx : x.1 ∈ Set.Icc (u timeZero) (u timeOne) := by
      simpa only [hzero] using x.property
    obtain ⟨t, _, ht⟩ :=
      intermediate_value_Icc h01 u.continuous.continuousOn hx
    exact ⟨t, ht⟩
  choose q hq using hpreimage
  refine ⟨q, hq, ?_⟩
  intro x y hxy
  by_contra! hgt
  have hyx : y.1 ≤ x.1 := by
    rw [← hq x, ← hq y]
    exact hmono hgt.le
  have hxy' : x = y := Subtype.ext (le_antisymm hxy hyx)
  subst y
  exact (lt_irrefl _) hgt

end Causalean.Stat.Concentration.BoundedVariation
