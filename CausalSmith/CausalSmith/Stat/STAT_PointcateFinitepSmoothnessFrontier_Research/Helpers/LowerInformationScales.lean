module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerRegularity

/-! Optimized rare-mark scales, target separation, and the numerical information budget. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- The interaction denominator is positive and at most two in the interaction region. -/
-- @node: lower_denominator_bounds
lemma lower_denominator_bounds (hκ : κ.Valid) (hb : boundary κ ≤ 1) :
    0 < lowerDenom κ ∧ lowerDenom κ ≤ 2 := by
  have hp : 0 < κ.p - 1 := sub_pos.mpr hκ.1.1
  have hq : 0 < qExp κ := div_pos hp (by linarith [hκ.1.1])
  have ha := hκ.2.1.1
  have hβ := hκ.2.2.1.1
  have hg := hκ.2.2.2.1
  have hs : 0 < sumReg κ := by unfold sumReg; positivity
  have hα : 2*κ.α ≤ 2*κ.α/(κ.p-1) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [hκ.1.2]
  have hid : boundary κ = sumReg κ/κ.γ + 2*κ.α/(κ.p-1) + κ.β/qExp κ := by
    unfold boundary qExp
    field_simp
    ring
  rw [hid] at hb
  unfold lowerDenom
  exact ⟨by positivity, by linarith⟩

/-- The optimized spacing makes the all-size geometric argument at most one quarter. -/
-- @node: lower_component_series_argument
lemma lower_component_series_argument (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    0 ≤ 54*(n : ℝ)*lowerEll κ n ∧ 54*(n : ℝ)*lowerEll κ n ≤ 1/4 := by
  have hd := lower_denominator_bounds κ hκ hb
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have he : -2/lowerDenom κ ≤ (-1 : ℝ) := by
    apply (div_le_iff₀ hd.1).mpr
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 he
  rw [Real.rpow_neg_one] at hpow
  have hc : 0 < lowerC κ := by unfold lowerC; positivity
  have hsmall : lowerC κ ≤ 1/1000 := min_le_left _ _
  have hprod : (n : ℝ)*lowerEll κ n ≤ lowerC κ := by
    unfold lowerEll
    calc
      _ ≤ (n : ℝ)*(lowerC κ*(n : ℝ)⁻¹) := by gcongr
      _ = lowerC κ := by field_simp
  have hell := lowerEll_pos κ n (by omega)
  exact ⟨by positivity, by linarith⟩

/-- The finite-p rare-mark weight keeps the exact moment-dependent power. -/
-- @node: lower_information_weight_identity
lemma lower_information_weight_identity (hκ : κ.Valid) (hn : 2 ≤ n) :
    lowerA κ n^2 * lowerB κ n^2 * lowerAmplitude κ n^(κ.p-2) =
      (1024 : ℝ)^(-(2+1/qExp κ)) * lowerEll κ n^(2*κ.α+κ.β/qExp κ) := by
  have he := (lower_scale_small κ n hκ hn).1.1
  have hb0 := (lower_scale_small κ n hκ hn).2.2.1
  have hp : κ.p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hκ.1.1)
  have hpp : κ.p ≠ 0 := ne_of_gt (by linarith [hκ.1.1] : 0 < κ.p)
  have hexp : 2 + (-1/(κ.p-1))*(κ.p-2) = 1/qExp κ := by
    unfold qExp
    field_simp
    ring
  rw [lowerAmplitude, ← Real.rpow_mul hb0.le, ← Real.rpow_natCast (lowerA κ n) 2,
    ← Real.rpow_natCast (lowerB κ n) 2, mul_assoc, ← Real.rpow_add hb0]
  norm_num only [Nat.cast_ofNat]
  rw [hexp]
  unfold lowerA lowerB
  rw [Real.div_rpow (Real.rpow_nonneg he.le _) (by norm_num),
    Real.div_rpow (Real.rpow_nonneg he.le _) (by norm_num),
    ← Real.rpow_mul he.le, ← Real.rpow_mul he.le]
  rw [div_mul_div_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1024),
    ← Real.rpow_add he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1024)]
  ring

/-- Optimization cancels the sample-size power in the information budget. -/
-- @node: lower_information_scale_identity
lemma lower_information_scale_identity (hκ : κ.Valid) (hn : 2 ≤ n) :
    (n : ℝ)^2 * lowerH κ n * lowerEll κ n *
      lowerEll κ n^(2*κ.α+κ.β/qExp κ) = lowerC κ^lowerDenom κ := by
  have he := (lower_scale_small κ n hκ hn).1.1
  have hp : 0 < κ.p-1 := sub_pos.mpr hκ.1.1
  have hq : 0 < qExp κ := div_pos hp (by linarith [hκ.1.1])
  have ha := hκ.2.1.1
  have hβ := hκ.2.2.1.1
  have hg := hκ.2.2.2.1
  have hs : 0 < sumReg κ := by unfold sumReg; positivity
  have hd : 0 < lowerDenom κ := by unfold lowerDenom; positivity
  have hc : 0 < lowerC κ := by unfold lowerC; positivity
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpower : lowerH κ n * lowerEll κ n * lowerEll κ n^(2*κ.α+κ.β/qExp κ) =
      lowerEll κ n^lowerDenom κ := by
    change lowerEll κ n^(sumReg κ/κ.γ) * lowerEll κ n * _ = _
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one (lowerEll κ n)]
    rw [← Real.rpow_add he, ← Real.rpow_add he]
    congr 1
    unfold lowerDenom
    ring
  rw [mul_assoc ((n : ℝ)^2) (lowerH κ n), mul_assoc ((n : ℝ)^2), hpower,
    lowerEll, Real.mul_rpow hc.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
  rw [show (-2/lowerDenom κ)*lowerDenom κ = -2 by field_simp]
  rw [Real.rpow_neg hn0.le, Real.rpow_two]
  field_simp

/-- The optimized squared Hellinger budget is bounded by two to the minus sixteen. -/
-- @node: lower_information_budget
lemma lower_information_budget (hκ : κ.Valid) (hn : 2 ≤ n) :
    (2 : ℝ)^24 * (n : ℝ)^2 * lowerH κ n * lowerEll κ n *
      lowerA κ n^2 * lowerB κ n^2 * lowerAmplitude κ n^(κ.p-2) ≤ 1/65536 := by
  have hp : 0 < κ.p-1 := sub_pos.mpr hκ.1.1
  have hq : 0 < qExp κ := div_pos hp (by linarith [hκ.1.1])
  have hqsmall : qExp κ ≤ 1/2 := by
    unfold qExp
    apply (div_le_iff₀ (by linarith [hκ.1.1] : 0 < κ.p)).mpr
    linarith [hκ.1.2]
  have hinv : 2 ≤ 1/qExp κ := (le_div_iff₀ hq).mpr (by linarith)
  have ha := hκ.2.1.1
  have hβ := hκ.2.2.1.1
  have hg := hκ.2.2.2.1
  have hs : 0 < sumReg κ := by unfold sumReg; positivity
  have hd : 0 ≤ lowerDenom κ := by unfold lowerDenom; positivity
  have hc : 0 ≤ lowerC κ := by unfold lowerC; positivity
  have hc1 : lowerC κ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcpow := Real.rpow_le_one hc hc1 hd
  have h1024 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 1024)
    (show -(2+1/qExp κ) ≤ (-4 : ℝ) by linarith)
  have hidentity : (2 : ℝ)^24 * (n : ℝ)^2 * lowerH κ n * lowerEll κ n *
      lowerA κ n^2 * lowerB κ n^2 * lowerAmplitude κ n^(κ.p-2) =
      (2 : ℝ)^24 * (1024 : ℝ)^(-(2+1/qExp κ)) * lowerC κ^lowerDenom κ := by
    calc
      _ = (2 : ℝ)^24 * ((n : ℝ)^2 * lowerH κ n * lowerEll κ n) *
          (lowerA κ n^2 * lowerB κ n^2 * lowerAmplitude κ n^(κ.p-2)) := by ring
      _ = _ := by
        rw [lower_information_weight_identity κ n hκ hn]
        rw [show (2 : ℝ)^24 * ((n : ℝ)^2 * lowerH κ n * lowerEll κ n) *
            ((1024 : ℝ)^(-(2+1/qExp κ)) * lowerEll κ n^(2*κ.α+κ.β/qExp κ)) =
            (2 : ℝ)^24 * (1024 : ℝ)^(-(2+1/qExp κ)) *
            ((n : ℝ)^2 * lowerH κ n * lowerEll κ n * lowerEll κ n^(2*κ.α+κ.β/qExp κ)) by ring]
        rw [lower_information_scale_identity κ n hκ hn]
  rw [hidentity]
  calc
    _ ≤ (2 : ℝ)^24 * (1024 : ℝ)^(-4 : ℝ) * 1 := by gcongr
    _ = 1/65536 := by norm_num

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
