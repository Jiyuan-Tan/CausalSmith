module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerDepthTuning

/-! # Combining the two common-kernel lower-bound regimes

Equations (52)--(53) compare the hidden coordinate with the parametric
coordinate and assemble the capped frontier from the two component bounds.
These are numerical assembly lemmas; the experiment bounds remain separate
obligations of the common-kernel theorem.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

/-- The hidden-to-parametric ratio has the power form used in (52). For [the q](hyp:q),
[the observed prefix](hyp:u), [the rate exponent](hyp:beta), [the q assumption](hyp:hq), and
[the observed prefix assumption](hyp:hu), this establishes
[the lower coordinate ratio factorization result](goal). -/
-- @node: lower_coordinate_ratio_factorization
lemma lower_coordinate_ratio_factorization (q u beta : ℝ)
    (hq : 0 < q) (hu : 0 < u) :
    q ^ (1 - beta) * u ^ (beta / 2) =
      (q ^ 2 / u) ^ ((1 - beta) / 2) * Real.sqrt u := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq,
    Real.rpow_def_of_pos hu, Real.rpow_def_of_pos (by positivity : 0 < q ^ 2 / u),
    Real.rpow_def_of_pos hu, ← Real.exp_add, ← Real.exp_add,
    Real.log_div (pow_ne_zero _ hq.ne') hu.ne', Real.log_pow]
  congr 1
  ring

/-- Outside the small-information regime the hidden coordinate is bounded by a fixed multiple of
the parametric coordinate, as in (52). For [the q](hyp:q), [the observed prefix](hyp:u),
[the rate exponent](hyp:beta), [the signal parameter](hyp:eta), [the q assumption](hyp:hq),
[the observed prefix assumption](hyp:hu), [the rate exponent assumption](hyp:hbeta),
[the signal parameter assumption](hyp:heta), and [the large assumption](hyp:hlarge), this
establishes [the lower hidden coordinate bound parametric result](goal). -/
-- @node: lower_hidden_coordinate_le_parametric
lemma lower_hidden_coordinate_le_parametric (q u beta eta : ℝ)
    (hq : 0 < q) (hu : 0 < u) (hbeta : beta ≤ 1) (heta : 0 < eta)
    (hlarge : eta * q ^ 2 ≤ u) :
    q ^ (1 - beta) * u ^ (beta / 2) ≤
      eta ^ (-((1 - beta) / 2)) * Real.sqrt u := by
  have hratio : q ^ 2 / u ≤ eta⁻¹ := by
    apply (div_le_iff₀ hu).mpr
    apply (le_inv_mul_iff₀ heta).mpr
    simpa only [mul_comm] using hlarge
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ q ^ 2 / u)
    hratio (by linarith : 0 ≤ (1 - beta) / 2)
  rw [← Real.rpow_neg_eq_inv_rpow] at hp
  rw [lower_coordinate_ratio_factorization q u beta hq hu]
  exact mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg u)

/-- Two component bounds give half their smaller constant times the sum, which is the numerical
step in (53). For [the c1](hyp:c1), [the c2](hyp:c2), [the observed state](hyp:x),
[the y](hyp:y), [the r](hyp:R), [the observed state assumption](hyp:hx),
[the y assumption](hyp:hy), [the 1 assumption](hyp:h1), and [the 2 assumption](hyp:h2), this
establishes [the lower two component sum bound result](goal). -/
-- @node: lower_two_component_sum_le
lemma lower_two_component_sum_le (c1 c2 x y R : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : c1 * x ≤ R) (h2 : c2 * y ≤ R) :
    min c1 c2 / 2 * (x + y) ≤ R := by
  have hx' := (mul_le_mul_of_nonneg_right (min_le_left c1 c2) hx).trans h1
  have hy' := (mul_le_mul_of_nonneg_right (min_le_right c1 c2) hy).trans h2
  nlinarith

/-- A dominated hidden coordinate allows the parametric bound to control the entire frontier
outside the small-information regime. For [the c](hyp:c), [the transition kernel](hyp:K),
[the observed state](hyp:x), [the y](hyp:y), [the r](hyp:R), [the c assumption](hyp:hc),
[the transition kernel assumption](hyp:hK), [the y assumption](hyp:hy), and
[the r assumption](hyp:hR), this establishes [the lower dominated frontier bound result](goal). -/
-- @node: lower_dominated_frontier_le
lemma lower_dominated_frontier_le (c K x y R : ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hy : y ≤ K * x) (hR : c * x ≤ R) :
    c / (1 + K) * min 1 (x + y) ≤ R := by
  have hden : 0 < 1 + K := by linarith
  calc
    _ ≤ c / (1 + K) * (x + y) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ ≤ c / (1 + K) * ((1 + K) * x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = c * x := by field_simp
    _ ≤ R := hR

/-- The regime-combination constant in the lower-bound roadmap is positive. For
[the c1](hyp:c1), [the c2](hyp:c2), [the transition kernel](hyp:K),
[the c1 assumption](hyp:hc1), [the c2 assumption](hyp:hc2), and
[the transition kernel assumption](hyp:hK), this establishes
[the lower combined constant positivity result](goal). -/
-- @node: lower_combined_constant_pos
lemma lower_combined_constant_pos (c1 c2 K : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hK : 0 ≤ K) :
    0 < min c1 (min (c1 / (1 + K)) (min c1 c2 / 2)) := by
  apply lt_min hc1
  exact lt_min (div_pos hc1 (by linarith)) (div_pos (lt_min hc1 hc2) (by norm_num))

/-- Given the proved component inequalities, the three numerical regimes and the zero-overlap
endpoint assemble the exact capped frontier. For [the q](hyp:q), [the observed prefix](hyp:u),
[the rate exponent](hyp:beta), [the signal parameter](hyp:eta), [the c1](hyp:c1),
[the c2](hyp:c2), [the r](hyp:R), [the q assumption](hyp:hq),
[the observed prefix assumption](hyp:hu), [the rate exponent assumption](hyp:hbeta),
[the signal parameter assumption](hyp:heta), [the c1 assumption](hyp:hc1),
[the c2 assumption](hyp:hc2), [the param assumption](hyp:hparam), and
[the hidden assumption](hyp:hhidden), this establishes
[the lower frontier of component bounds result](goal). -/
-- @node: lower_frontier_of_component_bounds
lemma lower_frontier_of_component_bounds (q u beta eta c1 c2 R : ℝ)
    (hq : 0 ≤ q) (hu : 0 < u) (hbeta : beta < 1) (heta : 0 < eta)
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hparam : c1 * min 1 (Real.sqrt u) ≤ R)
    (hhidden : 0 < q → u ≤ eta * q ^ 2 →
      c2 * (q ^ (1 - beta) * u ^ (beta / 2)) ≤ R) :
    let K := eta ^ (-((1 - beta) / 2))
    min c1 (min (c1 / (1 + K)) (min c1 c2 / 2)) *
      min 1 (Real.sqrt u + q ^ (1 - beta) * u ^ (beta / 2)) ≤ R := by
  dsimp only
  let K := eta ^ (-((1 - beta) / 2))
  let c := min c1 (min (c1 / (1 + K)) (min c1 c2 / 2))
  let y := q ^ (1 - beta) * u ^ (beta / 2)
  have hK : 0 ≤ K := Real.rpow_nonneg heta.le _
  have hc : 0 ≤ c := (lower_combined_constant_pos c1 c2 K hc1 hc2 hK).le
  have hc_c1 : c ≤ c1 := min_le_left _ _
  have hc_dom : c ≤ c1 / (1 + K) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hc_sum : c ≤ min c1 c2 / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hy : 0 ≤ y := mul_nonneg (Real.rpow_nonneg hq _) (Real.rpow_nonneg hu.le _)
  change c * min 1 (Real.sqrt u + y) ≤ R
  by_cases hu1 : 1 ≤ u
  · have hs : 1 ≤ Real.sqrt u := by
      simpa using Real.sqrt_le_sqrt hu1
    have hp : c1 ≤ R := by simpa [min_eq_left hs] using hparam
    calc
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hc
      _ ≤ c1 := by simpa using hc_c1
      _ ≤ R := hp
  · have hs : Real.sqrt u ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (le_of_not_ge hu1)
    have hp : c1 * Real.sqrt u ≤ R := by
      simpa [min_eq_right hs] using hparam
    by_cases hq0 : q = 0
    · have hy0 : y = 0 := by
        dsimp [y]
        rw [hq0, Real.zero_rpow (by linarith : 1 - beta ≠ 0), zero_mul]
      rw [hy0, add_zero, min_eq_right hs]
      exact (mul_le_mul_of_nonneg_right hc_c1 (Real.sqrt_nonneg u)).trans hp
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      by_cases hsmall : u ≤ eta * q ^ 2
      · have hb := lower_two_component_sum_le c1 c2 (Real.sqrt u) y R
          (Real.sqrt_nonneg u) hy hp (hhidden hqpos hsmall)
        calc
          _ ≤ c * (Real.sqrt u + y) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hc
          _ ≤ min c1 c2 / 2 * (Real.sqrt u + y) :=
            mul_le_mul_of_nonneg_right hc_sum (add_nonneg (Real.sqrt_nonneg u) hy)
          _ ≤ R := hb
      · have hdom : y ≤ K * Real.sqrt u :=
          lower_hidden_coordinate_le_parametric q u beta eta hqpos hu hbeta.le heta
            (le_of_not_ge hsmall)
        exact (mul_le_mul_of_nonneg_right hc_dom
          (le_min (by norm_num) (add_nonneg (Real.sqrt_nonneg u) hy))).trans
            (lower_dominated_frontier_le c1 K _ y R hc1.le hK hdom hp)

end CausalSmith.Stat.PomdpPolicyclassRegret
