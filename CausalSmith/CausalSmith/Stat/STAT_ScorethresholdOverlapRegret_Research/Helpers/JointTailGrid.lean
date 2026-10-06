module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTailDecomposition

/-! # Joint-tail bias — transition grid and crossing shells

Finite dyadic grids bracket each transition within a factor of two. Shells
crossing a transition are absorbed into the same two powers as the interior
regions, and a rounded upper cutoff retains the margin bound.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators

/-- A dyadic grid starting below a positive cutoff has a last point at or
below it, with the next point strictly above it. -/
-- @node: jointTail_dyadic_bracket
lemma jointTail_dyadic_bracket (q B : ℝ) (hq : 0 < q) (hqB : q ≤ B) :
    ∃ N : ℕ, q * (2 : ℝ) ^ N ≤ B ∧ B < 2 * (q * (2 : ℝ) ^ N) := by
  obtain ⟨N, hN, hnext⟩ := exists_nat_pow_near
    ((le_div_iff₀ hq).mpr (by simpa using hqB)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N, ?_, ?_⟩
  · simpa only [mul_comm] using (le_div_iff₀ hq).mp hN
  · have hn := (div_lt_iff₀ hq).mp hnext
    rw [pow_succ] at hn
    nlinarith

/-- Powers of two are increasing along the nonnegative dyadic grid. -/
-- @node: jointTail_dyadic_grid_mono
lemma jointTail_dyadic_grid_mono (q : ℝ) (hq : 0 ≤ q) {i j : ℕ}
    (hij : i ≤ j) : q * (2 : ℝ) ^ i ≤ q * (2 : ℝ) ^ j := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hq

/-- A shell whose lower endpoint is within a factor of two below a transition
has its power bounded by the transition power, with a fixed overshoot constant. -/
-- @node: jointTail_bracket_power
lemma jointTail_bracket_power (q B r : ℝ) (hq : 0 < q)
    (hqB : q ≤ B) (hBq : B ≤ 2 * q) :
    q ^ r ≤ max 1 ((2 : ℝ) ^ (-r)) * B ^ r := by
  have hB : 0 < B := hq.trans_le hqB
  by_cases hr : 0 ≤ r
  · exact (Real.rpow_le_rpow hq.le hqB hr).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hB.le _) (le_max_left _ _))
  · have hpow := Real.rpow_le_rpow_of_nonpos hB hBq (le_of_not_ge hr)
    rw [Real.mul_rpow (by norm_num) hq.le] at hpow
    have hinv : (2 : ℝ) ^ (-r) * (2 : ℝ) ^ r = 1 := by
      rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
    calc
      q ^ r = (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ r * q ^ r) := by rw [← mul_assoc, hinv, one_mul]
      _ ≤ (2 : ℝ) ^ (-r) * B ^ r :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by norm_num) _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hB.le _)

/-- The lower-region crossing shell is absorbed by the two headline powers.
This estimate covers either sign of the shell exponent, including zero. -/
-- @node: jointTail_lower_crossing_power
lemma jointTail_lower_crossing_power (α γ θ a q : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 < q)
    (hqB : q ≤ a ^ (γ / (γ + 1))) (hBq : a ^ (γ / (γ + 1)) ≤ 2 * q) :
    a ^ (α + 1) * q ^ (θ - α - 1) ≤
      max 1 ((2 : ℝ) ^ (-(θ - α - 1))) * (a ^ sLoc α γ θ + a ^ θ) := by
  calc
    _ ≤ a ^ (α + 1) * (max 1 ((2 : ℝ) ^ (-(θ - α - 1))) * 
        (a ^ (γ / (γ + 1))) ^ (θ - α - 1)) :=
      mul_le_mul_of_nonneg_left
        (jointTail_bracket_power q _ _ hq hqB hBq) (Real.rpow_nonneg ha.le _)
    _ = max 1 ((2 : ℝ) ^ (-(θ - α - 1))) * a ^ ((α + 1 + γ * θ) / (γ + 1)) := by
      rw [mul_left_comm, jointTail_lower_endpoint_power α γ θ a hγ ha]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (jointTail_intermediate_power α γ θ a hα hγ hθ ha ha1)
      (le_trans zero_le_one (le_max_left _ _))

/-- The middle-region crossing shell at the upper transition is bounded by
the local power, uniformly in the deletion level. -/
-- @node: jointTail_middle_crossing_power
lemma jointTail_middle_crossing_power (α γ θ a q : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 < a) (hq : 0 < q)
    (hqB : q ≤ a ^ (betaExp α γ θ / (betaExp α γ θ + 1)))
    (hBq : a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ 2 * q) :
    a * q ^ (θ + α / γ - 1) ≤ max 1 ((2 : ℝ) ^ (-(θ + α / γ - 1))) * a ^ sLoc α γ θ := by
  calc
    _ ≤ a * (max 1 ((2 : ℝ) ^ (-(θ + α / γ - 1))) * 
        (a ^ (betaExp α γ θ / (betaExp α γ θ + 1))) ^ (θ + α / γ - 1)) :=
      mul_le_mul_of_nonneg_left
        (jointTail_bracket_power q _ _ hq hqB hBq) ha.le
    _ = _ := by
      rw [mul_left_comm, jointTail_middle_upper_endpoint_power α γ θ a hα hγ hθ ha]

/-- Both transitions can be bracketed on the same dyadic grid, with ordered
indices and legal envelope cutoffs for every shell up to the upper bracket. -/
-- @node: jointTail_transition_grid
lemma jointTail_transition_grid (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hsmall : a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ 1 / 4) :
    ∃ L U : ℕ, L ≤ U ∧
      a * (2 : ℝ) ^ L ≤ a ^ (γ / (γ + 1)) ∧
      a ^ (γ / (γ + 1)) < 2 * (a * (2 : ℝ) ^ L) ∧
      a * (2 : ℝ) ^ U ≤ a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ∧
      a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) < 2 * (a * (2 : ℝ) ^ U) ∧
      ∀ k ≤ U, 2 * (a * (2 : ℝ) ^ k) ≤ 1 / 2 := by
  have hsc := jointTail_transition_scales α γ θ a hα hγ hθ ha ha1
  obtain ⟨L, hL, hLn⟩ := jointTail_dyadic_bracket a _ ha hsc.1
  obtain ⟨U, hU, hUn⟩ := jointTail_dyadic_bracket a _ ha (hsc.1.trans hsc.2.1)
  have hLU : L ≤ U := by
    by_contra hn
    have hUL : U + 1 ≤ L := by omega
    have hm := jointTail_dyadic_grid_mono a ha.le hUL
    rw [pow_succ] at hm
    nlinarith [hsc.2.1]
  refine ⟨L, U, hLU, hL, hLn, hU, hUn, ?_⟩
  intro k hk
  have hm := (jointTail_dyadic_grid_mono a ha.le hk).trans (hU.trans hsmall)
  linarith

/-- The margin bound at an arbitrary retained cutoff has the decreasing
upper-region shell power, with only public constants factored out. -/
-- @node: jointTail_margin_cutoff_power
lemma jointTail_margin_cutoff_power (α a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    (a / q) * (max Cm ((2 : ℝ) ^ α) * (2 * a / q) ^ α) =
      (max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) * (a ^ (α + 1) * q ^ (-α - 1)) := by
  rw [mul_div_assoc, Real.mul_rpow (by norm_num) (div_nonneg ha.le hq.le)]
  have hp := jointTail_lower_shell_power α 0 a q ha hq
  simp only [Real.rpow_zero, mul_one, zero_sub] at hp
  calc
    _ = (max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) * ((a / q) * (a / q) ^ α) := by ring
    _ = _ := by rw [hp]

/-- Rounding the upper transition down on a dyadic grid preserves the local
power for the entire final region, including atoms at its lower endpoint. -/
-- @node: jointTail_retained_rounded_upper_region
lemma jointTail_retained_rounded_upper_region (P : RowLaw) (α γ θ a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (hmargin : MarginCondition P α) (ha : 0 < a) (hq : 0 < q)
    (hqB : q ≤ a ^ (betaExp α γ θ / (betaExp α γ θ + 1)))
    (hBq : a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ 2 * q) :
    (∫ x, offsetG a P.logger x * 
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2 * offsetG a P.logger x then (1 : ℝ) else 0) ∂P.PX) ≤
      ((max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) * max 1 ((2 : ℝ) ^ (-(-α - 1)))) * 
        a ^ sLoc α γ θ := by
  have hK : 0 ≤ max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α := by
    apply mul_nonneg
    · exact (Real.rpow_nonneg (by norm_num) _).trans (le_max_right _ _)
    · positivity
  calc
    _ ≤ (a / q) * (max Cm ((2 : ℝ) ^ α) * (2 * a / q) ^ α) :=
      jointTail_retained_above_cutoff_integral_margin P α a q hwf hprob
        hα hmargin ha hq
    _ = (max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) * (a ^ (α + 1) * q ^ (-α - 1)) :=
      jointTail_margin_cutoff_power α a q ha hq
    _ ≤ (max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) * (a ^ (α + 1) * 
        (max 1 ((2 : ℝ) ^ (-(-α - 1))) * 
          (a ^ (betaExp α γ θ / (betaExp α γ θ + 1))) ^ (-α - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (jointTail_bracket_power q _ _ hq hqB hBq) (Real.rpow_nonneg ha.le _)) hK
    _ = _ := by
      rw [mul_left_comm (a ^ (α + 1)),
        jointTail_upper_endpoint_power α γ θ a hα hγ hθ ha]
      ring

/-- The actual bias integral obeys the transition-grid decomposition: deleted
mass, lower and middle shell powers, and a local-power final region. The shell
at the lower transition is kept explicitly by the inclusive index test. -/
-- @node: jointTail_bias_transition_grid_bound
lemma jointTail_bias_transition_grid_bound (P : RowLaw) (α γ θ a : ℝ) (L U : ℕ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (hmargin : MarginCondition P α) (henvelope : GlobalJointEnvelope P α γ θ)
    (hmag : ∀ᵐ x ∂P.PX, effectMagnitude P x ≤ 2)
    (ha : 0 < a) (hawindow : a ≤ co * (2 : ℝ) ^ γ)
    (hL : a * (2 : ℝ) ^ L ≤ a ^ (γ / (γ + 1)))
    (hLn : a ^ (γ / (γ + 1)) < 2 * (a * (2 : ℝ) ^ L))
    (hU : a * (2 : ℝ) ^ U ≤ a ^ (betaExp α γ θ / (betaExp α γ θ + 1)))
    (hUn : a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ 2 * (a * (2 : ℝ) ^ U))
    (hgrid : ∀ k ≤ U, 2 * (a * (2 : ℝ) ^ k) ≤ 1 / 2) :
    biasFunctional P a ≤ Co θ * (2 : ℝ) ^ α * a ^ θ + 
      (Co θ * (max 2 ((2 : ℝ) ^ (1 / γ))) ^ α * (2 : ℝ) ^ θ) * 
        (∑ k ∈ Finset.range U,
          if k ≤ L then a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)
          else a * (a * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) + 
      ((max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) * max 1 ((2 : ℝ) ^ (-(-α - 1)))) * 
        a ^ sLoc α γ θ := by
  have hs :
      (∑ k ∈ Finset.range U, ∫ x, offsetG a P.logger x * 
        (if a * (2 : ℝ) ^ k ≤ overlap P x ∧ overlap P x < 2 * (a * (2 : ℝ) ^ k) ∧
          0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2 * offsetG a P.logger x
          then (1 : ℝ) else 0) ∂P.PX) ≤
      (Co θ * (max 2 ((2 : ℝ) ^ (1 / γ))) ^ α * (2 : ℝ) ^ θ) * 
        (∑ k ∈ Finset.range U,
          if k ≤ L then a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)
          else a * (a * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hqa := jointTail_dyadic_grid_mono a ha.le (Nat.zero_le k)
    simp only [pow_zero, mul_one] at hqa
    have hhalf := hgrid k (Nat.le_of_lt (Finset.mem_range.mp hk))
    by_cases hkl : k ≤ L
    · rw [if_pos hkl]
      have hcut := (jointTail_dyadic_grid_mono a ha.le hkl).trans hL
      simpa only [mul_assoc] using jointTail_retained_lower_shell P α γ θ a
        (a * (2 : ℝ) ^ k) hwf hprob hα hγ hmargin henvelope ha hqa
        (by positivity) hhalf hcut
    · rw [if_neg hkl]
      have hmono := jointTail_dyadic_grid_mono a ha.le (show L + 1 ≤ k by omega)
      rw [pow_succ] at hmono
      have hcut : a ^ (γ / (γ + 1)) ≤ a * (2 : ℝ) ^ k := by nlinarith
      simpa only [mul_assoc] using jointTail_retained_middle_shell P α γ θ a
        (a * (2 : ℝ) ^ k) hwf hprob hα hγ hmargin henvelope ha hqa
        (by positivity) hhalf hcut
  have hd := jointTail_deleted_negative_bound P α γ θ a hprob henvelope
    hmag ha hawindow
  have hu := jointTail_retained_rounded_upper_region P α γ θ a (a * (2 : ℝ) ^ U)
    hwf hprob hα hγ hθ hmargin ha (by positivity) hU hUn
  unfold biasFunctional
  rw [jointTail_retained_dyadic_decomposition P a a U hwf hprob ha ha]
  exact (add_le_add hd (add_le_add hs hu)).trans_eq (by ring)

/-- Summing the rounded transition grid preserves the two headline powers.
The lower crossing shell is retained separately from the interior series. -/
-- @node: jointTail_rounded_grid_sum
lemma jointTail_rounded_grid_sum (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (L U : ℕ),
      0 < a → a ≤ 1 → L ≤ U →
      a * (2 : ℝ) ^ L ≤ a ^ (γ / (γ + 1)) →
      a ^ (γ / (γ + 1)) ≤ 2 * (a * (2 : ℝ) ^ L) →
      a * (2 : ℝ) ^ U ≤ a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) →
      (∑ k ∈ Finset.range U,
        if k ≤ L then a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)
        else a * (a * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) ≤
      C * (a ^ sLoc α γ θ + a ^ θ) := by
  obtain ⟨Cl, hCl, hl⟩ := jointTail_lower_region_sum α γ θ hα hγ hθ
  obtain ⟨Cm, hCm, hm⟩ := jointTail_middle_region_sum α γ θ hα hγ hθ
  let K := max 1 ((2 : ℝ) ^ (-(θ - α - 1)))
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  refine ⟨Cl + K + Cm, by positivity, ?_⟩
  intro a L U ha ha1 hLU hL hLn hU
  have hlower := hl a L ha ha1 hL
  have hcross := jointTail_lower_crossing_power α γ θ a (a * (2 : ℝ) ^ L)
    hα hγ hθ ha ha1 (by positivity) hL hLn
  have hprefix : (∑ k ∈ Finset.range (L + 1),
      a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)) ≤
      (Cl + K) * (a ^ sLoc α γ θ + a ^ θ) := by
    rw [Finset.sum_range_succ]
    exact (add_le_add hlower hcross).trans_eq (by dsimp [K]; ring)
  by_cases hUL : U ≤ L + 1
  · have hsum : (∑ k ∈ Finset.range U,
        if k ≤ L then a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)
        else a * (a * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) =
        ∑ k ∈ Finset.range U, a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (show k ≤ L by have := Finset.mem_range.mp hk; omega)]
    rw [hsum]
    have hext := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun k => a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1))
      (Finset.range_mono hUL)
      (fun k _ _ => mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by positivity) _))
    exact (hext.trans hprefix).trans (by
      have hn : 0 ≤ a ^ sLoc α γ θ + a ^ θ := by positivity
      nlinarith [mul_nonneg hCm hn])
  · have hcut : a ^ (γ / (γ + 1)) ≤ a * (2 : ℝ) ^ (L + 1) := by
      rw [pow_succ]
      nlinarith
    have hgrid : (a * (2 : ℝ) ^ (L + 1)) * (2 : ℝ) ^ (U - (L + 1)) ≤
        a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega : L + 1 ≤ U)]
      exact hU
    have hmiddle := hm a (a * (2 : ℝ) ^ (L + 1)) (U - (L + 1)) ha ha1 hcut hgrid
    have hsplit : (∑ k ∈ Finset.range U,
        if k ≤ L then a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)
        else a * (a * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) =
        (∑ k ∈ Finset.range (L + 1), a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)) +
        (∑ k ∈ Finset.range (U - (L + 1)),
          a * ((a * (2 : ℝ) ^ (L + 1)) * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) := by
      conv_lhs => rw [← Nat.add_sub_of_le (by omega : L + 1 ≤ U)]
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos (show k ≤ L by have := Finset.mem_range.mp hk; omega)]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [if_neg (by omega : ¬ L + 1 + k ≤ L), pow_add, ← mul_assoc]
    rw [hsplit]
    exact (add_le_add hprefix hmiddle).trans_eq (by ring)

end CausalSmith.Stat.ScorethresholdOverlapRegret
