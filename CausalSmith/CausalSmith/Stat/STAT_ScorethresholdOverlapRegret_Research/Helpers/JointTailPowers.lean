module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScoreIdentity
public import Mathlib.Algebra.Order.Field.GeomSum

/-! # Joint-tail bias — transition powers and dyadic sums

Algebraic transition identities and geometric-series bounds for the three
retained-overlap regions in the joint-tail bias proof.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open scoped BigOperators

-- @node: jointTail_intermediate_exponent
/-- The dyadic transition power is controlled by one of the two headline powers. -/
lemma jointTail_intermediate_exponent (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    min (sLoc α γ θ) θ ≤ (α+1+γ*θ)/(γ+1) := by
  have hB : 0 < α + θ*γ := by positivity
  have hD : 0 < α + θ*γ + α*γ := by positivity
  have hγ1 : 0 < γ+1 := by positivity
  have hs : sLoc α γ θ =
      (α+1)*(α+θ*γ)/(α+θ*γ+α*γ) := by
    unfold sLoc betaExp
    field_simp
  by_cases hcase : θ ≤ α+1
  · apply le_trans (min_le_right _ _)
    apply (le_div_iff₀ hγ1).2
    nlinarith
  · apply le_trans (min_le_left _ _)
    rw [hs]
    apply (div_le_div_iff₀ hD hγ1).2
    have hθ1 : 1 < θ := by linarith
    have hfactor : 0 ≤ γ*θ*(α+γ*θ-γ) := by
      apply mul_nonneg (mul_nonneg hγ.le hθ.le)
      nlinarith [mul_pos hγ (by linarith : 0 < θ-1)]
    nlinarith [hfactor]

-- @node: jointTail_intermediate_power
/-- The transition term in the dyadic bias sum is absorbed by the two
headline powers for deletion levels at most one. -/
lemma jointTail_intermediate_power (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ ((α+1+γ*θ)/(γ+1)) ≤ a ^ (sLoc α γ θ) + a ^ θ := by
  have hm := jointTail_intermediate_exponent α γ θ hα hγ hθ
  by_cases hs : sLoc α γ θ ≤ θ
  · rw [min_eq_left hs] at hm
    exact (Real.rpow_le_rpow_of_exponent_ge ha ha1 hm).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))
  · have ht : θ ≤ sLoc α γ θ := le_of_lt (lt_of_not_ge hs)
    rw [min_eq_right ht] at hm
    exact (Real.rpow_le_rpow_of_exponent_ge ha ha1 hm).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))

-- @node: jointTail_transition_scales
/-- The two cutoffs in the dyadic shell split occur in the stated order. -/
lemma jointTail_transition_scales (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    a ≤ a ^ (γ/(γ+1)) ∧
      a ^ (γ/(γ+1)) ≤ a ^ (betaExp α γ θ/(betaExp α γ θ+1)) ∧
      a ^ (betaExp α γ θ/(betaExp α γ θ+1)) ≤ 1 := by
  have hd : 0 < α + θ*γ := by positivity
  have hb : 0 < betaExp α γ θ := by
    unfold betaExp
    positivity
  have hbg : betaExp α γ θ < γ := by
    unfold betaExp
    apply (div_lt_iff₀ hd).2
    nlinarith [mul_pos hγ hθ]
  have he0 : γ/(γ+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < γ+1)).2
    linarith
  have he1 : betaExp α γ θ/(betaExp α γ θ+1) ≤ γ/(γ+1) := by
    apply (div_le_div_iff₀ (by positivity : 0 < betaExp α γ θ+1)
      (by positivity : 0 < γ+1)).2
    nlinarith
  have he2 : 0 ≤ betaExp α γ θ/(betaExp α γ θ+1) := by positivity
  constructor
  · simpa using (Real.rpow_le_rpow_of_exponent_ge ha ha1 he0)
  constructor
  · exact Real.rpow_le_rpow_of_exponent_ge ha ha1 he1
  · calc
      a ^ (betaExp α γ θ/(betaExp α γ θ+1)) ≤
          (1:ℝ) ^ (betaExp α γ θ/(betaExp α γ θ+1)) :=
        Real.rpow_le_rpow ha.le ha1 he2
      _ = 1 := by simp

-- @node: jointTail_upper_transition_small
/-- A fixed positive deletion window keeps the upper dyadic transition below
one half, as required to split retained overlap shells. -/
lemma jointTail_upper_transition_small (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 ≤ a)
    (ha0 : a ≤ (1/2 : ℝ) ^
      ((betaExp α γ θ + 1) / betaExp α γ θ)) :
    a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ 1/2 := by
  have hb : 0 < betaExp α γ θ := by
    unfold betaExp
    positivity
  have he : 0 ≤ betaExp α γ θ / (betaExp α γ θ + 1) := by
    positivity
  have hcancel : ((betaExp α γ θ + 1) / betaExp α γ θ) *
      (betaExp α γ θ / (betaExp α γ θ + 1)) = 1 := by
    field_simp
  calc
    a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤
        ((1/2 : ℝ) ^ ((betaExp α γ θ + 1) / betaExp α γ θ)) ^
          (betaExp α γ θ / (betaExp α γ θ + 1)) :=
      Real.rpow_le_rpow ha ha0 he
    _ = 1/2 := by
      rw [← Real.rpow_mul (by norm_num), hcancel, Real.rpow_one]

-- @node: jointTail_transition_balance
/-- At the upper transition scale, the two competing shell powers agree. -/
lemma jointTail_transition_balance (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (a ^ (betaExp α γ θ/(betaExp α γ θ+1))) ^
        (θ+α/γ+α) = a^α := by
  have hd : α + θ*γ ≠ 0 := ne_of_gt (by positivity)
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have he : (betaExp α γ θ/(betaExp α γ θ+1)) *
      (θ+α/γ+α) = α := by
    unfold betaExp
    field_simp
    ring
  rw [← Real.rpow_mul ha, he]

-- @node: jointTail_lower_transition_balance
/-- At the lower transition scale, the effect and overlap cutoffs agree. -/
lemma jointTail_lower_transition_balance (γ a : ℝ)
    (hγ : 0 < γ) (ha : 0 ≤ a) :
    (a ^ (γ/(γ+1))) ^ (1+1/γ) = a := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have he : (γ/(γ+1)) * (1+1/γ) = 1 := by
    field_simp
  rw [← Real.rpow_mul ha, he, Real.rpow_one]

/-- The lower-region shell power at the first transition is the intermediate
power appearing in the dyadic bias sum. -/
-- @node: jointTail_lower_endpoint_power
lemma jointTail_lower_endpoint_power (α γ θ a : ℝ)
    (hγ : 0 < γ) (ha : 0 < a) :
    a ^ (α+1) * (a ^ (γ/(γ+1))) ^ (θ-α-1) =
      a ^ ((α+1+γ*θ)/(γ+1)) := by
  rw [← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  congr 1
  have hd : γ+1 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The middle-region shell power at the first transition agrees with the
lower-region endpoint, so both adjacent sums share one intermediate power. -/
-- @node: jointTail_middle_lower_endpoint_power
lemma jointTail_middle_lower_endpoint_power (α γ θ a : ℝ)
    (hγ : 0 < γ) (ha : 0 < a) :
    a * (a ^ (γ/(γ+1))) ^ (θ+α/γ-1) =
      a ^ ((α+1+γ*θ)/(γ+1)) := by
  rw [← Real.rpow_mul ha.le]
  conv_lhs => lhs; rw [← Real.rpow_one a]
  rw [← Real.rpow_add ha]
  congr 1
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hd : γ+1 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The middle-region shell power at the second transition has precisely the
local exponent, with no third rate branch. -/
-- @node: jointTail_middle_upper_endpoint_power
lemma jointTail_middle_upper_endpoint_power (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (ha : 0 < a) :
    a * (a ^ (betaExp α γ θ/(betaExp α γ θ+1))) ^ (θ+α/γ-1) =
      a ^ sLoc α γ θ := by
  rw [← Real.rpow_mul ha.le]
  conv_lhs => lhs; rw [← Real.rpow_one a]
  rw [← Real.rpow_add ha]
  congr 1
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hd : α+θ*γ ≠ 0 := ne_of_gt (by positivity)
  unfold sLoc betaExp
  field_simp
  ring

/-- The upper-region shell power at the second transition is the same local
power as the adjacent middle-region endpoint. -/
-- @node: jointTail_upper_endpoint_power
lemma jointTail_upper_endpoint_power (α γ θ a : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (ha : 0 < a) :
    a ^ (α+1) * (a ^ (betaExp α γ θ/(betaExp α γ θ+1))) ^ (-α-1) =
      a ^ sLoc α γ θ := by
  rw [← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  congr 1
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  have hd : betaExp α γ θ+1 ≠ 0 := ne_of_gt (by positivity)
  unfold sLoc
  field_simp
  ring

/-- A power on a dyadic overlap grid is a geometric progression. -/
-- @node: jointTail_dyadic_power_sum
lemma jointTail_dyadic_power_sum (q r : ℝ) (N : ℕ) (hq : 0 ≤ q) :
    (∑ k ∈ Finset.range N, (q * (2:ℝ)^k)^r) =
      q^r * ∑ k ∈ Finset.range N, ((2:ℝ)^r)^k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.mul_rpow hq (by positivity), ← Real.rpow_natCast_mul (by norm_num)]
  rw [mul_comm (k:ℝ) r, Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- A strictly decreasing dyadic shell sum is bounded by its lower endpoint
with a constant independent of the number of shells. -/
-- @node: jointTail_dyadic_power_sum_negative
lemma jointTail_dyadic_power_sum_negative (q r : ℝ) (N : ℕ)
    (hq : 0 ≤ q) (hr : r < 0) :
    (∑ k ∈ Finset.range N, (q * (2:ℝ)^k)^r) ≤
      q^r / (1-(2:ℝ)^r) := by
  have hx : (2:ℝ)^r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr
  have hsum : (∑ k ∈ Finset.range N, ((2:ℝ)^r)^k) ≤
      1 / (1-(2:ℝ)^r) := by
    simpa using (geom_sum_Ico_le_of_lt_one
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) r) hx (m := 0) (n := N))
  rw [jointTail_dyadic_power_sum q r N hq, div_eq_mul_inv]
  simpa only [one_div] using
    mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hq r)

/-- A strictly increasing dyadic shell sum is bounded by the upper grid
endpoint with a constant independent of the number of shells. -/
-- @node: jointTail_dyadic_power_sum_positive
lemma jointTail_dyadic_power_sum_positive (q r : ℝ) (N : ℕ)
    (hq : 0 ≤ q) (hr : 0 < r) :
    (∑ k ∈ Finset.range N, (q * (2:ℝ)^k)^r) ≤
      (q * (2:ℝ)^N)^r / ((2:ℝ)^r-1) := by
  have hx : 1 < (2:ℝ)^r := Real.one_lt_rpow (by norm_num) hr
  have hsum : (∑ k ∈ Finset.range N, ((2:ℝ)^r)^k) ≤
      ((2:ℝ)^r)^N / ((2:ℝ)^r-1) := by
    rw [geom_sum_eq hx.ne']
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [jointTail_dyadic_power_sum q r N hq]
  calc
    _ ≤ q^r * (((2:ℝ)^r)^N / ((2:ℝ)^r-1)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hq r)
    _ = _ := by
      rw [Real.mul_rpow hq (by positivity), ← Real.rpow_natCast_mul (by norm_num)]
      rw [mul_comm (N:ℝ) r, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      ring


/-- A flat dyadic series loses no power when its prefactor has a strict
exponent gap. Comparison with a growing geometric series absorbs the shell
count, including a bounded overshoot of the terminal grid point. -/
-- @node: jointTail_flat_dyadic_sum
lemma jointTail_flat_dyadic_sum (a q B κ σ : ℝ) (N : ℕ)
    (ha : 0 < a) (hqa : a ≤ q) (hgap : σ < κ)
    (hgrid : q * (2:ℝ)^N ≤ B) :
    (∑ _k ∈ Finset.range N, a^κ) ≤
      (B^(κ-σ) / ((2:ℝ)^(κ-σ)-1)) * a^σ := by
  have hq : 0 < q := ha.trans_le hqa
  have hd : 0 < κ-σ := sub_pos.mpr hgap
  have hden : 0 < (2:ℝ)^(κ-σ)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hd)
  have hcount : (N:ℝ) * a^(κ-σ) ≤
      ∑ k ∈ Finset.range N, (q * (2:ℝ)^k)^(κ-σ) := by
    calc
      (N:ℝ) * a^(κ-σ) = ∑ _k ∈ Finset.range N, a^(κ-σ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        apply Real.rpow_le_rpow ha.le _ hd.le
        exact hqa.trans (le_mul_of_one_le_right hq.le
          (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)))
  have hbound : (N:ℝ) * a^(κ-σ) ≤
      B^(κ-σ) / ((2:ℝ)^(κ-σ)-1) := by
    exact hcount.trans ((jointTail_dyadic_power_sum_positive q (κ-σ) N hq.le hd).trans
      (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hgrid hd.le) hden.le))
  have hpower : a^σ * a^(κ-σ) = a^κ := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  calc
    (∑ _k ∈ Finset.range N, a^κ) = a^σ * ((N:ℝ) * a^(κ-σ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← hpower]
      ring
    _ ≤ a^σ * (B^(κ-σ) / ((2:ℝ)^(κ-σ)-1)) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg ha.le _)
    _ = _ := mul_comm _ _

/-- The local exponent has a strict gap below the margin prefactor, allowing
the flat lower-region series to be absorbed by the local power. -/
-- @node: jointTail_local_exponent_gap
lemma jointTail_local_exponent_gap (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    sLoc α γ θ < α+1 := by
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  unfold sLoc
  apply (div_lt_iff₀ (by positivity : 0 < 1+betaExp α γ θ)).2
  nlinarith [mul_pos (by linarith : 0 < α+1) hb]

/-- A flat middle-region series forces a strict gap between its prefactor
power one and the overlap-tail exponent. -/
-- @node: jointTail_middle_flat_exponent_gap
lemma jointTail_middle_flat_exponent_gap (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hflat : θ+α/γ=1) : θ < 1 := by
  have hdiv : 0 < α/γ := div_pos hα hγ
  linarith

/-- At the flat lower-region equality, the dyadic shell count is absorbed
by the local power with a constant independent of the deletion level. -/
-- @node: jointTail_lower_flat_sum
lemma jointTail_lower_flat_sum (α γ θ a : ℝ) (N : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (ha : 0 < a) (hflat : θ=α+1) (hgrid : a*(2:ℝ)^N ≤ 2) :
    (∑ k ∈ Finset.range N,
      a^(α+1) * (a*(2:ℝ)^k)^(θ-α-1)) ≤
      ((2:ℝ)^(α+1-sLoc α γ θ) /
        ((2:ℝ)^(α+1-sLoc α γ θ)-1)) * a^sLoc α γ θ := by
  have he : θ-α-1=0 := by linarith
  simp only [he, Real.rpow_zero, mul_one]
  exact jointTail_flat_dyadic_sum a a 2 (α+1) (sLoc α γ θ) N ha le_rfl
    (jointTail_local_exponent_gap α γ θ hα hγ hθ) hgrid

/-- At the flat middle-region equality, the dyadic shell count is absorbed
by the high-effect power with a constant independent of the deletion level. -/
-- @node: jointTail_middle_flat_sum
lemma jointTail_middle_flat_sum (α γ θ a q : ℝ) (N : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (ha : 0 < a) (hqa : a ≤ q)
    (hflat : θ+α/γ=1) (hgrid : q*(2:ℝ)^N ≤ 2) :
    (∑ k ∈ Finset.range N, a * (q*(2:ℝ)^k)^(θ+α/γ-1)) ≤
      ((2:ℝ)^(1-θ) / ((2:ℝ)^(1-θ)-1)) * a^θ := by
  have he : θ+α/γ-1=0 := by linarith
  simp only [he, Real.rpow_zero, mul_one]
  simpa only [Real.rpow_one] using
    jointTail_flat_dyadic_sum a q 2 1 θ N ha hqa
      (jointTail_middle_flat_exponent_gap α γ θ hα hγ hflat) hgrid


/-- Below the first transition, the effect cutoff dominates the overlap
cutoff in the joint envelope. -/
-- @node: jointTail_lower_cutoff_dominates
lemma jointTail_lower_cutoff_dominates (γ a q : ℝ)
    (hγ : 0 < γ) (ha : 0 < a) (hq : 0 < q)
    (hcut : q ≤ a^(γ/(γ+1))) : q^(1/γ) ≤ a/q := by
  apply (le_div_iff₀ hq).2
  calc
    q^(1/γ)*q = q^(1+1/γ) := by
      conv_lhs => rhs; rw [← Real.rpow_one q]
      rw [← Real.rpow_add hq]
      congr 1
      ring
    _ ≤ (a^(γ/(γ+1)))^(1+1/γ) :=
      Real.rpow_le_rpow hq.le hcut (by positivity)
    _ = a := jointTail_lower_transition_balance γ a hγ ha.le

/-- Above the first transition, the overlap cutoff dominates the effect
cutoff in the joint envelope. -/
-- @node: jointTail_middle_cutoff_dominates
lemma jointTail_middle_cutoff_dominates (γ a q : ℝ)
    (hγ : 0 < γ) (ha : 0 < a) (hq : 0 < q)
    (hcut : a^(γ/(γ+1)) ≤ q) : a/q ≤ q^(1/γ) := by
  apply (div_le_iff₀ hq).2
  calc
    a = (a^(γ/(γ+1)))^(1+1/γ) :=
      (jointTail_lower_transition_balance γ a hγ ha.le).symm
    _ ≤ q^(1+1/γ) := Real.rpow_le_rpow (by positivity) hcut (by positivity)
    _ = q^(1/γ)*q := by
      conv_rhs => rhs; rw [← Real.rpow_one q]
      rw [← Real.rpow_add hq]
      congr 1
      ring

/-- Rewriting the effect-dominated shell contribution exposes its dyadic
power and deletion prefactor. -/
-- @node: jointTail_lower_shell_power
lemma jointTail_lower_shell_power (α θ a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) :
    (a/q)*(a/q)^α*q^θ = a^(α+1)*q^(θ-α-1) := by
  have hid : θ-α-1 = θ-(α+1) := by ring
  conv_lhs => lhs; lhs; rw [← Real.rpow_one (a/q)]
  rw [← Real.rpow_add (div_pos ha hq)]
  rw [show (1:ℝ)+α=α+1 by ring, Real.div_rpow ha.le hq.le, hid,
    Real.rpow_sub hq]
  ring

/-- Rewriting the overlap-dominated shell contribution exposes its dyadic
power and deletion prefactor. -/
-- @node: jointTail_middle_shell_power
lemma jointTail_middle_shell_power (α γ θ a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) :
    (a/q)*(q^(1/γ))^α*q^θ = a*q^(θ+α/γ-1) := by
  rw [← Real.rpow_mul hq.le]
  have he : (1/γ)*α = α/γ := by ring
  rw [he]
  have hid : θ+α/γ-1 = (α/γ+θ)-1 := by ring
  rw [hid, Real.rpow_sub hq, Real.rpow_one, Real.rpow_add hq]
  ring

/-- Summing lower-region shells gives only the overlap-tail and local powers,
including the flat case, with a constant uniform in the deletion level. -/
-- @node: jointTail_lower_region_sum
lemma jointTail_lower_region_sum (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (N : ℕ),
      0 < a → a ≤ 1 → a*(2:ℝ)^N ≤ a^(γ/(γ+1)) →
      (∑ k ∈ Finset.range N, a^(α+1)*(a*(2:ℝ)^k)^(θ-α-1)) ≤
        C*(a^sLoc α γ θ+a^θ) := by
  rcases lt_trichotomy (θ-α-1) 0 with hr | hr | hr
  · have hden : 0 < 1-(2:ℝ)^(θ-α-1) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)
    refine ⟨1/(1-(2:ℝ)^(θ-α-1)), by positivity, ?_⟩
    intro a N ha ha1 hgrid
    rw [← Finset.mul_sum]
    have hb := mul_le_mul_of_nonneg_left
      (jointTail_dyadic_power_sum_negative a (θ-α-1) N ha.le hr)
      (Real.rpow_nonneg ha.le (α+1))
    have hp : a^(α+1)*a^(θ-α-1) = a^θ := by
      rw [← Real.rpow_add ha]
      congr 1
      ring
    calc
      _ ≤ a^(α+1)*(a^(θ-α-1)/(1-(2:ℝ)^(θ-α-1))) := hb
      _ = (1/(1-(2:ℝ)^(θ-α-1)))*a^θ := by rw [← mul_div_assoc, hp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _)) (by positivity)
  · refine ⟨(2:ℝ)^(α+1-sLoc α γ θ) /
        ((2:ℝ)^(α+1-sLoc α γ θ)-1), ?_, ?_⟩
    · have hg := jointTail_local_exponent_gap α γ θ hα hγ hθ
      have hd := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2)
        (sub_pos.mpr hg)
      positivity
    · intro a N ha ha1 hgrid
      have hflat : θ=α+1 := by linarith
      have hbound := jointTail_lower_flat_sum α γ θ a N hα hγ hθ ha hflat
        (hgrid.trans ((jointTail_transition_scales α γ θ a hα hγ hθ ha ha1).2.1.trans
          ((jointTail_transition_scales α γ θ a hα hγ hθ ha ha1).2.2.trans (by norm_num))))
      have hg := jointTail_local_exponent_gap α γ θ hα hγ hθ
      have hd := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (sub_pos.mpr hg)
      exact hbound.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _)) (by positivity))
  · have hden : 0 < (2:ℝ)^(θ-α-1)-1 := sub_pos.mpr
      (Real.one_lt_rpow (by norm_num) hr)
    refine ⟨1/((2:ℝ)^(θ-α-1)-1), by positivity, ?_⟩
    intro a N ha ha1 hgrid
    rw [← Finset.mul_sum]
    have hb := (jointTail_dyadic_power_sum_positive a (θ-α-1) N ha.le hr).trans
      (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hgrid hr.le) hden.le)
    calc
      _ ≤ a^(α+1)*((a^(γ/(γ+1)))^(θ-α-1)/((2:ℝ)^(θ-α-1)-1)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ha.le _)
      _ = (1/((2:ℝ)^(θ-α-1)-1))*a^((α+1+γ*θ)/(γ+1)) := by
        rw [← mul_div_assoc, jointTail_lower_endpoint_power α γ θ a hγ ha]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (jointTail_intermediate_power α γ θ a hα hγ hθ ha ha1) (by positivity)

/-- Summing middle-region shells also produces only the two headline powers;
the flat equality is absorbed by the strict gap below power one. -/
-- @node: jointTail_middle_region_sum
lemma jointTail_middle_region_sum (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a q : ℝ) (N : ℕ),
      0 < a → a ≤ 1 → a^(γ/(γ+1)) ≤ q →
      q*(2:ℝ)^N ≤ a^(betaExp α γ θ/(betaExp α γ θ+1)) →
      (∑ k ∈ Finset.range N, a*(q*(2:ℝ)^k)^(θ+α/γ-1)) ≤
        C*(a^sLoc α γ θ+a^θ) := by
  rcases lt_trichotomy (θ+α/γ-1) 0 with hr | hr | hr
  · have hden : 0 < 1-(2:ℝ)^(θ+α/γ-1) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)
    refine ⟨1/(1-(2:ℝ)^(θ+α/γ-1)), by positivity, ?_⟩
    intro a q N ha ha1 hq hgrid
    have hq0 : 0 < q := (Real.rpow_pos_of_pos ha _).trans_le hq
    rw [← Finset.mul_sum]
    have hb := (jointTail_dyadic_power_sum_negative q (θ+α/γ-1) N hq0.le hr).trans
      (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by positivity) hq hr.le) hden.le)
    calc
      _ ≤ a*((a^(γ/(γ+1)))^(θ+α/γ-1)/(1-(2:ℝ)^(θ+α/γ-1))) :=
        mul_le_mul_of_nonneg_left hb ha.le
      _ = (1/(1-(2:ℝ)^(θ+α/γ-1)))*a^((α+1+γ*θ)/(γ+1)) := by
        rw [← mul_div_assoc, jointTail_middle_lower_endpoint_power α γ θ a hγ ha]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (jointTail_intermediate_power α γ θ a hα hγ hθ ha ha1) (by positivity)
  · have hflat : θ+α/γ=1 := by linarith
    have hg := jointTail_middle_flat_exponent_gap α γ θ hα hγ hflat
    have hd := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (sub_pos.mpr hg)
    refine ⟨(2:ℝ)^(1-θ)/((2:ℝ)^(1-θ)-1), by positivity, ?_⟩
    intro a q N ha ha1 hq hgrid
    have hsc := jointTail_transition_scales α γ θ a hα hγ hθ ha ha1
    have hb := jointTail_middle_flat_sum α γ θ a q N hα hγ ha
      (hsc.1.trans hq) hflat (hgrid.trans (hsc.2.2.trans (by norm_num)))
    exact hb.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _)) (by positivity))
  · have hden : 0 < (2:ℝ)^(θ+α/γ-1)-1 := sub_pos.mpr
      (Real.one_lt_rpow (by norm_num) hr)
    refine ⟨1/((2:ℝ)^(θ+α/γ-1)-1), by positivity, ?_⟩
    intro a q N ha ha1 hq hgrid
    have hq0 : 0 < q := (Real.rpow_pos_of_pos ha _).trans_le hq
    rw [← Finset.mul_sum]
    have hb := (jointTail_dyadic_power_sum_positive q (θ+α/γ-1) N hq0.le hr).trans
      (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hgrid hr.le) hden.le)
    calc
      _ ≤ a*((a^(betaExp α γ θ/(betaExp α γ θ+1)))^(θ+α/γ-1) /
          ((2:ℝ)^(θ+α/γ-1)-1)) := mul_le_mul_of_nonneg_left hb ha.le
      _ = (1/((2:ℝ)^(θ+α/γ-1)-1))*a^sLoc α γ θ := by
        rw [← mul_div_assoc, jointTail_middle_upper_endpoint_power α γ θ a hα hγ hθ ha]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _)) (by positivity)

/-- The upper-region dyadic series is bounded by the local power alone,
independently of its length, using its decreasing geometric ratio. -/
-- @node: jointTail_upper_region_sum
lemma jointTail_upper_region_sum (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a q : ℝ) (N : ℕ),
      0 < a → a^(betaExp α γ θ/(betaExp α γ θ+1)) ≤ q →
      (∑ k ∈ Finset.range N, a^(α+1)*(q*(2:ℝ)^k)^(-α-1)) ≤
        C*a^sLoc α γ θ := by
  have hr : -α-1 < 0 := by linarith
  have hden : 0 < 1-(2:ℝ)^(-α-1) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)
  refine ⟨1/(1-(2:ℝ)^(-α-1)), by positivity, ?_⟩
  intro a q N ha hq
  have hq0 : 0 < q := (Real.rpow_pos_of_pos ha _).trans_le hq
  rw [← Finset.mul_sum]
  have hb := (jointTail_dyadic_power_sum_negative q (-α-1) N hq0.le hr).trans
    (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by positivity) hq hr.le) hden.le)
  calc
    _ ≤ a^(α+1)*((a^(betaExp α γ θ/(betaExp α γ θ+1)))^(-α-1) /
        (1-(2:ℝ)^(-α-1))) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ha.le _)
    _ = (1/(1-(2:ℝ)^(-α-1)))*a^sLoc α γ θ := by
      rw [← mul_div_assoc, jointTail_upper_endpoint_power α γ θ a hα hγ hθ ha]
      ring

/-- The three dyadic regions together obey the two-power bias envelope,
with one public constant and no logarithmic factor, including both flat cases.
The remaining analytic step is to dominate the retained integral by these sums. -/
-- @node: jointTail_three_region_sum
lemma jointTail_three_region_sum (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a q r : ℝ) (L M U : ℕ),
      0 < a → a ≤ 1 → a*(2:ℝ)^L ≤ a^(γ/(γ+1)) →
      a^(γ/(γ+1)) ≤ q →
      q*(2:ℝ)^M ≤ a^(betaExp α γ θ/(betaExp α γ θ+1)) →
      a^(betaExp α γ θ/(betaExp α γ θ+1)) ≤ r →
      (∑ k ∈ Finset.range L, a^(α+1)*(a*(2:ℝ)^k)^(θ-α-1)) +
        (∑ k ∈ Finset.range M, a*(q*(2:ℝ)^k)^(θ+α/γ-1)) +
        (∑ k ∈ Finset.range U, a^(α+1)*(r*(2:ℝ)^k)^(-α-1)) ≤
          C*(a^sLoc α γ θ+a^θ) := by
  obtain ⟨Cl, hCl, hl⟩ := jointTail_lower_region_sum α γ θ hα hγ hθ
  obtain ⟨Cm, hCm, hm⟩ := jointTail_middle_region_sum α γ θ hα hγ hθ
  obtain ⟨Cu, hCu, hu⟩ := jointTail_upper_region_sum α γ θ hα hγ hθ
  refine ⟨Cl+Cm+Cu, by positivity, ?_⟩
  intro a q r L M U ha ha1 hL hq hM hr
  have hupper := (hu a r U ha hr).trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.rpow_nonneg ha.le θ)) hCu)
  calc
    _ ≤ Cl*(a^sLoc α γ θ+a^θ) + Cm*(a^sLoc α γ θ+a^θ) +
        Cu*(a^sLoc α γ θ+a^θ) :=
      add_le_add (add_le_add (hl a L ha ha1 hL) (hm a q M ha ha1 hq hM)) hupper
    _ = _ := by ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
