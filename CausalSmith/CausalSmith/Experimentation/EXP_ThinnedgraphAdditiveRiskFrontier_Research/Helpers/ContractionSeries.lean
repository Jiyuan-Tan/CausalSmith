module
public import Causalean.Mathlib.Data.Nat.Choose.Bounds
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshChannelEnergy
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Geometric and exponential series for contraction
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Sampling a fixed number of hidden slots without replacement is bounded by
sampling with replacement from the same active-slot fraction.  [For the stated data and conditions](hyp:U,M,k,hUM,hk,hM), [the stated conclusion holds](goal). -/
-- @node: hidden_choose_ratio_le_power
lemma hidden_choose_ratio_le_power (U M k : ℕ) (hUM : U ≤ M) (hk : k ≤ U)
    (hM : 0 < M) :
    (U.choose k : ℝ) / (M.choose k : ℝ) ≤ ((U : ℝ) / M) ^ k := by
  exact Causalean.Mathlib.Data.Nat.Choose.choose_div_choose_le_div_pow U M k hUM hk

/-- On the good event, the active-slot fraction is bounded both by one and by
four times the active-row fraction.  [For the stated data and conditions](hyp:B,d,U,M,a,b,hB,hd,hUM,hU,hgood), [the stated conclusion holds](goal). -/
-- @node: hidden_active_slot_fraction
lemma hidden_active_slot_fraction (B d U M a b : ℕ) (hB : 0 < B) (hd : 0 < d)
    (hUM : U ≤ M) (hU : U ≤ d * (a + b))
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M) :
    (U : ℝ) / M ≤ min 1 (4 * (a + b : ℕ) / (B : ℝ)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hMr : (0 : ℝ) < M := by
    have : (0 : ℝ) < (B * d : ℕ) / (4 : ℝ) := by positivity
    exact this.trans_le hgood
  have hUMr : (U : ℝ) ≤ M := by exact_mod_cast hUM
  have hUr : (U : ℝ) ≤ d * (a + b : ℕ) := by exact_mod_cast hU
  have hgood' : (B : ℝ) * d ≤ 4 * M := by
    push_cast at hgood
    linarith
  apply le_min
  · exact (div_le_one hMr).mpr hUMr
  · rw [div_le_div_iff₀ hMr hBr]
    nlinarith [mul_le_mul_of_nonneg_right hUr hBr.le,
      mul_le_mul_of_nonneg_right hgood' (show (0 : ℝ) ≤ (a + b : ℕ) by positivity)]

/-- The binomial normalizer in the hidden-allocation second moment contracts by
one factor per active hidden row, including zero-degree and out-of-capacity terms.  [For the stated data and conditions](hyp:B,d,U,M,a,b,k,hB,hd,hUM,hU,hgood,hbk), [the stated conclusion holds](goal). -/
-- @node: hidden_choose_ratio_good_event
lemma hidden_choose_ratio_good_event (B d U M a b k : ℕ) (hB : 0 < B) (hd : 0 < d)
    (hUM : U ≤ M) (hU : U ≤ d * (a + b))
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M) (hbk : b ≤ k) :
    (U.choose k : ℝ) / (M.choose k : ℝ) ≤
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b := by
  have hMr : (0 : ℝ) < M := by
    have : (0 : ℝ) < (B * d : ℕ) / (4 : ℝ) := by positivity
    exact this.trans_le hgood
  by_cases hkU : k ≤ U
  · have hM : 0 < M := by exact_mod_cast hMr
    have hfrac := hidden_active_slot_fraction B d U M a b hB hd hUM hU hgood
    have hfrac0 : (0 : ℝ) ≤ (U : ℝ) / M := by positivity
    calc
      _ ≤ ((U : ℝ) / M) ^ k := hidden_choose_ratio_le_power U M k hUM hkU hM
      _ ≤ ((U : ℝ) / M) ^ b :=
        pow_le_pow_of_le_one hfrac0 (hfrac.trans (min_le_left _ _)) hbk
      _ ≤ _ := pow_le_pow_left₀ hfrac0 hfrac b
  · rw [Nat.choose_eq_zero_of_lt (by omega : U < k)]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- The factorial dominates the exponential-normalized power needed for the contraction series.  [For the stated data and conditions](hyp:b), [the stated conclusion holds](goal). -/
-- @node: factorial_exponential_bound
lemma factorial_exponential_bound (b : ℕ) :
    ((b : ℝ) ^ b) / (b.factorial : ℝ) ≤ Real.exp (b : ℝ) := by
  exact Real.pow_div_factorial_le_exp (b : ℝ) (Nat.cast_nonneg b) b

/-- Counting disjoint active revealed and hidden row sets gives the coefficient
bound used before extending the contraction sum to infinite series.  [For the stated data and conditions](hyp:B,a,b,hB), [the stated conclusion holds](goal). -/
-- @node: contraction_active_row_coefficient
lemma contraction_active_row_coefficient (B a b : ℕ) (hB : 0 < B) :
    (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b ≤
      ((Real.exp 1 * B) ^ a / (a.factorial : ℝ)) * (4 * Real.exp 1) ^ b := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hfa : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
  have hfb : (0 : ℝ) < b.factorial := by exact_mod_cast b.factorial_pos
  have hchooseA : (B.choose a : ℝ) ≤ (B : ℝ) ^ a / a.factorial :=
    Nat.choose_le_pow_div a B
  have hchooseB : ((B - a).choose b : ℝ) ≤ (B : ℝ) ^ b / b.factorial := by
    calc
      _ ≤ ((B - a : ℕ) : ℝ) ^ b / b.factorial := Nat.choose_le_pow_div b (B - a)
      _ ≤ _ := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le B a) b) hfb.le
  have hmin0 : (0 : ℝ) ≤ min 1 (4 * (a + b : ℕ) / (B : ℝ)) := by positivity
  calc
    _ ≤ ((B : ℝ) ^ a / a.factorial) * ((B : ℝ) ^ b / b.factorial) *
        (4 * (a + b : ℕ) / (B : ℝ)) ^ b := by
      apply mul_le_mul
      · exact mul_le_mul hchooseA hchooseB (by positivity) (by positivity)
      · exact pow_le_pow_left₀ hmin0 (min_le_right _ _) b
      · positivity
      · positivity
    _ = ((B : ℝ) ^ a / a.factorial) * 4 ^ b *
        ((a + b : ℕ) : ℝ) ^ b / b.factorial := by
      rw [div_pow, mul_pow]
      field_simp
    _ ≤ ((B : ℝ) ^ a / a.factorial) * 4 ^ b * Real.exp (a + b : ℕ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (Real.pow_div_factorial_le_exp (a + b : ℕ) (by positivity) b) (by positivity)
    _ = _ := by
      rw [Nat.cast_add, Real.exp_add,
        show Real.exp (a : ℝ) = Real.exp 1 ^ a by simp [← Real.exp_nat_mul],
        show Real.exp (b : ℝ) = Real.exp 1 ^ b by simp [← Real.exp_nat_mul],
        mul_pow, mul_pow]
      ring

/-- The nonnegative contraction geometric series sums to the reciprocal gap.  [For the stated data and conditions](hyp:r,hr,hr1), [the stated conclusion holds](goal). -/
-- @node: contraction_geometric_series
lemma contraction_geometric_series (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, r ^ k) = (1 - r)⁻¹ := by
  exact tsum_geometric_of_abs_lt_one (by simpa only [abs_of_nonneg hr] using hr1)

/-- The finite active-row contraction sum is dominated by an exponential series
in the revealed energy times a geometric series in the hidden energy.  [For the stated data and conditions](hyp:B,A,C,x,y,hB,hx,hy,hsmall), [the stated conclusion holds](goal). -/
-- @node: contraction_finite_rectangle_bound
lemma contraction_finite_rectangle_bound (B A C : ℕ) (x y : ℝ)
    (hB : 0 < B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsmall : 4 * Real.exp 1 * y < 1) :
    (∑ a ∈ Finset.range A, ∑ b ∈ Finset.range C,
      (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
        (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b * x ^ a * y ^ b) ≤
      Real.exp (Real.exp 1 * B * x) / (1 - 4 * Real.exp 1 * y) := by
  have hr0 : 0 ≤ 4 * Real.exp 1 * y := by positivity
  have hgeom : (∑ b ∈ Finset.range C, (4 * Real.exp 1 * y) ^ b) ≤
      (1 - 4 * Real.exp 1 * y)⁻¹ := by
    rw [← contraction_geometric_series _ hr0 hsmall]
    exact (summable_geometric_of_lt_one hr0 hsmall).sum_le_tsum _
      (fun b _ => pow_nonneg hr0 b)
  have hexp : (∑ a ∈ Finset.range A,
      (Real.exp 1 * B * x) ^ a / (a.factorial : ℝ)) ≤
      Real.exp (Real.exp 1 * B * x) :=
    Real.sum_le_exp_of_nonneg (by positivity) A
  calc
    _ ≤ ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range C,
        ((Real.exp 1 * B * x) ^ a / (a.factorial : ℝ)) *
          (4 * Real.exp 1 * y) ^ b := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (contraction_active_row_coefficient B a b hB)
          (pow_nonneg hx a)) (pow_nonneg hy b)
      convert h using 1
      simp only [mul_pow]
      ring
    _ = (∑ a ∈ Finset.range A, (Real.exp 1 * B * x) ^ a / (a.factorial : ℝ)) *
        (∑ b ∈ Finset.range C, (4 * Real.exp 1 * y) ^ b) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ Real.exp (Real.exp 1 * B * x) * (1 - 4 * Real.exp 1 * y)⁻¹ :=
      mul_le_mul hexp hgeom (Finset.sum_nonneg (fun b _ => pow_nonneg hr0 b))
        (Real.exp_nonneg _)
    _ = _ := by rw [div_eq_mul_inv]

/-- Removing the constant Walsh term from the finite active-row sum produces
exactly the minus-one bound in the contraction roadmap.  [For the stated data and conditions](hyp:B,x,y,hB,hx,hy,hsmall), [the stated conclusion holds](goal). -/
-- @node: contraction_nonconstant_sum_bound
lemma contraction_nonconstant_sum_bound (B : ℕ) (x y : ℝ)
    (hB : 0 < B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsmall : 4 * Real.exp 1 * y < 1) :
    (∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
      if a + b = 0 then 0 else
        (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
          (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b * x ^ a * y ^ b) ≤
      Real.exp (Real.exp 1 * B * x) / (1 - 4 * Real.exp 1 * y) - 1 := by
  let F : ℕ → ℕ → ℝ := fun a b =>
    (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b * x ^ a * y ^ b
  have hzero : F 0 0 = 1 := by simp [F]
  have hremove (a b : ℕ) : (if a + b = 0 then 0 else F a b) =
      F a b - if a = 0 ∧ b = 0 then 1 else 0 := by
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b; simp [hzero]
      · simp [hb]
    · simp [ha]
  change (∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
    if a + b = 0 then 0 else F a b) ≤ _
  simp_rw [hremove, Finset.sum_sub_distrib]
  have hone : (∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
      if a = 0 ∧ b = 0 then (1 : ℝ) else 0) = 1 := by
    simp_rw [ite_and]
    simp
  rw [hone]
  exact sub_le_sub_right (contraction_finite_rectangle_bound B (B + 1) (B + 1)
    x y hB hx hy hsmall) 1

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
