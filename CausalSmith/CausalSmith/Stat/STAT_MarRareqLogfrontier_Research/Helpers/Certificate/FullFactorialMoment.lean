module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CellIntensity
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CoefficientOverlap
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.HeavyFactorialBudget

/-! Full-range factorial second moments and the false-light product in (10)--(13). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:lam,v,w), [the stated mathematical conclusion holds](goal). -/
-- @node: factorialOverlap_le_intensity_add_orders_pow
lemma factorialOverlap_le_intensity_add_orders_pow (lam : ℝ≥0) (v w : ℕ) :
    factorialOverlap lam v w ≤ ((lam : ℝ) + v + w) ^ (v + w) := by
  have hv0 : (0 : ℝ) ≤ v := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have ht : 0 ≤ (lam : ℝ) := lam.coe_nonneg
  calc
    _ ≤ ∑ r ∈ Finset.range (v + 1),
        (v.choose r : ℝ) * (w : ℝ) ^ r * (lam : ℝ) ^ (v - r) * (lam : ℝ) ^ w := by
      unfold factorialOverlap
      apply (Finset.sum_le_sum fun r hr ↦ ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega : min v w + 1 ≤ v + 1))
          (fun r _ _ ↦ by positivity))
      have hrv : r ≤ v := by have := Finset.mem_range.mp hr; omega
      have hc : (w.choose r : ℝ) * (Nat.factorial r : ℝ) ≤ (w : ℝ) ^ r := by
        have h := Nat.choose_le_pow_div (α := ℝ) r w
        exact (le_div_iff₀ (by positivity : (0 : ℝ) < Nat.factorial r)).mp h
      have he : v + w - r = (v - r) + w := by omega
      rw [he, pow_add]
      calc
        _ = (v.choose r : ℝ) * ((w.choose r : ℝ) * Nat.factorial r) *
            (lam : ℝ) ^ (v - r) * (lam : ℝ) ^ w := by ring
        _ ≤ _ := by gcongr
    _ = ((w : ℝ) + lam) ^ v * (lam : ℝ) ^ w := by
      rw [← Finset.sum_mul, add_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ((lam : ℝ) + v + w) ^ v * ((lam : ℝ) + v + w) ^ w := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (pow_le_pow_left₀ ht (by linarith) _) (by positivity) (by positivity)
    _ = _ := (pow_add _ _ _).symm

/-- Given [the specified inputs and assumptions](hyp:n,d,q,lam,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: needleCoefficientOverlap_le_full_growth
lemma needleCoefficientOverlap_le_full_growth (n d : ℕ) (q : ℝ) (lam : ℝ≥0)
    (hb : needleBranch n d q) :
    needleCoefficientOverlap n d q lam ≤ (64 : ℝ) ^ needleDegree n q *
      max 1 (((lam + 2 * needleDegree n q) / needleRadius n q) ^
        (2 * needleDegree n q)) := by
  let k := needleDegree n q
  let B := needleRadius n q
  let S := Finset.Icc 1 (k - 1)
  let x : ℝ := ((lam : ℝ) + 2 * k) / B
  let M : ℝ := max 1 (x ^ (2 * k))
  let a : ℕ → ℝ := fun v ↦ |needleCoeff n d q v * B ^ v|
  have hB : 0 < B := by dsimp [B, needleRadius]; linarith [hb.1]
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hM : 0 ≤ M := le_trans (by norm_num) (le_max_left _ _)
  have hpow (r : ℕ) (hr : r ≤ 2 * k) : x ^ r ≤ M := by
    by_cases hx1 : x ≤ 1
    · exact (pow_le_one₀ hx hx1).trans (le_max_left _ _)
    · exact (pow_le_pow_right₀ (le_of_not_ge hx1) hr).trans (le_max_right _ _)
  have hterm (v w : ℕ) (hv : v ∈ S) (hw : w ∈ S) :
      |needleCoeff n d q v * needleCoeff n d q w| * factorialOverlap lam v w ≤
        a v * a w * M := by
    have hvk : v ≤ k := by have := (Finset.mem_Icc.mp hv).2; dsimp [S] at hv; omega
    have hwk : w ≤ k := by have := (Finset.mem_Icc.mp hw).2; dsimp [S] at hw; omega
    have horders : (v : ℝ) + w ≤ 2 * k := by exact_mod_cast (show v + w ≤ 2 * k by omega)
    have ho : factorialOverlap lam v w ≤ ((lam : ℝ) + 2 * k) ^ (v + w) := by
      apply (factorialOverlap_le_intensity_add_orders_pow lam v w).trans
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc
      _ ≤ |needleCoeff n d q v * needleCoeff n d q w| *
          (((lam : ℝ) + 2 * k) ^ (v + w)) := by gcongr
      _ = a v * a w * x ^ (v + w) := by
        dsimp [a, x]
        rw [div_pow, pow_add B, abs_mul, abs_mul, abs_mul,
          abs_pow, abs_pow, abs_of_pos hB]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow _ (by omega)) (by positivity)
  change (∑ v ∈ S, ∑ w ∈ S,
    |needleCoeff n d q v * needleCoeff n d q w| * factorialOverlap lam v w) ≤ _
  calc
    _ ≤ ∑ v ∈ S, ∑ w ∈ S, a v * a w * M := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact hterm v w hv hw
    _ = (∑ v ∈ S, a v) ^ 2 * M := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ ((8 : ℝ) ^ k) ^ 2 * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
      exact needle_scaled_coefficient_oneNorm_le n d q hb
    _ = _ := by
      change ((8 : ℝ) ^ k) ^ 2 * M = (64 : ℝ) ^ k * M
      rw [pow_right_comm]
      norm_num

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_markedPoissonFactorialBranch_le_full_growth
lemma integral_sq_markedPoissonFactorialBranch_le_full_growth
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q) :
    (∫ s, (poissonFactorialBranch n d q j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      (64 : ℝ) ^ needleDegree n q *
        max 1 (((streamSize n * arrivedCell P j + 2 * needleDegree n q) /
          needleRadius n q) ^ (2 * needleDegree n q)) := by
  have h := (integral_sq_poissonFactorialBranch_le_effective_overlap n d q j
    (markedObsLaw P) ((n : ℝ≥0) / 2)).trans
      (needleCoefficientOverlap_le_full_growth n d q
        (arrivedStreamIntensity n P 2 j) hb)
  simpa only [coe_arrivedStreamIntensity] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_light_mul_factorial_secondMoment_le_intensity
lemma markedPoisson_pilot_light_mul_factorial_secondMoment_le_intensity
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
      (∫ s, (poissonFactorialBranch n d q j s) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      Real.exp (-(streamSize n * arrivedCell P j) / 8) := by
  have hl : 0 < logScale n q := by linarith [hb.1]
  have hk : (needleDegree n q : ℝ) ≤ logScale n q / 64 :=
    Nat.floor_le (by positivity)
  have hx : 1 ≤ (streamSize n * arrivedCell P j + 2 * needleDegree n q) /
      needleRadius n q := by
    apply (le_div_iff₀ (by dsimp [needleRadius]; positivity)).2
    have hk0 : (0 : ℝ) ≤ needleDegree n q := by positivity
    linarith
  have hp := one_le_pow₀ hx (n := 2 * needleDegree n q)
  calc
    _ ≤ Real.exp (-(streamSize n * arrivedCell P j) / 4) *
        ((64 : ℝ) ^ needleDegree n q *
          max 1 (((streamSize n * arrivedCell P j + 2 * needleDegree n q) /
            needleRadius n q) ^ (2 * needleDegree n q))) := by
      apply mul_le_mul
        (markedPoisson_pilot_light_probability_le_of_heavy n d q P j hb hh)
        (integral_sq_markedPoissonFactorialBranch_le_full_growth n d q P j hb)
        (integral_nonneg fun _ ↦ sq_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [max_eq_right hp, ← mul_assoc]
      exact heavy_factorial_tail_growth_le (logScale n q)
        (streamSize n * arrivedCell P j) (needleDegree n q) hl hk hh.le

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_light_mul_factorial_secondMoment_le
lemma markedPoisson_pilot_light_mul_factorial_secondMoment_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
      (∫ s, (poissonFactorialBranch n d q j s) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      Real.exp (-32 * logScale n q) := by
  apply (markedPoisson_pilot_light_mul_factorial_secondMoment_le_intensity
    n d q P j hb hh).trans
  apply Real.exp_le_exp.mpr
  change 256 * logScale n q < streamSize n * arrivedCell P j at hh
  linarith

end CausalSmith.Stat.MarRareqLogfrontier
