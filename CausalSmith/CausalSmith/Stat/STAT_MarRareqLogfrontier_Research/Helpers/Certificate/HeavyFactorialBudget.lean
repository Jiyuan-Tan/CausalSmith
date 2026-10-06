module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotTailBounds

/-! Numerical heavy-cell exponential budgets for the false-light product (13).
These isolate the analytic step after the factorial second-moment bound (10). -/

public section

open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:ell,t,k,hell,hk,ht), [the stated mathematical conclusion holds](goal). -/
-- @node: heavy_factorial_exponent_budget
lemma heavy_factorial_exponent_budget (ell t : ℝ) (k : ℕ)
    (hell : 0 < ell) (hk : (k : ℝ) ≤ ell / 64) (ht : 256 * ell ≤ t) :
    6 * (k : ℝ) + 2 * (k : ℝ) * ((t + 2 * k) / (256 * ell)) ≤ t / 8 := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have ht0 : 0 ≤ t := by linarith
  have hkt : (k : ℝ) ≤ t / 16384 := by linarith
  have hratio : 2 * (k : ℝ) / (256 * ell) ≤ 1 / 8192 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 256 * ell)).2
    linarith
  have hprod := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ t + 2 * (k : ℝ) by positivity)
  have heq : 2 * (k : ℝ) * ((t + 2 * k) / (256 * ell)) =
      (2 * (k : ℝ) / (256 * ell)) * (t + 2 * k) := by ring
  rw [heq]
  linarith

/-- Given [the specified inputs and assumptions](hyp:ell,t,k,hell,hk,ht), [the stated mathematical conclusion holds](goal). -/
-- @node: heavy_factorial_tail_growth_le
lemma heavy_factorial_tail_growth_le (ell t : ℝ) (k : ℕ)
    (hell : 0 < ell) (hk : (k : ℝ) ≤ ell / 64) (ht : 256 * ell ≤ t) :
    Real.exp (-t / 4) * (64 : ℝ) ^ k *
      ((t + 2 * k) / (256 * ell)) ^ (2 * k) ≤ Real.exp (-t / 8) := by
  let x := (t + 2 * k) / (256 * ell)
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hcoeff : (64 : ℝ) ^ k ≤ Real.exp (6 * (k : ℝ)) := by
    calc
      (64 : ℝ) ^ k = ((2 : ℝ) ^ 6) ^ k := by norm_num
      _ = (2 : ℝ) ^ (6 * k) := by rw [← pow_mul]
      _ ≤ (Real.exp 1) ^ (6 * k) := by gcongr
      _ = Real.exp (6 * (k : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
  have hgrowth : x ^ (2 * k) ≤ Real.exp (2 * (k : ℝ) * x) := by
    calc
      _ ≤ (Real.exp x) ^ (2 * k) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc
    _ ≤ Real.exp (-t / 4) * Real.exp (6 * (k : ℝ)) *
        Real.exp (2 * (k : ℝ) * x) := by gcongr
    _ = Real.exp (-t / 4 + 6 * (k : ℝ) + 2 * (k : ℝ) * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-t / 8) := by
      apply Real.exp_le_exp.mpr
      have h := heavy_factorial_exponent_budget ell t k hell hk ht
      change 6 * (k : ℝ) + 2 * (k : ℝ) * x ≤ t / 8 at h
      linarith

/-- Given [the specified inputs and assumptions](hyp:ell,t,k,hell,hk,ht), [the stated mathematical conclusion holds](goal). -/
-- @node: heavy_factorial_tail_max_growth_le
lemma heavy_factorial_tail_max_growth_le (ell t : ℝ) (k : ℕ)
    (hell : 0 < ell) (hk : (k : ℝ) ≤ ell / 64) (ht : 256 * ell ≤ t) :
    Real.exp (-t / 4) * ((64 : ℝ) ^ k *
      max 1 (((t + 2 * k) / (256 * ell)) ^ (2 * k))) ≤
        Real.exp (-32 * ell) := by
  have hx : 1 ≤ (t + 2 * (k : ℝ)) / (256 * ell) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 256 * ell)).2
    have hk0 : (0 : ℝ) ≤ k := by positivity
    linarith
  have hpow : 1 ≤ ((t + 2 * (k : ℝ)) / (256 * ell)) ^ (2 * k) :=
    one_le_pow₀ hx
  rw [max_eq_right hpow, ← mul_assoc]
  apply (heavy_factorial_tail_growth_le ell t k hell hk ht).trans
  apply Real.exp_le_exp.mpr
  linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_light_mul_factorial_growth_le
lemma markedPoisson_pilot_light_mul_factorial_growth_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (finitePoissonSampleLaw
      (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount
        s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
      ((64 : ℝ) ^ needleDegree n q *
        max 1 (((streamSize n * arrivedCell P j + 2 * needleDegree n q) /
          needleRadius n q) ^ (2 * needleDegree n q))) ≤
      Real.exp (-32 * logScale n q) := by
  have hl : 0 < logScale n q := by linarith [hb.1]
  have hk : (needleDegree n q : ℝ) ≤ logScale n q / 64 :=
    Nat.floor_le (by positivity)
  calc
    _ ≤ Real.exp (-(streamSize n * arrivedCell P j) / 4) *
        ((64 : ℝ) ^ needleDegree n q *
          max 1 (((streamSize n * arrivedCell P j + 2 * needleDegree n q) /
            needleRadius n q) ^ (2 * needleDegree n q))) := by
      apply mul_le_mul_of_nonneg_right
        (markedPoisson_pilot_light_probability_le_of_heavy n d q P j hb hh)
      positivity
    _ ≤ _ := heavy_factorial_tail_max_growth_le (logScale n q)
      (streamSize n * arrivedCell P j) (needleDegree n q) hl hk hh.le

end CausalSmith.Stat.MarRareqLogfrontier
