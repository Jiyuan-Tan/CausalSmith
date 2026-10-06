module
public import Causalean.Stat.Quantile.FiniteMassTransport

/-!
# Integrated CDF distance and equally weighted atomic measures

This module fixes the metric and atomic-measure conventions used by the synchronized
rational approximation theorem. Measures are finite Borel measures on the real line.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace Causalean.Stat.Quantile.AtomicApproximation

/-- [The integrated-CDF distance](goal) between [a measure μ](hyp:μ) [and a
measure ν](hyp:ν) on the real line, over [the interval from a to
b](hyp:a,b), is [the absolute gap between their total masses plus the
integral from a to b of the absolute gap between their cumulative
distribution functions](step:1). -/
def cdfDistance (a b : ℝ) (μ ν : Measure ℝ) : ℝ :=
  |μ.real Set.univ - ν.real Set.univ| +
    ∫ t in a..b, |μ.real (Set.Iic t) - ν.real (Set.Iic t)|

/-- [The equally weighted atomic measure](goal) with [N atoms](hyp:N) [of
total weight w](hyp:w) [at locations x_1, …, x_N](hyp:x) is [the sum of
the point masses at the locations, each with weight w/N (read as zero when
w is negative)](step:1). -/
def equalAtomMeasure (N : ℕ) (w : ℝ) (x : Fin N → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (w / N) • Measure.dirac (x i)

/-- If [the number of atoms N is positive](hyp:N,hN) and [the total weight
w is nonnegative](hyp:w,hw), then [the equally weighted atomic measure at
any locations has total mass exactly w](goal). -/
theorem equalAtomMeasure_mass (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w)
    (x : Fin N → ℝ) : (equalAtomMeasure N w x).real Set.univ = w := by
  /- Expand the finite measure sum. Each Dirac mass of `univ` is one; convert
     `ENNReal.ofReal (w / N)` to a real and sum `N` equal terms. -/
  simp [equalAtomMeasure, Measure.real, Measure.finsetSum_apply, hw, div_nonneg,
    Nat.cast_nonneg]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

/-- Over [an interval whose endpoints satisfy a ≤ b](hyp:a,b,hab), [the
integrated-CDF distance between finite measures on the real line satisfies
the triangle inequality](goal). -/
theorem cdfDistance_triangle (a b : ℝ) (hab : a ≤ b)
    (μ ν ξ : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    cdfDistance a b μ ξ ≤ cdfDistance a b μ ν + cdfDistance a b ν ξ := by
  /- Use the real absolute-value triangle inequality pointwise, then monotonicity
     of the interval integral. The CDFs are interval integrable by
     `FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub`. -/
  let μf : FiniteMeasure ℝ := ⟨μ, inferInstance⟩
  let νf : FiniteMeasure ℝ := ⟨ν, inferInstance⟩
  let ξf : FiniteMeasure ℝ := ⟨ξ, inferInstance⟩
  have hμξ := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf ξf a b
  have hμν := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf νf a b
  have hνξ := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    νf ξf a b
  change IntervalIntegrable (fun t : ℝ => |μ.real (Iic t) - ξ.real (Iic t)|)
    volume a b at hμξ
  change IntervalIntegrable (fun t : ℝ => |μ.real (Iic t) - ν.real (Iic t)|)
    volume a b at hμν
  change IntervalIntegrable (fun t : ℝ => |ν.real (Iic t) - ξ.real (Iic t)|)
    volume a b at hνξ
  have hsum := hμν.add hνξ
  have hint : (∫ t in a..b, |μ.real (Iic t) - ξ.real (Iic t)|) ≤
      (∫ t in a..b, |μ.real (Iic t) - ν.real (Iic t)|) +
      (∫ t in a..b, |ν.real (Iic t) - ξ.real (Iic t)|) := by
    rw [← intervalIntegral.integral_add hμν hνξ]
    apply intervalIntegral.integral_mono_on hab hμξ hsum
    intro t _
    exact abs_sub_le _ _ _
  unfold cdfDistance
  have hmass := abs_sub_le (μ.real univ) (ν.real univ) (ξ.real univ)
  linarith

/-- Over [an interval with a ≤ b](hyp:a,b,hab), with [a positive number
of atoms N](hyp:N,hN) and [two nonnegative total weights m and
q](hyp:m,q,hm,hq), [the integrated-CDF distance between the two equally
weighted atomic measures at the same locations is at most
(1 + (b − a))·|m − q|](goal). -/
theorem cdfDistance_equalAtomMeasure_weight_le (a b : ℝ) (hab : a ≤ b)
    (N : ℕ) (hN : 0 < N) (m q : ℝ) (hm : 0 ≤ m) (hq : 0 ≤ q)
    (x : Fin N → ℝ) :
    cdfDistance a b (equalAtomMeasure N m x) (equalAtomMeasure N q x) ≤
      (1 + (b - a)) * |m - q| := by
  /- The two CDFs are the same empirical counting function multiplied by
     `m/N` or `q/N`. Its values lie in `[0,1]`. Integrate the resulting
     pointwise bound `|Fₘ(t)-F_q(t)| ≤ |m-q|` and use the mass lemma above. -/
  have hformula (w : ℝ) (hw : 0 ≤ w) (s : Set ℝ) :
      (equalAtomMeasure N w x).real s =
        (w / N) * ∑ i, (Measure.dirac (x i)).real s := by
    simp only [equalAtomMeasure, Measure.real, Measure.finsetSum_apply,
      Measure.smul_apply]
    rw [ENNReal.toReal_sum (by
      intro i hi
      by_cases hx : x i ∈ s <;> simp [Measure.dirac_apply, hx])]
    simp [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hw (Nat.cast_nonneg _)), ← Finset.mul_sum]
  have hscale (w : ℝ) (hw : 0 ≤ w) (s : Set ℝ) :
      (equalAtomMeasure N w x).real s =
        w * (equalAtomMeasure N 1 x).real s := by
    rw [hformula w hw s, hformula 1 (by norm_num) s]
    ring
  have hfinite (w : ℝ) : IsFiniteMeasure (equalAtomMeasure N w x) := by
    haveI : ∀ i : Fin N,
        IsFiniteMeasure (ENNReal.ofReal (w / N) • Measure.dirac (x i)) :=
      fun i => Measure.smul_finite _ (by simp)
    unfold equalAtomMeasure
    infer_instance
  letI : IsFiniteMeasure (equalAtomMeasure N 1 x) := hfinite 1
  have hunit : (equalAtomMeasure N 1 x).real univ = 1 :=
    equalAtomMeasure_mass N hN 1 (by norm_num) x
  have hpoint (t : ℝ) :
      |(equalAtomMeasure N m x).real (Iic t) -
        (equalAtomMeasure N q x).real (Iic t)| ≤ |m - q| := by
    rw [hscale m hm, hscale q hq, ← sub_mul, abs_mul,
      abs_of_nonneg (measureReal_nonneg (μ := equalAtomMeasure N 1 x))]
    apply mul_le_of_le_one_right (abs_nonneg _)
    have hle := measureReal_mono (μ := equalAtomMeasure N 1 x)
      (subset_univ (Iic t)) (by finiteness)
    rwa [hunit] at hle
  let μf : FiniteMeasure ℝ := ⟨equalAtomMeasure N m x, hfinite m⟩
  let νf : FiniteMeasure ℝ := ⟨equalAtomMeasure N q x, hfinite q⟩
  have hint := Causalean.Stat.Quantile.FiniteMassTransport.intervalIntegrable_abs_raw_cdf_sub
    μf νf a b
  change IntervalIntegrable
    (fun t : ℝ => |(equalAtomMeasure N m x).real (Iic t) -
      (equalAtomMeasure N q x).real (Iic t)|) volume a b at hint
  have hbound := intervalIntegral.integral_mono_on hab hint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => |m - q|) volume a b)
    (fun t _ => hpoint t)
  rw [intervalIntegral.integral_const] at hbound
  simp only [smul_eq_mul] at hbound
  rw [cdfDistance, equalAtomMeasure_mass N hN m hm x,
    equalAtomMeasure_mass N hN q hq x]
  nlinarith [abs_nonneg (m - q)]

end Causalean.Stat.Quantile.AtomicApproximation
