module
public import Causalean.Stat.Quantile.CDFBand

/-!
# Finite-sample Kolmogorov--Smirnov bounds

This module scales the uniform empirical-CDF deviation by the square root of
the sample size to obtain the two-sided Kolmogorov--Smirnov statistic and its
upper and lower one-sided variants. For finite sample vectors, all three have
finite-sample tail bounds inherited from the proved VC--McDiarmid radius
theorem. The two-sided and upper bounds are also transported to an arbitrary
`IIDSample` sample space; this file does not provide the parallel transported
lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Causalean.Stat

open Quantile.MarkedSubsampleEmpiricalCDF Quantile.VCMcDiarmid

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-- Given [a population law](hyp:P) and [a finite sample vector](hyp:z), the
[two-sided Kolmogorov--Smirnov statistic](goal) is the square root of the sample size times
the uniform absolute empirical-CDF deviation. -/
noncomputable def KSStatistic {n : ℕ} (P : Measure ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.sqrt n * uniformCDFDeviation P z

/-- Given [a population law](hyp:P) and [a finite sample vector](hyp:z), the
[upper one-sided Kolmogorov--Smirnov statistic](goal) is the square root of the sample size
times the supremum of empirical CDF minus population CDF. -/
noncomputable def KSUpperStatistic {n : ℕ} (P : Measure ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.sqrt n * upperCDFDeviation P z

/-- Given [a population law](hyp:P) and [a finite sample vector](hyp:z), the
[lower one-sided Kolmogorov--Smirnov statistic](goal) is the square root of the sample size
times the supremum of population CDF minus empirical CDF. -/
noncomputable def KSLowerStatistic {n : ℕ} (P : Measure ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.sqrt n * lowerCDFDeviation P z

/-- Given [an i.i.d. real sample](hyp:S), [a sample size](hyp:n), and [an outcome](hyp:ω),
the [sample's two-sided Kolmogorov--Smirnov statistic](goal) applies `KSStatistic` to the
first `n` observations. -/
noncomputable def IIDSample.ksStatistic (S : IIDSample Ω ℝ μ P) (n : ℕ) (ω : Ω) : ℝ :=
  KSStatistic P (fun i : Fin n => S.Z i ω)

/-- Given [an i.i.d. real sample](hyp:S), [a sample size](hyp:n), and [an outcome](hyp:ω),
the [sample's upper one-sided Kolmogorov--Smirnov statistic](goal) applies
`KSUpperStatistic` to the first `n` observations. -/
noncomputable def IIDSample.ksUpperStatistic (S : IIDSample Ω ℝ μ P)
    (n : ℕ) (ω : Ω) : ℝ :=
  KSUpperStatistic P (fun i : Fin n => S.Z i ω)

/-- Given [an i.i.d. real sample](hyp:S), [a sample size](hyp:n), and [an outcome](hyp:ω),
the [sample's lower one-sided Kolmogorov--Smirnov statistic](goal) applies
`KSLowerStatistic` to the first `n` observations. -/
noncomputable def IIDSample.ksLowerStatistic (S : IIDSample Ω ℝ μ P)
    (n : ℕ) (ω : Ω) : ℝ :=
  KSLowerStatistic P (fun i : Fin n => S.Z i ω)

private lemma upperCDFDeviation_le_uniformCDFDeviation {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] (z : Fin n → ℝ) :
    upperCDFDeviation P z ≤ uniformCDFDeviation P z := by
  unfold upperCDFDeviation
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    (abs_empiricalCDFVec_sub_cdf_le_uniformCDFDeviation P z x)

private lemma lowerCDFDeviation_le_uniformCDFDeviation {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] (z : Fin n → ℝ) :
    lowerCDFDeviation P z ≤ uniformCDFDeviation P z := by
  unfold lowerCDFDeviation
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hneg : cdf P x - empiricalCDFVec z x = -(empiricalCDFVec z x - cdf P x) := by
    ring
  change cdf P x - empiricalCDFVec z x ≤ uniformCDFDeviation P z
  rw [hneg]
  exact (neg_le_abs _).trans
    (abs_empiricalCDFVec_sub_cdf_le_uniformCDFDeviation P z x)

/-- **KS tail at an arbitrary threshold.** Given [a population probability law](hyp:P),
[a positive sample size](hyp:hn), and [a positive threshold](hyp:ht), [the product-law
probability that the two-sided KS statistic exceeds `t` is at most
`8 * (n+1) * exp (-t² / 32)`](goal). -/
theorem ksStatistic_tail_at (P : Measure ℝ) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => P)) {z | t < KSStatistic P z} ≤
      ENNReal.ofReal (8 * ((n : ℝ) + 1) * Real.exp (-(t ^ 2) / 32)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have hset : {z : Fin n → ℝ | t < KSStatistic P z} =
      fixedCDFBadSet P (t / Real.sqrt n) := by
    ext z
    change t < Real.sqrt (n : ℝ) * uniformCDFDeviation P z ↔
      t / Real.sqrt (n : ℝ) < uniformCDFDeviation P z
    constructor
    · intro h
      rw [div_lt_iff₀ hsqrt]
      simpa [mul_comm] using h
    · intro h
      rw [div_lt_iff₀ hsqrt] at h
      simpa [mul_comm] using h
  rw [hset]
  have hmain := empiricalCDF_vc_mcdiarmid P hn (div_pos ht hsqrt)
  convert hmain using 1
  congr 3
  field_simp [hsqrt.ne']
  exact congrArg (fun x : ℝ => -x) hsqrt_sq

/-- Given [a population probability law](hyp:P), [a positive sample size](hyp:hn), and
[a positive threshold](hyp:ht), [the product-law probability that the upper one-sided KS
statistic exceeds `t` is at most `8 * (n+1) * exp (-t² / 32)`](goal). -/
theorem ksUpperStatistic_tail_at (P : Measure ℝ) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => P)) {z | t < KSUpperStatistic P z} ≤
      ENNReal.ofReal (8 * ((n : ℝ) + 1) * Real.exp (-(t ^ 2) / 32)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have hset : {z : Fin n → ℝ | t < KSUpperStatistic P z} =
      upperCDFBadSet P (t / Real.sqrt n) := by
    ext z
    change t < Real.sqrt (n : ℝ) * upperCDFDeviation P z ↔
      t / Real.sqrt (n : ℝ) < upperCDFDeviation P z
    constructor
    · intro h
      rw [div_lt_iff₀ hsqrt]
      simpa [mul_comm] using h
    · intro h
      rw [div_lt_iff₀ hsqrt] at h
      simpa [mul_comm] using h
  rw [hset]
  have hmain := empiricalCDF_vc_mcdiarmid_upper P hn (div_pos ht hsqrt)
  convert hmain using 1
  congr 3
  field_simp [hsqrt.ne']
  exact congrArg (fun x : ℝ => -x) hsqrt_sq

/-- Given [a population probability law](hyp:P), [a positive sample size](hyp:hn), and
[a positive threshold](hyp:ht), [the product-law probability that the lower one-sided KS
statistic exceeds `t` is at most `8 * (n+1) * exp (-t² / 32)`](goal). -/
theorem ksLowerStatistic_tail_at (P : Measure ℝ) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => P)) {z | t < KSLowerStatistic P z} ≤
      ENNReal.ofReal (8 * ((n : ℝ) + 1) * Real.exp (-(t ^ 2) / 32)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have hset : {z : Fin n → ℝ | t < KSLowerStatistic P z} =
      lowerCDFBadSet P (t / Real.sqrt n) := by
    ext z
    change t < Real.sqrt (n : ℝ) * lowerCDFDeviation P z ↔
      t / Real.sqrt (n : ℝ) < lowerCDFDeviation P z
    constructor
    · intro h
      rw [div_lt_iff₀ hsqrt]
      simpa [mul_comm] using h
    · intro h
      rw [div_lt_iff₀ hsqrt] at h
      simpa [mul_comm] using h
  rw [hset]
  have hmain := empiricalCDF_vc_mcdiarmid_lower P hn (div_pos ht hsqrt)
  convert hmain using 1
  congr 3
  field_simp [hsqrt.ne']
  exact congrArg (fun x : ℝ => -x) hsqrt_sq

/-- **Finite-sample KS tail bound from VC--McDiarmid.** Given [a population probability law](hyp:P),
[a positive sample size](hyp:hn), and [a confidence level between zero and one](hyp:hα,hα_one),
[the product-law probability that the two-sided KS statistic exceeds the VC--McDiarmid critical value
is at most `α`](goal).

No asymptotic Kolmogorov distribution is used: this is exactly
`empiricalCDF_vc_mcdiarmid_radius` after multiplying both sides of the deviation
comparison by `sqrt n`. -/
theorem ksStatistic_tail (P : Measure ℝ) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1) :
    (Measure.pi (fun _ : Fin n => P))
        {z | Real.sqrt n * vcMcDiarmidRadius α n < KSStatistic P z} ≤
      ENNReal.ofReal α := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hset : {z : Fin n → ℝ | Real.sqrt n * vcMcDiarmidRadius α n < KSStatistic P z} =
      fixedCDFBadSet P (vcMcDiarmidRadius α n) := by
    ext z
    change Real.sqrt (n : ℝ) * vcMcDiarmidRadius α n <
        Real.sqrt (n : ℝ) * uniformCDFDeviation P z ↔
      vcMcDiarmidRadius α n < uniformCDFDeviation P z
    exact mul_lt_mul_iff_of_pos_left hsqrt
  rw [hset]
  exact empiricalCDF_vc_mcdiarmid_radius P hn hα hα_one

/-- **One-sided finite-sample KS tail bound from VC--McDiarmid.** Given [a population probability
law](hyp:P), [a positive sample size](hyp:hn), and [a confidence level between zero and
one](hyp:hα,hα_one), [the product-law probability that the upper one-sided KS statistic
exceeds the VC--McDiarmid critical value is at most `α`](goal). -/
theorem ksUpperStatistic_tail (P : Measure ℝ) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1) :
    (Measure.pi (fun _ : Fin n => P))
        {z | Real.sqrt n * vcMcDiarmidRadius α n < KSUpperStatistic P z} ≤
      ENNReal.ofReal α := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  calc
    (Measure.pi (fun _ : Fin n => P))
        {z | Real.sqrt n * vcMcDiarmidRadius α n < KSUpperStatistic P z} ≤
      (Measure.pi (fun _ : Fin n => P))
        (fixedCDFBadSet P (vcMcDiarmidRadius α n)) := by
          apply measure_mono
          intro z hz
          change Real.sqrt (n : ℝ) * vcMcDiarmidRadius α n <
            Real.sqrt (n : ℝ) * upperCDFDeviation P z at hz
          change vcMcDiarmidRadius α n < uniformCDFDeviation P z
          exact ((mul_lt_mul_iff_of_pos_left hsqrt).mp hz).trans_le
            (upperCDFDeviation_le_uniformCDFDeviation P z)
    _ ≤ ENNReal.ofReal α := empiricalCDF_vc_mcdiarmid_radius P hn hα hα_one

/-- Given [a population probability law](hyp:P), [a positive sample
size](hyp:hn), and [a confidence level between zero and one](hyp:hα,hα_one),
[the product-law probability that the lower one-sided KS statistic exceeds the
VC--McDiarmid critical value is at most `α`](goal). -/
theorem ksLowerStatistic_tail (P : Measure ℝ) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1) :
    (Measure.pi (fun _ : Fin n => P))
        {z | Real.sqrt n * vcMcDiarmidRadius α n < KSLowerStatistic P z} ≤
      ENNReal.ofReal α := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  calc
    (Measure.pi (fun _ : Fin n => P))
        {z | Real.sqrt n * vcMcDiarmidRadius α n < KSLowerStatistic P z} ≤
      (Measure.pi (fun _ : Fin n => P))
        (fixedCDFBadSet P (vcMcDiarmidRadius α n)) := by
          apply measure_mono
          intro z hz
          change Real.sqrt (n : ℝ) * vcMcDiarmidRadius α n <
            Real.sqrt (n : ℝ) * lowerCDFDeviation P z at hz
          change vcMcDiarmidRadius α n < uniformCDFDeviation P z
          exact ((mul_lt_mul_iff_of_pos_left hsqrt).mp hz).trans_le
            (lowerCDFDeviation_le_uniformCDFDeviation P z)
    _ ≤ ENNReal.ofReal α := empiricalCDF_vc_mcdiarmid_radius P hn hα hα_one

/-- For [an i.i.d. real sample](hyp:S), [a positive sample size](hyp:hn), and [a confidence
level between zero and one](hyp:hα,hα_one), [the probability that its KS statistic exceeds
the VC--McDiarmid critical value is at most `α`](goal). -/
theorem IIDSample.ksStatistic_tail (S : IIDSample Ω ℝ μ P)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα_one : α ≤ 1) :
    μ {ω | Real.sqrt n * vcMcDiarmidRadius α n < S.ksStatistic n ω} ≤
      ENNReal.ofReal α := by
  let sampleVec : Ω → (Fin n → ℝ) := fun ω i => S.Z i ω
  have hsampleVec : Measurable sampleVec := iidSample_finN_measurable S n
  have hset : {ω | Real.sqrt n * vcMcDiarmidRadius α n < S.ksStatistic n ω} =
      sampleVec ⁻¹' {z | Real.sqrt n * vcMcDiarmidRadius α n < KSStatistic P z} := rfl
  have htailMeas : MeasurableSet
      {z : Fin n → ℝ | Real.sqrt n * vcMcDiarmidRadius α n < KSStatistic P z} := by
    exact measurableSet_lt measurable_const
      ((measurable_uniformCDFDeviation P).const_mul _)
  rw [hset, ← Measure.map_apply hsampleVec htailMeas]
  rw [iidSample_finN_pushforward S n]
  exact Causalean.Stat.ksStatistic_tail P hn hα hα_one

/-- For [an i.i.d. real sample](hyp:S), [a positive sample size](hyp:hn), and [a confidence
level between zero and one](hyp:hα,hα_one), [the probability that its upper one-sided KS
statistic exceeds the VC--McDiarmid critical value is at most `α`](goal). -/
theorem IIDSample.ksUpperStatistic_tail (S : IIDSample Ω ℝ μ P)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα_one : α ≤ 1) :
    μ {ω | Real.sqrt n * vcMcDiarmidRadius α n < S.ksUpperStatistic n ω} ≤
      ENNReal.ofReal α := by
  let sampleVec : Ω → (Fin n → ℝ) := fun ω i => S.Z i ω
  calc
    μ {ω | Real.sqrt n * vcMcDiarmidRadius α n < S.ksUpperStatistic n ω} ≤
        μ (sampleVec ⁻¹' fixedCDFBadSet P (vcMcDiarmidRadius α n)) := by
          apply measure_mono
          intro ω hω
          have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
          change Real.sqrt (n : ℝ) * vcMcDiarmidRadius α n <
            Real.sqrt (n : ℝ) * upperCDFDeviation P (sampleVec ω) at hω
          change vcMcDiarmidRadius α n < uniformCDFDeviation P (sampleVec ω)
          exact ((mul_lt_mul_iff_of_pos_left hsqrt).mp hω).trans_le
            (upperCDFDeviation_le_uniformCDFDeviation P (sampleVec ω))
    _ = (Measure.pi (fun _ : Fin n => P))
        (fixedCDFBadSet P (vcMcDiarmidRadius α n)) := by
          rw [← iidSample_finN_pushforward S n,
            Measure.map_apply (iidSample_finN_measurable S n)
              (measurableSet_fixedCDFBadSet P _)]
    _ ≤ ENNReal.ofReal α := empiricalCDF_vc_mcdiarmid_radius P hn hα hα_one

end Causalean.Stat
