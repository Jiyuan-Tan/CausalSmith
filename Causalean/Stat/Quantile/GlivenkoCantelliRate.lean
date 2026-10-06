module
public import Causalean.Stat.EmpiricalProcess.GlivenkoCantelli
public import Causalean.Stat.Quantile.CDFBand

/-!
# Quantitative Glivenko--Cantelli bounds from VC--McDiarmid

This module derives expectation and convergence-in-probability consequences of
the proved finite-sample VC--McDiarmid inequality. The expectation statement is
written through `vcMcDiarmidRadius`, so changes to the upstream VC constant
propagate without duplicating a numeric tail formula here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Causalean.Stat

open Quantile.MarkedSubsampleEmpiricalCDF Quantile.VCMcDiarmid

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-- For [a population probability law](hyp:P) and [a finite sample vector](hyp:z), [the
uniform empirical-CDF deviation is nonnegative](goal). -/
lemma uniformCDFDeviation_nonneg {n : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (z : Fin n → ℝ) :
    0 ≤ uniformCDFDeviation P z := by
  exact (abs_nonneg (empiricalCDFVec z 0 - cdf P 0)).trans
    (abs_empiricalCDFVec_sub_cdf_le_uniformCDFDeviation P z 0)

/-- For [a population probability law](hyp:P) and [a finite sample vector](hyp:z), [the
uniform empirical-CDF deviation is at most one](goal). -/
lemma uniformCDFDeviation_le_one {n : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (z : Fin n → ℝ) :
    uniformCDFDeviation P z ≤ 1 := by
  unfold uniformCDFDeviation
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact abs_empiricalCDFVec_sub_cdf_le_one P z x

/-- The uniform empirical-CDF deviation is integrable under every finite product of a
population probability law. -/
@[fun_prop]
lemma integrable_uniformCDFDeviation {n : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P] :
    Integrable (uniformCDFDeviation (m := n) P) (Measure.pi (fun _ : Fin n => P)) := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_uniformCDFDeviation P).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (uniformCDFDeviation_nonneg P z)]
  exact uniformCDFDeviation_le_one P z

/-- **Integrated VC--McDiarmid expectation bound.** Given [a population probability law](hyp:P),
[a positive sample size](hyp:hn), and [a confidence level between zero and one](hyp:hα,hα_one),
[the expected uniform empirical-CDF deviation is at most the VC--McDiarmid radius plus `α`](goal).

This follows by splitting the layer-cake integral at `vcMcDiarmidRadius α n`: below the split
the contribution is at most the radius, while above it the deviation is at most one and
the VC--McDiarmid tail probability is at most `α`. -/
theorem integral_uniformCDFDeviation_le_radius_add (P : Measure ℝ)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα_one : α ≤ 1) :
    ∫ z, uniformCDFDeviation P z ∂(Measure.pi (fun _ : Fin n => P)) ≤
      vcMcDiarmidRadius α n + α := by
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => P)
  let r := vcMcDiarmidRadius α n
  let B : Set (Fin n → ℝ) := fixedCDFBadSet P r
  have hr : 0 ≤ r := vcMcDiarmidRadius_nonneg α n
  have hBmeas : MeasurableSet B := measurableSet_fixedCDFBadSet P r
  have hdevInt : Integrable (uniformCDFDeviation (m := n) P) ν :=
    integrable_uniformCDFDeviation P
  have hindInt : Integrable (B.indicator fun _ => (1 : ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator hBmeas
  have hdomInt : Integrable (fun z => r + B.indicator (fun _ => (1 : ℝ)) z) ν :=
    (integrable_const r).add hindInt
  have hpoint (z : Fin n → ℝ) :
      uniformCDFDeviation P z ≤ r + B.indicator (fun _ => (1 : ℝ)) z := by
    by_cases hz : z ∈ B
    · rw [indicator_of_mem hz]
      exact (uniformCDFDeviation_le_one P z).trans (by linarith)
    · rw [indicator_of_notMem hz, add_zero]
      exact le_of_not_gt hz
  have hbad := empiricalCDF_vc_mcdiarmid_radius P hn hα hα_one
  have hbadReal : ν.real B ≤ α := by
    change (ν B).toReal ≤ α
    calc
      (ν B).toReal ≤ (ENNReal.ofReal α).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
      _ = α := ENNReal.toReal_ofReal hα.le
  calc
    ∫ z, uniformCDFDeviation P z ∂ν ≤
        ∫ z, (r + B.indicator (fun _ => (1 : ℝ)) z) ∂ν :=
      integral_mono hdevInt hdomInt hpoint
    _ = r + ν.real B := by
      rw [integral_add (integrable_const r) hindInt, integral_const,
        integral_indicator hBmeas, setIntegral_const]
      simp [ν]
    _ ≤ r + α := by gcongr
    _ = vcMcDiarmidRadius α n + α := rfl

/-- For [an i.i.d. real sample](hyp:S), [a positive sample size](hyp:hn), and [a confidence
level between zero and one](hyp:hα,hα_one), [the expected uniform empirical-CDF deviation
of its first `n` observations is at most the VC--McDiarmid radius plus `α`](goal). -/
theorem IIDSample.integral_uniformCDFDeviation_le_radius_add
    (S : IIDSample Ω ℝ μ P) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα_one : α ≤ 1) :
    ∫ ω, uniformCDFDeviation P (fun i : Fin n => S.Z i ω) ∂μ ≤
      vcMcDiarmidRadius α n + α := by
  let sampleVec : Ω → (Fin n → ℝ) := fun ω i => S.Z i ω
  have hsampleVec : Measurable sampleVec := iidSample_finN_measurable S n
  have hdevMeas : AEStronglyMeasurable (uniformCDFDeviation (m := n) P)
      (Measure.map sampleVec μ) :=
    (measurable_uniformCDFDeviation P).aestronglyMeasurable
  rw [← integral_map hsampleVec.aemeasurable hdevMeas,
    iidSample_finN_pushforward S n]
  exact Causalean.Stat.integral_uniformCDFDeviation_le_radius_add P hn hα hα_one

/-- Given [an i.i.d. real sample](hyp:S) and [a positive sample size](hyp:hn), [its expected
uniform empirical-CDF deviation is at most the VC--McDiarmid radius at confidence `1/n`, plus
`1/n`](goal).

For the currently proved VC prefactor this is the explicit finite-sample
`sqrt(log n / n)`-scale expectation bound obtained directly from the VC--McDiarmid tail. -/
theorem IIDSample.integral_uniformCDFDeviation_le_vc_rate
    (S : IIDSample Ω ℝ μ P) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, uniformCDFDeviation P (fun i : Fin n => S.Z i ω) ∂μ ≤
      vcMcDiarmidRadius (n : ℝ)⁻¹ n + (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  exact S.integral_uniformCDFDeviation_le_radius_add hn
    (inv_pos.mpr hnR) ((inv_le_one₀ hnR).mpr (by exact_mod_cast hn))

private theorem tendsto_vc_mcdiarmid_bound_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * (ε / 2) ^ 2) / 32)))
      atTop (𝓝 0) := by
  let c : ℝ := (ε / 2) ^ 2 / 32
  have hc : 0 < c := by positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp hnat
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp hnat
  have hreal : Tendsto (fun n : ℕ =>
      8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * (ε / 2) ^ 2) / 32))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => 8 *
        ((((fun x => x ^ (1 : ℝ) * Real.exp (-c * x)) ∘ fun n : ℕ => (n : ℝ)) n) +
          (((fun x => x ^ (0 : ℝ) * Real.exp (-c * x)) ∘ fun n : ℕ => (n : ℝ)) n)))
        atTop (𝓝 0) := by
      simpa using (h1.add h0).const_mul 8
    convert hsum using 1
    funext n
    simp only [Function.comp_apply, Real.rpow_one, Real.rpow_zero, one_mul]
    have hexp : -c * (n : ℝ) = -((n : ℝ) * (ε / 2) ^ 2) / 32 := by
      dsimp [c]
      ring
    rw [hexp]
    ring
  simpa using ENNReal.tendsto_ofReal hreal

/-- **Quantitative Glivenko--Cantelli for lower rays.** Given [an i.i.d. real
sample](hyp:S), [the lower-ray indicator class is Glivenko--Cantelli](goal): for every
positive tolerance, the probability that some empirical CDF value differs from its
population value by at least that tolerance tends to zero.

This is the qualitative predicate used by
`Stat/EmpiricalProcess/GlivenkoCantelli.lean`, here obtained with the explicit finite-sample
VC--McDiarmid bound rather than a bracketing argument. -/
theorem IIDSample.cdfStat_glivenkoCantelli (S : IIDSample Ω ℝ μ P)
    [IsProbabilityMeasure P] :
    WeakGlivenkoCantelli S cdfStat := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  intro ε hε
  have hle (n : ℕ) :
      μ {ω | ∃ x : ℝ,
        ε ≤ |S.sampleMean (cdfStat x) n ω - ∫ z, cdfStat x z ∂P|} ≤
      ENNReal.ofReal
        (8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * (ε / 2) ^ 2) / 32)) := by
    by_cases hn : n = 0
    · subst n
      calc
        μ {ω | ∃ x : ℝ,
            ε ≤ |S.sampleMean (cdfStat x) 0 ω - ∫ z, cdfStat x z ∂P|} ≤ 1 :=
          prob_le_one
        _ ≤ ENNReal.ofReal
            (8 * (((0 : ℕ) : ℝ) + 1) *
              Real.exp (-(((0 : ℕ) : ℝ) * (ε / 2) ^ 2) / 32)) := by norm_num
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      calc
        μ {ω | ∃ x : ℝ,
            ε ≤ |S.sampleMean (cdfStat x) n ω - ∫ z, cdfStat x z ∂P|} ≤
            μ ((fun ω : Ω => fun i : Fin n => S.Z i ω) ⁻¹'
              fixedCDFBadSet P (ε / 2)) := by
                apply measure_mono
                rintro ω ⟨x, hx⟩
                change ε / 2 < uniformCDFDeviation P (fun i : Fin n => S.Z i ω)
                rw [integral_cdfStat] at hx
                have hpoint : |empiricalCDFVec (fun i : Fin n => S.Z i ω) x - cdf P x| ≤
                    uniformCDFDeviation P (fun i : Fin n => S.Z i ω) :=
                  abs_empiricalCDFVec_sub_cdf_le_uniformCDFDeviation P _ x
                rw [← S.empiricalCDF_eq_empiricalCDFVec n ω x] at hpoint
                change ε ≤ |S.empiricalCDF x n ω - cdf P x| at hx
                linarith
        _ = (Measure.pi (fun _ : Fin n => P)) (fixedCDFBadSet P (ε / 2)) := by
              rw [← iidSample_finN_pushforward S n,
                Measure.map_apply (iidSample_finN_measurable S n)
                  (measurableSet_fixedCDFBadSet P _)]
        _ ≤ ENNReal.ofReal
            (8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * (ε / 2) ^ 2) / 32)) :=
              empiricalCDF_vc_mcdiarmid P hnpos (by linarith)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_vc_mcdiarmid_bound_zero hε)
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall hle)

end Causalean.Stat
