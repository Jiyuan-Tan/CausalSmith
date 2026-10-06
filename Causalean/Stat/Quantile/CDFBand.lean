module
public import Causalean.Stat.Quantile.EmpiricalCDF
public import Causalean.Stat.Quantile.VCMcDiarmidRadius
public import Causalean.Stat.Sample.PiTransport

/-!
# Uniform empirical-CDF confidence bands

This module turns the product-law VC--McDiarmid deviation inequality into a
confidence band on the sample space of an arbitrary `IIDSample`. The band is
centered at the empirical CDF and covers the population CDF simultaneously at
every real threshold. Its radius is more conservative than the sharp
Dvoretzky--Kiefer--Wolfowitz--Massart radius.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Causalean.Stat

open Quantile.MarkedSubsampleEmpiricalCDF Quantile.VCMcDiarmid

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-- Given [an i.i.d. real sample](hyp:S), [a confidence level](hyp:α), [a sample
size](hyp:n), [an outcome](hyp:ω), and [a threshold](hyp:x), the [empirical-CDF
confidence band](goal) is the empirical-CDF interval of radius `vcMcDiarmidRadius α n`,
clipped to the CDF range `[0,1]`. -/
noncomputable def IIDSample.cdfBand (S : IIDSample Ω ℝ μ P) (α : ℝ) (n : ℕ)
    (ω : Ω) (x : ℝ) : Set ℝ :=
  Icc (max 0 (S.empiricalCDF x n ω - vcMcDiarmidRadius α n))
    (min 1 (S.empiricalCDF x n ω + vcMcDiarmidRadius α n))

/-- Given [an i.i.d. real sample](hyp:S), [a confidence level](hyp:α), and [a
sample size](hyp:n), the [simultaneous CDF-band coverage event](goal) consists of outcomes
for which the population CDF belongs to the empirical band at every real threshold. -/
def IIDSample.cdfBandCoverageEvent (S : IIDSample Ω ℝ μ P) (α : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ x : ℝ, cdf P x ∈ S.cdfBand α n ω x}

/-- The empirical CDF of the first `n` observations is the vector empirical CDF of the
finite-prefix map. -/
lemma IIDSample.empiricalCDF_eq_empiricalCDFVec (S : IIDSample Ω ℝ μ P)
    (n : ℕ) (ω : Ω) (x : ℝ) :
    S.empiricalCDF x n ω = empiricalCDFVec (fun i : Fin n => S.Z i ω) x := by
  unfold IIDSample.empiricalCDF IIDSample.sampleMean empiricalCDFVec
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i => cdfStat x (S.Z i ω)) n).symm

/-- For [a population probability law](hyp:P), [a finite sample vector](hyp:z), and [a real
threshold](hyp:x), [the absolute empirical-CDF error is at most one](goal). -/
lemma abs_empiricalCDFVec_sub_cdf_le_one {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] (z : Fin n → ℝ) (x : ℝ) :
    |empiricalCDFVec z x - cdf P x| ≤ 1 := by
  have hsum0 : 0 ≤ ∑ i : Fin n, cdfStat x (z i) :=
    Finset.sum_nonneg fun i _ => cdfStat_nonneg x (z i)
  have hsum1 : (∑ i : Fin n, cdfStat x (z i)) ≤ n := by
    calc
      (∑ i : Fin n, cdfStat x (z i)) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => cdfStat_le_one x (z i)
      _ = n := by simp
  have he0 : 0 ≤ empiricalCDFVec z x := by
    simp only [empiricalCDFVec]
    positivity
  have he1 : empiricalCDFVec z x ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      simp [empiricalCDFVec]
    · rw [empiricalCDFVec, inv_mul_le_iff₀ (by positivity)]
      simpa using hsum1
  have hP0 := cdf_nonneg P x
  have hP1 := cdf_le_one P x
  rw [abs_le]
  constructor <;> linarith

/-- For [a population probability law](hyp:P), [a finite sample vector](hyp:z), and [a real
threshold](hyp:x), [the pointwise absolute empirical-CDF error is at most the uniform CDF
deviation](goal). -/
lemma abs_empiricalCDFVec_sub_cdf_le_uniformCDFDeviation {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] (z : Fin n → ℝ) (x : ℝ) :
    |empiricalCDFVec z x - cdf P x| ≤ uniformCDFDeviation P z := by
  have hbdd : BddAbove (range fun y : ℝ => |empiricalCDFVec z y - cdf P y|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact abs_empiricalCDFVec_sub_cdf_le_one P z y
  exact le_csSup hbdd ⟨x, rfl⟩

/-- If a finite sample vector is outside the VC--McDiarmid bad set, its empirical band
contains the population CDF at every threshold. -/
lemma IIDSample.mem_cdfBand_of_prefix_not_bad (S : IIDSample Ω ℝ μ P)
    [IsProbabilityMeasure P] {α : ℝ} {n : ℕ} {ω : Ω}
    (hgood : (fun i : Fin n => S.Z i ω) ∉ fixedCDFBadSet P (vcMcDiarmidRadius α n)) :
    ∀ x : ℝ, cdf P x ∈ S.cdfBand α n ω x := by
  intro x
  have hdev : uniformCDFDeviation P (fun i : Fin n => S.Z i ω) ≤
      vcMcDiarmidRadius α n := by
    simpa [fixedCDFBadSet] using hgood
  have habs : |S.empiricalCDF x n ω - cdf P x| ≤ vcMcDiarmidRadius α n := by
    rw [S.empiricalCDF_eq_empiricalCDFVec n ω x]
    exact (abs_empiricalCDFVec_sub_cdf_le_uniformCDFDeviation P _ x).trans hdev
  rw [abs_le] at habs
  change max 0 (S.empiricalCDF x n ω - vcMcDiarmidRadius α n) ≤ cdf P x ∧
    cdf P x ≤ min 1 (S.empiricalCDF x n ω + vcMcDiarmidRadius α n)
  constructor
  · exact max_le (cdf_nonneg P x) (by linarith [habs.1])
  · exact le_min (cdf_le_one P x) (by linarith [habs.2])

/-- **Uniform CDF confidence band from a VC--McDiarmid bound.**
Given [an i.i.d. real sample](hyp:S), [a positive sample size](hyp:hn), and [a confidence
level between zero and one](hyp:hα,hα_one), [the data-dependent VC--McDiarmid-radius
band covers the population CDF simultaneously at every real threshold with probability at
least `1 - α`](goal).

The proof transports `empiricalCDF_vc_mcdiarmid_radius` from the finite product law to the
`IIDSample` sample space. It does not formalize the sharper DKW--Massart confidence band
stated as Wasserman, *All of Statistics*, Theorem 7.5. -/
theorem IIDSample.cdfBand_coverage (S : IIDSample Ω ℝ μ P)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα_one : α ≤ 1) :
    μ (S.cdfBandCoverageEvent α n) ≥ 1 - ENNReal.ofReal α := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => P)) := inferInstance
  let E : Set (Fin n → ℝ) := (fixedCDFBadSet P (vcMcDiarmidRadius α n))ᶜ
  have hbad := empiricalCDF_vc_mcdiarmid_radius P hn hα hα_one
  have hEprob : Measure.pi (fun _ : Fin n => P) E ≥ 1 - ENNReal.ofReal α := by
    rw [show E = (fixedCDFBadSet P (vcMcDiarmidRadius α n))ᶜ from rfl,
      measure_compl (measurableSet_fixedCDFBadSet P _)
        (MeasureTheory.measure_ne_top _ _), measure_univ]
    exact tsub_le_tsub_left hbad 1
  have htransport := event_pullback_along_iidSample S n
    (measurableSet_fixedCDFBadSet P _).compl hEprob
  dsimp only at htransport
  exact htransport.2.trans (measure_mono fun ω hω =>
    S.mem_cdfBand_of_prefix_not_bad hω)

end Causalean.Stat
