module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotAggregation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperGoodBadAssembly
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedMoments
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TIdentification

/-! # Good-pilot inputs for the implemented marked statistic

Roadmap (29)–(34) is assembled for the actual marked-count construction.
Count laws, pairwise cell independence, L² regularity, pilot-scale moments,
and bad-pilot losses are discharged. Only the two integrated good-pilot
content estimates remain as explicit inputs, retaining Jackson squared error.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal


-- @node: markedPoissonGoodPilot
/-- The true cell vector belongs to the rectangle constructed from the actual
pilot-marked observations.

For [the displayed parameters](hyp:d,n,P,H,hH,x), [markedPoissonGoodPilot](goal) is the object specified by this definition. -/
noncomputable def markedPoissonGoodPilot {d : ℕ} (n : ℕ) (P : DiscreteLaw d)
    (H : ℝ) (hH : 0 < H) (x : Fin d) : Set (FiniteSample (Obs d × Bool)) :=
  {s | let Np := markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x
    cellVector P x ∈ pilotRectangle
      (pilotLower H hH (poissonIntensityFormula n) (logAlphabet d) Np)
      (pilotUpperFormula H hH (poissonIntensityFormula n) (logAlphabet d) Np)}


-- @node: markedPoissonGoodPilot_measurableSet
/-- Localization of the implemented pilot is a measurable event. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH), the [stated conclusion](goal) holds. -/
lemma markedPoissonGoodPilot_measurableSet {d : ℕ} (n : ℕ) (P : DiscreteLaw d)
    (H : ℝ) (hH : 0 < H) (x : Fin d) :
    MeasurableSet (markedPoissonGoodPilot n P H hH x) := by
  let f : FiniteSample (Obs d × Bool) → Fin 4 → ℕ := fun s =>
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x
  have hf : Measurable f := measurable_pi_lambda _
    (fun j => markedPoissonCount_measurable d true x j)
  change MeasurableSet (f ⁻¹' {z | cellVector P x ∈ pilotRectangle
    (pilotLower H hH (poissonIntensityFormula n) (logAlphabet d) z)
    (pilotUpperFormula H hH (poissonIntensityFormula n) (logAlphabet d) z)})
  exact hf MeasurableSet.of_discrete


-- @node: markedPoissonPilot_iIndepFun
/-- Actual pilot counts within a cell are independent Poisson coordinates. This discharges the independence input in the bad-pilot estimate (22). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonPilot_iIndepFun {d : ℕ} (P : DiscreteLaw d) (n : ℕ) (x : Fin d) :
    iIndepFun (fun j : Fin 4 => fun s : FiniteSample (Obs d × Bool) =>
      markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x j)
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  let g : Fin 4 → Obs d × Bool := fun j =>
    ((x, decide (j.val / 2 = 1), decide (j.val % 2 = 1)), true)
  have hg : Function.Injective g := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all [g]
  simp_rw [markedCount_eq_markedPoissonHistogram]
  exact (markedPoissonHistogram_iIndepFun P n).precomp hg

open Classical in
/-- The implemented bad-pilot cell loss satisfies (22), including null cells. No distributional or moment inputs remain for the caller. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hε1,hP,hHpos,hH), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_bad_sq_le {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hP : ObservedClass ε P) (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H)
    (κ : ℝ) (x : Fin d) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    let Cd := 2 * (512 * H ^ 2 *
      (8 + 2 * (H / universalH) * productMomentConstant 4 1) +
      1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2)
    (∫ s, if s ∉ markedPoissonGoodPilot n P H hHpos x then
        (markedPoissonCellValue n d H hHpos κ ε x s -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
      Cd * (d : ℝ) ^ (-4 : ℝ) *
        (cellMass P x * logAlphabet d / (poissonIntensityFormula n * ε) +
          logAlphabet d ^ 2 / (poissonIntensityFormula n * ε) ^ 2) := by
  classical
  have hm : 0 < (n : ℝ≥0) / 8 := by positivity
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let W : Fin 4 → FiniteSample (Obs d × Bool) → ℕ := fun j s =>
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x j
  let Ne : FiniteSample (Obs d × Bool) → Fin 4 → ℕ := fun s =>
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) false x
  have hlaw (j : Fin 4) : HasLaw (W j)
      (poissonMeasure (((n : ℝ≥0) / 8) *
        ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ := by
    convert markedCount_poisson_hasLaw P n true x j using 1
    congr 1
  have ht := pilotRectangle_bad_clippedCellValue_alphabet_sq_le μ hd ε P hε hε1
    hP x W Ne ((n : ℝ≥0) / 8) hm H hHpos hH
    (fun j => markedPoissonCount_measurable d true x j) hlaw
    (markedPoissonPilot_iIndepFun P n x) (jacksonDegree κ d)
  simpa only [markedPoissonGoodPilot, Set.mem_setOf_eq, markedPoissonCellValue,
    W, Ne, poissonIntensityFormula, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat,
    mul_pow] using ht

open Classical in
/-- For the implemented statistic, only the good-pilot first and second moment content estimates remain in (29)–(34). The Jackson approximation term is retained; bad-pilot loss, independence, and regularity are derived. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hHpos,hH,hCv,hCe), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_goodPilotEstimates_rate_le
    (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H)
    (κ Cv Cb Ce : ℝ) (hCv : 0 ≤ Cv) (hCe : 0 ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n d : ℕ}, 1 ≤ n → 1 ≤ d →
      ∀ (P : DiscreteLaw d) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ObservedClass ε P →
      (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε →
      let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)
      let S := markedPoissonClippingScale n d H hHpos ε
      let T := markedPoissonCellValue n d H hHpos κ ε
      let E := markedPoissonGoodPilot n P H hHpos
      let t := fun x => armwiseExtensionFormula ε (cellVector P x)
      (∀ x, (∫ s, if s ∈ E x then (T x s - t x) ^ 2 else 0 ∂μ) ≤
        Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ s, S x s ^ 2 ∂μ) +
          Ce * (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
            1 / (poissonIntensityFormula n * ε * logAlphabet d)) ^ 2) →
      (∀ x, |∫ s, if s ∈ E x then T x s - t x else 0 ∂μ| ≤
        Cb * (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
          1 / (poissonIntensityFormula n * ε * logAlphabet d) +
          (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ s, S x s ∂μ))) →
      Causalean.Stat.sqRisk μ (markedPoissonStatistic n d H hHpos κ ε)
        (observedValue P) ≤ C * ((d : ℝ) / (poissonIntensityFormula n * ε * logAlphabet d)) := by
  classical
  let Cs := 512 * H ^ 2 * (1 + 9 * H)
  let Cd := 2 * (512 * H ^ 2 *
    (8 + 2 * (H / universalH) * productMomentConstant 4 1) +
    1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2)
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCd : 0 ≤ Cd := by
    have hu := universalH_pos
    have hc := productMomentConstant_pos 4 1
    dsimp [Cd]
    positivity
  obtain ⟨C, hC, hrate⟩ := activeBranch_pilotEvent_approximation_sqRisk_rate_le
    Cs Cv Cb Cd Ce hCs hCv hCd hCe
  refine ⟨C, hC, ?_⟩
  intro n d hn hd P ε hε hεhalf hP hactive μ S T E t hg₂ hg₁
  have hε1 : ε ≤ 1 := by linarith
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have ha : 0 < poissonIntensityFormula n * ε := mul_pos hm hε
  have hactive' : (d : ℝ) ≤ 8 * (poissonIntensityFormula n * ε) * logAlphabet d := by
    have hh := (div_le_iff₀ (logAlphabet_pos hd)).1 hactive
    have he : 8 * (poissonIntensityFormula n * ε) * logAlphabet d =
        (n : ℝ) * ε * logAlphabet d := by unfold poissonIntensityFormula; ring
    rw [he]
    exact hh
  have hS (x : Fin d) : MemLp (S x) 2 μ :=
    markedPoissonClippingScale_memLp_two hn hd P H hHpos hH ε hε hε1 x
  have hT (x : Fin d) : MemLp (T x) 2 μ :=
    markedPoissonCellValue_memLp_two hn hd P H hHpos hH κ ε hε hε1 x
  have hmom (x : Fin d) : (∫ s, S x s ^ 2 ∂μ) ≤
      Cs * (cellMass P x * logAlphabet d / (poissonIntensityFormula n * ε) +
        logAlphabet d ^ 2 / (poissonIntensityFormula n * ε) ^ 2) := by
    simpa only [mul_pow] using
      markedPoissonClippingScale_integral_sq_le hn hd P H hHpos ε hε hεhalf x
  have hb₂ (x : Fin d) : (∫ s, if s ∉ E x then (T x s - t x) ^ 2 else 0 ∂μ) ≤
      Cd * (d : ℝ) ^ (-4 : ℝ) *
        (cellMass P x * logAlphabet d / (poissonIntensityFormula n * ε) +
          logAlphabet d ^ 2 / (poissonIntensityFormula n * ε) ^ 2) :=
    markedPoissonCellValue_bad_sq_le hn hd P ε hε hε1 hP H hHpos hH κ x
  have hr := hrate μ hd P T S t E (poissonIntensityFormula n * ε) ha hactive' hT
    (markedPoissonCellValue_pairwise_indepFun P n H hHpos κ ε)
    (fun x => markedPoissonGoodPilot_measurableSet n P H hHpos x)
    (fun x => (hS x).integrable (by norm_num))
    (fun x => (hS x).integrable_sq) hmom hg₂ hg₁ hb₂
  have ht : (∑ x, t x) = observedValue P := by
    simp only [t, armwiseExtension_cellVector ε P hε hP]
    rfl
  rw [ht] at hr
  have hsum := markedPoissonCellValue_sum_memLp_two hn hd P H hHpos hH κ ε hε hε1
  exact (projectUnit_sqRisk_le μ (fun s => ∑ x, T x s) (observedValue P)
    hsum (observedValue_mem_unitInterval P)).trans hr

end CausalSmith.Stat.OptvalueVanishingoverlapRate
