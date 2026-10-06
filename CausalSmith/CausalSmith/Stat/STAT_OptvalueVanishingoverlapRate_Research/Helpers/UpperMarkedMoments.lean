module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedCounts

/-! # Implemented marked-pilot moments

The actual marked counts discharge the pilot moment input in roadmap (19)
and its mass-normalized sum in (30). These are unconditional bounds,
including null cells and bad pilots.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators NNReal


-- @node: markedPoissonClippingScale
/-- The clipping scale computed from the actual pilot-marked counts.
For the displayed parameters, markedPoissonClippingScale is the object specified by this definition. -/
noncomputable def markedPoissonClippingScale (n d : ℕ) (H : ℝ) (hH : 0 < H)
    (ε : ℝ) (x : Fin d) (s : FiniteSample (Obs d × Bool)) : ℝ :=
  let Np :=
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x
  clippingScaleFormula ε
    (pilotMidpoint H hH (poissonIntensityFormula n) (logAlphabet d) Np)
    (pilotRadiusFormula H hH (poissonIntensityFormula n) (logAlphabet d) Np)

-- @node: markedPoissonClippingScale_memLp_two
/-- The actual pilot scale is L² even on failed localization events. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hHpos,hH,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonClippingScale_memLp_two {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (H : ℝ) (hHpos : 0 < H)
    (hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Fin d) :
    MemLp (markedPoissonClippingScale n d H hHpos ε x) 2
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  have hm : 0 < (n : ℝ≥0) / 8 := by positivity
  have hL : 1 ≤ logAlphabet d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [logAlphabet, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hdR]
  unfold markedPoissonClippingScale
  simpa only [poissonIntensityFormula, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_ofNat] using
    pilotClippingScale_memLp_two
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))
      (fun j s => markedCount (le_refl s.1) (fun i => (s.2 i).1)
        (fun i => (s.2 i).2) true x j)
      (fun j => (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal)
      ((n : ℝ≥0) / 8) hm H hHpos (logAlphabet d) ε hH hL hε hε1
      (fun j => markedPoissonCount_measurable d true x j)
      (fun j => markedCount_poisson_hasLaw P n true x j)

/-- Equation (19) holds for the implemented counts, with no assumed count law or pilot regularity left for a caller to discharge. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hH,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma markedPoissonClippingScale_integral_sq_le {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (H : ℝ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (x : Fin d) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    (∫ s, markedPoissonClippingScale n d H hH ε x s ^ 2 ∂μ) ≤
      512 * H ^ 2 * (1 + 9 * H) *
        (cellMass P x * logAlphabet d / (poissonIntensityFormula n * ε) +
          logAlphabet d ^ 2 / (poissonIntensityFormula n ^ 2 * ε ^ 2)) := by
  dsimp only
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have hL := (logAlphabet_pos hd).le
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let W : Fin 4 → FiniteSample (Obs d × Bool) → ℕ := fun j s =>
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x j
  have hlaw (j : Fin 4) : HasLaw (W j) (poissonMeasure
      ⟨poissonIntensityFormula n * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ := by
    have hr : (⟨poissonIntensityFormula n * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩ : ℝ≥0) =
        (((n : ℝ≥0) / (8 : ℝ≥0)) *
          (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal : ℝ≥0) := by
      apply NNReal.coe_injective
      change poissonIntensityFormula n * cellVector P x j =
        ((n : ℝ) / 8) * (P.pmf (x, decide (j.val / 2 = 1),
          decide (j.val % 2 = 1))).toReal
      rfl
    rw [hr]
    exact markedCount_poisson_hasLaw P n true x j
  have hb := observedPilotClippingScale_integral_sq_le μ P x W
    H hH (poissonIntensityFormula n) (logAlphabet d) ε hm hL hε hεhalf hlaw
  simpa only [markedPoissonClippingScale, W] using hb

/-- Equation (30) for the actual pilot: the mass term sums to one, including zero-mass cells, so the envelope contains no extra factor d on that term. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hH,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma markedPoissonClippingScale_sum_integral_sq_le {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (H : ℝ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    (∑ x, ∫ s, markedPoissonClippingScale n d H hH ε x s ^ 2 ∂μ) ≤
      512 * H ^ 2 * (1 + 9 * H) *
        (logAlphabet d / (poissonIntensityFormula n * ε) +
          (d : ℝ) * logAlphabet d ^ 2 / (poissonIntensityFormula n ^ 2 * ε ^ 2)) := by
  dsimp only
  exact clippingScale_secondMoment_sum_le P _ _ _ _ _
    (fun x => markedPoissonClippingScale_integral_sq_le hn hd P H hH ε hε hεhalf x)

/-- Equations (29)–(34) for the implemented statistic. Only the still-to-be-proved cellwise variance and bias content estimates remain as inputs: count laws, independence, square-integrability, and pilot moments are discharged here. The constant is uniform in n, d, the overlap floor, and the observed law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hHpos,hH,hCv), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_cellEstimates_rate_le (H : ℝ) (hHpos : 0 < H)
    (hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H)
    (κ Cv Cb : ℝ) (hCv : 0 ≤ Cv) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n d : ℕ}, 1 ≤ n → 1 ≤ d →
      ∀ (P : DiscreteLaw d) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε →
      let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)
      let S := markedPoissonClippingScale n d H hHpos ε
      let T := markedPoissonCellValue n d H hHpos κ ε
      (∀ x, variance (T x) μ ≤
        Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ s, S x s ^ 2 ∂μ)) →
      (∀ x, |(∫ s, T x s ∂μ) -
          cellMass P x * max (outcomeMean P false x) (outcomeMean P true x)| ≤
        Cb * (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
          1 / (poissonIntensityFormula n * ε * logAlphabet d) +
          (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ s, S x s ∂μ))) →
      Causalean.Stat.sqRisk μ (markedPoissonStatistic n d H hHpos κ ε)
        (observedValue P) ≤ C * ((d : ℝ) / (poissonIntensityFormula n * ε * logAlphabet d)) := by
  obtain ⟨Av, hAv, hvariance⟩ := activeBranch_variance_scale_rate_le
  obtain ⟨Ab, hAb, hbias⟩ := activeBranch_combined_bias_rate_le
  let Cs := 512 * H ^ 2 * (1 + 9 * H)
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  let C := Cv * Cs * Av + 2 * Cb ^ 2 * (18 + Cs * Ab) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n d hn hd P ε hε hεhalf hactive μ S T hv hb
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have ha : 0 < poissonIntensityFormula n * ε := mul_pos hm hε
  have hL := logAlphabet_pos hd
  have hε1 : ε ≤ 1 := by linarith
  have hactive' : (d : ℝ) ≤ 8 * (poissonIntensityFormula n * ε) * logAlphabet d := by
    have hh := (div_le_iff₀ hL).1 hactive
    have he : 8 * (poissonIntensityFormula n * ε) * logAlphabet d =
        (n : ℝ) * ε * logAlphabet d := by unfold poissonIntensityFormula; ring
    rw [he]
    exact hh
  have hS (x : Fin d) : MemLp (S x) 2 μ :=
    markedPoissonClippingScale_memLp_two hn hd P H hHpos hH ε hε hε1 x
  have hS₁ (x : Fin d) : Integrable (S x) μ := (hS x).integrable (by norm_num)
  have hS₂ (x : Fin d) : Integrable (fun s => S x s ^ 2) μ := (hS x).integrable_sq
  have hmom (x : Fin d) : (∫ s, S x s ^ 2 ∂μ) ≤
      Cs * (cellMass P x * logAlphabet d / (poissonIntensityFormula n * ε) +
        logAlphabet d ^ 2 / (poissonIntensityFormula n * ε) ^ 2) := by
    simpa only [mul_pow] using
      markedPoissonClippingScale_integral_sq_le hn hd P H hHpos ε hε hεhalf x
  have hvs := hvariance hd P (fun x => ∫ s, S x s ^ 2 ∂μ)
    Cs (poissonIntensityFormula n * ε) hCs ha hactive' hmom
  have hbs := hbias μ hd P S Cs Cb (poissonIntensityFormula n * ε)
    hCs ha hactive' hS₁ hS₂ hmom
  have hab : |∑ x, ((∫ s, T x s ∂μ) -
      cellMass P x * max (outcomeMean P false x) (outcomeMean P true x))| ≤
      ∑ x, Cb * (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
        1 / (poissonIntensityFormula n * ε * logAlphabet d) +
        (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ s, S x s ∂μ)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => hb x)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hab 2
  simp only [sq_abs, Finset.sum_sub_distrib] at hsq
  rw [← observedValue] at hsq
  have hvsum : (∑ x, variance (T x) μ) ≤
      Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∑ x, ∫ s, S x s ^ 2 ∂μ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hv x
  have hvs' := mul_le_mul_of_nonneg_left hvs hCv
  have hproj := markedPoissonStatistic_sqRisk_le_variance_add_bias
    hn hd P H hHpos hH κ ε hε hε1
  change Causalean.Stat.sqRisk μ (markedPoissonStatistic n d H hHpos κ ε)
    (observedValue P) ≤ (∑ x, variance (T x) μ) +
      ((∑ x, ∫ s, T x s ∂μ) - observedValue P) ^ 2 at hproj
  have hR : 0 ≤ (d : ℝ) / (poissonIntensityFormula n * ε * logAlphabet d) := by positivity
  dsimp only [C]
  nlinarith

end CausalSmith.Stat.OptvalueVanishingoverlapRate
