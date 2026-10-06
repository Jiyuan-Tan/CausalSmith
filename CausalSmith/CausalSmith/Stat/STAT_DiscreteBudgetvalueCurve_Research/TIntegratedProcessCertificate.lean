module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.ScalarBiasSharp
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.BVLipschitz

/-! Uniform Jackson-factorial threshold-process certificate. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
open Causalean.Stat.Concentration.BoundedVariation

private lemma centeredPathSum_sq_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → Path)
    (hX : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) μ) :
    Integrable (fun ω =>
      ‖∑ i, (X i ω - ∫ x, X i x ∂μ)‖ ^ 2) μ := by
  have hab (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hcenter2 (i : ι) : Integrable (fun ω =>
      ‖X i ω - ∫ x, X i x ∂μ‖ ^ 2) μ := by
    have hdom : Integrable (fun ω =>
        2 * ‖X i ω‖ ^ 2 + 2 * ‖∫ x, X i x ∂μ‖ ^ 2) μ :=
      ((hX2 i).const_mul 2).add (integrable_const _)
    apply hdom.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖X i ω - ∫ x, X i x ∂μ‖ ^ 2 ≤
          (‖X i ω‖ + ‖∫ x, X i x ∂μ‖) ^ 2 := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := hab _ _
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ) * ∑ i : ι,
      ‖X i ω - ∫ x, X i x ∂μ‖ ^ 2) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ (fun i _ => hcenter2 i)
  apply hdom.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    ‖∑ i, (X i ω - ∫ x, X i x ∂μ)‖ ^ 2 ≤
        (∑ i : ι, ‖X i ω - ∫ x, X i x ∂μ‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := by
      simpa using pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset ι))
        (f := fun i => ‖X i ω - ∫ x, X i x ∂μ‖)
        (fun _ _ => norm_nonneg _) 1

private lemma idealPilotMean_good_add_bad_abs_le_bias_sum
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P))
    (lambda : ℝ) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    |idealPilotErrorMean (n := n) epsilon lambda P true +
        idealPilotErrorMean (n := n) epsilon lambda P false| ≤
      ∑ j : Fin d, uncappedJacksonCellBias (n := n) epsilon lambda P j := by
  classical
  let μ := idealCountLaw (n := n) P
  let E := fun j : Fin d => fun counts =>
    idealClippedCellPath (n := n) epsilon lambda counts j -
      thresholdFunReal epsilon lambda (cellVector P j)
  have hgood : Integrable (fun counts =>
      idealPilotErrorPart (n := n) epsilon lambda P counts true) μ := by
    simp_rw [idealPilotErrorPart_eq_sum_cells]
    apply integrable_finsetSum
    intro j _
    simpa [μ, idealPilotErrorCellPath] using
      (ContinuousMap.evalCLM ℝ (⟨lambda, hlambda⟩ : Time)).integrable_comp
        (idealGoodPilotCellPath_integrable epsilon he he' hn hd P hprob j)
  have hbad : Integrable (fun counts =>
      idealPilotErrorPart (n := n) epsilon lambda P counts false) μ := by
    simp_rw [idealPilotErrorPart_eq_sum_cells]
    apply integrable_finsetSum
    intro j _
    simpa [μ, idealPilotErrorCellPath] using
      (ContinuousMap.evalCLM ℝ (⟨lambda, hlambda⟩ : Time)).integrable_comp
        (idealBadPilotCellPath_integrable epsilon he hn (show 1 ≤ d by omega)
          P hprob j)
  have hE (j : Fin d) : Integrable (E j) μ := by
    simpa [E, μ] using idealClippedCell_error_integrable epsilon he hn
      (show 1 ≤ d by omega) P j lambda hlambda
  have hmean : idealPilotErrorMean (n := n) epsilon lambda P true +
      idealPilotErrorMean (n := n) epsilon lambda P false =
      ∑ j : Fin d, ∫ counts, E j counts ∂μ := by
    unfold idealPilotErrorMean
    change (∫ counts, idealPilotErrorPart (n := n) epsilon lambda P counts true ∂μ) +
      (∫ counts, idealPilotErrorPart (n := n) epsilon lambda P counts false ∂μ) = _
    rw [← integral_add hgood hbad]
    rw [← integral_finsetSum Finset.univ (fun j _ => hE j)]
    apply integral_congr_ae
    filter_upwards [] with counts
    rw [idealPilotErrorPart_eq_sum_cells, idealPilotErrorPart_eq_sum_cells,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hg : idealPilotGood (n := n) P counts j <;>
      simp [idealPilotErrorCell, E, idealClippedCellPath, hg]
  rw [hmean]
  calc
    |∑ j : Fin d, ∫ counts, E j counts ∂μ| ≤
        ∑ j : Fin d, |∫ counts, E j counts ∂μ| := by
      simpa using Finset.abs_sum_le_sum_abs (fun j : Fin d => ∫ counts, E j counts ∂μ)
        Finset.univ
    _ = ∑ j : Fin d, uncappedJacksonCellBias (n := n) epsilon lambda P j := by
      apply Finset.sum_congr rfl
      intro j _
      have hstat : Integrable (fun counts =>
          idealClippedCellPath (n := n) epsilon lambda counts j) μ := by
        apply ((hE j).add (integrable_const
          (thresholdFunReal epsilon lambda (cellVector P j)))).congr
        filter_upwards [] with counts
        dsimp [E]
        ring
      unfold uncappedJacksonCellBias expectedUncappedJacksonCell
      rw [integral_sub]
      · rw [integral_const]
        simp [E, μ, idealClippedCellPath]
      · exact hstat
      · exact integrable_const _

private lemma centeredGoodRisk_integrand_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) :
    Integrable (fun counts =>
      sSup ((fun lambda : ℝ =>
        |idealPilotErrorPart (n := n) epsilon lambda P counts true -
          idealPilotErrorMean (n := n) epsilon lambda P true|) ''
            Set.Icc 0 1) ^ 2) (idealCountLaw (n := n) P) := by
  classical
  let μ := idealCountLaw (n := n) P
  letI : IsProbabilityMeasure μ := by simpa [μ] using hprob
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
      (show 1 ≤ d by omega) P counts j true
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j counts => idealPilotErrorCellPath epsilon P counts j true (hcont j counts)
  have hX (j : Fin d) : Integrable (X j) μ := by
    simpa [X, hcont, μ] using
      idealGoodPilotCellPath_integrable epsilon he he' hn hd P hprob j
  have hX2 (j : Fin d) : Integrable (fun counts => ‖X j counts‖ ^ 2) μ := by
    have hs := idealGoodPilotCellPath_sq_integrable epsilon he he' hn hd P j
    have hs' : Integrable (fun counts => pathSize (X j counts) ^ 2) μ := by
      simpa [X, hcont, μ] using hs
    apply hs'.mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with counts
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnorm : ‖X j counts‖ ≤ pathSize (X j counts) := by
      unfold pathSize
      exact le_add_of_nonneg_right (pathTV_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hZ := centeredPathSum_sq_integrable μ X hX hX2
  apply hZ.congr
  filter_upwards [] with counts
  let Z : Path := ∑ j, (X j counts - ∫ x, X j x ∂μ)
  have hmean (lambda : Time) :
      idealPilotErrorMean (n := n) epsilon lambda P true =
        ∑ j : Fin d, ∫ x, X j x lambda ∂μ := by
    unfold idealPilotErrorMean
    simp_rw [idealPilotErrorPart_eq_sum_cells]
    rw [integral_finsetSum]
    · simp [X, idealPilotErrorCellPath, μ]
    · intro j _
      simpa [X, idealPilotErrorCellPath, μ] using
        (ContinuousMap.evalCLM ℝ lambda).integrable_comp (hX j)
  have heval (j : Fin d) (lambda : Time) :
      (∫ x, X j x ∂μ) lambda = ∫ x, X j x lambda ∂μ := by
    simpa using ((ContinuousMap.evalCLM ℝ lambda).integral_comp_comm (hX j)).symm
  have hpoint (lambda : Time) : Z lambda =
      idealPilotErrorPart (n := n) epsilon lambda P counts true -
        idealPilotErrorMean (n := n) epsilon lambda P true := by
    dsimp [Z]
    simp_rw [ContinuousMap.sum_apply, ContinuousMap.sub_apply, heval]
    rw [idealPilotErrorPart_eq_sum_cells, hmean, Finset.sum_sub_distrib]
    change (∑ j, idealPilotErrorCell (n := n) epsilon lambda P counts j true) -
      (∑ j, ∫ x, X j x lambda ∂μ) = _
    rfl
  rw [← path_norm_eq_sSup_abs_restrict
    (fun lambda => idealPilotErrorPart (n := n) epsilon lambda P counts true -
      idealPilotErrorMean (n := n) epsilon lambda P true)
    (centeredIdealGoodPilotError_continuous epsilon he he' hn hd P hprob counts)]
  congr 2
  apply ContinuousMap.ext
  exact hpoint

private lemma centeredBadRisk_integrand_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) :
    Integrable (fun counts =>
      sSup ((fun lambda : ℝ =>
        |idealPilotErrorPart (n := n) epsilon lambda P counts false -
          idealPilotErrorMean (n := n) epsilon lambda P false|) ''
            Set.Icc 0 1) ^ 2) (idealCountLaw (n := n) P) := by
  classical
  let μ := idealCountLaw (n := n) P
  letI : IsProbabilityMeasure μ := by simpa [μ] using hprob
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j false) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j counts => idealPilotErrorCellPath epsilon P counts j false (hcont j counts)
  have hX (j : Fin d) : Integrable (X j) μ := by
    simpa [X, hcont, μ] using
      idealBadPilotCellPath_integrable epsilon he hn hd P hprob j
  have hX2 (j : Fin d) : Integrable (fun counts => ‖X j counts‖ ^ 2) μ := by
    simpa [X, hcont, μ] using
      idealBadPilotCellPath_norm_sq_integrable epsilon he hn hd P j
  have hZ := centeredPathSum_sq_integrable μ X hX hX2
  apply hZ.congr
  filter_upwards [] with counts
  let Z : Path := ∑ j, (X j counts - ∫ x, X j x ∂μ)
  have hmean (lambda : Time) :
      idealPilotErrorMean (n := n) epsilon lambda P false =
        ∑ j : Fin d, ∫ x, X j x lambda ∂μ := by
    unfold idealPilotErrorMean
    simp_rw [idealPilotErrorPart_eq_sum_cells]
    rw [integral_finsetSum]
    · simp [X, idealPilotErrorCellPath, μ]
    · intro j _
      simpa [X, idealPilotErrorCellPath, μ] using
        (ContinuousMap.evalCLM ℝ lambda).integrable_comp (hX j)
  have heval (j : Fin d) (lambda : Time) :
      (∫ x, X j x ∂μ) lambda = ∫ x, X j x lambda ∂μ := by
    simpa using ((ContinuousMap.evalCLM ℝ lambda).integral_comp_comm (hX j)).symm
  have hpoint (lambda : Time) : Z lambda =
      idealPilotErrorPart (n := n) epsilon lambda P counts false -
        idealPilotErrorMean (n := n) epsilon lambda P false := by
    dsimp [Z]
    simp_rw [ContinuousMap.sum_apply, ContinuousMap.sub_apply, heval]
    rw [idealPilotErrorPart_eq_sum_cells, hmean, Finset.sum_sub_distrib]
    change (∑ j, idealPilotErrorCell (n := n) epsilon lambda P counts j false) -
      (∑ j, ∫ x, X j x lambda ∂μ) = _
    rfl
  rw [← path_norm_eq_sSup_abs_restrict
    (fun lambda => idealPilotErrorPart (n := n) epsilon lambda P counts false -
      idealPilotErrorMean (n := n) epsilon lambda P false)
    (centeredIdealBadPilotError_continuous epsilon he hn hd P hprob counts)]
  congr 2
  apply ContinuousMap.ext
  exact hpoint

private lemma bias_sum_and_envelope_sq_le_rate
    {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d)
    (hbranch : (d : ℝ) / logAlphabet d ≤ n) (P : DiscreteLaw d)
    (epsilon C : ℝ) (hC : 0 ≤ C)
    (hbias : ∀ (j : Fin d) (lambda : ℝ), lambda ∈ Set.Icc (0 : ℝ) 1 →
      uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
        C * (Real.sqrt (cellMass P j /
          (((n : ℝ) / 8) * logAlphabet d)) +
          1 / (((n : ℝ) / 8) * logAlphabet d)))
    (lambda : ℝ) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    (∑ j : Fin d, uncappedJacksonCellBias (n := n) epsilon lambda P j) ≤
        C * ∑ j : Fin d, (Real.sqrt (cellMass P j /
          (((n : ℝ) / 8) * logAlphabet d)) +
          1 / (((n : ℝ) / 8) * logAlphabet d)) ∧
      (C * ∑ j : Fin d, (Real.sqrt (cellMass P j /
          (((n : ℝ) / 8) * logAlphabet d)) +
          1 / (((n : ℝ) / 8) * logAlphabet d))) ^ 2 ≤
        144 * C ^ 2 * d / ((n : ℝ) * logAlphabet d) := by
  let R : ℝ := ((n : ℝ) / 8) * logAlphabet d
  let a : Fin d → ℝ := fun j =>
    Real.sqrt (cellMass P j / R) + 1 / R
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 (j : Fin d) : 0 ≤ a j := by dsimp [a]; positivity
  have hsum : (∑ j : Fin d,
      uncappedJacksonCellBias (n := n) epsilon lambda P j) ≤ C * ∑ j, a j := by
    rw [Finset.mul_sum]
    gcongr with j
    simpa [a, R] using hbias j lambda hlambda
  have hsq : (∑ j : Fin d, a j) ^ 2 ≤ (d : ℝ) * ∑ j, a j ^ 2 := by
    simpa using pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin d))) (f := a) (fun j _ => ha0 j) 1
  have hapoint (j : Fin d) : a j ^ 2 ≤
      2 * (cellMass P j / R + (1 / R) ^ 2) := by
    have hcell : 0 ≤ cellMass P j := by
      unfold cellMass
      exact Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hq : 0 ≤ cellMass P j / R := div_nonneg hcell hR.le
    have hsqrt := Real.sq_sqrt hq
    dsimp [a]
    nlinarith [sq_nonneg (Real.sqrt (cellMass P j / R) - 1 / R)]
  have hasum : ∑ j : Fin d, a j ^ 2 ≤
      2 * (1 / R + d * (1 / R) ^ 2) := by
    calc
      _ ≤ ∑ j : Fin d, 2 * (cellMass P j / R + (1 / R) ^ 2) := by
        gcongr with j
        exact hapoint j
      _ = 2 * (1 / R + d * (1 / R) ^ 2) := by
        rw [← Finset.mul_sum]
        simp_rw [Finset.sum_add_distrib, ← Finset.sum_div]
        rw [discreteLaw_sum_cellMass P]
        simp
  have hr : (d : ℝ) / ((n : ℝ) * logAlphabet d) ≤ 1 := by
    apply (div_le_one (mul_pos (by positivity) hL)).2
    have := (div_le_iff₀ hL).1 hbranch
    norm_num at this ⊢
    exact this
  have hr0 : 0 ≤ (d : ℝ) / ((n : ℝ) * logAlphabet d) := by positivity
  have hscale : (d : ℝ) * (2 * (1 / R + d * (1 / R) ^ 2)) ≤
      144 * d / ((n : ℝ) * logAlphabet d) := by
    let r : ℝ := (d : ℝ) / ((n : ℝ) * logAlphabet d)
    have hleft : (d : ℝ) * (2 * (1 / R + d * (1 / R) ^ 2)) =
        16 * r + 128 * r ^ 2 := by
      dsimp [R, r]
      field_simp
      ring
    have hright : 144 * (d : ℝ) / ((n : ℝ) * logAlphabet d) = 144 * r := by
      dsimp [r]
      ring
    rw [hleft, hright]
    nlinarith [mul_self_le_mul_self hr0 hr]
  refine ⟨by simpa [a, R] using hsum, ?_⟩
  change (C * ∑ j : Fin d, a j) ^ 2 ≤ _
  calc
    _ = C ^ 2 * (∑ j, a j) ^ 2 := by ring
    _ ≤ C ^ 2 * ((d : ℝ) * ∑ j, a j ^ 2) := by gcongr
    _ ≤ C ^ 2 * ((d : ℝ) * (2 * (1 / R + d * (1 / R) ^ 2))) := by gcongr
    _ ≤ C ^ 2 * (144 * d / ((n : ℝ) * logAlphabet d)) := by gcongr
    _ = 144 * C ^ 2 * d / ((n : ℝ) * logAlphabet d) := by ring

private lemma idealProcessRisk_le_rate
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d)
    (hbranch : (d : ℝ) / logAlphabet d ≤ n) (P : DiscreteLaw d)
    (Cbias Cgood Cbad : ℝ) (hCbias : 0 ≤ Cbias)
    (hbias : ∀ (j : Fin d) (lambda : ℝ), lambda ∈ Set.Icc (0 : ℝ) 1 →
      uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
        Cbias * (Real.sqrt (cellMass P j /
          (((n : ℝ) / 8) * logAlphabet d)) +
          1 / (((n : ℝ) / 8) * logAlphabet d)))
    (hgood : centeredIdealPilotErrorRisk (n := n) epsilon P true ≤
      Cgood * d / (((n : ℝ) / 8) * logAlphabet d))
    (hbad : centeredIdealPilotErrorRisk (n := n) epsilon P false ≤
      Cbad * d / (((n : ℝ) / 8) * logAlphabet d)) :
    idealProcessRisk (n := n) epsilon P ≤
      (24 * Cgood + 24 * Cbad + 432 * Cbias ^ 2) * d /
        ((n : ℝ) * logAlphabet d) := by
  classical
  let μ := idealCountLaw (n := n) P
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using idealCountLaw_isProbabilityMeasure P
  let A := fun counts => sSup ((fun lambda : ℝ =>
    |idealPilotErrorPart (n := n) epsilon lambda P counts true -
      idealPilotErrorMean (n := n) epsilon lambda P true|) '' Set.Icc 0 1)
  let B := fun counts => sSup ((fun lambda : ℝ =>
    |idealPilotErrorPart (n := n) epsilon lambda P counts false -
      idealPilotErrorMean (n := n) epsilon lambda P false|) '' Set.Icc 0 1)
  let S : ℝ := Cbias * ∑ j : Fin d,
    (Real.sqrt (cellMass P j / (((n : ℝ) / 8) * logAlphabet d)) +
      1 / (((n : ℝ) / 8) * logAlphabet d))
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    positivity
  have hterm0 (j : Fin d) : 0 ≤
      Real.sqrt (cellMass P j / (((n : ℝ) / 8) * logAlphabet d)) +
        1 / (((n : ℝ) / 8) * logAlphabet d) :=
    add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr (by positivity))
  have hAint : Integrable (fun counts => A counts ^ 2) μ := by
    simpa [A, μ] using centeredGoodRisk_integrand_integrable
      epsilon he he' hn hd P (idealCountLaw_isProbabilityMeasure P)
  have hBint : Integrable (fun counts => B counts ^ 2) μ := by
    simpa [B, μ] using centeredBadRisk_integrand_integrable
      epsilon he hn (show 1 ≤ d by omega) P (idealCountLaw_isProbabilityMeasure P)
  have hSint : Integrable (fun _counts :
      (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) => S ^ 2) μ := integrable_const _
  have hdom : Integrable (fun counts =>
      3 * A counts ^ 2 + 3 * B counts ^ 2 + 3 * S ^ 2) μ :=
    (((hAint.const_mul 3).add (hBint.const_mul 3)).add (hSint.const_mul 3))
  have hpoint (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) :
      sSup ((fun lambda : ℝ =>
        |idealErrorProcess (n := n) epsilon P counts lambda|) ''
          Set.Icc 0 1) ^ 2 ≤
        3 * A counts ^ 2 + 3 * B counts ^ 2 + 3 * S ^ 2 := by
    let E : Path := idealThresholdPath epsilon he hn (show 1 ≤ d by omega) counts -
      dualProcessPath epsilon P
    let G : Path := ⟨fun t : Time =>
      idealPilotErrorPart (n := n) epsilon t P counts true -
        idealPilotErrorMean (n := n) epsilon t P true,
      centeredIdealGoodPilotError_continuous epsilon he he' hn hd P
        (idealCountLaw_isProbabilityMeasure P) counts⟩
    let D : Path := ⟨fun t : Time =>
      idealPilotErrorPart (n := n) epsilon t P counts false -
        idealPilotErrorMean (n := n) epsilon t P false,
      centeredIdealBadPilotError_continuous epsilon he hn (show 1 ≤ d by omega) P
        (idealCountLaw_isProbabilityMeasure P) counts⟩
    have hmean (t : Time) :
        |idealPilotErrorMean (n := n) epsilon t P true +
          idealPilotErrorMean (n := n) epsilon t P false| ≤ S := by
      have hm := idealPilotMean_good_add_bad_abs_le_bias_sum epsilon he he' hn hd P
        (idealCountLaw_isProbabilityMeasure P) t t.2
      have hs := (bias_sum_and_envelope_sq_le_rate hn hd hbranch P epsilon Cbias
        hCbias hbias t t.2).1
      exact hm.trans (by simpa [S] using hs)
    have hnorm : ‖E‖ ≤ ‖G‖ + ‖D‖ + S := by
      apply (ContinuousMap.norm_le E (by
        have : 0 ≤ S := by
          dsimp [S]
          exact mul_nonneg hCbias (Finset.sum_nonneg fun j _ => hterm0 j)
        exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) this)).2
      intro t
      have hdecomp : E t = G t + D t +
          (idealPilotErrorMean (n := n) epsilon t P true +
            idealPilotErrorMean (n := n) epsilon t P false) := by
        dsimp [G, D]
        rw [show E t = idealErrorProcess (n := n) epsilon P counts t by
          simp [E, idealThresholdPath, dualProcessPath, idealErrorProcess,
            dualProcessReal, dualProcess, thresholdFunReal, t.2]]
        rw [idealErrorProcess_good_add_bad]
        ring
      rw [hdecomp, Real.norm_eq_abs]
      calc
        |G t + D t + (idealPilotErrorMean (n := n) epsilon t P true +
            idealPilotErrorMean (n := n) epsilon t P false)| ≤
            |G t| + |D t| + |idealPilotErrorMean (n := n) epsilon t P true +
              idealPilotErrorMean (n := n) epsilon t P false| := by
          calc
            _ ≤ |G t + D t| + |idealPilotErrorMean (n := n) epsilon t P true +
                idealPilotErrorMean (n := n) epsilon t P false| := abs_add_le _ _
            _ ≤ (|G t| + |D t|) +
                |idealPilotErrorMean (n := n) epsilon t P true +
                  idealPilotErrorMean (n := n) epsilon t P false| :=
              add_le_add (abs_add_le _ _) (le_refl _)
        _ ≤ ‖G‖ + ‖D‖ + S := by
          gcongr
          · simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm G t
          · simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm D t
          · exact hmean t
    have hAnorm : ‖G‖ = A counts := by
      simpa [G, A] using path_norm_eq_sSup_abs_restrict
        (fun lambda => idealPilotErrorPart (n := n) epsilon lambda P counts true -
          idealPilotErrorMean (n := n) epsilon lambda P true)
        (centeredIdealGoodPilotError_continuous epsilon he he' hn hd P
          (idealCountLaw_isProbabilityMeasure P) counts)
    have hBnorm : ‖D‖ = B counts := by
      simpa [D, B] using path_norm_eq_sSup_abs_restrict
        (fun lambda => idealPilotErrorPart (n := n) epsilon lambda P counts false -
          idealPilotErrorMean (n := n) epsilon lambda P false)
        (centeredIdealBadPilotError_continuous epsilon he hn (show 1 ≤ d by omega) P
          (idealCountLaw_isProbabilityMeasure P) counts)
    have hEnorm : ‖E‖ = sSup ((fun lambda : ℝ =>
        |idealErrorProcess (n := n) epsilon P counts lambda|) '' Set.Icc 0 1) := by
      simpa [E] using idealThresholdPath_error_norm_eq epsilon he hn
        (show 1 ≤ d by omega) P counts
    have hA0 : 0 ≤ A counts := by rw [← hAnorm]; exact norm_nonneg _
    have hB0 : 0 ≤ B counts := by rw [← hBnorm]; exact norm_nonneg _
    have hS0 : 0 ≤ S := by
      dsimp [S]
      exact mul_nonneg hCbias (Finset.sum_nonneg fun j _ => hterm0 j)
    rw [← hEnorm, ← hAnorm, ← hBnorm]
    have hsq : (‖E‖ : ℝ) ^ 2 ≤ (‖G‖ + ‖D‖ + S) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖G‖ - ‖D‖), sq_nonneg (‖G‖ - S),
      sq_nonneg (‖D‖ - S)]
  unfold idealProcessRisk
  have hideal := idealProcessRisk_integrand_integrable epsilon he hn
    (show 1 ≤ d by omega) P
  calc
    _ ≤ ∫ counts, (3 * A counts ^ 2 + 3 * B counts ^ 2 + 3 * S ^ 2) ∂μ := by
      apply integral_mono hideal hdom
      exact hpoint
    _ = 3 * centeredIdealPilotErrorRisk (n := n) epsilon P true +
        3 * centeredIdealPilotErrorRisk (n := n) epsilon P false + 3 * S ^ 2 := by
      rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const]
      · simp [A, B, μ, centeredIdealPilotErrorRisk]
      · exact hAint.const_mul 3
      · exact hBint.const_mul 3
      · exact (hAint.const_mul 3).add (hBint.const_mul 3)
      · exact hSint.const_mul 3
    _ ≤ 3 * (Cgood * d / (((n : ℝ) / 8) * logAlphabet d)) +
        3 * (Cbad * d / (((n : ℝ) / 8) * logAlphabet d)) +
        3 * (144 * Cbias ^ 2 * d / ((n : ℝ) * logAlphabet d)) := by
      gcongr
      exact (bias_sum_and_envelope_sq_le_rate hn hd hbranch P epsilon Cbias
        hCbias hbias 0 (by constructor <;> norm_num)).2
    _ = (24 * Cgood + 24 * Cbad + 432 * Cbias ^ 2) * d /
        ((n : ℝ) * logAlphabet d) := by ring

private lemma exponential_cap_remainder_le_rate
    {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) :
    Real.exp (-(n : ℝ) / 16) ≤
      16 * d / ((n : ℝ) * logAlphabet d) := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hdpos : 0 < (d : ℝ) := by positivity
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    positivity
  have hLd : logAlphabet d ≤ d := by
    have hlog := Real.log_le_sub_one_of_pos hdpos
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    linarith
  have hu : 0 < (n : ℝ) / 16 := by positivity
  have he : (n : ℝ) / 16 ≤ Real.exp ((n : ℝ) / 16) :=
    le_trans (le_add_of_nonneg_right zero_le_one)
      (Real.add_one_le_exp ((n : ℝ) / 16))
  have hinv : Real.exp (-((n : ℝ) / 16)) ≤ ((n : ℝ) / 16)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hu).2 he
  have hfirst : Real.exp (-(n : ℝ) / 16) ≤ 16 / (n : ℝ) := by
    rw [inv_div] at hinv
    simpa [div_eq_mul_inv] using hinv
  refine hfirst.trans ?_
  apply (div_le_div_iff₀ hnpos (mul_pos hnpos hL)).2
  nlinarith

private lemma pilot_bias_scale_eight
    {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    Real.sqrt (cellMass P j / (((n : ℝ) / 8) * logAlphabet d)) +
        1 / (((n : ℝ) / 8) * logAlphabet d) ≤
      8 * (Real.sqrt (cellMass P j / ((n : ℝ) * logAlphabet d)) +
        1 / ((n : ℝ) * logAlphabet d)) := by
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    positivity
  have hp : 0 ≤ cellMass P j := by
    unfold cellMass
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  let x := cellMass P j / ((n : ℝ) * logAlphabet d)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hrewrite :
      cellMass P j / (((n : ℝ) / 8) * logAlphabet d) = 8 * x := by
    dsimp [x]
    field_simp
  have hsqrt : Real.sqrt (8 * x) ≤ 8 * Real.sqrt x := by
    have hx8 : 0 ≤ 8 * x := by positivity
    have hsx := Real.sq_sqrt hx
    have hsx8 := Real.sq_sqrt hx8
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (8 * x)]
  rw [hrewrite]
  have hinv : 1 / (((n : ℝ) / 8) * logAlphabet d) =
      8 * (1 / ((n : ℝ) * logAlphabet d)) := by
    field_simp
  rw [hinv]
  nlinarith

private lemma observedMarginal_jointMass_local {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (a y : Bool) :
    jointMass (observedMarginal Q) x a y =
      ∑ y0 : Bool, ∑ y1 : Bool, fullMass Q (x, a, y, y0, y1) := by
  classical
  have hmap : (observedMarginal Q).pmf (x, a, y) =
      ∑ y0 : Bool, ∑ y1 : Bool, Q.pmf (x, a, y, y0, y1) := by
    change (Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))) (x, a, y) = _
    rw [PMF.map_apply, tsum_fintype]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · fin_cases a <;> fin_cases y <;> simp [Fintype.sum_prod_type]
    · intro b _hb hbx
      simp [Ne.symm hbx]
    · simp
  change ((observedMarginal Q).pmf (x, a, y)).toReal =
    ∑ y0 : Bool, ∑ y1 : Bool, (Q.pmf (x, a, y, y0, y1)).toReal
  rw [hmap]
  simp [ENNReal.toReal_add, PMF.apply_ne_top]

private lemma observedMarginal_cellMass_local {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) :
    cellMass (observedMarginal Q) x = poCellMass Q x := by
  change (∑ a : Bool, ∑ y : Bool, jointMass (observedMarginal Q) x a y) =
    ∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      fullMass Q (x, a, y, y0, y1)
  simp_rw [observedMarginal_jointMass_local]

-- @node: thm:integrated-process-certificate
/-- The integrated process certificate result. Under [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
theorem integrated_process_certificate (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ C ∈ processHandle epsilon ∧
      ∀ (n d : ℕ) (Q : PotentialLaw d)
        (mu : Measure (Fin n → Obs d)),
        1 ≤ n → 16 ≤ d → (d : ℝ) / logAlphabet d ≤ n →
        IidSampling (observedMarginal Q) mu →
        CausalModelClass epsilon Q →
        (∀ j : Fin d, ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
          uncappedJacksonCellBias (n := n) epsilon lambda (observedMarginal Q) j ≤
            C * (Real.sqrt (poCellMass Q j / (n * logAlphabet d)) +
              1 / (n * logAlphabet d))) ∧
        centeredIdealPilotErrorRisk (n := n) epsilon (observedMarginal Q) true ≤
          C * d / (n * logAlphabet d) ∧
        (∀ j : Fin d,
          badPilotCellEnvelope (n := n) epsilon (observedMarginal Q) j ≤
            C * (d : ℝ) ^ (1 / 4 : ℝ) *
              Real.exp (-10 * logAlphabet d) *
              badPilotCellScale (n := n) (observedMarginal Q) j) ∧
        centeredIdealPilotErrorRisk (n := n) epsilon (observedMarginal Q) false ≤
          C * d / (((n : ℝ) / 8) * logAlphabet d) ∧
        idealProcessRisk (n := n) epsilon (observedMarginal Q) ≤
          C * d / (n * logAlphabet d) ∧
        averagedProcessRisk (n := n) epsilon (observedMarginal Q) ≤
          C * d / (n * logAlphabet d) := by
  obtain ⟨Ccoeff, hCcoeff, hcoeff⟩ :=
    jacksonCoefficientBV_pilot_le epsilon he he'
  obtain ⟨Cbias, hCbias, hbias⟩ :=
    uncappedJacksonCellBias_le_rate epsilon he he'
  obtain ⟨Cgood, hCgood, hgood⟩ :=
    centeredIdealGoodPilotErrorRisk_le_rate epsilon he he'
  obtain ⟨Cenv, hCenv, henv⟩ := badPilotCellEnvelope_le epsilon he
  obtain ⟨Cbad, hCbad, hbad⟩ :=
    centeredIdealBadPilotErrorRisk_le_rate epsilon he
  obtain ⟨Ccap, hCcap, hcap⟩ := capTransferRisk epsilon he he'
  let Ki : ℝ := 24 * Cgood + 24 * Cbad + 432 * Cbias ^ 2
  let C : ℝ := 1 + Ccoeff + Real.exp 115 + 8 * Cbias + 8 * Cgood +
    Cenv + Cbad + Ki + Ccap * (Ki + 16)
  have hKi : 0 < Ki := by dsimp [Ki]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hcapKi : 0 < Ccap * (Ki + 16) := by positivity
  have hcoeffC : Ccoeff ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have hexpC : Real.exp 115 ≤ C := by
    dsimp [C]; nlinarith
  have hbiasC : 8 * Cbias ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have hgoodC : 8 * Cgood ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have henvC : Cenv ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have hbadC : Cbad ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have hidealC : Ki ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have havgC : Ccap * (Ki + 16) ≤ C := by
    dsimp [C]; nlinarith [Real.exp_pos 115]
  have hbiasBaseC : Cbias ≤ C := by nlinarith
  have hgoodBaseC : Cgood ≤ C := by nlinarith
  refine ⟨C, hC, ?_, ?_⟩
  · refine ⟨hC, ?_⟩
    intro n d P hn hd hbranch
    have hL : 0 < logAlphabet d := by
      unfold logAlphabet
      rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
      positivity
    have hprob : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
      idealCountLaw_isProbabilityMeasure P
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro pilot
      dsimp only
      constructor
      · calc
          jacksonCoefficientBV epsilon ((n : ℝ) / 8) d pilot ≤
              Ccoeff * (∑ zeta : Cell,
                pilotRadius ((n : ℝ) / 8) d pilot zeta) *
                Real.exp (12 * jacksonDegree d) :=
            hcoeff ((n : ℝ) / 8) (by positivity) d (by omega) pilot
          _ ≤ C * (∑ zeta : Cell,
                pilotRadius ((n : ℝ) / 8) d pilot zeta) *
                Real.exp (12 * jacksonDegree d) := by
            have hsum : 0 ≤ ∑ zeta : Cell,
                pilotRadius ((n : ℝ) / 8) d pilot zeta :=
              Finset.sum_nonneg fun z _ =>
                (pilotRadius_pos_of_pos (by positivity) (by omega) pilot z).le
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeffC hsum) (Real.exp_nonneg _)
      · have hdegree := jacksonDegree_exponential_budget d hd
        calc
          (∑ zeta : Cell, pilotRadius ((n : ℝ) / 8) d pilot zeta) ^ 2 *
              Real.exp (24 * jacksonDegree d +
                16 * (jacksonDegree d : ℝ) ^ 2 / logAlphabet d) ≤
              (∑ zeta : Cell, pilotRadius ((n : ℝ) / 8) d pilot zeta) ^ 2 *
                (Real.exp 115 * (d : ℝ) ^ (1 / 16 : ℝ)) := by
            gcongr
          _ = Real.exp 115 * (d : ℝ) ^ (1 / 16 : ℝ) *
                (∑ zeta : Cell, pilotRadius ((n : ℝ) / 8) d pilot zeta) ^ 2 := by
            ring
          _ ≤ C * (d : ℝ) ^ (1 / 16 : ℝ) *
                (∑ zeta : Cell, pilotRadius ((n : ℝ) / 8) d pilot zeta) ^ 2 := by
            gcongr
    · exact (hgood hn hd hbranch P hprob).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgoodBaseC (Nat.cast_nonneg d)) (by positivity))
    · intro j lambda hlambda
      exact (hbias hn hd P j lambda hlambda).trans
        (mul_le_mul_of_nonneg_right hbiasBaseC
          (add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr (by positivity))))
    · intro j
      have hscale : 0 ≤ badPilotCellScale (n := n) P j := by
        unfold badPilotCellScale
        exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg hL.le (by positivity))
      exact (henv hn (by omega) P j).trans (by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right henvC (Real.rpow_nonneg (by positivity) _))
            (Real.exp_nonneg _)) hscale)
    · exact (hbad hn hd hbranch P hprob).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbadC (Nat.cast_nonneg d)) (by positivity))
  · intro n d Q mu hn hd hbranch _hsampling _hmodel
    let P := observedMarginal Q
    have hL : 0 < logAlphabet d := by
      unfold logAlphabet
      rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
      positivity
    have hden : 0 ≤ (n : ℝ) * logAlphabet d := by positivity
    have hprob : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
      idealCountLaw_isProbabilityMeasure P
    have hgoodP := hgood hn hd hbranch P hprob
    have hbadP := hbad hn hd hbranch P hprob
    have hidealP : idealProcessRisk (n := n) epsilon P ≤
        Ki * d / ((n : ℝ) * logAlphabet d) := by
      simpa [Ki] using idealProcessRisk_le_rate epsilon he he' hn hd hbranch P
        Cbias Cgood Cbad hCbias.le (hbias hn hd P) hgoodP hbadP
    have havgP : averagedProcessRisk (n := n) epsilon P ≤
        (Ccap * (Ki + 16)) * d / ((n : ℝ) * logAlphabet d) := by
      calc
        _ ≤ Ccap * (idealProcessRisk (n := n) epsilon P +
              Real.exp (-(n : ℝ) / 16)) := hcap n d hn hd P
        _ ≤ Ccap * (Ki * d / ((n : ℝ) * logAlphabet d) +
              16 * d / ((n : ℝ) * logAlphabet d)) := by
          gcongr
          exact exponential_cap_remainder_le_rate hn hd
        _ = (Ccap * (Ki + 16)) * d / ((n : ℝ) * logAlphabet d) := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j lambda hlambda
      have hmass : cellMass P j = poCellMass Q j :=
        observedMarginal_cellMass_local Q j
      calc
        uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
            Cbias * (Real.sqrt (cellMass P j /
              (((n : ℝ) / 8) * logAlphabet d)) +
              1 / (((n : ℝ) / 8) * logAlphabet d)) :=
          hbias hn hd P j lambda hlambda
        _ ≤ Cbias * (8 * (Real.sqrt (cellMass P j /
              ((n : ℝ) * logAlphabet d)) +
              1 / ((n : ℝ) * logAlphabet d))) := by
          gcongr
          exact pilot_bias_scale_eight hn (by omega) P j
        _ = (8 * Cbias) * (Real.sqrt (poCellMass Q j /
              ((n : ℝ) * logAlphabet d)) +
              1 / ((n : ℝ) * logAlphabet d)) := by rw [hmass]; ring
        _ ≤ C * (Real.sqrt (poCellMass Q j /
              ((n : ℝ) * logAlphabet d)) +
              1 / ((n : ℝ) * logAlphabet d)) := by
          exact mul_le_mul_of_nonneg_right hbiasC
            (add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr hden))
    · calc
        centeredIdealPilotErrorRisk (n := n) epsilon P true ≤
            Cgood * d / (((n : ℝ) / 8) * logAlphabet d) := hgoodP
        _ = (8 * Cgood) * d / ((n : ℝ) * logAlphabet d) := by ring
        _ ≤ C * d / ((n : ℝ) * logAlphabet d) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hgoodC (Nat.cast_nonneg d)) hden
    · intro j
      have hscale : 0 ≤ badPilotCellScale (n := n) P j := by
        unfold badPilotCellScale
        exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg hL.le (by positivity))
      exact (henv hn (by omega) P j).trans (by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right henvC (Real.rpow_nonneg (by positivity) _))
            (Real.exp_nonneg _)) hscale)
    · exact hbadP.trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbadC (Nat.cast_nonneg d)) (by positivity))
    · exact hidealP.trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hidealC (Nat.cast_nonneg d)) hden)
    · exact havgP.trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right havgC (Nat.cast_nonneg d)) hden)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
