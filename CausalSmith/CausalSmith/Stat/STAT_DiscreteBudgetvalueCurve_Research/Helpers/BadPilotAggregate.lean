module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.BadPilotEnvelope
public import Mathlib.Analysis.Convex.Integral

/-! Aggregate centered risk of the bad-pilot cell paths. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Stat.Concentration.BoundedVariation

/-- A bad-pilot cell path is Bochner integrable once its squared norm is
integrable. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
-- @node: idealBadPilotCellPath_integrable
lemma idealBadPilotCellPath_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) (j : Fin d) :
    Integrable (fun counts =>
      idealPilotErrorCellPath epsilon P counts j false
        (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false))
      (idealCountLaw (n := n) P) := by
  let : BorelSpace Path := ⟨rfl⟩
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) := hprob
  let X := fun counts =>
    idealPilotErrorCellPath epsilon P counts j false
      (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false)
  have hX2 : Integrable (fun counts => ‖X counts‖ ^ 2)
      (idealCountLaw (n := n) P) := by
    simpa [X] using idealBadPilotCellPath_norm_sq_integrable
      epsilon he hn hd P j
  have hmem : MemLp X 2 (idealCountLaw (n := n) P) :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_of_countable X).aestronglyMeasurable).2 hX2
  exact hmem.integrable (by norm_num)

/-- The scalar centered bad-pilot risk is the squared norm risk of the
centered sum of continuous bad-pilot cell paths. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
-- @node: centeredIdealBadPilotErrorRisk_eq_path_integral
lemma centeredIdealBadPilotErrorRisk_eq_path_integral
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) :
    let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j false) :=
      fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn hd
        P counts j false
    centeredIdealPilotErrorRisk (n := n) epsilon P false =
      ∫ counts, ‖∑ j, (idealPilotErrorCellPath epsilon P counts j false
          (hcont j counts) -
        ∫ x, idealPilotErrorCellPath epsilon P x j false (hcont j x)
          ∂idealCountLaw (n := n) P)‖ ^ 2
        ∂idealCountLaw (n := n) P := by
  classical
  dsimp only
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j false) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn hd
      P counts j false
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j counts => idealPilotErrorCellPath epsilon P counts j false (hcont j counts)
  have hXint (j : Fin d) : Integrable (X j) (idealCountLaw (n := n) P) := by
    simpa [X, hcont] using
      idealBadPilotCellPath_integrable epsilon he hn hd P hprob j
  have hmean (lambda : Time) :
      idealPilotErrorMean (n := n) epsilon lambda P false =
        ∑ j : Fin d, ∫ x, X j x lambda ∂idealCountLaw (n := n) P := by
    unfold idealPilotErrorMean
    simp_rw [idealPilotErrorPart_eq_sum_cells]
    rw [integral_finsetSum]
    · simp [X, idealPilotErrorCellPath]
    · intro j _
      simpa [X, idealPilotErrorCellPath] using
        (ContinuousMap.evalCLM ℝ lambda).integrable_comp (hXint j)
  have heval (j : Fin d) (lambda : Time) :
      (∫ x, X j x ∂idealCountLaw (n := n) P) lambda =
        ∫ x, X j x lambda ∂idealCountLaw (n := n) P := by
    simpa using ((ContinuousMap.evalCLM ℝ lambda).integral_comp_comm
      (hXint j)).symm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun counts => by
    let Z : Path := ∑ j, (X j counts -
      ∫ x, X j x ∂idealCountLaw (n := n) P)
    have hpoint (lambda : Time) : Z lambda =
        idealPilotErrorPart (n := n) epsilon lambda P counts false -
          idealPilotErrorMean (n := n) epsilon lambda P false := by
      dsimp [Z]
      simp_rw [ContinuousMap.sum_apply, ContinuousMap.sub_apply, heval]
      rw [idealPilotErrorPart_eq_sum_cells, hmean, Finset.sum_sub_distrib]
      simp only [X, idealPilotErrorCellPath]
      congr 1
    have hg : Continuous (fun lambda : Time =>
        idealPilotErrorPart (n := n) epsilon lambda P counts false -
          idealPilotErrorMean (n := n) epsilon lambda P false) := by
      convert Z.continuous using 1
      funext lambda
      exact (hpoint lambda).symm
    change (sSup ((fun lambda : ℝ =>
      |idealPilotErrorPart (n := n) epsilon lambda P counts false -
        idealPilotErrorMean (n := n) epsilon lambda P false|) '' Set.Icc 0 1)) ^ 2 =
      ‖Z‖ ^ 2
    rw [← path_norm_eq_sSup_abs_restrict
      (fun lambda => idealPilotErrorPart (n := n) epsilon lambda P counts false -
        idealPilotErrorMean (n := n) epsilon lambda P false) hg]
    congr 2
    apply ContinuousMap.ext
    intro lambda
    exact (hpoint lambda).symm

/-- The centered aggregate bad-pilot error is continuous in the shadow price. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
lemma centeredIdealBadPilotError_continuous
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P))
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) :
    Continuous (fun lambda : Time =>
      idealPilotErrorPart (n := n) epsilon lambda P counts false -
        idealPilotErrorMean (n := n) epsilon lambda P false) := by
  classical
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j false) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j x => idealPilotErrorCellPath epsilon P x j false (hcont j x)
  have hXint (j : Fin d) : Integrable (X j) (idealCountLaw (n := n) P) := by
    simpa [X, hcont] using
      idealBadPilotCellPath_integrable epsilon he hn hd P hprob j
  let Y : Path := ∑ j, X j counts
  let M : Path := ∑ j, ∫ x, X j x ∂idealCountLaw (n := n) P
  apply (Y - M).continuous.congr
  intro lambda
  have heval (j : Fin d) :
      (∫ x, X j x ∂idealCountLaw (n := n) P) lambda =
        ∫ x, X j x lambda ∂idealCountLaw (n := n) P := by
    simpa using
      ((ContinuousMap.evalCLM ℝ lambda).integral_comp_comm (hXint j)).symm
  simp only [Y, M, ContinuousMap.sub_apply, ContinuousMap.sum_apply]
  simp_rw [heval]
  rw [idealPilotErrorPart_eq_sum_cells]
  unfold idealPilotErrorMean
  simp_rw [idealPilotErrorPart_eq_sum_cells]
  rw [integral_finsetSum]
  · simp [X, idealPilotErrorCellPath]
  · intro j _
    simpa [X, idealPilotErrorCellPath] using
      (ContinuousMap.evalCLM ℝ lambda).integrable_comp (hXint j)

/-- Centering and summing finitely many bad-pilot paths costs at most four
times the alphabet size times the sum of their uncentered squared norms. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
-- @node: centeredIdealBadPilotErrorRisk_le_cell_norms
lemma centeredIdealBadPilotErrorRisk_le_cell_norms
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) :
    centeredIdealPilotErrorRisk (n := n) epsilon P false ≤
      4 * d * ∑ j : Fin d, badPilotCellEnvelope (n := n) epsilon P j ^ 2 := by
  classical
  let μ := idealCountLaw (n := n) P
  letI : IsProbabilityMeasure μ := by simpa [μ] using hprob
  let : BorelSpace Path := ⟨rfl⟩
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j counts => idealPilotErrorCellPath epsilon P counts j false
      (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false)
  have hX2 (j : Fin d) : Integrable (fun counts => ‖X j counts‖ ^ 2) μ := by
    simpa [X, μ] using idealBadPilotCellPath_norm_sq_integrable
      epsilon he hn hd P j
  have hX (j : Fin d) : Integrable (X j) μ := by
    simpa [X, μ] using idealBadPilotCellPath_integrable epsilon he hn hd P hprob j
  have hab (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hmean2 (j : Fin d) : ‖∫ counts, X j counts ∂μ‖ ^ 2 ≤
      ∫ counts, ‖X j counts‖ ^ 2 ∂μ := by
    let q : Path → ℝ := fun z => ‖z‖ ^ 2
    have hconv : ConvexOn ℝ Set.univ q :=
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : Path → ℝ)).pow
        (fun z _ => norm_nonneg z) 2
    have hq : Integrable (q ∘ X j) μ := by
      change Integrable (fun counts => ‖X j counts‖ ^ 2) μ
      exact hX2 j
    simpa only [q, Function.comp_apply] using
      hconv.map_integral_le (by fun_prop) isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _) (hX j)
        hq
  have hcenter2 (j : Fin d) : Integrable (fun counts =>
      ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2) μ := by
    have hdom : Integrable (fun counts =>
        2 * ‖X j counts‖ ^ 2 + 2 * ‖∫ x, X j x ∂μ‖ ^ 2) μ :=
      ((hX2 j).const_mul 2).add (integrable_const _)
    apply hdom.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with counts
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2 ≤
          (‖X j counts‖ + ‖∫ x, X j x ∂μ‖) ^ 2 := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := hab _ _
  have hcenterInt (j : Fin d) :
      (∫ counts, ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2 ∂μ) ≤
        4 * ∫ counts, ‖X j counts‖ ^ 2 ∂μ := by
    calc
      _ ≤ ∫ counts,
          (2 * ‖X j counts‖ ^ 2 + 2 * ‖∫ x, X j x ∂μ‖ ^ 2) ∂μ := by
        apply integral_mono (hcenter2 j)
          (((hX2 j).const_mul 2).add (integrable_const _))
        intro counts
        calc
          ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2 ≤
              (‖X j counts‖ + ‖∫ x, X j x ∂μ‖) ^ 2 := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ _ := hab _ _
      _ = 2 * (∫ counts, ‖X j counts‖ ^ 2 ∂μ) +
          2 * ‖∫ x, X j x ∂μ‖ ^ 2 := by
        rw [integral_add, integral_const_mul, integral_const]
        · simp
        · exact (hX2 j).const_mul 2
        · exact integrable_const _
      _ ≤ _ := by nlinarith [hmean2 j]
  rw [centeredIdealBadPilotErrorRisk_eq_path_integral epsilon he hn hd P hprob]
  let Z : ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path := fun counts =>
    ∑ j : Fin d, (X j counts - ∫ x, X j x ∂μ)
  have hdom : Integrable (fun counts => (d : ℝ) * ∑ j : Fin d,
      ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ (fun j _ => hcenter2 j)
  have hZ2 : Integrable (fun counts => ‖Z counts‖ ^ 2) μ := by
    apply hdom.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with counts
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖Z counts‖ ^ 2 ≤
          (∑ j : Fin d, ‖X j counts - ∫ x, X j x ∂μ‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ _ := by
        simpa using pow_sum_le_card_mul_sum_pow
          (s := (Finset.univ : Finset (Fin d)))
          (f := fun j => ‖X j counts - ∫ x, X j x ∂μ‖)
          (fun _ _ => norm_nonneg _) 1
  calc
    _ = ∫ counts, ‖Z counts‖ ^ 2 ∂μ := by rfl
    _ ≤ ∫ counts, (d : ℝ) * ∑ j : Fin d,
        ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2 ∂μ := by
      apply integral_mono hZ2 hdom
      intro counts
      dsimp
      calc
        ‖Z counts‖ ^ 2 ≤
            (∑ j : Fin d, ‖X j counts - ∫ x, X j x ∂μ‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ _ := by
          simpa using pow_sum_le_card_mul_sum_pow
            (s := (Finset.univ : Finset (Fin d)))
            (f := fun j => ‖X j counts - ∫ x, X j x ∂μ‖)
            (fun _ _ => norm_nonneg _) 1
    _ = (d : ℝ) * ∑ j : Fin d,
        ∫ counts, ‖X j counts - ∫ x, X j x ∂μ‖ ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      intro j _
      exact hcenter2 j
    _ ≤ (d : ℝ) * ∑ j : Fin d,
        (4 * ∫ counts, ‖X j counts‖ ^ 2 ∂μ) := by
      gcongr with j
      exact hcenterInt j
    _ = 4 * ((d : ℝ) * ∑ j : Fin d, ∫ counts, ‖X j counts‖ ^ 2 ∂μ) := by
      rw [← Finset.mul_sum]
      ring
    _ = 4 * d * ∑ j : Fin d,
        badPilotCellEnvelope (n := n) epsilon P j ^ 2 := by
      have hcell (j : Fin d) : (∫ counts, ‖X j counts‖ ^ 2 ∂μ) =
          badPilotCellEnvelope (n := n) epsilon P j ^ 2 := by
        unfold badPilotCellEnvelope
        rw [Real.sq_sqrt]
        · apply integral_congr_ae
          filter_upwards [] with counts
          rw [idealPilotErrorCellPath_norm_eq_sSup epsilon P counts j false]
          by_cases hg : idealPilotGood (n := n) P counts j <;>
            simp [X, μ, idealPilotErrorCell, idealClippedCellPath, hg]
        · exact integral_nonneg fun _ => sq_nonneg _
      rw [Finset.sum_congr rfl (fun j _ => hcell j)]
      ring

/-- Equations (28) and (32) give the centered bad-pilot aggregate bound before
the final elementary exponential absorption. With [the specified inputs and conditions](hyp:epsilon,he), [the stated relationship holds](goal). -/
-- @node: centeredIdealBadPilotErrorRisk_le_raw
lemma centeredIdealBadPilotErrorRisk_le_raw
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d),
      IsProbabilityMeasure (idealCountLaw (n := n) P) →
      centeredIdealPilotErrorRisk (n := n) epsilon P false ≤
        C * d * (d : ℝ) ^ (1 / 2 : ℝ) *
          Real.exp (-20 * logAlphabet d) *
          (2 * logAlphabet d / ((n : ℝ) / 8) +
            2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) := by
  obtain ⟨C₀, hC₀, henv⟩ := badPilotCellEnvelope_le epsilon he
  refine ⟨4 * C₀ ^ 2, by positivity, ?_⟩
  intro n d hn hd P hprob
  have hcell (j : Fin d) : badPilotCellEnvelope (n := n) epsilon P j ^ 2 ≤
      C₀ ^ 2 * (d : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-20 * logAlphabet d) *
        badPilotCellScale (n := n) P j ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (henv hn hd P j) 2
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hr : ((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
        (d : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0]
      norm_num
    have he2 : (Real.exp (-10 * logAlphabet d)) ^ 2 =
        Real.exp (-20 * logAlphabet d) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [badPilotCellEnvelope, mul_pow, hr, he2] using h
  calc
    centeredIdealPilotErrorRisk (n := n) epsilon P false ≤
        4 * d * ∑ j : Fin d,
          badPilotCellEnvelope (n := n) epsilon P j ^ 2 :=
      centeredIdealBadPilotErrorRisk_le_cell_norms epsilon he hn hd P hprob
    _ ≤ 4 * d * ∑ j : Fin d,
        (C₀ ^ 2 * (d : ℝ) ^ (1 / 2 : ℝ) *
          Real.exp (-20 * logAlphabet d) *
          badPilotCellScale (n := n) P j ^ 2) := by
      gcongr with j
      exact hcell j
    _ = (4 * C₀ ^ 2) * d * (d : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-20 * logAlphabet d) *
        ∑ j : Fin d, badPilotCellScale (n := n) P j ^ 2 := by
      simp_rw [← Finset.mul_sum]
      ring
    _ ≤ (4 * C₀ ^ 2) * d * (d : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-20 * logAlphabet d) *
          (2 * logAlphabet d / ((n : ℝ) / 8) +
            2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) := by
      gcongr
      exact sum_badPilotCellScale_sq_le hn hd P

/-- The exponential bad-event factor absorbs the residual alphabet and
logarithmic powers on the large-alphabet branch. With [the specified inputs and conditions](hyp:n,d,hn,hd,hbranch), [the stated relationship holds](goal). -/
-- @node: badPilot_raw_scale_le_rate
lemma badPilot_raw_scale_le_rate {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d)
    (hbranch : (d : ℝ) / logAlphabet d ≤ n) :
    (d : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-20 * logAlphabet d) *
        (2 * logAlphabet d / ((n : ℝ) / 8) +
          2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) ≤
      18 / (((n : ℝ) / 8) * logAlphabet d) := by
  let D : ℝ := d
  let L : ℝ := logAlphabet d
  let m : ℝ := (n : ℝ) / 8
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ d by omega)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hL : L = 1 + Real.log D := by
    dsimp [L, D]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hDpos),
      Real.log_exp]
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hLD : L ≤ D := by
    rw [hL]
    linarith [Real.log_le_sub_one_of_pos hDpos]
  have hm : 0 < m := by dsimp [m]; positivity
  have hbranch' : D / L ≤ 8 * m := by
    dsimp [D, L, m] at hbranch ⊢
    norm_num at hbranch ⊢
    linarith
  have hDLm : D * L / m ≤ 8 * L ^ 2 := by
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    apply (div_le_iff₀ hm).2
    have h := (div_le_iff₀ hLpos).1 hbranch'
    nlinarith
  have hexp : Real.exp (-20 * L) ≤ D ^ (-(9 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hDpos]
    apply Real.exp_le_exp.mpr
    rw [hL]
    nlinarith
  have hpow : D ^ (1 / 2 : ℝ) * D ^ (-(9 / 2 : ℝ)) = D⁻¹ ^ 4 := by
    rw [← Real.rpow_add hDpos]
    norm_num
  have hcoef : D ^ (1 / 2 : ℝ) * Real.exp (-20 * L) ≤ D⁻¹ ^ 4 := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hDpos.le _)
  have hpoly : 2 * L ^ 2 + 16 * L ^ 4 ≤ 18 * D ^ 4 := by
    have hL0 : 0 ≤ L := hL1.trans' zero_le_one
    have h2 : L ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hL0 hLD 2
    have h4 : L ^ 4 ≤ D ^ 4 := pow_le_pow_left₀ hL0 hLD 4
    have hDsq : 1 ≤ D ^ 2 := by nlinarith [sq_nonneg (D - 1)]
    have hD2 : D ^ 2 ≤ D ^ 4 := by
      nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hDsq)]
    nlinarith
  have hcore : D ^ (1 / 2 : ℝ) * Real.exp (-20 * L) *
      (2 * L ^ 2 + 16 * L ^ 4) ≤ 18 := by
    calc
      _ ≤ D⁻¹ ^ 4 * (2 * L ^ 2 + 16 * L ^ 4) := by gcongr
      _ ≤ D⁻¹ ^ 4 * (18 * D ^ 4) := by gcongr
      _ = 18 := by field_simp
  have hrewrite :
      (2 * L / m + 2 * D * (L / m) ^ 2) * (m * L) =
        2 * L ^ 2 + 2 * (D * L / m) * L ^ 2 := by field_simp
  have hscaled : D ^ (1 / 2 : ℝ) * Real.exp (-20 * L) *
      (2 * L / m + 2 * D * (L / m) ^ 2) * (m * L) ≤ 18 := by
    rw [mul_assoc, hrewrite]
    calc
      D ^ (1 / 2 : ℝ) * Real.exp (-20 * L) *
          (2 * L ^ 2 + 2 * (D * L / m) * L ^ 2) ≤
          D ^ (1 / 2 : ℝ) * Real.exp (-20 * L) *
            (2 * L ^ 2 + 16 * L ^ 4) := by
        have hh := mul_le_mul_of_nonneg_right hDLm (sq_nonneg L)
        have hin : 2 * L ^ 2 + 2 * (D * L / m) * L ^ 2 ≤
            2 * L ^ 2 + 16 * L ^ 4 := by
          nlinarith [sq_nonneg (L ^ 2)]
        exact mul_le_mul_of_nonneg_left hin
          (mul_nonneg (Real.rpow_nonneg hDpos.le _) (Real.exp_nonneg _))
      _ ≤ 18 := hcore
  have hmL : 0 < m * L := mul_pos hm (lt_of_lt_of_le zero_lt_one hL1)
  apply (le_div_iff₀ hmL).2
  simpa [D, L, m, mul_assoc] using hscaled

/-- Equation (34): the centered bad-pilot aggregate has the advertised rate. With [the specified inputs and conditions](hyp:epsilon,he), [the stated relationship holds](goal). -/
-- @node: centeredIdealBadPilotErrorRisk_le_rate
lemma centeredIdealBadPilotErrorRisk_le_rate
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d)
      (hbranch : (d : ℝ) / logAlphabet d ≤ n) (P : DiscreteLaw d),
      IsProbabilityMeasure (idealCountLaw (n := n) P) →
      centeredIdealPilotErrorRisk (n := n) epsilon P false ≤
        C * d / (((n : ℝ) / 8) * logAlphabet d) := by
  obtain ⟨C₀, hC₀, hraw⟩ :=
    centeredIdealBadPilotErrorRisk_le_raw epsilon he
  refine ⟨18 * C₀, by positivity, ?_⟩
  intro n d hn hd hbranch P hprob
  calc
    _ ≤ C₀ * d * ((d : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-20 * logAlphabet d) *
        (2 * logAlphabet d / ((n : ℝ) / 8) +
          2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2)) := by
      simpa [mul_assoc] using hraw hn (show 1 ≤ d by omega) P hprob
    _ ≤ C₀ * d * (18 / (((n : ℝ) / 8) * logAlphabet d)) := by
      gcongr
      exact badPilot_raw_scale_le_rate hn hd hbranch
    _ = (18 * C₀) * d / (((n : ℝ) / 8) * logAlphabet d) := by ring

end CausalSmith.Stat.DiscreteBudgetvalueCurve
