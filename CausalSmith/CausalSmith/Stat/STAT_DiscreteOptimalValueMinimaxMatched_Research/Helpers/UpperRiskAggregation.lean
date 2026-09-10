import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.UpperRiskCoupling
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TIdentificationAndExtension

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: sumCellBias_sq_le
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the stated c condition holds](hyp:hC), and [the Poisson intensity is positive](hyp:hm), and [the Lipschitz scale is positive](hyp:hL), and [the stated p condition holds](hyp:hp), and [the stated sump condition holds](hyp:hsump), and [the quadratic weights are nonnegative](hyp:hb), then [the stated sum cell bias squared upper bound relation holds](goal). -/
lemma sumCellBias_sq_le {d : ℕ} {b p : Fin d → ℝ} {C m L : ℝ}
    (hd : 1 ≤ d) (hC : 0 ≤ C) (hm : 0 < m) (hL : 0 < L)
    (hp : ∀ x, 0 ≤ p x) (hsump : ∑ x, p x = 1)
    (hb : ∀ x, |b x| ≤ C * (Real.sqrt (p x / (m * L)) + 1 / (m * L))) :
    (∑ x, b x) ^ 2 ≤ 2 * C ^ 2 * (d / (m * L) + d ^ 2 / (m ^ 2 * L ^ 2)) := by
  have hsqrt : (∑ x : Fin d, Real.sqrt (p x)) ^ 2 ≤ d := by
    calc
      (∑ x : Fin d, Real.sqrt (p x)) ^ 2 ≤
          (∑ _x : Fin d, (1 : ℝ) ^ 2) * ∑ x : Fin d, (Real.sqrt (p x)) ^ 2 :=
        by simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _ => (1 : ℝ)) (fun x => Real.sqrt (p x)))
      _ = d := by simp [Real.sq_sqrt (hp _), hsump]
  have habs : |∑ x, b x| ≤ C *
      (Real.sqrt (d / (m * L)) + d / (m * L)) := by
    calc
      |∑ x, b x| ≤ ∑ x, |b x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, C * (Real.sqrt (p x / (m * L)) + 1 / (m * L)) :=
        Finset.sum_le_sum fun x _ => hb x
      _ = C * ((∑ x, Real.sqrt (p x / (m * L))) + d / (m * L)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
        ring
      _ ≤ C * (Real.sqrt (d / (m * L)) + d / (m * L)) := by
        gcongr
        rw [show (∑ x : Fin d, Real.sqrt (p x / (m * L))) =
            (∑ x, Real.sqrt (p x)) / Real.sqrt (m * L) by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          rw [Real.sqrt_div (hp x)]]
        rw [div_le_iff₀ (Real.sqrt_pos.2 (mul_pos hm hL))]
        rw [← Real.sqrt_mul (by positivity : 0 ≤ (d : ℝ) / (m * L)),
          show d / (m * L) * (m * L) = d by field_simp]
        have hs0 : 0 ≤ ∑ x : Fin d, Real.sqrt (p x) := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
        have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        exact (sq_le_sq₀ hs0 (Real.sqrt_nonneg _)).mp (by
          simpa [Real.sq_sqrt hd0] using hsqrt)
  have hright0 : 0 ≤ C * (Real.sqrt (d / (m * L)) + d / (m * L)) := by positivity
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hright0).2 habs
  rw [sq_abs] at hsquare
  have hinner : (Real.sqrt (d / (m * L)) + d / (m * L)) ^ 2 ≤
      2 * (d / (m * L) + (d / (m * L)) ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt (d / (m * L)) - d / (m * L)),
      Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ) / (m * L))]
  calc
    (∑ x, b x) ^ 2 ≤ C ^ 2 *
        (Real.sqrt (d / (m * L)) + d / (m * L)) ^ 2 := by
      simpa [mul_pow] using hsquare
    _ ≤ C ^ 2 * (2 * (d / (m * L) + (d / (m * L)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hinner (sq_nonneg C)
    _ = _ := by field_simp

-- @node: canonicalJacksonCellStatistic_memLp_two
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq), then [the stated canonical jackson cell statistic mem lp two relation holds](goal). -/
lemma canonicalJacksonCellStatistic_memLp_two
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j) :
    MemLp (fun z : (Cell → ℕ) × (Cell → ℕ) =>
      jacksonCellStatistic canonicalJacksonTuning epsilon d m z.1 z.2 hm) 2
      (pilotEvaluationLaw m q) := by
  let μp := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  let μe := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  let score := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
    (fun j (w : Cell → ℕ) => w j)
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH (logAlphabet d)
    m.toNNReal (fun j => (q j).toNNReal)
  let target := globalCellValue epsilon q
  let A := 2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)
  have hscoreLp : MemLp score 2 μp := by
    simpa [score, μp] using
      canonicalNormalizedAggregateScore_memLp_two m hm d hd q hq
  have hL0 : 0 ≤ logAlphabet d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hdR]
  have hdom : MemLp (fun z : (Cell → ℕ) × (Cell → ℕ) => A * score z.1)
      2 (μp.prod μe) := (hscoreLp.const_mul A).comp_fst μe
  have herr : MemLp (fun z : (Cell → ℕ) × (Cell → ℕ) =>
      jacksonCellStatistic canonicalJacksonTuning epsilon d m z.1 z.2 hm - target)
      2 (μp.prod μe) := by
    apply hdom.mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have hs0 : 0 ≤ score z.1 := by
      dsimp [score]
      unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
      apply Finset.sum_nonneg
      intro j _hj
      unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedDeviation
        Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
      exact add_nonneg (abs_nonneg _) (mul_nonneg (by positivity)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity)))
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    rw [abs_of_nonneg hs0, abs_of_nonneg hA0]
    simpa [A, score, target] using
      canonicalJacksonCellError_le_normalizedAggregateScore
        epsilon m hepsilon hm d hd z.1 z.2 q hq
  have hconst : MemLp (fun _ : (Cell → ℕ) × (Cell → ℕ) => target)
      2 (μp.prod μe) := memLp_const _
  rw [show pilotEvaluationLaw m q = μp.prod μe by rfl]
  convert herr.add hconst using 1
  ext z
  simp only [Pi.add_apply]
  ring

-- @node: sumIndependentCellRisk_le
/-- If [the stated t condition holds](hyp:hT), then [the stated sum independent cell risk upper bound relation holds](goal). -/
lemma sumIndependentCellRisk_le {d : ℕ}
    (μ : Fin d → Measure ((Cell → ℕ) × (Cell → ℕ)))
    [hprob : ∀ x, IsProbabilityMeasure (μ x)]
    (T : Fin d → ((Cell → ℕ) × (Cell → ℕ)) → ℝ)
    (target : Fin d → ℝ) (hT : ∀ x, MemLp (T x) 2 (μ x)) :
    ∫ z, ((∑ x, T x (z x)) - ∑ x, target x) ^ 2 ∂Measure.pi μ ≤
      2 * (∑ x, Var[T x; μ x]) +
        2 * ((∑ x, ∫ z, T x z ∂(μ x)) - ∑ x, target x) ^ 2 := by
  let S := fun z : Fin d → ((Cell → ℕ) × (Cell → ℕ)) => ∑ x, T x (z x)
  let ES := ∑ x, ∫ z, T x z ∂μ x
  have hS : MemLp S 2 (Measure.pi μ) := memLp_finsetSum _ fun x _ =>
    (hT x).comp_measurePreserving (MeasureTheory.measurePreserving_eval μ x)
  have hpoint (z : Fin d → ((Cell → ℕ) × (Cell → ℕ))) :
      (S z - ∑ x, target x) ^ 2 ≤
        2 * (S z - ES) ^ 2 + 2 * (ES - ∑ x, target x) ^ 2 := by
    nlinarith [sq_nonneg ((S z - ES) - (ES - ∑ x, target x))]
  have hleft : Integrable (fun z => (S z - ∑ x, target x) ^ 2) (Measure.pi μ) :=
    (hS.sub (memLp_const _)).integrable_sq
  have hright : Integrable (fun z =>
      2 * (S z - ES) ^ 2 + 2 * (ES - ∑ x, target x) ^ 2) (Measure.pi μ) :=
    ((hS.sub (memLp_const _)).integrable_sq.const_mul 2).add (integrable_const _)
  calc
    (∫ z, (S z - ∑ x, target x) ^ 2 ∂Measure.pi μ) ≤
        ∫ z, (2 * (S z - ES) ^ 2 + 2 * (ES - ∑ x, target x) ^ 2) ∂Measure.pi μ :=
      integral_mono hleft hright hpoint
    _ = 2 * Var[S; Measure.pi μ] + 2 * (ES - ∑ x, target x) ^ 2 := by
      have hES : (∫ z, S z ∂Measure.pi μ) = ES := by
          dsimp [S, ES]
          have hfun : (fun z : Fin d → ((Cell → ℕ) × (Cell → ℕ)) =>
              ∑ x, T x (z x)) =
              ∑ x, fun z : Fin d → ((Cell → ℕ) × (Cell → ℕ)) => T x (z x) := by
            funext z
            simp
          rw [hfun]
          calc
            (∫ z, (∑ x, fun z : Fin d → ((Cell → ℕ) × (Cell → ℕ)) =>
                T x (z x)) z ∂Measure.pi μ) =
                ∑ x ∈ Finset.univ, ∫ z, T x (z x) ∂Measure.pi μ := by
              simpa only [Finset.sum_const_zero, Finset.sum_apply,
                Finset.sum_filter, Function.comp_apply] using
                (integral_finset_sum Finset.univ fun x _ =>
                  ((hT x).comp_measurePreserving
                    (MeasureTheory.measurePreserving_eval μ x)).integrable one_le_two)
            _ = ∑ x, ∫ z, T x z ∂μ x := by
              apply Finset.sum_congr rfl
              intro x _
              let hmp := MeasureTheory.measurePreserving_eval μ x
              have htmap : AEStronglyMeasurable (T x)
                  (Measure.map (Function.eval x) (Measure.pi μ)) := by
                rw [hmp.map_eq]
                exact (hT x).aestronglyMeasurable
              simpa only [Function.comp_apply, hmp.map_eq] using
                (integral_map hmp.aemeasurable htmap).symm
      have hcInt : Integrable (fun z => 2 * (S z - ES) ^ 2) (Measure.pi μ) :=
        (hS.sub (memLp_const _)).integrable_sq.const_mul 2
      have hkInt : Integrable (fun _ : Fin d → ((Cell → ℕ) × (Cell → ℕ)) =>
          2 * (ES - ∑ x, target x) ^ 2) (Measure.pi μ) := integrable_const _
      rw [integral_add hcInt hkInt, integral_const_mul,
        variance_eq_integral hS.aestronglyMeasurable.aemeasurable, hES,
        integral_const, probReal_univ, one_smul]
    _ = 2 * (∑ x, Var[T x; μ x]) +
        2 * ((∑ x, ∫ z, T x z ∂(μ x)) - ∑ x, target x) ^ 2 := by
      have hvar : Var[S; Measure.pi μ] = ∑ x, Var[T x; μ x] := by
        have hfun : S = ∑ x, fun z => T x (z x) := by
          funext z
          simp [S]
        rw [hfun]
        exact ProbabilityTheory.variance_sum_pi hT
      rw [hvar]

/-- Regrouping the independent pilot and evaluation tables by cells gives a
product of the cellwise pilot--evaluation laws. [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: pilotEvaluationTableLaw_pairing
lemma pilotEvaluationTableLaw_pairing {d : ℕ} (m : ℝ) (P : DiscreteLaw d) :
    Measure.map (fun z : UncappedCountTable d => fun x => (z.1 x, z.2 x))
        (pilotEvaluationTableLaw m P) =
      Measure.pi (fun x : Fin d => pilotEvaluationLaw m (cellVector P x)) := by
  let μ : Fin d → Measure (Cell → ℕ) := fun x =>
    Measure.pi (fun j : Cell => poissonMeasure
      (m * cellVector P x j).toNNReal)
  have hmp := MeasureTheory.measurePreserving_arrowProdEquivProdArrow
    (Cell → ℕ) (Cell → ℕ) (Fin d) μ μ
  have hs := hmp.symm.map_eq
  have hfun : (fun z : UncappedCountTable d => fun x => (z.1 x, z.2 x)) =
      ⇑(MeasurableEquiv.arrowProdEquivProdArrow
        (Cell → ℕ) (Cell → ℕ) (Fin d)).symm := by
    funext z x
    rfl
  rw [hfun]
  simpa [pilotEvaluationTableLaw, pilotEvaluationLaw, cellVector, μ] using hs

/-- The uncapped statistic's risk is the squared-error integral of the
cellwise sum under the independent product of cell laws. This uses [the sample size satisfies its stated restriction](hyp:hn). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: sqRisk_jacksonUncapped_eq_pairTable
lemma sqRisk_jacksonUncapped_eq_pairTable {n d : ℕ} (P : DiscreteLaw d)
    (epsilon theta : ℝ) (hn : 0 < n) :
    Causalean.Stat.sqRisk
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          ((obsLaw P).prod uncappedFairMarkLaw) (Real.toNNReal (n / 4)))
        (jacksonUncappedStatistic canonicalJacksonTuning epsilon n hn) theta =
      ∫ z : Fin d → ((Cell → ℕ) × (Cell → ℕ)),
        (max 0 (min 1 (∑ x : Fin d,
          jacksonCellStatistic canonicalJacksonTuning epsilon d (n / 8)
            (z x).1 (z x).2 (by positivity))) - theta) ^ 2
        ∂Measure.pi (fun x : Fin d => pilotEvaluationLaw (n / 8) (cellVector P x)) := by
  let F := fun table : UncappedCountTable d =>
    max 0 (min 1 (∑ x : Fin d,
      jacksonCellStatistic canonicalJacksonTuning epsilon d (n / 8)
        (table.1 x) (table.2 x) (by positivity)))
  let pair := fun table : UncappedCountTable d => fun x => (table.1 x, table.2 x)
  have hpair : Measurable pair := by fun_prop
  have hF : Measurable F := by fun_prop
  have hsq : AEStronglyMeasurable (fun r : ℝ => (r - theta) ^ 2)
      (Measure.map F (pilotEvaluationTableLaw (n / 8) P)) := by fun_prop
  unfold Causalean.Stat.sqRisk
  calc
    (∫ s, (jacksonUncappedStatistic canonicalJacksonTuning epsilon n hn s - theta) ^ 2
        ∂Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          ((obsLaw P).prod uncappedFairMarkLaw) (Real.toNNReal (n / 4))) =
      ∫ z, (F z.2 - theta) ^ 2 ∂uncappedMarkedCountLaw n P := by
        rw [uncappedMarkedCountLaw]
        symm
        rw [integral_map measurable_uncappedMarkedCountMap.aemeasurable]
        · rfl
        · fun_prop
    _ = ∫ table, (F table - theta) ^ 2 ∂pilotEvaluationTableLaw (n / 8) P := by
      rw [← uncappedMarkedCountLaw_table n P]
      symm
      rw [integral_map measurable_snd.aemeasurable]
      fun_prop
    _ = ∫ z : Fin d → ((Cell → ℕ) × (Cell → ℕ)),
        (max 0 (min 1 (∑ x : Fin d,
          jacksonCellStatistic canonicalJacksonTuning epsilon d (n / 8)
            (z x).1 (z x).2 (by positivity))) - theta) ^ 2
        ∂Measure.pi (fun x : Fin d => pilotEvaluationLaw (n / 8) (cellVector P x)) := by
      rw [← pilotEvaluationTableLaw_pairing (n / 8) P]
      symm
      rw [integral_map hpair.aemeasurable]
      fun_prop

/-- Projection onto the unit interval does not increase squared loss from a
target in that interval. This uses [the target or contrast satisfies the stated unit-range restriction](hyp:htheta). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: sq_clip_unitInterval_le
lemma sq_clip_unitInterval_le (u theta : ℝ) (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
    (max 0 (min 1 u) - theta) ^ 2 ≤ (u - theta) ^ 2 := by
  by_cases hu0 : u < 0
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    nlinarith [htheta.1]
  by_cases hu1 : 1 < u
  · rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
    nlinarith [htheta.2]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Cellwise bias and variance bounds aggregate under Poisson splitting into
the projected uncapped risk bound. This uses [the sample size satisfies its stated restriction](hyp:hn), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated c condition holds](hyp:hC), and [the target or contrast satisfies the stated unit-range restriction](hyp:htheta), and [the target lies in the unit interval](hyp:htarget), and [the stated cellwise bias bound holds](hyp:hbias). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: sqRisk_jacksonUncapped_le_cellRisk
lemma sqRisk_jacksonUncapped_le_cellRisk {n d : ℕ} (P : DiscreteLaw d)
    (epsilon theta C : ℝ) (hn : 0 < n) (hd : 1 ≤ d) (hepsilon : 0 < epsilon)
    (hC : 0 ≤ C)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1)
    (htarget : theta = ∑ x : Fin d, globalCellValue epsilon (cellVector P x))
    (hbias : ∀ x : Fin d,
      |cellStatisticExpectation canonicalJacksonTuning epsilon d (n / 8)
          (cellVector P x) (by positivity) - globalCellValue epsilon (cellVector P x)| ≤
        C * (Real.sqrt (cellMass P x / ((n / 8) * logAlphabet d)) +
          1 / ((n / 8) * logAlphabet d))) :
    Causalean.Stat.sqRisk
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          ((obsLaw P).prod uncappedFairMarkLaw) (Real.toNNReal (n / 4)))
        (jacksonUncappedStatistic canonicalJacksonTuning epsilon n hn) theta ≤
      2 * (∑ x : Fin d, cellStatisticVariance canonicalJacksonTuning epsilon d
        (n / 8) (cellVector P x) (by positivity)) +
      4 * C ^ 2 * (d / ((n / 8) * logAlphabet d) +
        d ^ 2 / ((n / 8) ^ 2 * logAlphabet d ^ 2)) := by
  let μ := fun x : Fin d => pilotEvaluationLaw (n / 8) (cellVector P x)
  let T := fun x : Fin d => fun z : (Cell → ℕ) × (Cell → ℕ) =>
    jacksonCellStatistic canonicalJacksonTuning epsilon d (n / 8) z.1 z.2
      (by positivity)
  let target := fun x : Fin d => globalCellValue epsilon (cellVector P x)
  letI : ∀ x, IsProbabilityMeasure (μ x) := fun x => by
    dsimp [μ, pilotEvaluationLaw]
    infer_instance
  have hq (x : Fin d) (j : Cell) : 0 ≤ cellVector P x j := ENNReal.toReal_nonneg
  have hT : ∀ x, MemLp (T x) 2 (μ x) := fun x => by
    simpa [T, μ] using canonicalJacksonCellStatistic_memLp_two
      epsilon (n / 8) hepsilon (by positivity) d hd (cellVector P x) (hq x)
  have hsumMass : ∑ x : Fin d, cellMass P x = 1 := by
    calc
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := by
        simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  have hmass0 (x : Fin d) : 0 ≤ cellMass P x := by
    unfold cellMass
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  rw [sqRisk_jacksonUncapped_eq_pairTable P epsilon theta hn]
  calc
    (∫ z, (max 0 (min 1 (∑ x, T x (z x))) - theta) ^ 2 ∂Measure.pi μ) ≤
        ∫ z, ((∑ x, T x (z x)) - ∑ x, target x) ^ 2 ∂Measure.pi μ := by
      have hTsum : MemLp (fun z => ∑ x, T x (z x)) 2 (Measure.pi μ) :=
        memLp_finsetSum _ fun x _ =>
          (hT x).comp_measurePreserving (MeasureTheory.measurePreserving_eval μ x)
      have hright : Integrable
          (fun z => ((∑ x, T x (z x)) - ∑ x, target x) ^ 2)
          (Measure.pi μ) :=
        (hTsum.sub (memLp_const (∑ x, target x))).integrable_sq
      have hleft : Integrable
          (fun z => (max 0 (min 1 (∑ x, T x (z x))) - theta) ^ 2)
          (Measure.pi μ) := by
        apply hright.mono'
        · exact Measurable.of_discrete.aestronglyMeasurable
        · filter_upwards with z
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← htarget]
          exact sq_clip_unitInterval_le _ theta htheta
      apply integral_mono hleft hright
      intro z
      rw [← htarget]
      exact sq_clip_unitInterval_le _ theta htheta
    _ ≤ 2 * (∑ x, Var[T x; μ x]) +
        2 * ((∑ x, ∫ z, T x z ∂μ x) - ∑ x, target x) ^ 2 :=
      sumIndependentCellRisk_le μ T target hT
    _ ≤ 2 * (∑ x : Fin d, cellStatisticVariance canonicalJacksonTuning epsilon d
          (n / 8) (cellVector P x) (by positivity)) +
        4 * C ^ 2 * (d / ((n / 8) * logAlphabet d) +
          d ^ 2 / ((n / 8) ^ 2 * logAlphabet d ^ 2)) := by
      have hlog : 0 < logAlphabet d := by
        unfold logAlphabet
        apply Real.log_pos
        have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
        calc
          1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          _ = Real.exp 1 * 1 := by ring
          _ ≤ Real.exp 1 * d := mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)
      have hb := sumCellBias_sq_le hd hC (by positivity) hlog
        hmass0 hsumMass hbias
      have hb' : ((∑ x, ∫ z, T x z ∂μ x) - ∑ x, target x) ^ 2 ≤
          2 * C ^ 2 * (d / ((n / 8) * logAlphabet d) +
            d ^ 2 / ((n / 8) ^ 2 * logAlphabet d ^ 2)) := by
        simpa [T, μ, target, cellStatisticExpectation] using hb
      have hvar : (∑ x, Var[T x; μ x]) =
          ∑ x : Fin d, cellStatisticVariance canonicalJacksonTuning epsilon d
            (n / 8) (cellVector P x) (by positivity) := by
        apply Finset.sum_congr rfl
        intro x _
        unfold cellStatisticVariance cellStatisticExpectation
        rw [variance_eq_integral (hT x).aestronglyMeasurable.aemeasurable]
      rw [hvar]
      nlinarith [hb']

/-- The two logarithmic variance factors are uniformly absorbed by the
fractional alphabet power left by the factorial coefficient envelope. This uses [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: canonicalVarianceLogAbsorption
lemma canonicalVarianceLogAbsorption (d : ℕ) (hd : 1 ≤ d) :
    logAlphabet d ^ 2 * d ^ (-15 / 16 : ℝ) ≤ 225 ∧
    logAlphabet d ^ 4 * d ^ (-15 / 16 : ℝ) ≤ 50625 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hbase := (canonicalLogSquaredPowerBounds d hd).1
  have hp12 : (d : ℝ) ^ (-12 / 16 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hdR (by norm_num)
  have hp9 : (d : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hdR (by norm_num)
  have hA0 : 0 ≤ logAlphabet d ^ 2 * d ^ (-3 / 16 : ℝ) := by positivity
  constructor
  · calc
      logAlphabet d ^ 2 * d ^ (-15 / 16 : ℝ) =
          (logAlphabet d ^ 2 * d ^ (-3 / 16 : ℝ)) *
            d ^ (-12 / 16 : ℝ) := by
        rw [show (-15 / 16 : ℝ) = -3 / 16 + -12 / 16 by norm_num,
          Real.rpow_add (by positivity)]
        ring
      _ ≤ 225 * 1 := mul_le_mul hbase hp12 (by positivity) (by norm_num)
      _ = 225 := by ring
  · calc
      logAlphabet d ^ 4 * d ^ (-15 / 16 : ℝ) =
          (logAlphabet d ^ 2 * d ^ (-3 / 16 : ℝ)) ^ 2 *
            d ^ (-9 / 16 : ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hd0,
          show (-15 / 16 : ℝ) = (-3 / 16) * 2 + -9 / 16 by norm_num,
          Real.rpow_add (by positivity)]
        ring
      _ ≤ 225 ^ 2 * 1 := by
        exact mul_le_mul (pow_le_pow_left₀ hA0 hbase 2) hp9 (by positivity) (by positivity)
      _ = 50625 := by norm_num

/-- In the nontrivial Jackson regime, the summed cell bounds yield the target
`d /(n log(ed))` risk rate. This uses [the sample size satisfies its stated restriction](hyp:hn), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated c condition holds](hyp:hC), and [the target or contrast satisfies the stated unit-range restriction](hyp:htheta), and [the target lies in the unit interval](hyp:htarget), and [the stated scale inequality holds](hyp:hscale), and [the stated cellwise bias bound holds](hyp:hbias), and [the stated cellwise variance bound holds](hyp:hvar). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: sqRisk_jacksonUncapped_le_rate
lemma sqRisk_jacksonUncapped_le_rate {n d : ℕ} (P : DiscreteLaw d)
    (epsilon theta C : ℝ) (hn : 0 < n) (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hC : 0 < C) (htheta : theta ∈ Set.Icc (0 : ℝ) 1)
    (htarget : theta = ∑ x : Fin d, globalCellValue epsilon (cellVector P x))
    (hscale : d / logAlphabet d ≤ (n : ℝ))
    (hbias : ∀ x : Fin d,
      |cellStatisticExpectation canonicalJacksonTuning epsilon d (n / 8)
          (cellVector P x) (by positivity) - globalCellValue epsilon (cellVector P x)| ≤
        C * (Real.sqrt (cellMass P x / ((n / 8) * logAlphabet d)) +
          1 / ((n / 8) * logAlphabet d)))
    (hvar : ∀ x : Fin d,
      cellStatisticVariance canonicalJacksonTuning epsilon d (n / 8)
          (cellVector P x) (by positivity) ≤
        C * d ^ (1 / 16 : ℝ) *
          (cellMass P x * logAlphabet d / (n / 8) +
            logAlphabet d ^ 2 / (n / 8) ^ 2)) :
    Causalean.Stat.sqRisk
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          ((obsLaw P).prod uncappedFairMarkLaw) (Real.toNNReal (n / 4)))
        (jacksonUncappedStatistic canonicalJacksonTuning epsilon n hn) theta ≤
      (10000000 * (1 + C + C ^ 2)) * (d / (n * logAlphabet d)) := by
  have hraw := sqRisk_jacksonUncapped_le_cellRisk P epsilon theta C hn
    (le_trans (by omega : 1 ≤ 2) hd) hepsilon (le_of_lt hC) htheta htarget hbias
  have hsumMass : ∑ x : Fin d, cellMass P x = 1 := by
    calc
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := by
        simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  have hvsum : (∑ x : Fin d, cellStatisticVariance canonicalJacksonTuning epsilon d
      (n / 8) (cellVector P x) (by positivity)) ≤
      C * d ^ (1 / 16 : ℝ) *
        (logAlphabet d / (n / 8) + d * logAlphabet d ^ 2 / (n / 8) ^ 2) := by
    calc
      _ ≤ ∑ x : Fin d, C * d ^ (1 / 16 : ℝ) *
          (cellMass P x * logAlphabet d / (n / 8) +
            logAlphabet d ^ 2 / (n / 8) ^ 2) := Finset.sum_le_sum fun x _ => hvar x
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib]
        have hf : (∑ x : Fin d, cellMass P x * logAlphabet d / (n / 8)) =
            (∑ x : Fin d, cellMass P x) * logAlphabet d / (n / 8) := by
          calc
            _ = ∑ x : Fin d, cellMass P x * (logAlphabet d / (n / 8)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = (∑ x : Fin d, cellMass P x) *
                (logAlphabet d / (n / 8)) := by rw [← Finset.sum_mul]
            _ = _ := by ring
        rw [hf, hsumMass]
        simp
        ring
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    apply Real.log_pos
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hd)
    calc
      1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      _ = Real.exp 1 * 1 := by ring
      _ ≤ Real.exp 1 * d := mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let r : ℝ := d / (n * logAlphabet d)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one (mul_pos hnR hL)]
    rw [div_le_iff₀ hL] at hscale
    exact_mod_cast hscale
  have hpow := canonicalVarianceLogAbsorption d (le_trans (by omega : 1 ≤ 2) hd)
  have hbiasAbsorb :
      d / ((n / 8) * logAlphabet d) + d ^ 2 / ((n / 8) ^ 2 * logAlphabet d ^ 2) ≤
        72 * r := by
    dsimp [r]
    have hrSq : (d / (n * logAlphabet d)) ^ 2 ≤ d / (n * logAlphabet d) := by
      nlinarith [hr0, hr1]
    norm_num at *
    field_simp [ne_of_gt hnR, ne_of_gt hL] at hrSq ⊢
    nlinarith
  have hvarAbsorb :
      d ^ (1 / 16 : ℝ) *
        (logAlphabet d / (n / 8) + d * logAlphabet d ^ 2 / (n / 8) ^ 2) ≤
        3300000 * r := by
    have hfirst : d ^ (1 / 16 : ℝ) * (logAlphabet d / (n / 8)) ≤
        1800 * r := by
      dsimp [r]
      norm_num
      field_simp [ne_of_gt hnR, ne_of_gt hL]
      have hdpos : (0 : ℝ) < d := by positivity
      have hid : d ^ (1 / 16 : ℝ) * logAlphabet d ^ 2 =
          logAlphabet d ^ 2 * d ^ (-15 / 16 : ℝ) * d := by
        rw [show (1 / 16 : ℝ) = -15 / 16 + 1 by norm_num,
          Real.rpow_add hdpos, Real.rpow_one]
        ring
      rw [hid]
      nlinarith [hpow.1]
    have hsecond : d ^ (1 / 16 : ℝ) *
        (d * logAlphabet d ^ 2 / (n / 8) ^ 2) ≤ 3240000 * r := by
      dsimp [r]
      norm_num
      field_simp [ne_of_gt hnR, ne_of_gt hL]
      have hdpos : (0 : ℝ) < d := by positivity
      have hid : d ^ (1 / 16 : ℝ) * d * logAlphabet d ^ 3 =
          (logAlphabet d ^ 4 * d ^ (-15 / 16 : ℝ)) *
            (d * d / logAlphabet d) := by
        rw [show (1 / 16 : ℝ) = -15 / 16 + 1 by norm_num,
          Real.rpow_add hdpos, Real.rpow_one]
        field_simp [ne_of_gt hL]
      have hscaleMul := mul_le_mul_of_nonneg_left hscale
        (show 0 ≤ logAlphabet d ^ 4 * d ^ (-15 / 16 : ℝ) by positivity)
      have hratio :
          (logAlphabet d ^ 4 * d ^ (-15 / 16 : ℝ)) * (d / logAlphabet d) =
            d ^ (1 / 16 : ℝ) * logAlphabet d ^ 3 := by
        rw [show (1 / 16 : ℝ) = -15 / 16 + 1 by norm_num,
          Real.rpow_add hdpos, Real.rpow_one]
        field_simp [ne_of_gt hL]
      rw [hratio] at hscaleMul
      have hAn := mul_le_mul_of_nonneg_right hpow.2 (le_of_lt hnR)
      nlinarith
    nlinarith
  calc
    _ ≤ 2 * (C * d ^ (1 / 16 : ℝ) *
        (logAlphabet d / (n / 8) + d * logAlphabet d ^ 2 / (n / 8) ^ 2)) +
        4 * C ^ 2 * (d / ((n / 8) * logAlphabet d) +
          d ^ 2 / ((n / 8) ^ 2 * logAlphabet d ^ 2)) := by
      exact hraw.trans (add_le_add
        (mul_le_mul_of_nonneg_left hvsum (by norm_num)) (le_refl _))
    _ ≤ 2 * C * (3300000 * r) + 4 * C ^ 2 * (72 * r) := by
      have hv := mul_le_mul_of_nonneg_left hvarAbsorb
        (show 0 ≤ 2 * C by positivity)
      have hb := mul_le_mul_of_nonneg_left hbiasAbsorb
        (show 0 ≤ 4 * C ^ 2 by positivity)
      nlinarith
    _ ≤ (10000000 * (1 + C + C ^ 2)) * r := by
      have := sq_nonneg C
      nlinarith
  
end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
