module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.CapCoupling
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.BadPilotAggregate
public import Causalean.Stat.Concentration.Poisson.UpperTail
public import Causalean.Stat.Concentration.BoundedVariation.ConditionalAverage

/-! Capped, conditional-averaged threshold-process risk. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.BoundedVariation
open scoped NNReal

/-- The true dual curve, restricted to the shadow-price interval, is a
continuous Path. -/
-- @node: dualProcessPath
noncomputable def dualProcessPath {d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) : Path := by
  let G : Path := ∑ j : Fin d,
    ⟨fun t : Time => thresholdFunReal epsilon t.1 (cellVector P j),
      thresholdFunReal_continuous_time epsilon (cellVector P j)⟩
  refine ⟨fun t : Time => dualProcessReal epsilon P t.1, G.continuous.congr ?_⟩
  intro t
  simp [G, dualProcessReal, dualProcess, thresholdFunReal, t.2]

/-- On a nonnegative four-vector, each arm value lies between zero and the
total mass. With [the specified inputs and conditions](hyp:epsilon,he,u,hu,a), [the stated relationship holds](goal). -/
-- @node: armValue_mem_totalMass
lemma armValue_mem_totalMass {epsilon : ℝ} (he : 0 < epsilon)
    (u : Cell → ℝ) (hu : ∀ z, 0 ≤ u z) (a : Fin 2) :
    0 ≤ armValue epsilon a u ∧ armValue epsilon a u ≤ totalMass u := by
  have harm0 : 0 ≤ armMassFn a u := by
    unfold armMassFn
    exact add_nonneg (hu _) (hu _)
  have htotal0 : 0 ≤ totalMass u := by
    unfold totalMass armMassFn
    exact add_nonneg (add_nonneg (hu _) (hu _))
      (add_nonneg (hu _) (hu _))
  have hsuccess : u (a, 1) ≤ armMassFn a u := by
    unfold armMassFn
    linarith [hu (a, 0)]
  let D := max (armMassFn a u) (epsilon * totalMass u)
  have hD0 : 0 ≤ D := le_trans harm0 (le_max_left _ _)
  by_cases hD : D = 0
  · have hs0 : u (a, 1) = 0 := by
      have : armMassFn a u = 0 := le_antisymm
        (le_trans (le_max_left _ _) (le_of_eq hD)) harm0
      linarith [hu (a, 1)]
    simp [armValue, D, hD, hs0, htotal0]
  · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD)
    have hfrac0 : 0 ≤ u (a, 1) / D := div_nonneg (hu _) hD0
    have hfrac1 : u (a, 1) / D ≤ 1 := by
      rw [div_le_one hDpos]
      exact hsuccess.trans (le_max_left _ _)
    unfold armValue
    change 0 ≤ totalMass u * u (a, 1) / D ∧
      totalMass u * u (a, 1) / D ≤ totalMass u
    constructor
    · exact div_nonneg (mul_nonneg htotal0 (hu _)) hD0
    · rw [mul_div_assoc]
      nlinarith [mul_le_mul_of_nonneg_left hfrac1 htotal0]

/-- The true dual threshold lies between zero and one after summing the cell
masses of a discrete law. With [the specified inputs and conditions](hyp:d,epsilon,lambda,he,P,hlambda), [the stated relationship holds](goal). -/
-- @node: dualProcessReal_mem_unit
lemma dualProcessReal_mem_unit {d : ℕ} {epsilon lambda : ℝ}
    (he : 0 < epsilon) (P : DiscreteLaw d)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ dualProcessReal epsilon P lambda ∧
      dualProcessReal epsilon P lambda ≤ 1 := by
  have hq (j : Fin d) (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hthreshold (j : Fin d) :
      0 ≤ thresholdFun epsilon ⟨lambda, hlambda⟩ (cellVector P j) ∧
        thresholdFun epsilon ⟨lambda, hlambda⟩ (cellVector P j) ≤
          totalMass (cellVector P j) := by
    obtain ⟨hg0, hg0le⟩ := armValue_mem_totalMass he _ (hq j) 0
    obtain ⟨hg1, hg1le⟩ := armValue_mem_totalMass he _ (hq j) 1
    unfold thresholdFun
    constructor
    · positivity
    · rw [add_max]
      apply max_le
      · simpa using hg0le
      · have hmass0 : 0 ≤ totalMass (cellVector P j) := by
          unfold totalMass armMassFn
          exact add_nonneg (add_nonneg (hq j _) (hq j _))
            (add_nonneg (hq j _) (hq j _))
        calc
          armValue epsilon 0 (cellVector P j) +
              (armValue epsilon 1 (cellVector P j) -
                armValue epsilon 0 (cellVector P j) -
                  lambda * totalMass (cellVector P j)) =
              armValue epsilon 1 (cellVector P j) -
                lambda * totalMass (cellVector P j) := by ring
          _ ≤ totalMass (cellVector P j) := by
            nlinarith [mul_nonneg hlambda.1 hmass0]
  have hmass : ∑ j : Fin d, totalMass (cellVector P j) = 1 := by
    have hcell (j : Fin d) :
        totalMass (cellVector P j) = cellMass P j := by
      simp [totalMass, armMassFn,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass,
        finTwoEquiv]
      ring
    simpa only [hcell] using discreteLaw_sum_cellMass P
  simp only [dualProcessReal, dif_pos hlambda, dualProcess]
  constructor
  · exact Finset.sum_nonneg fun j _ => (hthreshold j).1
  · calc
      _ ≤ ∑ j : Fin d, totalMass (cellVector P j) :=
        Finset.sum_le_sum fun j _ => (hthreshold j).2
      _ = 1 := hmass

/-- The true dual target Path has unit supremum norm. With [the specified inputs and conditions](hyp:d,epsilon,he,P), [the stated relationship holds](goal). -/
-- @node: dualProcessPath_norm_le_one
lemma dualProcessPath_norm_le_one {d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (P : DiscreteLaw d) :
    ‖dualProcessPath epsilon P‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro t
  change |dualProcessReal epsilon P t.1| ≤ 1
  rw [abs_le]
  exact ⟨by linarith [(dualProcessReal_mem_unit he P t.2).1],
    (dualProcessReal_mem_unit he P t.2).2⟩

/-- One auxiliary Jackson estimate, restricted to the shadow-price interval,
as a continuous path. -/
-- @node: auxiliaryThresholdPath
noncomputable def auxiliaryThresholdPath {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (sample : Fin n → Obs d) (perm : Equiv.Perm (Fin n))
    (M : ℕ) (marks : Fin n → Bool) : Path := by
  refine ⟨fun t => auxiliaryThresholdProcess epsilon sample perm M marks t.1, ?_⟩
  unfold auxiliaryThresholdProcess
  apply continuous_finsetSum
  intro j _
  apply jacksonCellStatistic_continuous_time
  intro lambda
  apply pilotRectangle_threshold_pullback_continuousOn he
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  · exact hd

/-- The ideal Jackson estimate is a continuous path for every count table. -/
-- @node: idealThresholdPath
noncomputable def idealThresholdPath {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) : Path := by
  refine ⟨fun t => ∑ j : Fin d,
    jacksonCellStatistic epsilon t.1 ((n : ℝ) / 8) d
      (counts.1 j) (counts.2 j), ?_⟩
  apply continuous_finsetSum
  intro j _
  apply jacksonCellStatistic_continuous_time
  intro lambda
  apply pilotRectangle_threshold_pullback_continuousOn he
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  · exact hd

/-- The promoted quarter-mean Poisson cap estimate implies the weaker
exponential remainder used in equation (37) of the paper. With [the specified inputs and conditions](hyp:n), [the stated relationship holds](goal). -/
-- @node: poissonQuarterCapTail_le_paperRemainder
lemma poissonQuarterCapTail_le_paperRemainder (n : ℕ) :
    ((poissonMeasure ((n : ℝ≥0) / 4)) (Set.Ioi n)).toReal ≤
      Real.exp (-(n : ℝ) / 16) := by
  have htail := poisson_quarter_mean_cap_tail n
  have hreal :
      ((poissonMeasure ((n : ℝ≥0) / 4)) (Set.Ioi n)).toReal ≤
        Real.exp (-(n : ℝ) / 2) := by
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (Real.exp_nonneg _)).mp htail
  exact hreal.trans (Real.exp_le_exp.mpr (by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith))

/-- The uncapped shadow-price process in the ideal Poisson experiment. -/
noncomputable def idealErrorProcess {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (lambda : ℝ) : ℝ :=
  ∑ j : Fin d,
    (jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
      (counts.1 j) (counts.2 j) -
      thresholdFunReal epsilon lambda (cellVector P j))

/-- The ideal path error has exactly the paper's scalar supremum loss. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,counts), [the stated relationship holds](goal). -/
-- @node: idealThresholdPath_error_norm_eq
lemma idealThresholdPath_error_norm_eq {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) :
    ‖idealThresholdPath epsilon he hn hd counts - dualProcessPath epsilon P‖ =
      sSup ((fun lambda : ℝ =>
        |idealErrorProcess (n := n) epsilon P counts lambda|) ''
          Set.Icc 0 1) := by
  rw [← path_norm_eq_sSup_abs_restrict
    (fun lambda => idealErrorProcess (n := n) epsilon P counts lambda)]
  · congr 1
    apply ContinuousMap.ext
    intro t
    simp [idealThresholdPath, dualProcessPath, idealErrorProcess,
      dualProcessReal, dualProcess, thresholdFunReal, t.2]
  · apply ((idealThresholdPath epsilon he hn hd counts).continuous.sub
      (dualProcessPath epsilon P).continuous).congr
    intro t
    simp [idealThresholdPath, dualProcessPath, idealErrorProcess,
      dualProcessReal, dualProcess, thresholdFunReal, t.2]

/-- The squared supremum loss of the full uncapped ideal process is integrable
for every discrete law; this coarse fact uses no overlap assumption. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). -/
-- @node: idealProcessRisk_integrand_integrable
lemma idealProcessRisk_integrand_integrable {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) :
    Integrable (fun counts =>
      sSup ((fun lambda : ℝ =>
        |idealErrorProcess (n := n) epsilon P counts lambda|) ''
          Set.Icc 0 1) ^ 2) (idealCountLaw (n := n) P) := by
  classical
  let cellSup := fun counts
      (j : Fin d) => sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1)
  let envelope := fun counts => (d : ℝ) * ∑ j : Fin d, cellSup counts j ^ 2
  have henv : Integrable envelope (idealCountLaw (n := n) P) := by
    dsimp [envelope]
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    simpa [cellSup] using
      idealClippedCell_error_sSup_sq_integrable epsilon he hn hd P j
  apply henv.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with counts
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hcellBdd (j : Fin d) : BddAbove ((fun lambda : ℝ =>
      |idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1) := by
    refine ⟨((3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)) *
      ∑ z : Cell,
        (|pilotCenter ((n : ℝ) / 8) (counts.1 j) z - cellVector P j z| +
          pilotHalfWidth ((n : ℝ) / 8) d (counts.1 j) z), ?_⟩
    rintro y ⟨lambda, hlambda, rfl⟩
    exact idealClippedCell_error_le_badScore he hn hd P counts j lambda hlambda
  have hcell0 (j : Fin d) : 0 ≤ cellSup counts j := by
    dsimp [cellSup]
    exact le_trans (abs_nonneg _) (le_csSup (hcellBdd j)
      ⟨0, by simp, rfl⟩)
  have hcellPoint (j : Fin d) (lambda : ℝ)
      (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
      |idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j)| ≤ cellSup counts j := by
    exact le_csSup (hcellBdd j) ⟨lambda, hlambda, rfl⟩
  let totalSet := (fun lambda : ℝ =>
    |idealErrorProcess (n := n) epsilon P counts lambda|) '' Set.Icc 0 1
  have htotalPoint (lambda : ℝ) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
      |idealErrorProcess (n := n) epsilon P counts lambda| ≤
        ∑ j : Fin d, cellSup counts j := by
    unfold idealErrorProcess
    calc
      |∑ j : Fin d, (jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
          (counts.1 j) (counts.2 j) -
          thresholdFunReal epsilon lambda (cellVector P j))| ≤
          ∑ j : Fin d, |jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
            (counts.1 j) (counts.2 j) -
            thresholdFunReal epsilon lambda (cellVector P j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d, cellSup counts j := by
        apply Finset.sum_le_sum
        intro j _
        simpa [idealClippedCellPath] using hcellPoint j lambda hlambda
  have htotalBdd : BddAbove totalSet := by
    refine ⟨∑ j : Fin d, cellSup counts j, ?_⟩
    rintro y ⟨lambda, hlambda, rfl⟩
    exact htotalPoint lambda hlambda
  have htotal0 : 0 ≤ sSup totalSet :=
    le_trans (abs_nonneg _) (le_csSup htotalBdd ⟨0, by simp, rfl⟩)
  have htotal : sSup totalSet ≤ ∑ j : Fin d, cellSup counts j :=
    csSup_le ⟨|idealErrorProcess (n := n) epsilon P counts 0|,
      ⟨0, by simp, rfl⟩⟩ (by
        rintro y ⟨lambda, hlambda, rfl⟩
        exact htotalPoint lambda hlambda)
  have hsum0 : 0 ≤ ∑ j : Fin d, cellSup counts j :=
    Finset.sum_nonneg fun j _ => hcell0 j
  have hsq : (sSup totalSet) ^ 2 ≤ (∑ j : Fin d, cellSup counts j) ^ 2 :=
    pow_le_pow_left₀ htotal0 htotal 2
  have hcs : (∑ j : Fin d, cellSup counts j) ^ 2 ≤
      (d : ℝ) * ∑ j : Fin d, cellSup counts j ^ 2 := by
    simpa using pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin d))) (f := fun j => cellSup counts j)
      (fun j _ => hcell0 j) 1
  dsimp [envelope]
  exact (by simpa [totalSet] using hsq.trans hcs)

/-- The good and bad pilot events partition the ideal cell error exactly. With [the specified inputs and conditions](hyp:n,d,epsilon,P,counts,lambda), [the stated relationship holds](goal). -/
-- @node: idealErrorProcess_good_add_bad
lemma idealErrorProcess_good_add_bad {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (lambda : ℝ) :
    idealErrorProcess (n := n) epsilon P counts lambda =
      idealPilotErrorPart (n := n) epsilon lambda P counts true +
        idealPilotErrorPart (n := n) epsilon lambda P counts false := by
  classical
  simp only [idealErrorProcess, idealPilotErrorPart, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : idealPilotGood (n := n) P counts j <;> simp [h]

/-- The structural Jackson degree leaves a fixed power of the alphabet to
absorb the coefficient envelope. With [the specified inputs and conditions](hyp:d,hd), [the stated relationship holds](goal). -/
-- @node: jacksonDegree_exponential_budget
lemma jacksonDegree_exponential_budget (d : ℕ) (hd : 16 ≤ d) :
    Real.exp (24 * jacksonDegree d +
      16 * (jacksonDegree d : ℝ) ^ 2 / logAlphabet d) ≤
        Real.exp 115 * (d : ℝ) ^ (1 / 16 : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdge : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hL : logAlphabet d = 1 + Real.log d := by
    unfold logAlphabet
    rw [Real.log_mul (by positivity : Real.exp 1 ≠ 0) (ne_of_gt hdpos)]
    simp
  have hLge : 1 ≤ logAlphabet d := by
    rw [hL]
    have := Real.log_nonneg hdge
    linarith
  have hfloor : (⌊jacksonDegreeConstant * logAlphabet d⌋₊ : ℝ) ≤
      logAlphabet d / 512 := by
    calc
      _ ≤ jacksonDegreeConstant * logAlphabet d :=
        Nat.floor_le (by unfold jacksonDegreeConstant; positivity)
      _ = logAlphabet d / 512 := by unfold jacksonDegreeConstant; ring
  have hK : (jacksonDegree d : ℝ) ≤ 2 + logAlphabet d / 512 := by
    unfold jacksonDegree
    rw [Nat.cast_max]
    exact max_le (by linarith) (by linarith)
  have hKnonneg : (0 : ℝ) ≤ jacksonDegree d := Nat.cast_nonneg _
  have hscale :
      24 * (jacksonDegree d : ℝ) * logAlphabet d +
        16 * (jacksonDegree d : ℝ) ^ 2 ≤
          114 * logAlphabet d + (logAlphabet d) ^ 2 / 16 := by
    have hprod := mul_nonneg (show 0 ≤ 2 + logAlphabet d / 512 - (jacksonDegree d : ℝ) by linarith)
      (show 0 ≤ 2 + logAlphabet d / 512 + (jacksonDegree d : ℝ) by positivity)
    nlinarith [sq_nonneg (logAlphabet d - 1)]
  have hbound :
      24 * (jacksonDegree d : ℝ) +
        16 * (jacksonDegree d : ℝ) ^ 2 / logAlphabet d ≤
          114 + logAlphabet d / 16 := by
    have hLpos : 0 < logAlphabet d := by linarith
    calc
      _ = (24 * (jacksonDegree d : ℝ) * logAlphabet d +
          16 * (jacksonDegree d : ℝ) ^ 2) / logAlphabet d := by
            field_simp
      _ ≤ (114 * logAlphabet d + (logAlphabet d) ^ 2 / 16) /
          logAlphabet d := by gcongr
      _ = _ := by field_simp
  have hexp : Real.exp (24 * jacksonDegree d +
      16 * (jacksonDegree d : ℝ) ^ 2 / logAlphabet d) ≤
      Real.exp (115 + Real.log d / 16) := by
    apply Real.exp_le_exp.mpr
    rw [hL] at hbound ⊢
    linarith
  calc
    _ ≤ Real.exp (115 + Real.log d / 16) := hexp
    _ = Real.exp 115 * (d : ℝ) ^ (1 / 16 : ℝ) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hdpos]
      congr 1
      ring_nf

/-- Constants completing the common-polynomial handle. One constant works for
all sample sizes, alphabets, observed laws, cells, and shadow prices. -/
-- @node: def:process-handle
noncomputable def processHandle (epsilon : ℝ) : Set ℝ :=
  {C | 0 < C ∧ ∀ (n d : ℕ) (P : DiscreteLaw d),
    1 ≤ n → 16 ≤ d → (d : ℝ) / logAlphabet d ≤ n →
    (∀ pilot : Cell → ℕ,
      let m := (n : ℝ) / 8
      let L := logAlphabet d
      let S := ∑ zeta : Cell, pilotRadius m d pilot zeta
      jacksonCoefficientBV epsilon m d pilot ≤
        C * S * Real.exp (12 * jacksonDegree d) ∧
        S ^ 2 * Real.exp (24 * jacksonDegree d +
          16 * (jacksonDegree d : ℝ) ^ 2 / L) ≤
          C * (d : ℝ) ^ (1 / 16 : ℝ) * S ^ 2) ∧
    centeredIdealPilotErrorRisk (n := n) epsilon P true ≤
      C * d / (((n : ℝ) / 8) * logAlphabet d) ∧
    (∀ j : Fin d, ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
      uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
        C * (Real.sqrt (cellMass P j /
          (((n : ℝ) / 8) * logAlphabet d)) +
          1 / (((n : ℝ) / 8) * logAlphabet d))) ∧
    (∀ j : Fin d,
      badPilotCellEnvelope (n := n) epsilon P j ≤
        C * (d : ℝ) ^ (1 / 4 : ℝ) *
          Real.exp (-10 * logAlphabet d) *
          badPilotCellScale (n := n) P j) ∧
    centeredIdealPilotErrorRisk (n := n) epsilon P false ≤
      C * d / (((n : ℝ) / 8) * logAlphabet d)}
  -- @realizes \mathsf H_{n,d}(one epsilon-dependent constant for all regimes)

/-- Squared supremum error in the ideal, uncapped count experiment. -/
noncomputable def idealProcessRisk {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) : ℝ :=
  ∫ counts,
    (sSup ((fun lambda : ℝ =>
      |idealErrorProcess (n := n) epsilon P counts lambda|) ''
        Set.Icc 0 1)) ^ 2
    ∂idealCountLaw (n := n) P

/-- The expected squared continuum error of the deterministic averaged process. -/
noncomputable def averagedProcessRisk {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) : ℝ :=
  ∫ sample : Fin n → Obs d,
    (sSup ((fun lambda : ℝ =>
      |averagedThresholdProcess epsilon sample lambda - dualProcessReal epsilon P lambda|) ''
        Set.Icc 0 1)) ^ 2
    ∂productLaw P n

/-- The finite auxiliary estimator path, with the overflow atom assigned the
zero path exactly as in the capped construction. -/
-- @node: finiteCapEstimatePath
noncomputable def finiteCapEstimatePath {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (sample : Fin n → Obs d) : FiniteCapAuxState n → Path
  | none => 0
  | some a => auxiliaryThresholdPath epsilon he hn hd sample a.2.1 a.1 a.2.2

/-- The weighted finite auxiliary path evaluates to the deterministic averaged
threshold process. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,sample,t), [the stated relationship holds](goal). -/
-- @node: finiteCapEstimatePath_average_apply
lemma finiteCapEstimatePath_average_apply {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (sample : Fin n → Obs d) (t : Time) :
    (∑ a : FiniteCapAuxState n,
      finiteCapAuxWeight n a •
        finiteCapEstimatePath epsilon he hn hd sample a) t =
      averagedThresholdProcess epsilon sample t.1 := by
  classical
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change (∑ a : FiniteCapAuxState n,
    finiteCapAuxWeight n a *
      finiteCapEstimatePath epsilon he hn hd sample a t) = _
  rw [Fintype.sum_option]
  simp only [finiteCapEstimatePath, ContinuousMap.zero_apply, mul_zero, zero_add]
  simp_rw [Fintype.sum_prod_type]
  unfold averagedThresholdProcess cappedThresholdProcess
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro M _
  simp only [finiteCapAuxWeight, auxiliaryWeight, auxiliaryThresholdPath]
  have hM : M.val ≤ n := Nat.le_of_lt_succ M.isLt
  simp only [if_pos hM]
  simp [auxiliaryThresholdPath]
  rw [show (poissonMeasure ((n : ℝ≥0) / 4) {M.val}).toReal *
      ((∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
        auxiliaryThresholdProcess epsilon sample perm M.val marks t.1) /
        ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (2 : ℝ) ^ n)) =
      ((poissonMeasure ((n : ℝ≥0) / 4) {M.val}).toReal /
        ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (2 : ℝ) ^ n)) *
        (∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
          auxiliaryThresholdProcess epsilon sample perm M.val marks t.1) by ring]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro perm _
  rw [Finset.mul_sum]

/-- The finite auxiliary average of error paths is the averaged estimator
error path pointwise. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,sample,t), [the stated relationship holds](goal). -/
-- @node: finiteCapErrorPath_average_apply
lemma finiteCapErrorPath_average_apply {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (sample : Fin n → Obs d) (t : Time) :
    (∑ a : FiniteCapAuxState n,
      finiteCapAuxWeight n a •
        (finiteCapEstimatePath epsilon he hn hd sample a -
          dualProcessPath epsilon P)) t =
      averagedThresholdProcess epsilon sample t.1 -
        dualProcessReal epsilon P t.1 := by
  classical
  have hest := finiteCapEstimatePath_average_apply epsilon he hn hd sample t
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, smul_eq_mul]
  change (∑ a : FiniteCapAuxState n, finiteCapAuxWeight n a *
    (finiteCapEstimatePath epsilon he hn hd sample a t -
      dualProcessPath epsilon P t)) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    finiteCapAuxWeight_sum, one_mul]
  change (∑ a : FiniteCapAuxState n, finiteCapAuxWeight n a *
    finiteCapEstimatePath epsilon he hn hd sample a t) - _ = _
  rw [show (∑ a : FiniteCapAuxState n, finiteCapAuxWeight n a *
    finiteCapEstimatePath epsilon he hn hd sample a t) =
      averagedThresholdProcess epsilon sample t.1 by simpa using hest]
  rfl

/-- Transfer from ideal uncapped Poisson error to the capped, averaged
fixed-sample estimator; the cap penalty is stated separately. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
lemma capTransferRisk (epsilon : ℝ) (he : 0 < epsilon)
    (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 1 ≤ n → 16 ≤ d →
      ∀ P : DiscreteLaw d,
        averagedProcessRisk (n := n) epsilon P ≤
          C * (idealProcessRisk (n := n) epsilon P +
            Real.exp (-(n : ℝ) / 16)) := by
  classical
  refine ⟨1, zero_lt_one, ?_⟩
  intro n d hn hd P
  have hd' : 1 ≤ d := by omega
  let F := dualProcessPath epsilon P
  let Z := fun sample : Fin n → Obs d => fun a : FiniteCapAuxState n =>
    finiteCapEstimatePath epsilon he hn hd' sample a - F
  have hJensen := finite_conditional_path_risk_le (productLaw P n)
    (fun _ a => finiteCapAuxWeight n a)
    (fun _ a => finiteCapAuxWeight_nonneg n a)
    (fun _ => finiteCapAuxWeight_sum n)
    (fun _ => measurable_const)
    Z (fun _ => measurable_of_countable _)
    (Integrable.of_finite : Integrable (fun sample : Fin n → Obs d =>
      ∑ a : FiniteCapAuxState n,
        finiteCapAuxWeight n a * ‖Z sample a‖ ^ 2) (productLaw P n))
  let g := fun counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) =>
    ‖idealThresholdPath epsilon he hn hd' counts - F‖ ^ 2
  have hg : Integrable g (idealCountLaw (n := n) P) := by
    have h := idealProcessRisk_integrand_integrable epsilon he hn hd' P
    apply h.congr
    filter_upwards [] with counts
    dsimp [g, F]
    rw [idealThresholdPath_error_norm_eq epsilon he hn hd' P counts]
  have hcouple := CappedMarkedCountIntegralIdentity (n := n) P g hg
  let uncapped :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountLaw n P
  have hfull : Integrable (fun z : ℕ ×
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.UncappedCountTable d =>
        g z.2) uncapped := by
    change Integrable (g ∘ Prod.snd) uncapped
    have hmap := uncappedMarkedCountLaw_table_eq_idealCountLaw (n := n) P
    apply (integrable_map_measure (by
      rw [show Measure.map Prod.snd uncapped = idealCountLaw (n := n) P by
        simpa [uncapped] using hmap]
      exact hg.aestronglyMeasurable) measurable_snd.aemeasurable).mp
    rw [show Measure.map Prod.snd uncapped = idealCountLaw (n := n) P by
      simpa [uncapped] using hmap]
    exact hg
  have htrunc : Integrable (fun z : ℕ ×
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.UncappedCountTable d =>
        if z.1 ≤ n then g z.2 else 0) uncapped := by
    apply hfull.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with z
    split_ifs <;> simp [g, abs_of_nonneg]
  have htrunc_le :
      (∫ z : ℕ ×
          CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.UncappedCountTable d,
        if z.1 ≤ n then g z.2 else 0 ∂uncapped) ≤
        ∫ counts, g counts ∂idealCountLaw (n := n) P := by
    have hle : (∫ z : ℕ ×
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.UncappedCountTable d,
          if z.1 ≤ n then g z.2 else 0 ∂uncapped) ≤
        ∫ z, g z.2 ∂uncapped := by
      apply integral_mono htrunc hfull
      exact fun z => by
        dsimp
        split_ifs <;> simp [g]
    have hmap := uncappedMarkedCountLaw_table_eq_idealCountLaw (n := n) P
    calc
      _ ≤ ∫ z, g z.2 ∂uncapped := hle
      _ = ∫ counts, g counts ∂idealCountLaw (n := n) P := by
        rw [← hmap]
        rw [integral_map measurable_snd.aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]
  have hright :
      (∫ sample : Fin n → Obs d,
        ∑ a : FiniteCapAuxState n,
          finiteCapAuxWeight n a * ‖Z sample a‖ ^ 2 ∂productLaw P n) ≤
        (∫ counts, g counts ∂idealCountLaw (n := n) P) +
          ((poissonMeasure ((n : ℝ≥0) / 4)) (Set.Ioi n)).toReal := by
    rw [show (∫ sample : Fin n → Obs d,
        ∑ a : FiniteCapAuxState n,
          finiteCapAuxWeight n a * ‖Z sample a‖ ^ 2 ∂productLaw P n) =
        ((poissonMeasure ((n : ℝ≥0) / 4)) (Set.Ioi n)).toReal * ‖F‖ ^ 2 +
          ∫ sample : Fin n → Obs d,
            ∑ M ∈ Finset.range (n + 1),
              ∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
                auxiliaryWeight n M *
                  g (permutedMarkedCountTable sample perm M marks)
            ∂productLaw P n by
      simp only [Z, Fintype.sum_option, finiteCapAuxWeight,
        finiteCapEstimatePath, zero_sub, norm_neg]
      rw [integral_add]
      · rw [integral_const]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with sample
        simp_rw [Fintype.sum_prod_type]
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro perm _
        apply Finset.sum_congr rfl
        intro marks _
        congr 2
      · exact integrable_const _
      · exact Integrable.of_finite]
    rw [hcouple]
    have hF2 : ‖F‖ ^ 2 ≤ 1 := by
      nlinarith [dualProcessPath_norm_le_one he P, norm_nonneg F]
    have htail0 : 0 ≤
        ((poissonMeasure ((n : ℝ≥0) / 4)) (Set.Ioi n)).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [htrunc_le]
  have hleft : averagedProcessRisk (n := n) epsilon P =
      ∫ sample : Fin n → Obs d,
        ‖∑ a : FiniteCapAuxState n, finiteCapAuxWeight n a • Z sample a‖ ^ 2
          ∂productLaw P n := by
    unfold averagedProcessRisk
    apply integral_congr_ae
    filter_upwards [] with sample
    rw [← path_norm_eq_sSup_abs_restrict
      (fun lambda => averagedThresholdProcess epsilon sample lambda -
        dualProcessReal epsilon P lambda)]
    · congr 2
      apply ContinuousMap.ext
      intro t
      exact (finiteCapErrorPath_average_apply epsilon he hn hd' P sample t).symm
    · let W : Path := ∑ a : FiniteCapAuxState n,
        finiteCapAuxWeight n a • Z sample a
      apply W.continuous.congr
      intro t
      exact finiteCapErrorPath_average_apply epsilon he hn hd' P sample t
  have hideal : (∫ counts, g counts ∂idealCountLaw (n := n) P) =
      idealProcessRisk (n := n) epsilon P := by
    unfold idealProcessRisk
    apply integral_congr_ae
    filter_upwards [] with counts
    dsimp [g, F]
    rw [idealThresholdPath_error_norm_eq epsilon he hn hd' P counts]
  rw [hleft, one_mul, ← hideal]
  exact hJensen.trans (hright.trans (add_le_add (le_refl _)
    (poissonQuarterCapTail_le_paperRemainder n)))

end CausalSmith.Stat.DiscreteBudgetvalueCurve
