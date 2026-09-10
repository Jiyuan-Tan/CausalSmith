import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.PilotControlPointwise

/-! Integrated good-pilot and pilot-failure bounds for the cellwise factorial risk. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: canonicalGoodPilotConditionalMSE
/-- Conditional on a good pilot, clipping and the product-factorial bound
give the stated local second-moment scale. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalGoodPilotConditionalMSE
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot : Cell → ℕ) (q : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j)
    (hgood : pilotGoodEvent canonicalJacksonTuning m d pilot q) :
    ∫ eval : Cell → ℕ,
        (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
          globalCellValue epsilon q) ^ 2
      ∂Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal) ≤
      4 * Real.exp 1000 * d ^ (1 / 16 : ℝ) *
        ((1 + epsilon⁻¹) * ∑ j : Cell, rectangleRadius
          (pilotRectangle canonicalJacksonTuning m d pilot) j) ^ 2 := by
  let Q := pilotRectangle canonicalJacksonTuning m d pilot
  let center := rectangleCenter Q
  let radius := rectangleRadius Q
  let K := jacksonDegree canonicalJacksonTuning d
  let p := jacksonTensorPolynomial epsilon K
    (jacksonDegree_ge_two canonicalJacksonTuning d) Q
    (pilotRectangle_valid canonicalJacksonTuning m d pilot hm)
    (pilotRectangle_nonneg canonicalJacksonTuning m d pilot)
  let centerValue := globalCellValue epsilon center
  let lift := fun eval : Cell → ℕ =>
    factorialPolynomialLift m p eval center radius centerValue
  let S := ∑ j : Cell, radius j
  let scale := (1 + epsilon⁻¹) * S
  let μe := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  have hr : ∀ j, 0 < radius j :=
    pilotRectangle_radius_pos canonicalJacksonTuning m d pilot hm hd
  have hqmem := pilotGoodEvent_mem_pilotRectangle
    canonicalJacksonTuning m d pilot q hq hgood
  have hdist : l1CellDistance center q ≤ S := by
    unfold l1CellDistance
    apply Finset.sum_le_sum
    intro j _
    rw [abs_le]
    have hj := hqmem j
    simp only [Q, center, radius, rectangleCenter, rectangleRadius] at hj ⊢
    constructor <;> linarith [hj.1, hj.2]
  have hlip := globalCellValue_lipschitz hepsilon center q
    (fun j => by
      have hlo := pilotRectangle_nonneg canonicalJacksonTuning m d pilot j
      have hv := pilotRectangle_valid canonicalJacksonTuning m d pilot hm j
      simp only [Q, center, rectangleCenter] at hlo hv ⊢
      linarith)
    hq
  have hcenterErr : |centerValue - globalCellValue epsilon q| ≤ scale := by
    dsimp [centerValue, scale]
    exact hlip.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
  have hscale0 : 0 ≤ scale := by
    dsimp [scale, S]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => le_of_lt (hr j))
  have hpoint (eval : Cell → ℕ) :
      (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon q) ^ 2 ≤
      2 * (lift eval) ^ 2 + 2 * scale ^ 2 := by
    have hc : |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        centerValue| ≤ |lift eval| := by
      rw [jacksonCellStatistic_eq_clipAround]
      simpa [centerValue, lift] using abs_clipAround_sub_center_le centerValue
        (d ^ (1 / 4 : ℝ) * scale) (centerValue + lift eval)
        (mul_nonneg (by positivity) hscale0)
    have habs : |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon q| ≤ |lift eval| + scale := by
      calc
        |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            globalCellValue epsilon q| =
          |(jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            centerValue) + (centerValue - globalCellValue epsilon q)| := by ring_nf
        _ ≤ |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            centerValue| + |centerValue - globalCellValue epsilon q| := abs_add_le _ _
        _ ≤ |lift eval| + scale := add_le_add hc hcenterErr
    have hsquare := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) hscale0)).2 habs
    rw [sq_abs] at hsquare
    nlinarith [hsquare, sq_nonneg (|lift eval| - scale), sq_abs (lift eval)]
  have hliftInt : Integrable (fun eval => (lift eval) ^ 2) μe := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mp
    dsimp [lift, μe]
    simp only [factorialPolynomialLift]
    exact memLp_finsetSum _ fun alpha halpha =>
      (normalizedCenteredFactorialMonomial_memLp_two
        m q center radius hr alpha).const_mul _
  have herrInt : Integrable (fun eval =>
      (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon q) ^ 2) μe := by
    apply ((hliftInt.const_mul 2).add (integrable_const (2 * scale ^ 2))).mono'
    · fun_prop
    · filter_upwards with eval
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [Pi.add_apply] using hpoint eval
  calc
    (∫ eval, (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon q) ^ 2 ∂μe) ≤
      ∫ eval, (2 * (lift eval) ^ 2 + 2 * scale ^ 2) ∂μe :=
        integral_mono herrInt ((hliftInt.const_mul 2).add (integrable_const _)) hpoint
    _ = 2 * (∫ eval, (lift eval) ^ 2 ∂μe) + 2 * scale ^ 2 := by
      rw [integral_add, integral_const_mul, integral_const,
        probReal_univ, one_smul]
      · exact hliftInt.const_mul 2
      · exact integrable_const _
    _ ≤ 2 * (Real.exp 1000 * d ^ (1 / 16 : ℝ) * scale ^ 2) +
        2 * scale ^ 2 := by
      gcongr
      exact canonicalGoodPilotFactorialLift_sq_le
        epsilon m hepsilon hm d hd pilot q hq hgood
    _ ≤ 4 * Real.exp 1000 * d ^ (1 / 16 : ℝ) * scale ^ 2 := by
      have he : 1 ≤ Real.exp 1000 := Real.one_le_exp (by norm_num)
      have hdpow : 1 ≤ (d : ℝ) ^ (1 / 16 : ℝ) :=
        Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
      nlinarith [sq_nonneg scale,
        mul_le_mul he hdpow (by norm_num) (by positivity)]
    _ = _ := by rfl

-- @node: canonicalNormalizedAggregateScore_memLp_two
/-- The normalized four-coordinate pilot score is square-integrable under
the independent product-Poisson pilot law. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalNormalizedAggregateScore_memLp_two
    (m : ℝ) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d)
    (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j) :
    MemLp (Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
      (fun j (w : Cell → ℕ) => w j)
      Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
      (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)) 2
      (Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)) := by
  let L := logAlphabet d
  have hL : 1 ≤ L := by
    dsimp [L, logAlphabet]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    linarith
  let coord := fun j (w : Cell → ℕ) =>
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedDeviation
      m.toNNReal (q j).toNNReal (w j) +
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH *
      Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius
        m.toNNReal L (w j)
  have hmean (j : Cell) : m.toNNReal * (q j).toNNReal = (m * q j).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, Real.coe_toNNReal m (le_of_lt hm),
      Real.coe_toNNReal (q j) (hq j), Real.coe_toNNReal (m * q j)
        (mul_nonneg (le_of_lt hm) (hq j))]
  have hcoord (j : Cell) : MemLp (coord j) 2
      (Measure.pi (fun i : Cell => poissonMeasure (m * q i).toNNReal)) := by
    let scalar := fun w : ℕ =>
      Causalean.Stat.Concentration.PoissonSelfNormalized.score
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH L
        (m.toNNReal * (q j).toNNReal) w / m
    have hscalarSq : Integrable (fun w => (scalar w) ^ 2)
        (poissonMeasure (m * q j).toNNReal) := by
      rw [← hmean j]
      exact (Causalean.Stat.Concentration.PoissonSelfNormalized.integrable_score_pow
        (m.toNNReal * (q j).toNNReal) hL (t := 2) (by norm_num)).const_mul (1 / m ^ 2)
        |>.congr (Filter.Eventually.of_forall fun w => by dsimp [scalar]; ring)
    have hscalar : MemLp scalar 2 (poissonMeasure (m * q j).toNNReal) :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hscalarSq
    have hcomp := hscalar.comp_measurePreserving (MeasureTheory.measurePreserving_eval
      (fun i : Cell => poissonMeasure (m * q i).toNNReal) j)
    have heq : coord j = scalar ∘ Function.eval j := by
      funext w
      dsimp [coord, scalar]
      unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedDeviation
        Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius
        Causalean.Stat.Concentration.PoissonSelfNormalized.score
        Causalean.Stat.Concentration.PoissonSelfNormalized.deviation
        Causalean.Stat.Concentration.PoissonSelfNormalized.radius
      rw [Real.coe_toNNReal m (le_of_lt hm), Real.coe_toNNReal (q j) (hq j)]
      have hsqrt : Real.sqrt (((w j : ℝ) / m) * (L / m)) =
          Real.sqrt ((w j : ℝ) * L) / m := by
        rw [show ((w j : ℝ) / m) * (L / m) = ((w j : ℝ) * L) / m ^ 2 by field_simp]
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hm]
      rw [hsqrt]
      rw [show |(w j : ℝ) / m - q j| = |(w j : ℝ) - m * q j| / m by
        rw [show (w j : ℝ) / m - q j = ((w j : ℝ) - m * q j) / m by
          field_simp, abs_div, abs_of_pos hm]]
      simp only [NNReal.coe_mul, Real.coe_toNNReal m (le_of_lt hm),
        Real.coe_toNNReal (q j) (hq j)]
      ring
    rw [heq]
    exact hcomp
  unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
  exact memLp_finsetSum _ fun j _ => hcoord j

-- @node: canonicalPilotFailureBounds
/-- Integrating the pointwise clipping bound on the bad-pilot event gives the
promoted exponentially small local first- and second-moment contributions. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotFailureBounds
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j) :
    let v := Real.sqrt (((∑ j : Cell, q j) * logAlphabet d) / m) +
      logAlphabet d / m
    pilotFailureContribution canonicalJacksonTuning epsilon d m q hm ≤
      2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) *
        Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 1 *
        Real.exp (-20 * logAlphabet d) * v ∧
    pilotFailureSecondMomentContribution canonicalJacksonTuning epsilon d m q hm ≤
      (2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)) ^ 2 *
        Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 2 *
        Real.exp (-20 * logAlphabet d) * v ^ 2 := by
  classical
  dsimp only
  let μp := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  let μe := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  let bad := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
    (fun j (w : Cell → ℕ) => w j)
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
    (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)
  let score := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
    (fun j (w : Cell → ℕ) => w j)
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
    (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)
  let A := 2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)
  have hscoreLp := canonicalNormalizedAggregateScore_memLp_two m hm d hd q hq
  have hscoreInt : Integrable score μp := hscoreLp.integrable one_le_two
  have hscoreSqInt : Integrable (fun pilot => score pilot ^ 2) μp :=
    hscoreLp.integrable_sq
  have hbadMeas : MeasurableSet bad := by
    exact (Set.to_countable bad).measurableSet
  have hbadEq : {pilot : Cell → ℕ |
      ¬ pilotGoodEvent canonicalJacksonTuning m d pilot q} = bad :=
    pilotGoodEvent_compl_eq_normalizedBadAny m hm d q hq
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hone :
      pilotFailureContribution canonicalJacksonTuning epsilon d m q hm ≤
        A * ∫ pilot, bad.indicator score pilot ∂μp := by
    let f := fun z : (Cell → ℕ) × (Cell → ℕ) =>
      if pilotGoodEvent canonicalJacksonTuning m d z.1 q then 0 else
        |jacksonCellStatistic canonicalJacksonTuning epsilon d m z.1 z.2 hm -
          globalCellValue epsilon q|
    let g := fun z : (Cell → ℕ) × (Cell → ℕ) =>
      A * bad.indicator score z.1
    have hgInt : Integrable g (μp.prod μe) := by
      exact ((hscoreInt.indicator hbadMeas).const_mul A).comp_fst μe
    have hpoint (z : (Cell → ℕ) × (Cell → ℕ)) : f z ≤ g z := by
      have h := canonicalPilotFailureIntegrand_le_badScore
        epsilon m hepsilon hm d hd z.1 z.2 q hq
      dsimp [f, g, A]
      by_cases hz : pilotGoodEvent canonicalJacksonTuning m d z.1 q
      · have hznot : z.1 ∉ bad := by
          rw [← hbadEq]
          simpa only [Set.mem_setOf_eq, not_not]
        simp [hz, hznot]
      · have hzbad : z.1 ∈ bad := by rw [← hbadEq]; exact hz
        simp only [hz, ↓reduceIte, bad, score, Set.indicator_of_mem hzbad]
        exact canonicalJacksonCellError_le_normalizedAggregateScore
          epsilon m hepsilon hm d hd z.1 z.2 q hq
    have hfInt : Integrable f (μp.prod μe) := by
      apply hgInt.mono'
      · fun_prop
      · filter_upwards with z
        have hf0 : 0 ≤ f z := by dsimp [f]; split_ifs <;> positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hf0]
        exact hpoint z
    unfold pilotFailureContribution pilotEvaluationLaw
    change (∫ z, f z ∂μp.prod μe) ≤ _
    calc
      (∫ z, f z ∂μp.prod μe) ≤ ∫ z, g z ∂μp.prod μe :=
        integral_mono hfInt hgInt hpoint
      _ = A * ∫ pilot, bad.indicator score pilot ∂μp := by
        rw [MeasureTheory.integral_prod g hgInt]
        simp only [g, integral_const, probReal_univ, one_smul,
          integral_const_mul]
  have htwo :
      pilotFailureSecondMomentContribution canonicalJacksonTuning epsilon d m q hm ≤
        A ^ 2 * ∫ pilot, bad.indicator (fun pilot => score pilot ^ 2) pilot ∂μp := by
    let f := fun z : (Cell → ℕ) × (Cell → ℕ) =>
      if pilotGoodEvent canonicalJacksonTuning m d z.1 q then 0 else
        (jacksonCellStatistic canonicalJacksonTuning epsilon d m z.1 z.2 hm -
          globalCellValue epsilon q) ^ 2
    let g := fun z : (Cell → ℕ) × (Cell → ℕ) =>
      A ^ 2 * bad.indicator (fun pilot => score pilot ^ 2) z.1
    have hgInt : Integrable g (μp.prod μe) := by
      exact ((hscoreSqInt.indicator hbadMeas).const_mul (A ^ 2)).comp_fst μe
    have hpoint (z : (Cell → ℕ) × (Cell → ℕ)) : f z ≤ g z := by
      have h := canonicalPilotFailureSqIntegrand_le_badScoreSq
        epsilon m hepsilon hm d hd z.1 z.2 q hq
      dsimp [f, g, A]
      by_cases hz : pilotGoodEvent canonicalJacksonTuning m d z.1 q
      · have hznot : z.1 ∉ bad := by
          rw [← hbadEq]
          simpa only [Set.mem_setOf_eq, not_not]
        simp [hz, hznot]
      · have hzbad : z.1 ∈ bad := by rw [← hbadEq]; exact hz
        simp only [hz, ↓reduceIte, bad, score, Set.indicator_of_mem hzbad]
        simpa only [A, bad, score, Set.indicator_of_mem hzbad] using h
    have hfInt : Integrable f (μp.prod μe) := by
      apply hgInt.mono'
      · fun_prop
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hpoint z
        · dsimp [f]; split_ifs <;> positivity
    unfold pilotFailureSecondMomentContribution pilotEvaluationLaw
    change (∫ z, f z ∂μp.prod μe) ≤ _
    calc
      (∫ z, f z ∂μp.prod μe) ≤ ∫ z, g z ∂μp.prod μe :=
        integral_mono hfInt hgInt hpoint
      _ = A ^ 2 * ∫ pilot, bad.indicator (fun pilot => score pilot ^ 2) pilot ∂μp := by
        rw [MeasureTheory.integral_prod g hgInt]
        simp only [g, integral_const, probReal_univ, one_smul,
          integral_const_mul]
  have hL : 1 ≤ logAlphabet d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hdR]
  have hmean (j : Cell) : m.toNNReal * (q j).toNNReal = (m * q j).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, Real.coe_toNNReal m (le_of_lt hm),
      Real.coe_toNNReal (q j) (hq j), Real.coe_toNNReal (m * q j)
        (mul_nonneg (le_of_lt hm) (hq j))]
  constructor
  · have hmom := canonicalPilotBadMoment (fun j => (q j).toNNReal) m.toNNReal
      (by simpa using hm) (t := 1) (Or.inl rfl) hL
    simp_rw [hmean] at hmom
    have hmom' : (∫ pilot, bad.indicator score pilot ∂μp) ≤
        Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 1 *
          Real.exp (-20 * logAlphabet d) *
          (Real.sqrt (((∑ j : Cell, q j) * logAlphabet d) / m) +
            logAlphabet d / m) := by
      simpa [μp, bad, score, Real.coe_toNNReal m (le_of_lt hm),
        Real.coe_toNNReal (q _) (hq _)] using hmom
    refine hone.trans ?_
    exact (mul_le_mul_of_nonneg_left hmom' hA).trans_eq (by dsimp [A]; ring)
  · have hmom := canonicalPilotBadMoment (fun j => (q j).toNNReal) m.toNNReal
      (by simpa using hm) (t := 2) (Or.inr (Or.inl rfl)) hL
    simp_rw [hmean] at hmom
    have hmom' : (∫ pilot, bad.indicator (fun pilot => score pilot ^ 2) pilot ∂μp) ≤
        Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 2 *
          Real.exp (-20 * logAlphabet d) *
          (Real.sqrt (((∑ j : Cell, q j) * logAlphabet d) / m) +
            logAlphabet d / m) ^ 2 := by
      simpa [μp, bad, score, Real.coe_toNNReal m (le_of_lt hm),
        Real.coe_toNNReal (q _) (hq _)] using hmom
    refine htwo.trans ?_
    exact (mul_le_mul_of_nonneg_left hmom' (sq_nonneg A)).trans_eq (by dsimp [A]; ring)

-- @node: canonicalLogPowerBounds
/-- The logarithmic factors left by approximation and bad-pilot integration
are absorbed by the fixed fractional powers of the alphabet size. This uses [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalLogPowerBounds (d : ℕ) (hd : 1 ≤ d) :
    logAlphabet d / jacksonDegree canonicalJacksonTuning d ≤ 150000 ∧
    logAlphabet d * d ^ (-3 / 16 : ℝ) ≤ 7 ∧
    logAlphabet d * d ^ (1 / 4 : ℝ) * Real.exp (-20 * logAlphabet d) ≤ 7 ∧
    d ^ (1 / 2 : ℝ) * Real.exp (-20 * logAlphabet d) ≤ d ^ (1 / 16 : ℝ) := by
  let L := logAlphabet d
  let K := jacksonDegree canonicalJacksonTuning d
  have hdpos : (0 : ℝ) < d := by positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpow (a : ℝ) (ha : 0 ≤ a) : 1 ≤ (d : ℝ) ^ a :=
    Real.one_le_rpow (by exact_mod_cast hd) ha
  have hL : 1 ≤ L := by
    dsimp [L, logAlphabet]
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    linarith [Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)]
  have hLK : L / K ≤ 150000 := by
    have hdeg := canonicalJacksonDegree_log_le d
    have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast jacksonDegree_ge_two canonicalJacksonTuning d
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hlogpow : L ≤ 7 * (d : ℝ) ^ (3 / 16 : ℝ) := by
    have hlog := Real.log_natCast_le_rpow_div d (show (0 : ℝ) < 3 / 16 by norm_num)
    have hpow1 := hdpow (3 / 16) (by norm_num)
    dsimp [L, logAlphabet]
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    norm_num at hlog
    nlinarith
  have hsecond : L * d ^ (-3 / 16 : ℝ) ≤ 7 := by
    rw [show (-3 / 16 : ℝ) = -(3 / 16) by norm_num,
      Real.rpow_neg (le_of_lt hdpos), ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hdpos _)).2 hlogpow
  have hexp : Real.exp (-20 * L) ≤ 1 / (d : ℝ) := by
    have hneg : -20 * L ≤ -L := by nlinarith
    calc
      Real.exp (-20 * L) ≤ Real.exp (-L) := Real.exp_le_exp.mpr hneg
      _ = (Real.exp 1 * d)⁻¹ := by
        dsimp [L, logAlphabet]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ ≤ 1 / d := by
        simpa only [one_div] using inv_anti₀ hdpos (by
          calc
            (d : ℝ) = 1 * d := by ring
            _ ≤ Real.exp 1 * d := by
              gcongr
              exact Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num))
  have hthird : L * d ^ (1 / 4 : ℝ) * Real.exp (-20 * L) ≤ 7 := by
    calc
      L * d ^ (1 / 4 : ℝ) * Real.exp (-20 * L) ≤
          L * d ^ (1 / 4 : ℝ) * (1 / d) := by gcongr
      _ = L * d ^ (-3 / 4 : ℝ) := by
        rw [show (-3 / 4 : ℝ) = 1 / 4 - 1 by norm_num,
          Real.rpow_sub hdpos, Real.rpow_one]
        field_simp
      _ ≤ L * d ^ (-3 / 16 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)) (by linarith)
      _ ≤ 7 := hsecond
  have hfourth : d ^ (1 / 2 : ℝ) * Real.exp (-20 * L) ≤
      d ^ (1 / 16 : ℝ) := by
    calc
      d ^ (1 / 2 : ℝ) * Real.exp (-20 * L) ≤ d ^ (1 / 2 : ℝ) * (1 / d) := by
        gcongr
      _ = d ^ (-1 / 2 : ℝ) := by
        rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num,
          Real.rpow_sub hdpos, Real.rpow_one]
        field_simp
      _ ≤ d ^ (1 / 16 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)
  exact ⟨hLK, hsecond, hthird, hfourth⟩

-- @node: canonicalLogSquaredPowerBounds
/-- Two coarse logarithmic bounds used to absorb the squared localized pilot
radius into fixed powers of the alphabet size. This uses [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalLogSquaredPowerBounds (d : ℕ) (hd : 1 ≤ d) :
    logAlphabet d ^ 2 * d ^ (-3 / 16 : ℝ) ≤ 225 ∧
    logAlphabet d ^ 2 * d ^ (1 / 4 : ℝ) *
      Real.exp (-20 * logAlphabet d) ≤ 225 := by
  let L := logAlphabet d
  have hdpos : (0 : ℝ) < d := by positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ L := by
    dsimp [L, logAlphabet]
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    linarith [Real.log_nonneg hdR]
  have hlog := Real.log_natCast_le_rpow_div d
    (show (0 : ℝ) < 3 / 32 by norm_num)
  have hpow : 1 ≤ (d : ℝ) ^ (3 / 32 : ℝ) :=
    Real.one_le_rpow hdR (by norm_num)
  have hLpow : L ≤ 15 * (d : ℝ) ^ (3 / 32 : ℝ) := by
    dsimp [L, logAlphabet]
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
    norm_num at hlog
    nlinarith
  have hsquare : L ^ 2 ≤ 225 * (d : ℝ) ^ (3 / 16 : ℝ) := by
    have hs := (sq_le_sq₀ (by linarith) (by positivity)).2 hLpow
    calc
      L ^ 2 ≤ (15 * (d : ℝ) ^ (3 / 32 : ℝ)) ^ 2 := hs
      _ = 225 * (d : ℝ) ^ (3 / 16 : ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (le_of_lt hdpos)]
        norm_num
  have hfirst : L ^ 2 * (d : ℝ) ^ (-3 / 16 : ℝ) ≤ 225 := by
    rw [show (-3 / 16 : ℝ) = -(3 / 16) by norm_num,
      Real.rpow_neg (le_of_lt hdpos), ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hdpos _)).2 hsquare
  have hexp : Real.exp (-20 * L) ≤ 1 / (d : ℝ) := by
    have hneg : -20 * L ≤ -L := by nlinarith
    calc
      Real.exp (-20 * L) ≤ Real.exp (-L) := Real.exp_le_exp.mpr hneg
      _ = (Real.exp 1 * d)⁻¹ := by
        dsimp [L, logAlphabet]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ ≤ 1 / d := by
        simpa only [one_div] using inv_anti₀ hdpos (by
          calc
            (d : ℝ) = 1 * d := by ring
            _ ≤ Real.exp 1 * d := by
              gcongr
              exact Real.one_le_exp (by norm_num))
  refine ⟨hfirst, ?_⟩
  calc
    L ^ 2 * d ^ (1 / 4 : ℝ) * Real.exp (-20 * L) ≤
        L ^ 2 * d ^ (1 / 4 : ℝ) * (1 / d) := by gcongr
    _ = L ^ 2 * d ^ (-3 / 4 : ℝ) := by
      rw [show (-3 / 4 : ℝ) = 1 / 4 - 1 by norm_num,
        Real.rpow_sub hdpos, Real.rpow_one]
      field_simp
    _ ≤ L ^ 2 * d ^ (-3 / 16 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)) (sq_nonneg L)
    _ ≤ 225 := hfirst

-- @node: sum_cell_sqrt_mul_le
/-- Cauchy--Schwarz over the four cell coordinates controls the sum of local
square-root scales by twice the aggregate square-root scale. This uses [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated tau condition holds](hyp:htau). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma sum_cell_sqrt_mul_le (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j)
    (tau : ℝ) (htau : 0 ≤ tau) :
    (∑ j : Cell, Real.sqrt (q j * tau)) ≤
      2 * Real.sqrt ((∑ j : Cell, q j) * tau) := by
  have hsum0 : 0 ≤ ∑ j : Cell, Real.sqrt (q j * tau) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hqsum0 : 0 ≤ (∑ j : Cell, q j) * tau :=
    mul_nonneg (Finset.sum_nonneg fun j _ => hq j) htau
  apply (sq_le_sq₀ hsum0 (by positivity)).mp
  calc
    (∑ j : Cell, Real.sqrt (q j * tau)) ^ 2 ≤
        4 * ∑ j : Cell, (Real.sqrt (q j * tau)) ^ 2 := by
      simpa [Cell] using Causalean.Mathlib.Analysis.weighted_inner_sq_le
        (Finset.univ : Finset Cell) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
        (fun j => Real.sqrt (q j * tau)) (fun _ _ => by norm_num)
    _ = (2 * Real.sqrt ((∑ j : Cell, q j) * tau)) ^ 2 := by
      simp_rw [Real.sq_sqrt (mul_nonneg (hq _) htau)]
      rw [show ∑ x : Cell, q x * tau = (∑ x : Cell, q x) * tau by
        rw [Finset.sum_mul]]
      rw [show (2 * Real.sqrt ((∑ j : Cell, q j) * tau)) ^ 2 =
        4 * Real.sqrt ((∑ j : Cell, q j) * tau) ^ 2 by ring,
        Real.sq_sqrt hqsum0]


end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
