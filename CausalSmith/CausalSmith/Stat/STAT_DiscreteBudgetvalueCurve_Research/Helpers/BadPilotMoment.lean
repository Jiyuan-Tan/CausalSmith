module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PilotRadiusMoment
public import Causalean.Stat.Concentration.Poisson.EmpiricalRadius.Product

/-! Coordinatewise empirical-radius estimates for bad pilot cells. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped NNReal ENNReal

/-- The paper's one-coordinate bad pilot event has the promoted exponential
probability bound. With [the specified inputs and conditions](hyp:m,q,hm,hq,d,hd,zeta), [the stated relationship holds](goal). -/
-- @node: poisson_pilotCoordinateBad_probability
lemma poisson_pilotCoordinateBad_probability {m q : ℝ} (hm : 0 < m)
    (hq : 0 ≤ q) {d : ℕ} (hd : 1 ≤ d) (zeta : Cell) :
    poissonMeasure (Real.toNNReal (m * q))
      {w : ℕ | |pilotCenter m (fun _ => w) zeta - q| >
        pilotHalfWidth m d (fun _ => w) zeta / 4} ≤
      ENNReal.ofReal (2 * Real.exp (-40 * logAlphabet d)) := by
  let mNN : ℝ≥0 := Real.toNNReal m
  let qNN : ℝ≥0 := Real.toNNReal q
  have hmNN : 0 < mNN := Real.toNNReal_pos.mpr hm
  have hL : 1 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdR]
  have hrate : mNN * qNN = Real.toNNReal (m * q) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, mNN, qNN]
    rw [Real.coe_toNNReal m hm.le, Real.coe_toNNReal q hq,
      Real.coe_toNNReal (m * q) (mul_nonneg hm.le hq)]
  rw [← hrate]
  have hevent :
      {w : ℕ | |pilotCenter m (fun _ => w) zeta - q| >
        pilotHalfWidth m d (fun _ => w) zeta / 4} =
      {w : ℕ | normalizedDeviation mNN qNN w >
        empiricalRadius pilotRadiusConstant mNN
          (logAlphabet d / (mNN : ℝ)) w / 4} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    rw [pilotHalfWidth_eq_empiricalRadius hm d (fun _ => w) zeta]
    simp only [pilotCenter, mNN, qNN, Real.coe_toNNReal m hm.le,
      Real.coe_toNNReal q hq, normalizedDeviation]
  rw [hevent]
  exact poisson_empiricalRadius_bad_probability qNN mNN hmNN
    pilotRadiusConstant (logAlphabet d)
    (by unfold pilotRadiusConstant Causalean.Stat.Concentration.PoissonSelfNormalized.universalH;
        norm_num)
    hL

/-- On its bad event, the squared paper coordinate score satisfies the
promoted empirical-radius moment bound. With [the specified inputs and conditions](hyp:m,q,hm,hq,d,hd,zeta), [the stated relationship holds](goal). -/
-- @node: poisson_pilotCoordinateBad_second_moment
lemma poisson_pilotCoordinateBad_second_moment {m q : ℝ} (hm : 0 < m)
    (hq : 0 ≤ q) {d : ℕ} (hd : 1 ≤ d) (zeta : Cell) :
    (∫ w : ℕ,
      (if |pilotCenter m (fun _ => w) zeta - q| >
          pilotHalfWidth m d (fun _ => w) zeta / 4 then
        (|pilotCenter m (fun _ => w) zeta - q| +
          pilotHalfWidth m d (fun _ => w) zeta) ^ 2 else 0)
      ∂poissonMeasure (Real.toNNReal (m * q))) ≤
      (pilotRadiusConstant /
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH) ^ 2 *
        Causalean.Stat.Concentration.PoissonSelfNormalized.scalarBadMomentConstant 2 *
        Real.exp (-20 * logAlphabet d) *
        (Real.sqrt (q * logAlphabet d / m) + logAlphabet d / m) ^ 2 := by
  let mNN : ℝ≥0 := Real.toNNReal m
  let qNN : ℝ≥0 := Real.toNNReal q
  have hmNN : 0 < mNN := Real.toNNReal_pos.mpr hm
  have hL : 1 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdR]
  have hrate : mNN * qNN = Real.toNNReal (m * q) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, mNN, qNN]
    rw [Real.coe_toNNReal m hm.le, Real.coe_toNNReal q hq,
      Real.coe_toNNReal (m * q) (mul_nonneg hm.le hq)]
  rw [← hrate]
  convert poisson_empiricalRadius_bad_second_moment qNN mNN hmNN
    pilotRadiusConstant (logAlphabet d)
    (by unfold pilotRadiusConstant Causalean.Stat.Concentration.PoissonSelfNormalized.universalH;
        norm_num)
    hL using 1
  · congr 1
    funext w
    rw [pilotHalfWidth_eq_empiricalRadius hm d (fun _ => w) zeta]
    simp only [pilotCenter, mNN, qNN, Real.coe_toNNReal m hm.le,
      Real.coe_toNNReal q hq, normalizedDeviation]
    rfl
  · simp only [qNN, mNN, Real.coe_toNNReal q hq, Real.coe_toNNReal m hm.le]

/-- On its bad event, the fourth power of the paper coordinate score satisfies
the promoted empirical-radius moment bound. With [the specified inputs and conditions](hyp:m,q,hm,hq,d,hd,zeta), [the stated relationship holds](goal). -/
-- @node: poisson_pilotCoordinateBad_fourth_moment
lemma poisson_pilotCoordinateBad_fourth_moment {m q : ℝ} (hm : 0 < m)
    (hq : 0 ≤ q) {d : ℕ} (hd : 1 ≤ d) (zeta : Cell) :
    (∫ w : ℕ,
      (if |pilotCenter m (fun _ => w) zeta - q| >
          pilotHalfWidth m d (fun _ => w) zeta / 4 then
        (|pilotCenter m (fun _ => w) zeta - q| +
          pilotHalfWidth m d (fun _ => w) zeta) ^ 4 else 0)
      ∂poissonMeasure (Real.toNNReal (m * q))) ≤
      (pilotRadiusConstant /
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH) ^ 4 *
        Causalean.Stat.Concentration.PoissonSelfNormalized.scalarBadMomentConstant 4 *
        Real.exp (-20 * logAlphabet d) *
        (Real.sqrt (q * logAlphabet d / m) + logAlphabet d / m) ^ 4 := by
  let mNN : ℝ≥0 := Real.toNNReal m
  let qNN : ℝ≥0 := Real.toNNReal q
  have hmNN : 0 < mNN := Real.toNNReal_pos.mpr hm
  have hL : 1 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdR]
  have hrate : mNN * qNN = Real.toNNReal (m * q) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, mNN, qNN]
    rw [Real.coe_toNNReal m hm.le, Real.coe_toNNReal q hq,
      Real.coe_toNNReal (m * q) (mul_nonneg hm.le hq)]
  rw [← hrate]
  convert poisson_empiricalRadius_bad_fourth_moment qNN mNN hmNN
    pilotRadiusConstant (logAlphabet d)
    (by unfold pilotRadiusConstant Causalean.Stat.Concentration.PoissonSelfNormalized.universalH;
        norm_num)
    hL using 1
  · congr 1
    funext w
    rw [pilotHalfWidth_eq_empiricalRadius hm d (fun _ => w) zeta]
    simp only [pilotCenter, mNN, qNN, Real.coe_toNNReal m hm.le,
      Real.coe_toNNReal q hq, normalizedDeviation]
    rfl
  · simp only [qNN, mNN, Real.coe_toNNReal q hq, Real.coe_toNNReal m hm.le]

/-- The universal four-coordinate bad-score moment specializes to one pilot
cell with total intensity `m * cellMass`. With [the specified inputs and conditions](hyp:d,P,j,m,L,hm,hL,t,ht), [the stated relationship holds](goal). -/
-- @node: pilotCell_universalBadScore_moment
lemma pilotCell_universalBadScore_moment {d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) {m L : ℝ} (hm : 0 < m) (hL : 1 ≤ L)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    let rate : Fin 4 → ℝ≥0 := fun i =>
      Real.toNNReal (m * cellVector P j (CellFourEquiv.symm i))
    let μ := poissonTableLaw rate
    let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
    (∫ p, (badAny W universalH L rate).indicator
        (fun p => (aggregateScore W universalH L rate p) ^ t) p ∂μ) ≤
      productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt (m * cellMass P j * L) + L) ^ t := by
  dsimp only
  let rate : Fin 4 → ℝ≥0 := fun i =>
    Real.toNNReal (m * cellVector P j (CellFourEquiv.symm i))
  let μ := poissonTableLaw rate
  let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, poissonTableLaw]
    infer_instance
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate i)) μ := by
    simpa [W, μ] using poissonTable_eval_coordinate_law rate i
  have hWindep : iIndepFun W μ := by
    simpa [W, μ] using poissonTable_eval_independent rate
  have hraw := independent_poisson_badAny_moment_four μ W rate
    (fun _ => measurable_pi_apply _) hWlaw hWindep ht hL
  have hq (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hrate (i : Fin 4) : (rate i : ℝ) =
      m * cellVector P j (CellFourEquiv.symm i) := by
    dsimp [rate]
    exact max_eq_left (mul_nonneg hm.le (hq _))
  have hcellmass : ∑ z : Cell, cellVector P j z = cellMass P j := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    simp [cellMass, cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass,
      finTwoEquiv]
    ring
  have hmass : ∑ i : Fin 4, (rate i : ℝ) = m * cellMass P j := by
    calc
      _ = m * ∑ i : Fin 4, cellVector P j (CellFourEquiv.symm i) := by
        simp_rw [hrate, Finset.mul_sum]
      _ = m * ∑ z : Cell, cellVector P j z := by
        rw [Equiv.sum_comp CellFourEquiv.symm]
      _ = _ := by rw [hcellmass]
  simpa [μ, W, hmass] using hraw

/-- The promoted empirical-radius product theorem, specialized to the four
pilot counts of one paper cell. With [the specified inputs and conditions](hyp:n,d,P,j,hn,hd,t,ht), [the stated relationship holds](goal). -/
-- @node: pilotCell_empiricalBadScore_moment
lemma pilotCell_empiricalBadScore_moment {n d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) (hn : 1 ≤ n) (hd : 1 ≤ d)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    let m : ℝ := (n : ℝ) / 8
    let mNN : ℝ≥0 := Real.toNNReal m
    let q : Fin 4 → ℝ≥0 := fun i =>
      Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
    let μ := poissonTableLaw (fun i => mNN * q i)
    let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
    (∫ p, (empiricalBadAny W pilotRadiusConstant (logAlphabet d) mNN q).indicator
        (fun p => (empiricalAggregateScore W pilotRadiusConstant
          (logAlphabet d) mNN q p) ^ t) p ∂μ) ≤
      (pilotRadiusConstant / universalH) ^ t * productMomentConstant 4 t *
        Real.exp (-20 * logAlphabet d) *
        badPilotCellScale (n := n) P j ^ t := by
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let mNN : ℝ≥0 := Real.toNNReal m
  let q : Fin 4 → ℝ≥0 := fun i =>
    Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
  let μ := poissonTableLaw (fun i => mNN * q i)
  let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
  have hm : 0 < m := by dsimp [m]; positivity
  have hmNN : 0 < mNN := Real.toNNReal_pos.mpr hm
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, poissonTableLaw]
    infer_instance
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (mNN * q i)) μ := by
    simpa [W, μ] using poissonTable_eval_coordinate_law
      (fun i => mNN * q i) i
  have hWindep : iIndepFun W μ := by
    simpa [W, μ] using poissonTable_eval_independent
      (fun i => mNN * q i)
  have hL : 1 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdR]
  have hprod := independent_poisson_empiricalRadius_badAny_moment_four
    μ W q mNN hmNN (fun _ => measurable_pi_apply _) hWlaw hWindep ht
    pilotRadiusConstant (logAlphabet d)
    (by unfold pilotRadiusConstant universalH; norm_num) hL
  have hq (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hqcoe (i : Fin 4) : (q i : ℝ) =
      cellVector P j (CellFourEquiv.symm i) := by
    dsimp [q]
    exact max_eq_left (hq _)
  have hcellmass : ∑ z : Cell, cellVector P j z = cellMass P j := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    simp [cellMass, cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass,
      finTwoEquiv]
    ring
  have hqsum : ∑ i : Fin 4, (q i : ℝ) = cellMass P j := by
    calc
      _ = ∑ z : Cell, cellVector P j z := by
        simp_rw [hqcoe]
        rw [Equiv.sum_comp CellFourEquiv.symm]
      _ = _ := hcellmass
  have hmcoe : (mNN : ℝ) = m := Real.coe_toNNReal m hm.le
  rw [hqsum, hmcoe] at hprod
  simpa [μ, W, q, hqsum, badPilotCellScale, m] using hprod

/-- The squared empirical aggregate score restricted to the union of the four
bad-radius events is integrable under independent Poisson coordinates. With [the specified inputs and conditions](hyp:W,q,m,hm,hWmeas,hWlaw,H,L,hH,hL), [the stated relationship holds](goal). -/
-- @node: independent_poisson_empiricalBadScore_sq_integrable_four
lemma independent_poisson_empiricalBadScore_sq_integrable_four
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (m * q i)) μ)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) :
    Integrable (fun ω =>
      (empiricalBadAny W H L m q).indicator
        (fun ω => (empiricalAggregateScore W H L m q ω) ^ 2) ω) μ := by
  let lambda : Fin 4 → ℝ≥0 := fun i => m * q i
  let c : ℝ := H / universalH / (m : ℝ)
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hH0 : 0 ≤ H := le_trans universalH_pos.le hH
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (div_nonneg hH0 universalH_pos.le) hmR.le
  have hscoreInt (i : Fin 4) :
      Integrable (fun ω => (score universalH L (lambda i) (W i ω)) ^ 2) μ := by
    have h := integrable_score_pow (lambda i) hL (t := 2)
    rw [← (hWlaw i).map_eq] at h
    exact h.comp_aemeasurable (hWlaw i).aemeasurable
  have hdomInt : Integrable (fun ω =>
      4 * ∑ i, (score universalH L (lambda i) (W i ω)) ^ 2) μ :=
    (integrable_finsetSum _ fun i _ => hscoreInt i).const_mul 4
  have hrawInt : Integrable (fun ω =>
      (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ 2) ω) μ := by
    apply Integrable.mono' hdomInt
    · unfold badAny aggregateScore score deviation radius
      measurability
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · by_cases hb : ω ∈ badAny W universalH L lambda
        · rw [Set.indicator_of_mem hb]
          simpa [aggregateScore] using pow_sum_le_card_mul_sum_pow
            (s := (Finset.univ : Finset (Fin 4)))
            (f := fun i => score universalH L (lambda i) (W i ω))
            (fun i _ => by
              unfold score deviation radius
              exact add_nonneg (abs_nonneg _)
                (mul_nonneg universalH_pos.le (by positivity))) 1
        · simp only [Set.indicator_of_notMem hb, norm_zero, abs_zero]
          exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      · by_cases hb : ω ∈ badAny W universalH L lambda
        · rw [Set.indicator_of_mem hb]
          positivity
        · simp [hb]
  apply Integrable.mono' (hrawInt.const_mul (c ^ 2))
  · unfold empiricalBadAny empiricalAggregateScore normalizedDeviation empiricalRadius
    measurability
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · by_cases hb : ω ∈ empiricalBadAny W H L m q
      · have hrb : ω ∈ badAny W universalH L lambda :=
          empiricalBadAny_subset_raw W q m hm H L hH hL hb
        rw [Set.indicator_of_mem hb, Set.indicator_of_mem hrb]
        have hscore := empiricalAggregateScore_le_raw W q m hm H L hH hL ω
        have hemp0 : 0 ≤ empiricalAggregateScore W H L m q ω := by
          unfold empiricalAggregateScore
          apply Finset.sum_nonneg
          intro i _
          have hd : 0 ≤ normalizedDeviation m (q i) (W i ω) := by
            unfold normalizedDeviation
            positivity
          have hr : 0 ≤ empiricalRadius H m (L / (m : ℝ)) (W i ω) := by
            rw [empiricalRadius_eq_normalizedRadius]
            unfold normalizedRadius
            exact mul_nonneg hH0 (add_nonneg (Real.sqrt_nonneg _) (by positivity))
          exact add_nonneg hd hr
        calc
          (empiricalAggregateScore W H L m q ω) ^ 2 ≤
              (c * aggregateScore W universalH L lambda ω) ^ 2 := by
            apply pow_le_pow_left₀ hemp0
            calc
              _ ≤ (H / universalH) *
                  (aggregateScore W universalH L (fun i => m * q i) ω /
                    (m : ℝ)) := hscore
              _ = c * aggregateScore W universalH L lambda ω := by
                dsimp [c, lambda]
                ring
          _ = c ^ 2 * aggregateScore W universalH L lambda ω ^ 2 := by ring
      · rw [Set.indicator_of_notMem hb]
        by_cases hrb : ω ∈ badAny W universalH L lambda
        · rw [Set.indicator_of_mem hrb]
          exact mul_nonneg (sq_nonneg c) (sq_nonneg _)
        · simp [hrb]
    · by_cases hb : ω ∈ empiricalBadAny W H L m q
      · rw [Set.indicator_of_mem hb]
        positivity
      · rw [Set.indicator_of_notMem hb]

/-- Without restricting to the bad event, the squared empirical aggregate
score is still integrable under four Poisson coordinates. With [the specified inputs and conditions](hyp:W,q,m,hm,hWmeas,hWlaw,H,L,hH,hL), [the stated relationship holds](goal). -/
-- @node: independent_poisson_empiricalAggregateScore_sq_integrable_four
lemma independent_poisson_empiricalAggregateScore_sq_integrable_four
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (m * q i)) μ)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) :
    Integrable (fun ω =>
      (empiricalAggregateScore W H L m q ω) ^ 2) μ := by
  let lambda : Fin 4 → ℝ≥0 := fun i => m * q i
  let c : ℝ := H / universalH / (m : ℝ)
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hH0 : 0 ≤ H := le_trans universalH_pos.le hH
  have hscoreInt (i : Fin 4) :
      Integrable (fun ω => (score universalH L (lambda i) (W i ω)) ^ 2) μ := by
    have h := integrable_score_pow (lambda i) hL (t := 2)
    rw [← (hWlaw i).map_eq] at h
    exact h.comp_aemeasurable (hWlaw i).aemeasurable
  have hdomInt : Integrable (fun ω =>
      4 * ∑ i, (score universalH L (lambda i) (W i ω)) ^ 2) μ :=
    (integrable_finsetSum _ fun i _ => hscoreInt i).const_mul 4
  have hrawInt : Integrable (fun ω =>
      (aggregateScore W universalH L lambda ω) ^ 2) μ := by
    apply hdomInt.mono'
    · unfold aggregateScore score deviation radius
      measurability
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa [aggregateScore] using pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i => score universalH L (lambda i) (W i ω))
        (fun i _ => by
          unfold score deviation radius
          exact add_nonneg (abs_nonneg _)
            (mul_nonneg universalH_pos.le (by positivity))) 1
  apply (hrawInt.const_mul (c ^ 2)).mono'
  · unfold empiricalAggregateScore normalizedDeviation empiricalRadius
    measurability
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hemp0 : 0 ≤ empiricalAggregateScore W H L m q ω := by
      unfold empiricalAggregateScore
      apply Finset.sum_nonneg
      intro i _
      have hd : 0 ≤ normalizedDeviation m (q i) (W i ω) := by
        unfold normalizedDeviation
        positivity
      have hr : 0 ≤ empiricalRadius H m (L / (m : ℝ)) (W i ω) := by
        rw [empiricalRadius_eq_normalizedRadius]
        unfold normalizedRadius
        exact mul_nonneg hH0 (add_nonneg (Real.sqrt_nonneg _) (by positivity))
      exact add_nonneg hd hr
    calc
      (empiricalAggregateScore W H L m q ω) ^ 2 ≤
          (c * aggregateScore W universalH L lambda ω) ^ 2 := by
        apply pow_le_pow_left₀ hemp0
        calc
          _ ≤ (H / universalH) *
              (aggregateScore W universalH L (fun i => m * q i) ω /
                (m : ℝ)) :=
            empiricalAggregateScore_le_raw W q m hm H L hH hL ω
          _ = c * aggregateScore W universalH L lambda ω := by
            dsimp [c, lambda]
            ring
      _ = c ^ 2 * aggregateScore W universalH L lambda ω ^ 2 := by ring

/-- The four paper pilot coordinates have an exponentially small squared
aggregate score on failure of the good-pilot rectangle. With [the specified inputs and conditions](hyp:n,d,P,j,hn,hd), [the stated relationship holds](goal). -/
-- @node: pilotCell_badScore_sq_integral_le
lemma pilotCell_badScore_sq_integral_le {n d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    let m : ℝ := (n : ℝ) / 8
    let mNN : ℝ≥0 := Real.toNNReal m
    let q : Fin 4 → ℝ≥0 := fun i =>
      Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
    let μ := poissonTableLaw (fun i => mNN * q i)
    (∫ p : Fin 4 → ℕ,
      (if (∀ z : Cell,
          |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
            pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4)
        then 0 else
          (∑ z : Cell,
            (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
              pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)) ^ 2) ∂μ) ≤
      (pilotRadiusConstant / universalH) ^ 2 * productMomentConstant 4 2 *
        Real.exp (-20 * logAlphabet d) *
        badPilotCellScale (n := n) P j ^ 2 := by
  classical
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let mNN : ℝ≥0 := Real.toNNReal m
  let q : Fin 4 → ℝ≥0 := fun i =>
    Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
  let μ := poissonTableLaw (fun i => mNN * q i)
  let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
  have hm : 0 < m := by dsimp [m]; positivity
  have hmcoe : (mNN : ℝ) = m := Real.coe_toNNReal m hm.le
  have hq (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hqcoe (i : Fin 4) : (q i : ℝ) =
      cellVector P j (CellFourEquiv.symm i) := by
    dsimp [q]
    exact max_eq_left (hq _)
  have hmoment := pilotCell_empiricalBadScore_moment P j hn hd
    (t := 2) (Or.inr (Or.inl rfl))
  have hscore (p : Fin 4 → ℕ) :
      empiricalAggregateScore W pilotRadiusConstant (logAlphabet d) mNN q p =
        ∑ z : Cell,
          (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
            pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z) := by
    unfold empiricalAggregateScore
    calc
      _ = ∑ i : Fin 4,
          (|pilotCenter m (fun z => p (CellFourEquiv z))
              (CellFourEquiv.symm i) - cellVector P j (CellFourEquiv.symm i)| +
            pilotHalfWidth m d (fun z => p (CellFourEquiv z))
              (CellFourEquiv.symm i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pilotHalfWidth_eq_empiricalRadius hm d
          (fun z => p (CellFourEquiv z)) (CellFourEquiv.symm i)]
        simp only [W, normalizedDeviation, hmcoe, hqcoe, mNN,
          Equiv.apply_symm_apply, pilotCenter]
      _ = _ := Equiv.sum_comp CellFourEquiv.symm (fun z : Cell =>
        |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)
  have hbad (p : Fin 4 → ℕ) :
      p ∈ empiricalBadAny W pilotRadiusConstant (logAlphabet d) mNN q ↔
        ¬(∀ z : Cell,
          |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
            pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4) := by
    unfold empiricalBadAny
    constructor
    · rintro ⟨i, hi⟩ hgood
      let z := CellFourEquiv.symm i
      have hz := hgood z
      rw [pilotHalfWidth_eq_empiricalRadius hm d
        (fun z => p (CellFourEquiv z)) z] at hz
      simp only [W, normalizedDeviation, hmcoe, hqcoe, z,
        Equiv.apply_symm_apply, pilotCenter] at hi hz
      linarith
    · intro hgood
      push_neg at hgood
      obtain ⟨z, hz⟩ := hgood
      refine ⟨CellFourEquiv z, ?_⟩
      rw [pilotHalfWidth_eq_empiricalRadius hm d
        (fun z => p (CellFourEquiv z)) z] at hz
      simpa only [W, normalizedDeviation, hmcoe, hqcoe,
        Equiv.symm_apply_apply, pilotCenter] using hz
  calc
    _ = ∫ p, (empiricalBadAny W pilotRadiusConstant
          (logAlphabet d) mNN q).indicator
        (fun p => (empiricalAggregateScore W pilotRadiusConstant
          (logAlphabet d) mNN q p) ^ 2) p ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        change (if (∀ z : Cell,
            |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
              pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4)
          then 0 else
            (∑ z : Cell,
              (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
                pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)) ^ 2) = _
        by_cases hg : ∀ z : Cell,
          |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
            pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4
        · have hb : p ∉ empiricalBadAny W pilotRadiusConstant
              (logAlphabet d) mNN q := fun hp => (hbad p).1 hp hg
          rw [if_pos hg, Set.indicator_of_notMem hb]
        · have hb : p ∈ empiricalBadAny W pilotRadiusConstant
              (logAlphabet d) mNN q := (hbad p).2 hg
          rw [if_neg hg, Set.indicator_of_mem hb, hscore]
    _ ≤ _ := by simpa [m, mNN, q, μ, W] using hmoment

/-- The paper's squared four-coordinate bad score is integrable under its
one-cell product Poisson law. With [the specified inputs and conditions](hyp:n,d,P,j,hn,hd), [the stated relationship holds](goal). -/
-- @node: pilotCell_badScore_sq_integrable
lemma pilotCell_badScore_sq_integrable {n d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    let m : ℝ := (n : ℝ) / 8
    let mNN : ℝ≥0 := Real.toNNReal m
    let q : Fin 4 → ℝ≥0 := fun i =>
      Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
    let μ := poissonTableLaw (fun i => mNN * q i)
    Integrable (fun p : Fin 4 → ℕ =>
      if (∀ z : Cell,
          |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
            pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4)
      then 0 else
        (∑ z : Cell,
          (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
            pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)) ^ 2) μ := by
  classical
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let mNN : ℝ≥0 := Real.toNNReal m
  let q : Fin 4 → ℝ≥0 := fun i =>
    Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
  let μ := poissonTableLaw (fun i => mNN * q i)
  let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
  have hm : 0 < m := by dsimp [m]; positivity
  have hmNN : 0 < mNN := Real.toNNReal_pos.mpr hm
  have hmcoe : (mNN : ℝ) = m := Real.coe_toNNReal m hm.le
  have hq (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hqcoe (i : Fin 4) : (q i : ℝ) =
      cellVector P j (CellFourEquiv.symm i) := by
    dsimp [q]
    exact max_eq_left (hq _)
  letI : IsProbabilityMeasure μ := by dsimp [μ, poissonTableLaw]; infer_instance
  have hbase := independent_poisson_empiricalBadScore_sq_integrable_four
    μ W q mNN hmNN (fun _ => measurable_pi_apply _)
    (fun i => by
      simpa [W, μ] using poissonTable_eval_coordinate_law
        (fun i => mNN * q i) i)
    pilotRadiusConstant (logAlphabet d)
    (by unfold pilotRadiusConstant universalH; norm_num)
    (by
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp]
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith [Real.log_nonneg hdR])
  apply hbase.congr
  filter_upwards [] with p
  have hscore : empiricalAggregateScore W pilotRadiusConstant
      (logAlphabet d) mNN q p =
      ∑ z : Cell,
        (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z) := by
    unfold empiricalAggregateScore
    calc
      _ = ∑ i : Fin 4,
          (|pilotCenter m (fun z => p (CellFourEquiv z))
              (CellFourEquiv.symm i) - cellVector P j (CellFourEquiv.symm i)| +
            pilotHalfWidth m d (fun z => p (CellFourEquiv z))
              (CellFourEquiv.symm i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pilotHalfWidth_eq_empiricalRadius hm d
          (fun z => p (CellFourEquiv z)) (CellFourEquiv.symm i)]
        simp only [W, normalizedDeviation, hmcoe, hqcoe, mNN,
          Equiv.apply_symm_apply, pilotCenter]
      _ = _ := Equiv.sum_comp CellFourEquiv.symm (fun z : Cell =>
        |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)
  have hbad : p ∈ empiricalBadAny W pilotRadiusConstant
      (logAlphabet d) mNN q ↔ ¬(∀ z : Cell,
        |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4) := by
    unfold empiricalBadAny
    constructor
    · rintro ⟨i, hi⟩ hgood
      have hz := hgood (CellFourEquiv.symm i)
      rw [pilotHalfWidth_eq_empiricalRadius hm d
        (fun z => p (CellFourEquiv z)) (CellFourEquiv.symm i)] at hz
      simp only [W, normalizedDeviation, hmcoe, hqcoe,
        Equiv.apply_symm_apply, pilotCenter] at hi hz
      linarith
    · push Not
      rintro ⟨z, hz⟩
      refine ⟨CellFourEquiv z, ?_⟩
      rw [pilotHalfWidth_eq_empiricalRadius hm d
        (fun z => p (CellFourEquiv z)) z] at hz
      simpa only [W, normalizedDeviation, hmcoe, hqcoe,
        Equiv.symm_apply_apply, pilotCenter] using hz
  by_cases hg : ∀ z : Cell,
      |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
        pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4
  · rw [if_pos hg, Set.indicator_of_notMem (fun hp => (hbad.mp hp) hg)]
  · rw [if_neg hg, Set.indicator_of_mem (hbad.mpr hg), hscore]

/-- The unrestricted squared four-coordinate pilot score has a finite moment
under its one-cell product Poisson law. With [the specified inputs and conditions](hyp:n,d,P,j,hn,hd), [the stated relationship holds](goal). -/
-- @node: pilotCell_score_sq_integrable
lemma pilotCell_score_sq_integrable {n d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    let m : ℝ := (n : ℝ) / 8
    let mNN : ℝ≥0 := Real.toNNReal m
    let q : Fin 4 → ℝ≥0 := fun i =>
      Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
    let μ := poissonTableLaw (fun i => mNN * q i)
    Integrable (fun p : Fin 4 → ℕ =>
      (∑ z : Cell,
        (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)) ^ 2) μ := by
  classical
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let mNN : ℝ≥0 := Real.toNNReal m
  let q : Fin 4 → ℝ≥0 := fun i =>
    Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
  let μ := poissonTableLaw (fun i => mNN * q i)
  let W : Fin 4 → (Fin 4 → ℕ) → ℕ := fun i p => p i
  have hm : 0 < m := by dsimp [m]; positivity
  have hmNN : 0 < mNN := Real.toNNReal_pos.mpr hm
  have hmcoe : (mNN : ℝ) = m := Real.coe_toNNReal m hm.le
  have hq (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hqcoe (i : Fin 4) : (q i : ℝ) =
      cellVector P j (CellFourEquiv.symm i) := by
    dsimp [q]
    exact max_eq_left (hq _)
  letI : IsProbabilityMeasure μ := by dsimp [μ, poissonTableLaw]; infer_instance
  have hbase := independent_poisson_empiricalAggregateScore_sq_integrable_four
    μ W q mNN hmNN (fun _ => measurable_pi_apply _)
    (fun i => by
      simpa [W, μ] using poissonTable_eval_coordinate_law
        (fun i => mNN * q i) i)
    pilotRadiusConstant (logAlphabet d)
    (by unfold pilotRadiusConstant universalH; norm_num)
    (by
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp]
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith [Real.log_nonneg hdR])
  apply hbase.congr
  filter_upwards [] with p
  congr 1
  unfold empiricalAggregateScore
  calc
    _ = ∑ i : Fin 4,
        (|pilotCenter m (fun z => p (CellFourEquiv z))
            (CellFourEquiv.symm i) - cellVector P j (CellFourEquiv.symm i)| +
          pilotHalfWidth m d (fun z => p (CellFourEquiv z))
            (CellFourEquiv.symm i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pilotHalfWidth_eq_empiricalRadius hm d
        (fun z => p (CellFourEquiv z)) (CellFourEquiv.symm i)]
      simp only [W, normalizedDeviation, hmcoe, hqcoe, mNN,
        Equiv.apply_symm_apply, pilotCenter]
    _ = _ := Equiv.sum_comp CellFourEquiv.symm (fun z : Cell =>
      |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
        pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
