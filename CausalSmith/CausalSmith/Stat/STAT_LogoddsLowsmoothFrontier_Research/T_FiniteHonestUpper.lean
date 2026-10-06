module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.TwoPointLength
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.LengthSensitivity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ObservableOdds
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CoordinateBias
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FixedBudgetRealization
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.RankRates

/-! # T FiniteHonestUpper

Confidence-rectangle inversion covers the observable causal effect. Finite second
moments and Chebyshev concentration give ninety-percent coverage once the
coordinate bias bounds are supplied. The literal single-record
branch is honest with unit length. Native-logit Hölder bounds and projection
approximation prove both coordinate biases. Unconditional rectangle sensitivity and
absolute numerator moments give a radius-sensitive expected-length inequality;
proved rank-budget estimates give an absolute uniform diagnostic rate bound.
Endpoint realization remains an imported open dependency. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Clipped logarithmic inversion preserves the ordering of its quotient argument.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: inversion_le_of_quotient_le
lemma inversion_le_of_quotient_le (c d c' d' : ℝ) (h : c / d ≤ c' / d') :
    inversion c d ≤ inversion c' d' := by
  apply Real.log_le_log
  · exact (Real.exp_pos (-1/2 : ℝ)).trans_le (le_max_left _ _)
  · exact max_le_max_left _ (min_le_min_left _ (by linarith : 1 + c / d ≤ 1 + c' / d'))

/-- [On a positive denominator interval the extrema occur at its two endpoints,
with the direction determined by the sign of the numerator. [the documented result](goal) Under [the stated assumptions](hyp:hm,hmd,hdp). -/
-- @node: inversion_denominator_corners
lemma inversion_denominator_corners (c dm d dp : ℝ)
    (hm : 0 < dm) (hmd : dm ≤ d) (hdp : d ≤ dp) :
    min (inversion c dm) (inversion c dp) ≤ inversion c d ∧
    inversion c d ≤ max (inversion c dm) (inversion c dp) := by
  have hd : 0 < d := hm.trans_le hmd
  have hp : 0 < dp := hd.trans_le hdp
  by_cases hc : 0 ≤ c
  · have hlow : inversion c dp ≤ inversion c d := by
      apply inversion_le_of_quotient_le
      apply (div_le_div_iff₀ hp hd).2
      exact mul_le_mul_of_nonneg_left hdp hc
    have hhigh : inversion c d ≤ inversion c dm := by
      apply inversion_le_of_quotient_le
      apply (div_le_div_iff₀ hd hm).2
      exact mul_le_mul_of_nonneg_left hmd hc
    exact ⟨(min_le_right _ _).trans hlow, hhigh.trans (le_max_left _ _)⟩
  · have hc' : c ≤ 0 := (lt_of_not_ge hc).le
    have hlow : inversion c dm ≤ inversion c d := by
      apply inversion_le_of_quotient_le
      apply (div_le_div_iff₀ hm hd).2
      exact mul_le_mul_of_nonpos_left hmd hc'
    have hhigh : inversion c d ≤ inversion c dp := by
      apply inversion_le_of_quotient_le
      apply (div_le_div_iff₀ hd hp).2
      exact mul_le_mul_of_nonpos_left hdp hc'
    exact ⟨(min_le_left _ _).trans hlow, hhigh.trans (le_max_right _ _)⟩

/-- [The two selected corners cover the inversion of every point of a positive
confidence rectangle. [the documented result](goal) Under [the stated assumptions](hyp:hcm,hcp,hm,hmd,hdp). -/
-- @node: inversion_rectangle_coverage
lemma inversion_rectangle_coverage (cm c cp dm d dp : ℝ)
    (hcm : cm ≤ c) (hcp : c ≤ cp) (hm : 0 < dm)
    (hmd : dm ≤ d) (hdp : d ≤ dp) :
    inversion c d ∈ Set.Icc
      (min (inversion cm dm) (inversion cm dp))
      (max (inversion cp dm) (inversion cp dp)) := by
  have hd : 0 < d := hm.trans_le hmd
  exact ⟨(inversion_denominator_corners cm dm d dp hm hmd hdp).1.trans
      (inversion_mono_numerator d hd hcm),
    (inversion_mono_numerator d hd hcp).trans
      (inversion_denominator_corners cp dm d dp hm hmd hdp).2⟩

/-- [The clipped inversion identifies the causal effect on the model, since the
observable odds already lie inside the public exponential effect envelope. [the documented result](goal) Under [the stated assumptions](hyp:hP). -/
-- @node: inversion_model_coordinates
lemma inversion_model_coordinates (α β : ℝ) (P : ObservedLaw)
    (hP : Model α β P) :
    inversion (covarianceCoordinate P) (denominatorCoordinate P) = effect P := by
  have hS := denominatorCoordinate_lower α β P hP
  have hpos : 0 < denominatorCoordinate P := by
    have : (0 : ℝ) < denominatorFloor := by norm_num [denominatorFloor]
    exact this.trans_le hS
  have hC := covarianceCoordinate_eq_odds P hP.uniform hP.homogeneous
  have hquot : 1 + covarianceCoordinate P/denominatorCoordinate P = Real.exp (effect P) := by
    rw [hC, mul_div_cancel_right₀ _ (ne_of_gt hpos)]
    ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp hP.effect_envelope
  rw [inversion, hquot, clip, min_eq_right (Real.exp_le_exp.mpr hhi),
    max_eq_right (Real.exp_le_exp.mpr (by linarith : -1/2 ≤ effect P)), Real.log_exp]

/-- [Denominator clipping retains any true coordinate in the public interval
that was contained in the original error interval. [the documented result](goal) Under [the stated assumptions](hyp:hs,herr). -/
-- @node: clip_error_interval_contains
lemma clip_error_interval_contains (l u shat s b : ℝ)
    (hs : s ∈ Set.Icc l u) (herr : |shat - s| ≤ b) :
    clip l u (shat - b) ≤ s ∧ s ≤ clip l u (shat + b) := by
  obtain ⟨hminus, hplus⟩ := abs_le.mp herr
  constructor
  · exact max_le hs.1 ((min_le_right _ _).trans (by linarith))
  · exact (le_min hs.2 (by linarith)).trans (le_max_right _ _)

/-- [A coordinate confidence event covers the inverted target at the exact
minimum and maximum corners used by the upper construction. [the documented result](goal) Under [the stated assumptions](hyp:hl,hs,hc,hserr). -/
-- @node: inversion_confidence_rectangle
lemma inversion_confidence_rectangle (chat shat c s bC bS l u : ℝ)
    (hl : 0 < l) (hs : s ∈ Set.Icc l u)
    (hc : |chat - c| ≤ bC) (hserr : |shat - s| ≤ bS) :
    inversion c s ∈ Set.Icc
      (min (inversion (chat - bC) (clip l u (shat - bS)))
        (inversion (chat - bC) (clip l u (shat + bS))))
      (max (inversion (chat + bC) (clip l u (shat - bS)))
        (inversion (chat + bC) (clip l u (shat + bS)))) := by
  obtain ⟨hcm, hcp⟩ := abs_le.mp hc
  obtain ⟨hsm, hsp⟩ := clip_error_interval_contains l u shat s bS hs hserr
  apply inversion_rectangle_coverage
  · linarith
  · linarith
  · exact hl.trans_le (le_max_left _ _)
  · exact hsm
  · exact hsp

/-- [The integrated off-diagonal product is at most one under the public design. [the stated conclusion](goal) holds. -/
-- @node: denominatorCoordinate_le_one
lemma denominatorCoordinate_le_one (P : ObservedLaw) : denominatorCoordinate P ≤ 1 := by
  have hprob : IsProbabilityMeasure uniformLaw := by
    constructor
    rw [uniformLaw, comap_subtype_coe_apply measurableSet_Icc]
    rw [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
    norm_num
  let :=  hprob
  have hi : Integrable (fun x => P.cells true false x * P.cells false true x) uniformLaw :=
    ((P.continuous_cells true false).mul (P.continuous_cells false true)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb (x : Covariate) : P.cells true false x * P.cells false true x ≤ 1 :=
    (mul_le_mul (P.interior_cells true false x).2.le
      (P.interior_cells false true x).2.le
      (P.interior_cells false true x).1.le (by norm_num)).trans (by norm_num)
  have h := integral_mono hi (integrable_const (1 : ℝ)) hb
  simpa only [denominatorCoordinate, cellProbability_eq_cells, integral_const,
    probReal_univ, one_smul] using h

/-- The paper's two coordinate error bounds imply coverage of the causal effect
by the exact ideal interval, prior to outward rational rounding. [the documented result](goal) Under [the stated assumptions](hyp:hP,hc,hs). -/
-- @node: idealEndpoints_cover_effect
lemma idealEndpoints_cover_effect (E : ArithmeticEngine) (N : NamingPolicy)
    (n : ℕ) (α β : ℝ) (o : Fin n → Record) (P : ObservedLaw)
    (hP : Model α β P)
    (hc : |cHat n (resolutions E N n α β).1 o - covarianceCoordinate P| ≤
      8 * ((resolutions E N n α β).1 : ℝ) ^ (-(α + β)) +
        Real.sqrt (20 * varianceRadius n (resolutions E N n α β).1))
    (hs : |sHat n (resolutions E N n α β).2 o - denominatorCoordinate P| ≤
      25 * ((resolutions E N n α β).2 : ℝ) ^ (-2 * β) +
        Real.sqrt (20 * varianceRadius n (resolutions E N n α β).2)) :
    effect P ∈ Set.Icc (idealEndpoints E N n α β o).1 (idealEndpoints E N n α β o).2 := by
  rw [← inversion_model_coordinates α β P hP]
  exact inversion_confidence_rectangle _ _ _ _ _ _ _ _
    (by norm_num [denominatorFloor])
    ⟨denominatorCoordinate_lower α β P hP, denominatorCoordinate_le_one P⟩ hc hs

/-- [The literal single-record output is the full public effect interval.](goal) Under [the stated assumptions](hyp:hN). -/
-- @node: upperInterval_one_set
lemma upperInterval_one_set (E : ArithmeticEngine) (N : NamingPolicy)
    (hN : N.Admissible) (α β : ℝ) (ω : Experiment 1) :
    intervalSet ((upperInterval E N hN 1 α β).output ω) =
      Set.Icc (-(1/2 : ℝ)) (1/2) := by
  ext t
  simp only [upperInterval, upperOutput, upperRawBox, show (1 : ℕ) < 2 by omega,
    ↓reduceIte, intervalSet, fullEffectBox, rationalBox, Set.mem_ofPred_eq, Set.mem_Icc]
  norm_num
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨le_of_lt_or_eq hlo, le_of_lt_or_eq hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨lt_or_eq_of_le hlo, lt_or_eq_of_le hhi⟩

/-- [The single-record procedure has coverage one because it returns the full
effect envelope on every input. [the documented result](goal) Under [the stated assumptions](hyp:hN). -/
-- @node: upperInterval_one_honest
lemma upperInterval_one_honest (E : ArithmeticEngine) (N : NamingPolicy)
    (hN : N.Admissible) (α β : ℝ) :
    HonestProcedure 1 α β (upperInterval E N hN 1 α β) := by
  constructor
  intro P hP
  let :=  experimentLaw_probability P 1
  have hAll : {ω : Experiment 1 | effect P ∈
      intervalSet ((upperInterval E N hN 1 α β).output ω)} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, upperInterval_one_set, Set.mem_Icc, Set.mem_univ, iff_true]
    exact abs_le.mp hP.effect_envelope
  rw [hAll, measure_univ]
  exact ENNReal.div_le_of_le_mul (by norm_num)

/-- [The literal single-record interval has length one.](goal) Under [the stated assumptions](hyp:hN). -/
-- @node: upperInterval_one_length
lemma upperInterval_one_length (E : ArithmeticEngine) (N : NamingPolicy)
    (hN : N.Admissible) (α β : ℝ) (ω : Experiment 1) :
    intervalLength ((upperInterval E N hN 1 α β).output ω) = 1 := by
  norm_num [upperInterval, intervalLength, upperOutput, upperRawBox, fullEffectBox, rationalBox]

/-- [At one record the expected length obeys the diagnostic bound for any
constant at least one and any nonnegative radius. [the documented result](goal) Under [the stated assumptions](hyp:hN,hr,hK). -/
-- @node: upperInterval_one_expectedLength_bound
lemma upperInterval_one_expectedLength_bound (E : ArithmeticEngine) (N : NamingPolicy)
    (hN : N.Admissible) (α β r K : ℝ) (hr : 0 ≤ r) (hK : 1 ≤ K) (P : ObservedLaw) :
    expectedLength P 1 (upperInterval E N hN 1 α β) ≤ K*diagnosticEnvelope 1 α β r := by
  let :=  experimentLaw_probability P 1
  have hLen : expectedLength P 1 (upperInterval E N hN 1 α β) = 1 := by
    simp [expectedLength, upperInterval_one_length]
  rw [hLen]
  norm_num [diagnosticEnvelope]
  nlinarith

/-- [A bias bound and the sharp variance radius give the one-twentieth coordinate
failure probability used in the paper's Chebyshev step. [the documented result](goal) Under [the stated assumptions](hyp:μ,hX,hV,hbias,hvar). -/
-- @node: coordinate_error_probability_le
lemma coordinate_error_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (c b V : ℝ) (hV : 0 < V)
    (hbias : |(∫ ω, X ω ∂μ) - c| ≤ b) (hvar : variance X μ ≤ V) :
    μ {ω | b + Real.sqrt (20*V) < |X ω - c|} ≤ (1/20 : ℝ≥0∞) := by
  have hsqrt : 0 < Real.sqrt (20*V) := Real.sqrt_pos.2 (by positivity)
  have hsquare : (Real.sqrt (20*V))^2 = 20*V := Real.sq_sqrt (by positivity)
  have hsub : {ω | b + Real.sqrt (20*V) < |X ω - c|} ⊆
      {ω | Real.sqrt (20*V) ≤ |X ω - ∫ x, X x ∂μ|} := by
    intro ω hω
    have htri : |X ω - c| ≤ |X ω - ∫ x, X x ∂μ| + |(∫ x, X x ∂μ) - c| := by
      exact abs_sub_le (X ω) (∫ x, X x ∂μ) c
    change b + Real.sqrt (20*V) < |X ω - c| at hω
    change Real.sqrt (20*V) ≤ |X ω - ∫ x, X x ∂μ|
    linarith
  calc
    μ {ω | b + Real.sqrt (20*V) < |X ω - c|} ≤
        μ {ω | Real.sqrt (20*V) ≤ |X ω - ∫ x, X x ∂μ|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance X μ / (Real.sqrt (20*V))^2) :=
      meas_ge_le_variance_div_sq hX hsqrt
    _ ≤ ENNReal.ofReal (1/20) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hsquare]
      apply (div_le_iff₀ (by positivity : 0 < 20*V)).2
      linarith
    _ = (1/20 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

/-- [The public variance radius is strictly positive for every multi-record sample.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: varianceRadius_pos
lemma varianceRadius_pos (n k : ℕ) (hn : 2 ≤ n) : 0 < varianceRadius n k := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  unfold varianceRadius
  positivity

/-- [The union of the two coordinate failure events has probability at most one
 tenth. Endpoint realization then transfers rectangle coverage to the literal output. [the documented result](goal) Under [the stated assumptions](hyp:hE,hN,hn,hab,hP,hcBias,hsBias,hcVar,hsVar). -/
-- @node: upperInterval_coverage_of_coordinate_moments
lemma upperInterval_coverage_of_coordinate_moments
    (E : ArithmeticEngine) (hE : E.Admissible) (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (hn : 2 ≤ n) (α β : ℝ) (hab : ExponentDomain α β)
    (P : ObservedLaw) (hP : Model α β P)
    (hcBias : |(∫ ω : Experiment n, cHat n (resolutions E N n α β).1 ω.1
      ∂experimentLaw P n) - covarianceCoordinate P| ≤
      8 * ((resolutions E N n α β).1 : ℝ) ^ (-(α + β)))
    (hsBias : |(∫ ω : Experiment n, sHat n (resolutions E N n α β).2 ω.1
      ∂experimentLaw P n) - denominatorCoordinate P| ≤
      25 * ((resolutions E N n α β).2 : ℝ) ^ (-2 * β))
    (hcVar : variance (fun ω : Experiment n => cHat n (resolutions E N n α β).1 ω.1)
      (experimentLaw P n) ≤ varianceRadius n (resolutions E N n α β).1)
    (hsVar : variance (fun ω : Experiment n => sHat n (resolutions E N n α β).2 ω.1)
      (experimentLaw P n) ≤ varianceRadius n (resolutions E N n α β).2) :
    (9/10 : ℝ≥0∞) ≤ experimentLaw P n {ω | effect P ∈
      intervalSet ((upperInterval E N hN n α β).output ω)} := by
  let := experimentLaw_probability P n
  let k := resolutions E N n α β
  let bC := 8*(k.1 : ℝ) ^ (-(α + β)) + Real.sqrt (20*varianceRadius n k.1)
  let bS := 25*(k.2 : ℝ) ^ (-2 * β) + Real.sqrt (20*varianceRadius n k.2)
  let badC : Set (Experiment n) := {ω | bC < |cHat n k.1 ω.1 - covarianceCoordinate P|}
  let badS : Set (Experiment n) := {ω | bS < |sHat n k.2 ω.1 - denominatorCoordinate P|}
  obtain ⟨hcLp, hsLp⟩ := coordinateEstimates_memLp P n k.1 k.2
  have hcProb : experimentLaw P n badC ≤ (1/20 : ℝ≥0∞) :=
    coordinate_error_probability_le _ _ hcLp _ _ _ (varianceRadius_pos n k.1 hn) hcBias hcVar
  have hsProb : experimentLaw P n badS ≤ (1/20 : ℝ≥0∞) :=
    coordinate_error_probability_le _ _ hsLp _ _ _ (varianceRadius_pos n k.2 hn) hsBias hsVar
  have hBad : experimentLaw P n (badC ∪ badS) ≤ (1/10 : ℝ≥0∞) := by
    calc
      _ ≤ experimentLaw P n badC + experimentLaw P n badS := measure_union_le _ _
      _ ≤ (1/20 : ℝ≥0∞) + 1/20 := add_le_add hcProb hsProb
      _ = _ := by
        simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (20 : NNReal) ≠ 0),
          ENNReal.coe_div (by norm_num : (10 : NNReal) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using
          congrArg (fun x : NNReal => (x : ℝ≥0∞))
            (by norm_num : (1/20 : NNReal) + 1/20 = 1/10)
  have hAll : Set.univ ⊆ {ω | effect P ∈
      intervalSet ((upperInterval E N hN n α β).output ω)} ∪ (badC ∪ badS) := by
    intro ω _
    by_cases hc : ω ∈ badC
    · exact Or.inr (Or.inl hc)
    by_cases hs : ω ∈ badS
    · exact Or.inr (Or.inr hs)
    apply Or.inl
    have hCover := idealEndpoints_cover_effect E N n α β ω.1 P hP
      (le_of_not_gt hc) (le_of_not_gt hs)
    obtain ⟨c, s, L, R, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hSubset, _⟩ :=
      fixed_budget_realization.2 E hE N hN n hn α β hab ω.1
    exact hSubset hCover
  have hTotal : (1 : ℝ≥0∞) ≤ experimentLaw P n {ω | effect P ∈
      intervalSet ((upperInterval E N hN n α β).output ω)} + 1/10 := by
    calc
      1 = experimentLaw P n Set.univ := (measure_univ).symm
      _ ≤ experimentLaw P n ({ω | effect P ∈
          intervalSet ((upperInterval E N hN n α β).output ω)} ∪ (badC ∪ badS)) := measure_mono hAll
      _ ≤ experimentLaw P n {ω | effect P ∈
          intervalSet ((upperInterval E N hN n α β).output ω)} +
          experimentLaw P n (badC ∪ badS) := measure_union_le _ _
      _ ≤ _ := add_le_add_right hBad _
  have hnum : (9/10 : ℝ≥0∞) = 1 - 1/10 := by
    simpa only [ENNReal.coe_sub, ENNReal.coe_div (by norm_num : (10 : NNReal) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat] using
      congrArg (fun x : NNReal => (x : ℝ≥0∞))
        (show (9/10 : NNReal) = 1 - 1/10 from by
          apply NNReal.coe_injective
          norm_num [NNReal.sub_def, Real.coe_toNNReal])
  rw [hnum]
  exact (tsub_le_iff_right).2 hTotal

/-- [The ranks selected before sampling are positive, using only the rank contract.](goal) Under [the stated assumptions](hyp:hE,hN,hn,hab). -/
-- @node: resolutions_one_le
lemma resolutions_one_le (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) :
    1 ≤ (resolutions E N n α β).1 ∧ 1 ≤ (resolutions E N n α β).2 := by
  obtain ⟨c, s, hRank, hcR, hsR, hcW, hsW⟩ :=
    rankBoxes_rank_budget_contract E hE N hN n (by omega) α β hab
  obtain ⟨hcOne, hsOne⟩ := rank_targets_one_le n hn α β hab
  have hc := hcOne.trans (enclosure_ceiling_rank_bounds c _ hcOne hcR hcW).1
  have hs := hsOne.trans (enclosure_ceiling_rank_bounds s _ hsOne hsR hsW).1
  have hc' : 1 ≤ (⌈c.hi⌉ : ℤ).toNat := by exact_mod_cast hc
  have hs' : 1 ≤ (⌈s.hi⌉ : ℤ).toNat := by exact_mod_cast hs
  simpa only [resolutions, hRank] using And.intro hc' hs'

/-- [The effect envelope controls the observable numerator linearly, with the roadmap's constant.](goal) Under [the stated assumptions](hyp:hP). -/
-- @node: covarianceCoordinate_abs_le_effect
lemma covarianceCoordinate_abs_le_effect (α β : ℝ) (P : ObservedLaw) (hP : Model α β P) :
    |covarianceCoordinate P| ≤ Real.exp (1/2) * |effect P| := by
  have he : |Real.exp (effect P) - 1| ≤ Real.exp (1/2) * |effect P| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := Real.exp) (s := Set.Icc (-(1/2 : ℝ)) (1/2))
      (fun x _ => Real.differentiableAt_exp)
      (fun x hx => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr hx.2)
      (convex_Icc _ _) (show (0 : ℝ) ∈ Set.Icc (-(1/2 : ℝ)) (1/2) by norm_num)
      (abs_le.mp hP.effect_envelope)
    simpa only [Real.exp_zero, Real.norm_eq_abs, sub_zero] using h
  have hs : 0 ≤ denominatorCoordinate P := by
    have := denominatorCoordinate_lower α β P hP
    have : 0 < denominatorFloor := by norm_num [denominatorFloor]
    linarith
  rw [covarianceCoordinate_eq_odds P hP.uniform hP.homogeneous, abs_mul, abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left (denominatorCoordinate_le_one P) (abs_nonneg _)).trans
    (by simpa using he)

/-- [Bias and sharp variance control the unconditional absolute numerator mean.](goal) Under [the stated assumptions](hyp:hE,hN,hn,hab,hP). -/
-- @node: cHat_integral_abs_le
lemma cHat_integral_abs_le (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) (P : ObservedLaw) (hP : Model α β P) :
    let k := resolutions E N n α β
    let bC := 8*(k.1 : ℝ)^(-(α+β)) + Real.sqrt (20*varianceRadius n k.1)
    (∫ ω : Experiment n, |cHat n k.1 ω.1| ∂experimentLaw P n) ≤ |covarianceCoordinate P|+bC := by
  letI := experimentLaw_probability P n
  obtain ⟨hcMem, _⟩ := coordinateEstimates_memLp P n
    (resolutions E N n α β).1 (resolutions E N n α β).2
  obtain ⟨hcVar, _⟩ := coordinateEstimates_variance_bounds P hP.uniform n
    (resolutions E N n α β).1 (resolutions E N n α β).2 hn
  obtain ⟨hcIdentity, _⟩ := coordinateEstimates_bias_identities P hP.uniform n
    (resolutions E N n α β).1 (resolutions E N n α β).2 hn
  obtain ⟨hk, _⟩ := resolutions_one_le E hE N hN n hn α β hab
  have hcBias : |(∫ ω : Experiment n, cHat n (resolutions E N n α β).1 ω.1
      ∂experimentLaw P n) - covarianceCoordinate P| ≤
      8*((resolutions E N n α β).1 : ℝ)^(-(α+β)) := by
    rw [hcIdentity]
    exact numerator_projection_bias_bound P α β hab hP _ hk
  have h := integral_abs_le_bias_sqrt_variance _ _ hcMem _ _ _ hcBias hcVar
  have hV := (varianceRadius_pos n (resolutions E N n α β).1 hn).le
  have hS : Real.sqrt (varianceRadius n (resolutions E N n α β).1) ≤
      Real.sqrt (20*varianceRadius n (resolutions E N n α β).1) :=
    Real.sqrt_le_sqrt (by linarith)
  dsimp only
  linarith

/-- [Integrating the samplewise rectangle bound gives the unconditional radius-sensitive length bound.](goal) Under [the stated assumptions](hyp:hE,hN,hn,hab,hP). -/
-- @node: upperInterval_expectedLength_le_radii
lemma upperInterval_expectedLength_le_radii (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) (r : ℝ) (P : ObservedLaw)
    (hP : RadiusModel α β r P) :
    let k := resolutions E N n α β
    let bC := 8*(k.1 : ℝ)^(-(α+β)) + Real.sqrt (20*varianceRadius n k.1)
    let bS := 25*(k.2 : ℝ)^(-2*β) + Real.sqrt (20*varianceRadius n k.2)
    expectedLength P n (upperInterval E N hN n α β) ≤
      2*Real.exp (1/2)/denominatorFloor*bC +
        2*Real.exp (1/2)/denominatorFloor^2*bS*(Real.exp (1/2)*r+2*bC) + 2/(n : ℝ) := by
  letI := experimentLaw_probability P n
  let k := resolutions E N n α β
  let bC := 8*(k.1 : ℝ)^(-(α+β)) + Real.sqrt (20*varianceRadius n k.1)
  let bS := 25*(k.2 : ℝ)^(-2*β) + Real.sqrt (20*varianceRadius n k.2)
  obtain ⟨hcMem, _⟩ := coordinateEstimates_memLp P n k.1 k.2
  have hi := (hcMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).abs
  have hm : (∫ ω : Experiment n, |cHat n k.1 ω.1| ∂experimentLaw P n) ≤
      Real.exp (1/2)*r+bC := by
    have hc := cHat_integral_abs_le E hE N hN n hn α β hab P hP.toModel
    have he := (covarianceCoordinate_abs_le_effect α β P hP.toModel).trans
      (mul_le_mul_of_nonneg_left hP.radius (Real.exp_pos _).le)
    dsimp only at hc
    change _ ≤ Real.exp (1/2)*r + bC
    linarith
  calc
    expectedLength P n (upperInterval E N hN n α β) ≤
        ∫ ω : Experiment n, (2*Real.exp (1/2)/denominatorFloor*bC +
          2*Real.exp (1/2)/denominatorFloor^2*bS*(|cHat n k.1 ω.1|+bC) + 2/(n : ℝ))
          ∂experimentLaw P n := by
      apply integral_mono (procedure_length_integrable P n (upperInterval E N hN n α β))
        (((integrable_const _).add ((hi.add (integrable_const bC)).const_mul _)).add
          (integrable_const _))
      intro ω
      exact upperOutput_length_le E hE N hN n hn α β hab ω.1
    _ = 2*Real.exp (1/2)/denominatorFloor*bC +
        2*Real.exp (1/2)/denominatorFloor^2*bS*
          ((∫ ω : Experiment n, |cHat n k.1 ω.1| ∂experimentLaw P n)+bC) + 2/(n : ℝ) := by
      integral_linearity
      simp
    _ ≤ _ := by
      have hm' : (∫ ω : Experiment n, |cHat n k.1 ω.1| ∂experimentLaw P n)+bC ≤
          Real.exp (1/2)*r+2*bC := by linarith
      have hc : 0 ≤ 2*Real.exp (1/2)/denominatorFloor^2*bS := by dsimp [bS]; positivity
      have ht := mul_le_mul_of_nonneg_left hm' hc
      change _ ≤ 2*Real.exp (1/2)/denominatorFloor*bC +
        2*Real.exp (1/2)/denominatorFloor^2*bS*(Real.exp (1/2)*r+2*bC) + 2/(n : ℝ)
      linarith

-- @node: thm:finite-honest-upper
/-- An absolute expected-length bound and global honesty for every supplied implementation. Under the stated assumptions. [The stated conclusion follows](goal). -/
theorem finite_honest_upper : ∃ K₀ : ℝ, 0 < K₀ ∧
  ∀ (E : ArithmeticEngine), E.Admissible →
  ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
  ∀ n : ℕ, 1 ≤ n →
    HonestProcedure n α β (upperInterval E N hN n α β) ∧
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
      ∀ P : ObservedLaw, RadiusModel α β r P →
        expectedLength P n (upperInterval E N hN n α β) ≤ K₀*diagnosticEnvelope n α β r) ∧
    (∀ ω, RationalOutputShape ((upperInterval E N hN n α β).output ω)) ∧
    (n = 1 → ∀ ω, intervalSet ((upperInterval E N hN n α β).output ω) = Set.Icc (-(1/2 : ℝ)) (1/2)) := by
  -- Assemble coordinate moments, coverage, unconditional sensitivity, and the
  -- deterministic uniform power estimates for the represented ranks.
  obtain ⟨K, hK, hMulti⟩ : ∃ K : ℝ, 1 ≤ K ∧
      ∀ (E : ArithmeticEngine), E.Admissible →
      ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
      ∀ n : ℕ, 2 ≤ n →
        HonestProcedure n α β (upperInterval E N hN n α β) ∧
        (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
          ∀ P : ObservedLaw, RadiusModel α β r P →
            expectedLength P n (upperInterval E N hN n α β) ≤
              K*diagnosticEnvelope n α β r) := by
    obtain ⟨K, hK, hLength⟩ : ∃ K : ℝ, 1 ≤ K ∧
        ∀ (E : ArithmeticEngine), E.Admissible →
        ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
        ∀ n : ℕ, 2 ≤ n →
        ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
        ∀ P : ObservedLaw, RadiusModel α β r P →
          expectedLength P n (upperInterval E N hN n α β) ≤
            K*diagnosticEnvelope n α β r := by
      obtain ⟨K, hK, hRates⟩ : ∃ K : ℝ, 1 ≤ K ∧
          ∀ (E : ArithmeticEngine), E.Admissible →
          ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
          ∀ n : ℕ, 2 ≤ n → ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
            let k := resolutions E N n α β
            let bC := 8*(k.1 : ℝ)^(-(α+β)) + Real.sqrt (20*varianceRadius n k.1)
            let bS := 25*(k.2 : ℝ)^(-2*β) + Real.sqrt (20*varianceRadius n k.2)
            2*Real.exp (1/2)/denominatorFloor*bC +
              2*Real.exp (1/2)/denominatorFloor^2*bS*(Real.exp (1/2)*r+2*bC) + 2/(n : ℝ) ≤
                K*diagnosticEnvelope n α β r := by
        exact upper_radii_uniform_rate
      refine ⟨K, hK, ?_⟩
      intro E hE N hN α β hab n hn r hr P hP
      exact (upperInterval_expectedLength_le_radii E hE N hN n hn α β hab r P hP).trans
        (hRates E hE N hN α β hab n hn r hr)
    refine ⟨K, hK, ?_⟩
    intro E hE N hN α β hab n hn
    refine ⟨⟨?_⟩, hLength E hE N hN α β hab n hn⟩
    intro P hP
    obtain ⟨hcBias, hsBias, hcVar, hsVar⟩ :
        |(∫ ω : Experiment n, cHat n (resolutions E N n α β).1 ω.1
          ∂experimentLaw P n) - covarianceCoordinate P| ≤
          8 * ((resolutions E N n α β).1 : ℝ) ^ (-(α + β)) ∧
        |(∫ ω : Experiment n, sHat n (resolutions E N n α β).2 ω.1
          ∂experimentLaw P n) - denominatorCoordinate P| ≤
          25 * ((resolutions E N n α β).2 : ℝ) ^ (-2 * β) ∧
        variance (fun ω : Experiment n => cHat n (resolutions E N n α β).1 ω.1)
          (experimentLaw P n) ≤ varianceRadius n (resolutions E N n α β).1 ∧
        variance (fun ω : Experiment n => sHat n (resolutions E N n α β).2 ω.1)
          (experimentLaw P n) ≤ varianceRadius n (resolutions E N n α β).2 := by
      obtain ⟨hcVar, hsVar⟩ := coordinateEstimates_variance_bounds P hP.uniform n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn
      obtain ⟨hcIdentity, hsIdentity⟩ := coordinateEstimates_bias_identities P hP.uniform n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn
      obtain ⟨hkC, hkS⟩ := resolutions_one_le E hE N hN n hn α β hab
      refine ⟨?_, ?_, hcVar, hsVar⟩
      · rw [hcIdentity]
        exact numerator_projection_bias_bound P α β hab hP _ hkC
      · rw [hsIdentity, abs_neg]
        exact denominator_projection_bias_bound P α β hab hP _ hkS
    exact upperInterval_coverage_of_coordinate_moments E hE N hN n hn α β hab P hP
      hcBias hsBias hcVar hsVar
  refine ⟨K, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hK, ?_⟩
  intro E hE N hN α β hab n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hOne : n = 1
    · subst n
      exact upperInterval_one_honest E N hN α β
    · exact (hMulti E hE N hN α β hab n (by omega)).1
  · intro r hr P hP
    by_cases hOne : n = 1
    · subst n
      exact upperInterval_one_expectedLength_bound E N hN α β r K hr.1 hK P
    · exact (hMulti E hE N hN α β hab n (by omega)).2 r hr P hP
  · intro ω
    exact upperOutput_rational_shape E N n α β ω.1
  · intro hOne
    subst n
    exact upperInterval_one_set E N hN α β
end CausalSmith.Stat.LogoddsLowsmoothFrontier
