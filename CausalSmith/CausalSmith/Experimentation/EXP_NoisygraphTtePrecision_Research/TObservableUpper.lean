module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierRates
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.RawScoreMoments
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TObservableUpper

/-!
# Observable finite-risk and honest-interval upper bounds

The interval length, positive envelope, and risk-to-coverage calibration are proved.
The squared-risk assembly uses unbiasedness, clipping, and the exact variance helper;
the latter retains its visible proof obligation.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- [Clipping both endpoints bounds interval length by the ambient width and twice its radius.](goal) -/
-- @node: upperInterval_length_le
lemma upperInterval_length_le (n d : ℕ) (q r : ℝ) (o : Record V) :
    (upperInterval n d q r o).2 - (upperInterval n d q r o).1 ≤
      min 2 (2 * Real.sqrt (10 * boundedEnvelope n d q r)) := by
  have horder := upperInterval_order n d q r o
  apply le_min
  · linarith [horder.1, horder.2.2.2]
  · change min 1 _ - max (-1) _ ≤ _
    have hu := min_le_right (1 : ℝ)
      (upperRule n d q r o + Real.sqrt (10 * boundedEnvelope n d q r))
    have hl := le_max_right (-1 : ℝ)
      (upperRule n d q r o - Real.sqrt (10 * boundedEnvelope n d q r))
    linarith

/-- Given [the stated assumptions](hyp:hqr,hq), [At zero acquisition probability, channel admissibility forces the envelope to be one.](goal) -/
-- @node: boundedEnvelope_zero_channel
lemma boundedEnvelope_zero_channel (n d : ℕ) (q r : ℝ)
    (hqr : ChannelDomain q r) (hq : q = 0) : boundedEnvelope n d q r = 1 := by
  have hr : r = 0 := le_antisymm (hq ▸ hqr.2.1) hqr.1
  simp [boundedEnvelope, upperEnvelope, hq, hr]

/-- Given [the stated assumptions](hyp:hn,hqr), [The public risk envelope is strictly positive on admissible finite populations.](goal) -/
-- @node: boundedEnvelope_pos
lemma boundedEnvelope_pos (n d : ℕ) (hn : 4 ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) : 0 < boundedEnvelope n d q r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr0 : 0 ≤ r := hqr.1
  have hq0 : 0 ≤ q := hqr.1.trans hqr.2.1
  have hr1 : r ≤ 1 := hqr.2.1.trans hqr.2.2
  have hq1 : 0 ≤ 1-q := sub_nonneg.mpr hqr.2.2
  have hr1' : 0 ≤ 1-r := sub_nonneg.mpr hr1
  unfold boundedEnvelope upperEnvelope
  split_ifs with hrq
  · apply ENNReal.toReal_pos
    · apply ne_of_gt
      apply lt_min (by norm_num)
      apply ENNReal.ofReal_pos.mpr
      have hp : 0 < 5 * ((d : ℝ) + 1)^2 / n := by positivity
      have hnon : 0 ≤ 4 * (d*q*(1-q) + ((n : ℝ)-1)*r*(1-r)) /
          (n*(q-r)^2) := by positivity
      linarith
    · exact ne_of_lt ((min_le_left _ _).trans_lt (by simp))
  · norm_num

/-- Given [the stated assumptions](hyp:hθ,hv,hD,hrisk), [The squared-risk bound calibrates the clipped interval by Markov's inequality.](goal) -/
-- @node: upperInterval_coverage_of_sqLoss
lemma upperInterval_coverage_of_sqLoss (n d : ℕ) (q r : ℝ)
    (D : Design V) (η : Schedule V) (hD : IsProbabilityMeasure (D η))
    (hθ : |CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η| ≤ 1)
    (hv : 0 < boundedEnvelope n d q r)
    (hrisk : sqLoss D η (upperEstimator n d q r) ≤
      ENNReal.ofReal (boundedEnvelope n d q r)) :
    ENNReal.ofReal (9/10) ≤ recordLaw D η
      {x | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η ∈
        Set.Icc (upperInterval n d q r x.1).1 (upperInterval n d q r x.1).2} := by
  let μ := recordLaw D η
  let θ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η
  let v := boundedEnvelope n d q r
  let f := fun x : Record V × ℝ => ENNReal.ofReal ((upperRule n d q r x.1 - θ)^2)
  let B := {x : Record V × ℝ | ENNReal.ofReal (10*v) ≤ f x}
  haveI : IsProbabilityMeasure μ := recordLaw_probability D η hD
  have hv' : 0 < v := hv
  have hf : Measurable f := by fun_prop
  have hB : MeasurableSet B := measurableSet_le measurable_const hf
  have hmark : μ B ≤ ENNReal.ofReal (1/10) := by
    calc
      μ B ≤ (∫⁻ x, f x ∂μ) / ENNReal.ofReal (10*v) :=
        meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal v / ENNReal.ofReal (10*v) :=
        ENNReal.div_le_div_right hrisk _
      _ = ENNReal.ofReal (1/10) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 10*v)]
        congr 1
        field_simp [ne_of_gt hv']
  have hgood : Bᶜ ⊆ {x | θ ∈ Set.Icc (upperInterval n d q r x.1).1
      (upperInterval n d q r x.1).2} := by
    intro x hx
    have hsq : (upperRule n d q r x.1 - θ)^2 < 10*v := by
      have : f x < ENNReal.ofReal (10*v) := lt_of_not_ge hx
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp this
    have habs : |upperRule n d q r x.1 - θ| ≤ Real.sqrt (10*v) := by
      have hs := Real.sq_sqrt (show 0 ≤ 10*v by positivity)
      nlinarith [sq_abs (upperRule n d q r x.1 - θ),
        Real.sqrt_nonneg (10*v)]
    have he := abs_le.mp habs
    have ht := abs_le.mp hθ
    change max (-1) _ ≤ θ ∧ θ ≤ min 1 _
    exact ⟨max_le ht.1 (by dsimp [v] at *; linarith),
      le_min ht.2 (by dsimp [v] at *; linarith)⟩
  calc
    ENNReal.ofReal (9/10) = 1 - ENNReal.ofReal (1/10) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1/10)]
      congr 1
      norm_num
    _ ≤ 1 - μ B := tsub_le_tsub_left hmark _
    _ = μ Bᶜ := by rw [measure_compl hB (measure_ne_top _ _)]; simp
    _ ≤ μ {x | θ ∈ Set.Icc (upperInterval n d q r x.1).1
        (upperInterval n d q r x.1).2} := measure_mono hgood

/-- [Ignoring the seed reduces the explicit estimator loss to its finite design integral.](goal) -/
-- @node: upperEstimator_sqLoss_seedless
lemma upperEstimator_sqLoss_seedless (n d : ℕ) (q r : ℝ)
    (D : Design V) (η : Schedule V) :
    sqLoss D η (upperEstimator n d q r) =
      ∫⁻ ω, ENNReal.ofReal ((upperRule n d q r (recordOf η ω) - tte η)^2) ∂D η := by
  letI : IsProbabilityMeasure seedLaw := ⟨by
    simp [seedLaw, ThinnedgraphAdditiveRiskFrontier.seedLaw, Real.volume_Icc]⟩
  have hm : Measurable (fun ω : (Assign V × Acq V) × ℝ =>
      (recordOf η ω.1, ω.2)) := by fun_prop
  unfold sqLoss recordLaw
  dsimp only [upperEstimator]
  rw [lintegral_map (by fun_prop) hm, lintegral_prod _ (by fun_prop)]
  simp

/-- Given [the stated assumptions](hyp:hn,hd,hη,hqr,hrq,ha,hH,hi), [Unbiasedness and the exact variance identity bound the raw score's squared loss.](goal) -/
-- @node: rawScore_squared_error_le_envelope
lemma rawScore_squared_error_le_envelope (η : Schedule V) (d : ℕ) (q r : ℝ)
    (hn : 4 ≤ Fintype.card V) (hd : 1 ≤ d) (hη : ScheduleClass η d)
    (hqr : ChannelDomain q r) (hrq : r < q)
    (D : Design V) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) :
    (∫ ω, (rawScore q r (recordOf η ω) - tte η)^2 ∂D η) ≤
      5 * ((d : ℝ)+1)^2 / Fintype.card V +
      4 * (d*q*(1-q) + ((Fintype.card V : ℝ)-1)*r*(1-r)) /
        (Fintype.card V*(q-r)^2) := by
  letI := ThinnedgraphAdditiveRiskFrontier.halfBernoulli_probability (V := V)
  have hmean := integral_rawScore_eq_tte η q r hqr hrq D ha hH hi
  change (∫ ω, rawScore q r (recordOf η ω) ∂D η) = tte η at hmean
  have hm : Measurable (fun ω => rawScore q r (recordOf η ω)) := by fun_prop
  rw [← hmean, ← ProbabilityTheory.variance_eq_integral hm.aemeasurable,
    rawScore_variance η q r hqr hrq D ha hH hi]
  have horacle := ThinnedgraphAdditiveRiskFrontier.oracle_variance_le
    η d hn hd ((scheduleClass_iff_thin η d).mp hη)
  have hnpos : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hn1 : (0 : ℝ) ≤ (Fintype.card V : ℝ)-1 := by
    have : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hr0 : 0 ≤ r := hqr.1
  have hq0 : 0 ≤ q := hqr.1.trans hqr.2.1
  have hq1 : 0 ≤ 1-q := sub_nonneg.mpr hqr.2.2
  have hr1 : 0 ≤ 1-r := sub_nonneg.mpr (hqr.2.1.trans hqr.2.2)
  have hy (i : V) : (∫ z, potentialOutcome η i z ^ 2
      ∂ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) ≤ 1 := by
    calc
      _ ≤ ∫ _z, (1 : ℝ) ∂ThinnedgraphAdditiveRiskFrontier.halfBernoulli V := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro z
        exact (sq_le_one_iff_abs_le_one _).mpr (abs_potentialOutcome_le_one hη i z)
      _ = 1 := by simp
  have hcost (i : V) :
      0 ≤ (incomingDegree η i : ℝ)*q*(1-q) +
        ((Fintype.card V : ℝ)-1-incomingDegree η i)*r*(1-r) := by
    have he : (incomingDegree η i : ℝ) ≤ (Fintype.card V : ℝ)-1 := by
      have he := incomingDegree_le η i
      have hnNat : 1 ≤ Fintype.card V := by omega
      exact_mod_cast (show incomingDegree η i ≤ Fintype.card V - 1 from he)
    have hsub : 0 ≤ (Fintype.card V : ℝ)-1-incomingDegree η i := sub_nonneg.mpr he
    positivity
  have hsum : (∑ i, (∫ z, potentialOutcome η i z ^ 2
      ∂ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) *
        ((incomingDegree η i : ℝ)*q*(1-q) +
          ((Fintype.card V : ℝ)-1-incomingDegree η i)*r*(1-r))) ≤
      Fintype.card V * (d*q*(1-q) + ((Fintype.card V : ℝ)-1)*r*(1-r)) := by
    calc
      _ ≤ ∑ _i : V, (d*q*(1-q) + ((Fintype.card V : ℝ)-1)*r*(1-r)) := by
        apply Finset.sum_le_sum
        intro i _
        have he : (incomingDegree η i : ℝ) ≤ d := by exact_mod_cast hη.inDegree i
        have he0 : (0 : ℝ) ≤ incomingDegree η i := Nat.cast_nonneg _
        calc
          _ ≤ 1 * ((incomingDegree η i : ℝ)*q*(1-q) +
              ((Fintype.card V : ℝ)-1-incomingDegree η i)*r*(1-r)) :=
            mul_le_mul_of_nonneg_right (hy i) (hcost i)
          _ ≤ _ := by
            nlinarith [mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hq0 hq1),
              mul_nonneg he0 (mul_nonneg hqr.1 hr1)]
      _ = _ := by simp; ring
  have hc : 0 ≤ 4 / ((Fintype.card V : ℝ)^2 * (q-r)^2) := by positivity
  calc
    _ ≤ 5 * ((d : ℝ)+1)^2 / Fintype.card V +
        4 / ((Fintype.card V : ℝ)^2 * (q-r)^2) *
          (Fintype.card V * (d*q*(1-q) + ((Fintype.card V : ℝ)-1)*r*(1-r))) :=
      add_le_add horacle (mul_le_mul_of_nonneg_left hsum hc)
    _ = _ := by field_simp <;> ring

/-- Given [the stated assumptions](hyp:hn,hd,hη,hqr,ha,hH,hi), [Clipping on the small-envelope branch and using zero elsewhere attains the bounded envelope.](goal) -/
-- @node: upperEstimator_sqLoss_le_envelope
lemma upperEstimator_sqLoss_le_envelope (η : Schedule V) (d : ℕ) (q r : ℝ)
    (hn : 4 ≤ Fintype.card V) (hd : 1 ≤ d) (hη : ScheduleClass η d)
    (hqr : ChannelDomain q r) (D : Design V) (ha : AssignmentLaw D)
    (hH : AcquisitionLaw D q r) (hi : DesignIndependent D) :
    sqLoss D η (upperEstimator (Fintype.card V) d q r) ≤
      ENNReal.ofReal (boundedEnvelope (Fintype.card V) d q r) := by
  letI : IsProbabilityMeasure (D η) := by
    rw [design_eq_noisyDesign D q r ha hH hi]
    exact noisyDesign_probability q r hqr η
  rw [upperEstimator_sqLoss_seedless]
  rw [boundedEnvelope, ENNReal.ofReal_toReal (ne_of_lt
    ((min_le_left _ _).trans_lt (by simp : (1 : ℝ≥0∞) < ⊤)))]
  by_cases hbranch : r < q ∧ upperEnvelope (Fintype.card V) d q r < 1
  · rw [min_eq_right hbranch.2.le, upperEnvelope, if_pos hbranch.1]
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((rawScore q r (recordOf η ω) - tte η)^2) ∂D η := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        simpa only [upperRule, if_pos hbranch] using
          ThinnedgraphAdditiveRiskFrontier.clipped_sq_error_le
            (rawScore q r (recordOf η ω)) (tte η) (abs_tte_le_one hη)
      _ = ENNReal.ofReal (∫ ω, (rawScore q r (recordOf η ω) - tte η)^2 ∂D η) :=
        (ofReal_integral_eq_lintegral_ofReal (by first | fun_prop | exact Integrable.of_finite)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (rawScore_squared_error_le_envelope η d q r hn hd hη hqr hbranch.1 D ha hH hi)
  · have henv : 1 ≤ upperEnvelope (Fintype.card V) d q r := by
      by_cases hrq : r < q
      · exact le_of_not_gt (fun h => hbranch ⟨hrq, h⟩)
      · simp [upperEnvelope, hrq]
    rw [min_eq_left henv]
    calc
      _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂D η := by
        apply lintegral_mono
        intro ω
        have ht := (sq_le_one_iff_abs_le_one (tte η)).mpr (abs_tte_le_one hη)
        simpa [upperRule, hbranch] using ENNReal.ofReal_le_ofReal ht
      _ = 1 := by simp

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,ha,hH,hi,hη), [The complete original-record rules are measurable, calibrated, unbiased before clipping,
and satisfy the exact channel variance identity and the public rate comparison.](goal) -/
-- @node: thm:observable-upper
theorem observable_upper (d : ℕ) (q r : ℝ) (hn : 4 ≤ Fintype.card V)
    (hd : 1 ≤ d) (hdu : d ≤ Fintype.card V - 1) (hqr : ChannelDomain q r)
    (D : Design V) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) (η : Schedule V) (hη : ScheduleClass η d) :
    let n := Fintype.card V
    let v := boundedEnvelope n d q r
    Measurable (upperRule (V := V) n d q r) ∧
    Measurable (upperInterval (V := V) n d q r) ∧
    sqLoss D η (upperEstimator n d q r) ≤ ENNReal.ofReal v ∧
    ENNReal.ofReal (9/10) ≤ recordLaw D η
      {x | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η ∈ Set.Icc (upperInterval n d q r x.1).1 (upperInterval n d q r x.1).2} ∧
    (∀ o : Record V, (upperInterval n d q r o).2 - (upperInterval n d q r o).1 ≤
      min 2 (2 * Real.sqrt (10*v))) ∧
    (r < q →
      (∫ ω, rawScore q r (recordOf η ω) ∂D η) = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η ∧
      ProbabilityTheory.variance (fun ω => rawScore q r (recordOf η ω)) (D η) =
        ProbabilityTheory.variance (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracleScore η) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) +
        4 / ((n : ℝ)^2 * (q-r)^2) * ∑ i,
          (∫ z, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z ^ 2 ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) *
          (((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card : ℝ)*q*(1-q) +
            ((n : ℝ)-1-(CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card)*r*(1-r)) ∧
      ProbabilityTheory.variance (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracleScore η) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) ≤
        5 * ((d : ℝ)+1)^2/n) ∧
    (0 < q → v ≤ 20 * min 1 ((d : ℝ)^2/n + d/(n*q) + r/q^2)) ∧
    (q = 0 → v = 1) := by
  dsimp only
  have hrisk : sqLoss D η (upperEstimator (Fintype.card V) d q r) ≤
      ENNReal.ofReal (boundedEnvelope (Fintype.card V) d q r) := by
    exact upperEstimator_sqLoss_le_envelope η d q r hn hd hη hqr D ha hH hi
  have hD : IsProbabilityMeasure (D η) := by
    rw [design_eq_noisyDesign D q r ha hH hi]
    exact noisyDesign_probability q r hqr η
  refine ⟨upperRule_measurable _ _ _ _, upperInterval_measurable _ _ _ _,
    hrisk, ?_, upperInterval_length_le _ _ _ _, ?_, ?_, ?_⟩
  · exact upperInterval_coverage_of_sqLoss _ _ _ _ D η hD (abs_tte_le_one hη)
      (boundedEnvelope_pos _ _ hn q r hqr) hrisk
  · intro hrq
    refine ⟨integral_rawScore_eq_tte η q r hqr hrq D ha hH hi,
      rawScore_variance η q r hqr hrq D ha hH hi, ?_⟩
    exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracle_variance_le
      η d hn hd ((scheduleClass_iff_thin η d).mp hη)
  · intro hq
    simpa only [rho, if_pos hq] using
      envelope_rate_le (Fintype.card V) d hn hd hdu q r hqr
  · exact boundedEnvelope_zero_channel _ _ _ _ hqr

end CausalSmith.Experimentation.NoisygraphTtePrecision
