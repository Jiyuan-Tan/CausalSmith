module
public import Causalean.Stat.Concentration.Chebyshev
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.UpperGeometry
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LowerLength

/-! # Probabilistic steps of the honest upper bound

Markov's inequality supplies the two calibrated error tails and the bad-slope
probability in the roadmap. These interfaces keep square integrability explicit;
they do not add assumptions to the paper theorem. The expected-length assembly
uses the exact interval's good-slope bound and its deterministic length cap.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Exact cancellation of the calibrated radius and the mean-square rate.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,n,hα,hC), [the stated conclusion holds](goal). -/
-- @node: scoreRadius_sq
lemma scoreRadius_sq (α c_f C_f L : ℝ) (n : ℕ)
    (hα : 0 < α) (hC : 0 ≤ mseEnvelope c_f C_f L) :
    scoreRadius α c_f C_f L n ^ 2 =
      (2 * mseEnvelope c_f C_f L / α) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  unfold scoreRadius
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 2
  ring

/-- Each reduced-form estimator has noncoverage at most `α/2`.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,P,n,hα,hf,hF,hL,hn,hP,A,hi), [the stated conclusion holds](goal). -/
-- @node: cubicEstimator_error_tail_le
lemma cubicEstimator_error_tail_le (α c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hα : 0 < α) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool)
    (hi : Integrable (fun ω : TwoSample n n =>
      (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2) (dataLaw P n n)) :
    (dataLaw P n n {ω | scoreRadius α c_f C_f L n <
      |cubicEstimator c_f C_f ω A - transportedForm P A|}).toReal ≤ α / 2 := by
  let := dataLaw_isProbabilityMeasure_of_model c_f C_f L P n hP
  have hC := mseEnvelope_positive c_f C_f L hf.1 hF hL
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (by norm_num [threshold] : 0 < threshold) hn
    exact_mod_cast this
  have hr : 0 < scoreRadius α c_f C_f L n := by
    unfold scoreRadius
    exact mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.rpow_pos_of_pos hnpos _)
  have htail := Causalean.Stat.Concentration.absolute_error_tail_le_second_moment
    (dataLaw P n n)
    (fun ω => cubicEstimator c_f C_f ω A - transportedForm P A)
    (scoreRadius α c_f C_f L n) hr hi
  have hmse := marked_cubic_mse c_f C_f L P n hf hF hL hn hP A
  apply htail.trans
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  rw [scoreRadius_sq α c_f C_f L n hα hC.le]
  calc
    _ ≤ mseEnvelope c_f C_f L * (n : ℝ) ^ (-(2 / 3 : ℝ)) := hmse
    _ = _ := by field_simp

/-- Roadmap equation (2), for the exact estimated first stage.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hf,hF,hL,hn,hP,hi), [the stated conclusion holds](goal). -/
-- @node: cubicEstimator_bad_slope_probability_le
lemma cubicEstimator_bad_slope_probability_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n)
    (hi : Integrable (fun ω : TwoSample n n =>
      (cubicEstimator c_f C_f ω false - firstStage P) ^ 2) (dataLaw P n n)) :
    (dataLaw P n n {ω | firstStage P / 2 <
      |cubicEstimator c_f C_f ω false - firstStage P|}).toReal ≤
      4 * mseEnvelope c_f C_f L * (n : ℝ) ^ (-(2 / 3 : ℝ)) / firstStage P ^ 2 := by
  let := dataLaw_isProbabilityMeasure_of_model c_f C_f L P n hP
  have hμ : 0 < firstStage P := hP.strength
  have ht := Causalean.Stat.Concentration.absolute_error_tail_le_second_moment
    (dataLaw P n n)
    (fun ω => cubicEstimator c_f C_f ω false - firstStage P)
    (firstStage P / 2) (half_pos hμ) hi
  apply ht.trans
  calc
    _ ≤ (mseEnvelope c_f C_f L * (n : ℝ) ^ (-(2 / 3 : ℝ))) /
        (firstStage P / 2) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact marked_cubic_mse c_f C_f L P n hf hF hL hn hP false
    _ = _ := by field_simp; ring

/-- Square integrability suffices for null measurability of the error tail.  Under [the displayed assumptions and inputs](hyp:Ω,Q,e,r,hr,hi), [the stated conclusion holds](goal). -/
-- @node: absolute_error_tail_nullMeasurable
lemma absolute_error_tail_nullMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (e : Ω → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hi : Integrable (fun ω => e ω ^ 2) Q) :
    NullMeasurableSet {ω | r < |e ω|} Q := by
  have heq : {ω | r < |e ω|} = {ω | r ^ 2 < e ω ^ 2} := by
    ext ω
    change (r < |e ω|) ↔ (r ^ 2 < e ω ^ 2)
    have hs := sq_abs (e ω)
    have ha := abs_nonneg (e ω)
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact hi.aemeasurable.nullMeasurable measurableSet_Ioi

/-- The union bound and identification give honest coverage for the exact
interval. Square integrability is an explicit interface obligation.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,P,n,hα,hf,hF,hL,hP,hi), [the stated conclusion holds](goal). -/
-- @node: scoreInterval_coverage_of_square_integrable
lemma scoreInterval_coverage_of_square_integrable (α c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hα : 0 < α ∧ α < 1)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f) (hL : 1 < L)
    (hP : ModelClass c_f C_f L P n)
    (hi : ∀ A : Bool, Integrable (fun ω : TwoSample n n =>
      (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2) (dataLaw P n n)) :
    1 - α ≤ (dataLaw P n n {ω | targetCACE P ∈
      scoreInterval α c_f C_f L ω}).toReal := by
  classical
  let := dataLaw_isProbabilityMeasure_of_model c_f C_f L P n hP
  by_cases hn : n < threshold
  · have hθ := (transported_cace_identification c_f C_f L P n hf hF hL hP).2.2.2.2.2.2
    have heq : {ω : TwoSample n n | targetCACE P ∈ scoreInterval α c_f C_f L ω} = univ := by
      ext ω
      simp [scoreInterval, hn, hθ]
    rw [heq]
    simp only [measure_univ, ENNReal.toReal_one]
    linarith [hα.1]
  · have hn' : threshold ≤ n := le_of_not_gt hn
    let B : Bool → Set (TwoSample n n) := fun A =>
      {ω | scoreRadius α c_f C_f L n <
        |cubicEstimator c_f C_f ω A - transportedForm P A|}
    have hB : ∀ A, NullMeasurableSet (B A) (dataLaw P n n) := fun A =>
      absolute_error_tail_nullMeasurable _ _ _
        (scoreRadius_nonneg α c_f C_f L n) (hi A)
    have htail : ∀ A, (dataLaw P n n (B A)).toReal ≤ α / 2 := fun A =>
      cubicEstimator_error_tail_le α c_f C_f L P n hα.1 hf hF hL hn' hP A (hi A)
    have hgood : (B true ∪ B false)ᶜ ⊆
        {ω | targetCACE P ∈ scoreInterval α c_f C_f L ω} := by
      intro ω hω
      have hY : |cubicEstimator c_f C_f ω true - transportedForm P true| ≤
          scoreRadius α c_f C_f L n := by
        exact le_of_not_gt (fun h => hω (Or.inl h))
      have hD : |cubicEstimator c_f C_f ω false - firstStage P| ≤
          scoreRadius α c_f C_f L n := by
        exact le_of_not_gt (fun h => hω (Or.inr h))
      exact targetCACE_mem_scoreInterval_of_errors α c_f C_f L P n hf hF hL hP ω hY hD
    have hu := measureReal_union_le (μ := dataLaw P n n) (B true) (B false)
    have hc := measureReal_compl₀ (μ := dataLaw P n n) ((hB true).union (hB false))
    have hg := measureReal_mono (μ := dataLaw P n n) hgood
    simp only [probReal_univ] at hc
    change 1 - α ≤ (dataLaw P n n).real _
    have htY : (dataLaw P n n).real (B true) ≤ α / 2 := htail true
    have htD : (dataLaw P n n).real (B false) ≤ α / 2 := htail false
    linarith

/-- Restricted length is bounded by the parameter-space length pointwise.  Under [the displayed assumptions and inputs](hyp:C), [the stated conclusion holds](goal). -/
-- @node: restrictedLength_le_two
lemma restrictedLength_le_two (C : Set ℝ) : restrictedLength C ≤ 2 := by
  unfold restrictedLength Causalean.Stat.restrictedSetVolume
  have h := ENNReal.toReal_mono (show volume parameterSpace ≠ ⊤ by
    simp [parameterSpace, Real.volume_Icc])
    (measure_mono (inter_subset_right : C ∩ parameterSpace ⊆ parameterSpace))
  norm_num [parameterSpace, Real.volume_Icc] at h ⊢
  exact h

/-- Integrating the exact good-slope bound and bounding the complement gives
roadmap equations (1)--(2) with the displayed constants eight.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,P,n,hf,hF,hL,hn,hP,hi), [the stated conclusion holds](goal). -/
-- @node: scoreInterval_expectedLength_le_of_square_integrable
lemma scoreInterval_expectedLength_le_of_square_integrable (α c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n)
    (hi : Integrable (fun ω : TwoSample n n =>
      (cubicEstimator c_f C_f ω false - firstStage P) ^ 2) (dataLaw P n n)) :
    expectedLength P n n (scoreInterval α c_f C_f L) ≤
      max 2 (8 * Real.sqrt (2 * mseEnvelope c_f C_f L / α) +
        8 * mseEnvelope c_f C_f L) *
      min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / firstStage P) := by
  classical
  let := dataLaw_isProbabilityMeasure_of_model c_f C_f L P n hP
  have hμ : 0 < firstStage P := hP.strength
  have hC := mseEnvelope_positive c_f C_f L hf.1 hF hL
  let B : Set (TwoSample n n) :=
    {ω | firstStage P / 2 < |cubicEstimator c_f C_f ω false - firstStage P|}
  have hB : NullMeasurableSet B (dataLaw P n n) :=
    absolute_error_tail_nullMeasurable _ _ _ (half_pos hμ).le hi
  have htail := cubicEstimator_bad_slope_probability_le c_f C_f L P n hf hF hL hn hP hi
  let b : ℝ := 8 * scoreRadius α c_f C_f L n / firstStage P
  have hb : 0 ≤ b := div_nonneg
    (mul_nonneg (by norm_num) (scoreRadius_nonneg α c_f C_f L n)) hμ.le
  have hmajorant : ∀ ω : TwoSample n n,
      restrictedLength (scoreInterval α c_f C_f L ω) ≤
        b + B.indicator (fun _ => (2 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      exact (restrictedLength_le_two _).trans (by linarith)
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hg : |cubicEstimator c_f C_f ω false - firstStage P| ≤ firstStage P / 2 :=
        le_of_not_gt hω
      exact (restrictedLength_scoreInterval_le_on_good_slope α c_f C_f L P n hn hμ ω hg).trans
        (min_le_right _ _)
  have hbi := (integrable_const (2 : ℝ) (μ := dataLaw P n n)).indicator₀ hB
  have hmean : expectedLength P n n (scoreInterval α c_f C_f L) ≤
      b + 2 * (dataLaw P n n B).toReal := by
    calc
      _ ≤ ∫ ω, b + B.indicator (fun _ => (2 : ℝ)) ω ∂dataLaw P n n :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
          ((integrable_const b).add hbi) (Filter.Eventually.of_forall hmajorant)
      _ = _ := by
        rw [integral_add (integrable_const b) hbi, integral_indicator₀ hB]
        simp [mul_comm, Measure.real]
  have hx : 0 ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) / firstStage P := by positivity
  have hsq : ((n : ℝ) ^ (-(1 / 3 : ℝ)) / firstStage P) ^ 2 =
      (n : ℝ) ^ (-(2 / 3 : ℝ)) / firstStage P ^ 2 := by
    rw [div_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 2
    ring
  apply upper_length_two_regime_bound _ _ _ _ hx hC.le
    (expectedLength_le_two P n _)
  calc
    _ ≤ b + 2 * (4 * mseEnvelope c_f C_f L *
        (n : ℝ) ^ (-(2 / 3 : ℝ)) / firstStage P ^ 2) := by
      exact hmean.trans (add_le_add (le_refl b)
        (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2)))
    _ = _ := by
      rw [hsq]
      dsimp [b, scoreRadius]
      ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
