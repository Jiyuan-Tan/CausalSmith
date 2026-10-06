module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ScoreAudit

/-!
# Observable total upper bound
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Ignoring the independent seed reduces squared loss to the original design integral.  [For the stated data and conditions](hyp:D,θ,f,hf), [the stated conclusion holds](goal). -/
-- @node: sqLoss_seedless
lemma sqLoss_seedless (D : Measure (Assign V × Audit V)) (θ : Schedule V)
    (f : Record V → ℝ) (hf : Measurable f) :
    sqLoss D θ ⟨fun x => f x.1, hf.comp measurable_fst⟩ =
      ∫⁻ ω, ENNReal.ofReal ((f (recordOf θ ω) - tte θ) ^ 2) ∂D := by
  let : IsProbabilityMeasure seedLaw := ⟨by simp [seedLaw, Real.volume_Icc]⟩
  have hr : Measurable (recordOf θ) := by
    fun_prop (disch := exact Measurable.of_discrete)
  have hm : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
      (recordOf θ ω.1, ω.2)) := (hr.comp measurable_fst).prodMk measurable_snd
  unfold sqLoss recordLaw
  dsimp only
  rw [lintegral_map (by fun_prop) hm,
    lintegral_prod _ (by fun_prop)]
  simp

/-- Projection onto the target interval cannot increase squared error.  [For the stated data and conditions](hyp:v,s,hs), [the stated conclusion holds](goal). -/
-- @node: clipped_sq_error_le
lemma clipped_sq_error_le (v s : ℝ) (hs : |s| ≤ 1) :
    (max (-1) (min 1 v) - s) ^ 2 ≤ (v - s) ^ 2 := by
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  by_cases hlo : v < -1
  · rw [min_eq_right (by linarith), max_eq_left hlo.le]
    nlinarith
  · by_cases hhi : 1 < v
    · rw [min_eq_left hhi.le, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      nlinarith
    · rw [min_eq_right (le_of_not_gt hhi), max_eq_right (le_of_not_gt hlo)]

/-- The audit-score moments and bounded outcomes give the unclipped squared-risk envelope.  [For the stated data and conditions](hyp:θ,d,q,hn,hd,hdu,hclass,hq,hqpos), [the stated conclusion holds](goal). -/
-- @node: auditScore_squared_error_le
lemma auditScore_squared_error_le (θ : Schedule V) (d : ℕ) (q : ℝ)
    (hn : 4 ≤ Fintype.card V) (hd : 1 ≤ d) (hdu : d ≤ Fintype.card V - 1)
    (hclass : ScheduleClass θ d) (hq : q ∈ Set.Icc 0 1) (hqpos : 0 < q) :
    (∫ ω, (auditScore q (recordOf θ ω) - tte θ) ^ 2 ∂thinnedDesign V q) ≤
      5 * ((d : ℝ) + 1) ^ 2 / Fintype.card V +
        4 * d * (1 - q) / (Fintype.card V * q) := by
  let : IsProbabilityMeasure (thinnedDesign V q) := thinnedDesign_probabilityDesign q hq
  let : IsProbabilityMeasure (halfBernoulli V) := by
    let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
      bernoulliLaw_probability _ (by constructor <;> norm_num)
    unfold halfBernoulli
    infer_instance
  obtain ⟨hunbiased, hvariance, horacle⟩ := score_audit (thinnedDesign V q) θ d q
    hn hd hdu hclass (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq) hqpos
  have hm : Measurable (fun ω => auditScore q (recordOf θ ω)) := by
    fun_prop (disch := exact Measurable.of_discrete)
  rw [← hunbiased, ← ProbabilityTheory.variance_eq_integral hm.aemeasurable, hvariance]
  have hy (i : V) : (∫ z, (potentialOutcome θ i z) ^ 2 ∂halfBernoulli V) ≤ 1 := by
    calc
      _ ≤ ∫ _z, (1 : ℝ) ∂halfBernoulli V := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro z
        exact (sq_le_one_iff_abs_le_one _).mpr (abs_potentialOutcome_le_one hclass i z)
      _ = 1 := by simp
  have hsum : (∑ i, (inNbhd θ i).card *
      ∫ z, (potentialOutcome θ i z) ^ 2 ∂halfBernoulli V) ≤ Fintype.card V * (d : ℝ) := by
    calc
      _ ≤ ∑ _i : V, (d : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ (inNbhd θ i).card * (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (hy i) (Nat.cast_nonneg _)
          _ ≤ d := by simpa using (show ((inNbhd θ i).card : ℝ) ≤ d by
            exact_mod_cast hclass.inDegree i)
      _ = _ := by simp
  have hc : 0 ≤ 4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq.2))
      (mul_nonneg (sq_nonneg _) hqpos.le)
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  calc
    _ ≤ 5 * ((d : ℝ) + 1) ^ 2 / Fintype.card V +
        4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) * (Fintype.card V * (d : ℝ)) :=
      add_le_add horacle (mul_le_mul_of_nonneg_left hsum hc)
    _ = _ := by field_simp

/-- The total observable upper rule attains the envelope, including zero retention.  [For the stated data and conditions](hyp:d,q,hn,hd,hdu,hq), [the stated conclusion holds](goal). -/
-- @node: thm:observable-upper
theorem observable_upper (d : ℕ) (q : ℝ) (hn : 4 ≤ Fintype.card V)
    (hd : 1 ≤ d) (hdu : d ≤ Fintype.card V - 1) (hq : q ∈ Set.Icc 0 1) :
    minimaxRisk (thinnedDesign V q) d ≤
      worstRisk (thinnedDesign V q) d (upperEstimator (Fintype.card V) d q) ∧
    worstRisk (thinnedDesign V q) d (upperEstimator (Fintype.card V) d q) ≤
      min 1 (upperEnvelope (Fintype.card V) d q) ∧
    Measurable (upperRule (V := V) (Fintype.card V) d q)  := by
  let : IsProbabilityMeasure (thinnedDesign V q) := thinnedDesign_probabilityDesign q hq
  refine ⟨Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk _, ?_,
    upperRule_measurable _ _ _⟩
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro θ
  rw [show upperEstimator (V := V) (Fintype.card V) d q =
    ⟨fun x => upperRule (Fintype.card V) d q x.1,
      (upperRule_measurable _ _ _).comp measurable_fst⟩ from rfl,
    sqLoss_seedless _ _ _ (upperRule_measurable _ _ _)]
  by_cases hbranch : 0 < q ∧ upperEnvelope (Fintype.card V) d q < 1
  · have hrisk := auditScore_squared_error_le θ.1 d q hn hd hdu θ.2 hq hbranch.1
    rw [min_eq_right hbranch.2.le, upperEnvelope, if_pos hbranch.1]
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((auditScore q (recordOf θ.1 ω) - tte θ.1) ^ 2)
          ∂thinnedDesign V q := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        simpa only [upperRule, if_pos hbranch] using
          clipped_sq_error_le (auditScore q (recordOf θ.1 ω)) (tte θ.1) (abs_tte_le_one θ.2)
      _ = ENNReal.ofReal (∫ ω, (auditScore q (recordOf θ.1 ω) - tte θ.1) ^ 2
          ∂thinnedDesign V q) :=
        (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hrisk
  · have henv : 1 ≤ upperEnvelope (Fintype.card V) d q := by
      by_cases hpos : 0 < q
      · exact le_of_not_gt (fun h => hbranch ⟨hpos, h⟩)
      · simp [upperEnvelope, hpos]
    rw [min_eq_left henv]
    calc
      _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂thinnedDesign V q := by
        apply lintegral_mono
        intro ω
        have ht := (sq_le_one_iff_abs_le_one (tte θ.1)).mpr (abs_tte_le_one θ.2)
        simpa [upperRule, hbranch] using ENNReal.ofReal_le_ofReal ht
      _ = 1 := by simp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
