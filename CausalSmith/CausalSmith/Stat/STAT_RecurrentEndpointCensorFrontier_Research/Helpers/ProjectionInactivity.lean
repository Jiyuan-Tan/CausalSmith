module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UpperRiskAssembly
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedFullIdentification

/-!
# Inactivity of the armwise projection near an interior target

Model-class arm means lie strictly inside the clipping interval.  Consequently,
the ordinary estimator's armwise projections are inactive whenever both raw
arm estimators are closer to their targets than the corresponding distance to
the boundary.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A model-class arm mean is strictly inside the projection interval. -/
lemma armMean_mem_projectionInterior (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) : armMean P a ∈ Ioo (0 : ℝ) c.lambdaMax := by
  let f : ℝ → ℝ := fun t => survival P a t * P.lam a t
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (modelClass_survival_continuousOn c P hP a).mul
      (hP.recurrenceHolder a).1.continuousOn
  have hlambdaMax : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  have hf_nonneg (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 ≤ f t := by
    have hl := hP.recurrenceBounds a t ⟨ht.1.le, ht.2⟩
    exact mul_nonneg (Real.exp_pos _).le (c.lambdaMin_pos.le.trans hl.1)
  have hf_le (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : f t ≤ c.lambdaMax := by
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht.1.le, ht.2⟩
    have hl := hP.recurrenceBounds a t ⟨ht.1.le, ht.2⟩
    calc
      f t ≤ 1 * P.lam a t :=
        mul_le_mul_of_nonneg_right hs.2 (c.lambdaMin_pos.le.trans hl.1)
      _ ≤ c.lambdaMax := by simpa using hl.2
  have hlower : 0 < ∫ t in (0 : ℝ)..1, f t := by
    have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => 0) (g := f) (by norm_num) continuousOn_const hf
      (fun t ht => hf_nonneg t ht) ?_
    · simpa [f] using hstrict
    · refine ⟨0, by norm_num, ?_⟩
      have hl := hP.recurrenceBounds a 0 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      have hlam : 0 < P.lam a 0 := c.lambdaMin_pos.trans_le hl.1
      simpa [f, survival] using hlam
  have hcum : 0 < ∫ t in (0 : ℝ)..1, P.hazard a t := by
    have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (by norm_num) (intervalIntegrable_const (c := c.dMin))
      (hP.deathHazard.1 a) (fun t ht => (hP.deathBounds a t ht).1)
    have : c.dMin ≤ ∫ t in (0 : ℝ)..1, P.hazard a t := by
      simpa using hmono
    exact c.dMin_pos.trans_le this
  have hsurvival_one : survival P a 1 < 1 := by
    unfold survival
    rw [Real.exp_lt_one_iff]
    linarith
  have hf_one : f 1 < c.lambdaMax := by
    have hl := hP.recurrenceBounds a 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    calc
      f 1 ≤ survival P a 1 * c.lambdaMax :=
        mul_le_mul_of_nonneg_left hl.2 (Real.exp_pos _).le
      _ < 1 * c.lambdaMax := mul_lt_mul_of_pos_right hsurvival_one hlambdaMax
      _ = c.lambdaMax := one_mul _
  have hupper : ∫ t in (0 : ℝ)..1, f t < c.lambdaMax := by
    have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := f) (g := fun _ : ℝ => c.lambdaMax) (by norm_num) hf continuousOn_const
      (fun t ht => hf_le t ht) ⟨1, by norm_num, hf_one⟩
    simpa [f] using hstrict
  simpa [armMean, f] using And.intro hlower hupper

/-- The causal contrast is strictly inside its symmetric clipping range. -/
lemma causalTarget_mem_projectionInterior (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) : causalTarget P ∈ Ioo (-c.lambdaMax) c.lambdaMax := by
  have htarget : causalTarget P = armMean P true - armMean P false := by
    rw [hP.causalTarget_eq_survival_intensity_contrast]
    rw [intervalIntegral.integral_sub
      (hP.armMean_integrand_intervalIntegrable true)
      (hP.armMean_integrand_intervalIntegrable false)]
    rfl
  rw [htarget]
  rcases armMean_mem_projectionInterior c P hP true with ⟨ht0, htM⟩
  rcases armMean_mem_projectionInterior c P hP false with ⟨hf0, hfM⟩
  constructor <;> linarith

/-- Clipping is the identity at every point in the projection interval. -/
lemma projectArm_eq_self (c : ClassConstants) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) c.lambdaMax) :
    projectArm c x = x := by
  simp [projectArm, min_eq_right hx.2, max_eq_right hx.1]

/-- A point closer to an interior target than either boundary is not clipped. -/
lemma projectArm_eq_self_of_abs_sub_lt_boundaryDistance (c : ClassConstants)
    {x m : ℝ} (hm : m ∈ Ioo (0 : ℝ) c.lambdaMax)
    (hx : |x - m| < min m (c.lambdaMax - m)) : projectArm c x = x := by
  apply projectArm_eq_self c
  have hmargin : 0 < min m (c.lambdaMax - m) := lt_min hm.1 (sub_pos.mpr hm.2)
  have hleft : |x - m| < m := hx.trans_le (min_le_left _ _)
  have hright : |x - m| < c.lambdaMax - m := hx.trans_le (min_le_right _ _)
  constructor <;> nlinarith [hmargin, le_abs_self (x - m), neg_le_abs (x - m)]

/-- On the joint interior-neighborhood event, the ordinary estimator equals its raw arm contrast. -/
lemma ordinaryEstimator_eq_rawContrast_of_close (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) {n : ℕ} (s : Fin n → ObsHistory)
    (htrue : |ordinaryMuTilde true s - armMean P true| <
      min (armMean P true) (c.lambdaMax - armMean P true))
    (hfalse : |ordinaryMuTilde false s - armMean P false| <
      min (armMean P false) (c.lambdaMax - armMean P false)) :
    ordinaryEstimator c s = ordinaryMuTilde true s - ordinaryMuTilde false s := by
  unfold ordinaryEstimator ordinaryMuHat
  rw [projectArm_eq_self_of_abs_sub_lt_boundaryDistance c
      (armMean_mem_projectionInterior c P hP true) htrue,
    projectArm_eq_self_of_abs_sub_lt_boundaryDistance c
      (armMean_mem_projectionInterior c P hP false) hfalse]

/-- Failure of projection inactivity is contained in one of the two armwise boundary-tail events. -/
lemma projectionActivity_subset_armBoundaryTails (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (n : ℕ) :
    {s : Fin n → ObsHistory |
      ordinaryEstimator c s ≠ ordinaryMuTilde true s - ordinaryMuTilde false s} ⊆
      {s | min (armMean P true) (c.lambdaMax - armMean P true) ≤
        |ordinaryMuTilde true s - armMean P true|} ∪
    {s | min (armMean P false) (c.lambdaMax - armMean P false) ≤
        |ordinaryMuTilde false s - armMean P false|} := by
  intro s hs
  by_cases ht : min (armMean P true) (c.lambdaMax - armMean P true) ≤
      |ordinaryMuTilde true s - armMean P true|
  · exact Or.inl ht
  by_cases hf : min (armMean P false) (c.lambdaMax - armMean P false) ≤
      |ordinaryMuTilde false s - armMean P false|
  · exact Or.inr hf
  · exact (hs (ordinaryEstimator_eq_rawContrast_of_close c P hP s
      (lt_of_not_ge ht) (lt_of_not_ge hf))).elim

/-- Projection activity has probability at most the sum of the two raw arm boundary tails. -/
lemma projectionActivity_probability_le_armBoundaryTails (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (n : ℕ) :
    (sampleLaw P n).real {s : Fin n → ObsHistory |
      ordinaryEstimator c s ≠ ordinaryMuTilde true s - ordinaryMuTilde false s} ≤
      (sampleLaw P n).real
        {s | min (armMean P true) (c.lambdaMax - armMean P true) ≤
          |ordinaryMuTilde true s - armMean P true|} +
    (sampleLaw P n).real
        {s | min (armMean P false) (c.lambdaMax - armMean P false) ≤
          |ordinaryMuTilde false s - armMean P false|} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw
    infer_instance
  calc
    _ ≤ (sampleLaw P n).real
        ({s | min (armMean P true) (c.lambdaMax - armMean P true) ≤
            |ordinaryMuTilde true s - armMean P true|} ∪
          {s | min (armMean P false) (c.lambdaMax - armMean P false) ≤
            |ordinaryMuTilde false s - armMean P false|}) :=
      measureReal_mono (projectionActivity_subset_armBoundaryTails c P hP n) (by finiteness)
    _ ≤ _ := measureReal_union_le _ _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
