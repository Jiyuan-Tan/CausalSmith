module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceAssembly
public import Causalean.Stat.CLT.Lindeberg

/-!
# Gaussian limit for the actual subcritical influence sum

Roadmap (29)--(30): the exact contrast moments imply the fixed-law Lindeberg
condition. The iid row CLT and the product pushforward identity then give
the Gaussian limit of the paper influence sum, without a higher moment.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The scalar contrast law uses the actual paper influence. -/
-- @node: subcriticalContrastLaw
noncomputable def subcriticalContrastLaw (c : ClassConstants) (P : SubjectLaw) : Measure ℝ :=
  (observedLaw P).map (fun o => subcriticalInfluence c P true o -
    subcriticalInfluence c P false o)

/-- The observed contrast is almost everywhere measurable. -/
-- @node: aemeasurable_subcriticalContrast
lemma aemeasurable_subcriticalContrast (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) :
    AEMeasurable (fun o => subcriticalInfluence c P true o -
      subcriticalInfluence c P false o) (observedLaw P) := by
  exact (aemeasurable_subcriticalInfluence c P hP hk true).sub
    (aemeasurable_subcriticalInfluence c P hP hk false)

/-- The pushforward contrast law has zero mean and the exact paper variance. -/
-- @node: subcriticalContrastLaw_moments
lemma subcriticalContrastLaw_moments (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) :
    MemLp id 2 (subcriticalContrastLaw c P) ∧
    (∫ x, x ∂subcriticalContrastLaw c P) = 0 ∧
    (∫ x, x ^ 2 ∂subcriticalContrastLaw c P) = subcriticalVariance c P := by
  have hm := subcriticalInfluence_contrast_moments c P hP hk
  have ha := aemeasurable_subcriticalContrast c P hP hk
  have hs : Integrable (fun x : ℝ => x ^ 2) (subcriticalContrastLaw c P) :=
    (integrable_map_measure (by fun_prop) ha).2 hm.2.2.1
  refine ⟨(memLp_two_iff_integrable_sq (by fun_prop)).2 hs, ?_, ?_⟩
  · rw [subcriticalContrastLaw, integral_map ha (by fun_prop)]
    exact hm.2.1
  · rw [subcriticalContrastLaw, integral_map ha (by fun_prop)]
    exact hm.2.2.2

/-- Finite contrast variance gives the square-root-scale Lindeberg tail,
with no boundedness or third-moment assumption. -/
-- @node: subcriticalContrastLaw_lindeberg
lemma subcriticalContrastLaw_lindeberg (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ∫ x in {x : ℝ | ε * Real.sqrt n ≤ |x|},
      x ^ 2 ∂subcriticalContrastLaw c P) atTop (nhds 0) := by
  let Q := subcriticalContrastLaw c P
  have hi : Integrable (fun x : ℝ => x ^ 2) Q :=
    (memLp_two_iff_integrable_sq (by fun_prop)).1
      (subcriticalContrastLaw_moments c P hP hk).1
  have ht : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := Q) (f := fun _ : ℝ => (0 : ℝ))
    (F := fun n : ℕ => {x : ℝ | ε * Real.sqrt n ≤ |x|}.indicator (fun x => x ^ 2))
    (fun x : ℝ => x ^ 2)
    (Eventually.of_forall (fun n : ℕ =>
      ((measurable_id.pow_const 2).indicator
        (measurableSet_le measurable_const measurable_id.abs)).aestronglyMeasurable))
    (Eventually.of_forall (fun n : ℕ => by
      filter_upwards [] with x
      by_cases hx : ε * Real.sqrt n ≤ |x|
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx, sq_nonneg])) hi (by
      filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [ht.eventually_gt_atTop |x|] with n hn
      simp [Set.indicator, not_le.mpr hn])
  change Tendsto (fun n : ℕ => ∫ x,
    {x : ℝ | ε * Real.sqrt n ≤ |x|}.indicator (fun x => x ^ 2) x ∂Q)
    atTop (nhds (∫ x : ℝ, (0 : ℝ) ∂Q)) at h
  have he (n : ℕ) : (∫ x,
      {x : ℝ | ε * Real.sqrt n ≤ |x|}.indicator (fun x => x ^ 2) x ∂Q) =
      ∫ x in {x : ℝ | ε * Real.sqrt n ≤ |x|}, x ^ 2 ∂Q :=
    integral_indicator (measurableSet_le measurable_const measurable_id.abs)
  simp_rw [he] at h
  simpa only [integral_zero] using h

/-- The actual finite-sample influence-sum law is the iid scalar row law. -/
-- @node: subcriticalInfluence_normalizedSumLaw_eq
lemma subcriticalInfluence_normalizedSumLaw_eq (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) (n : ℕ) :
    (sampleLaw P n).map (fun s => (∑ i : Fin n,
      (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
        Real.sqrt n) =
    (Measure.pi (fun _ : Fin n => subcriticalContrastLaw c P)).map
      (fun y => (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have ha := aemeasurable_subcriticalContrast c P hP hk
  let Z := fun o => subcriticalInfluence c P true o - subcriticalInfluence c P false o
  letI : IsProbabilityMeasure (subcriticalContrastLaw c P) :=
    Measure.isProbabilityMeasure_map ha
  have hp := Measure.pi_map_pi (fun _ : Fin n => ha)
  unfold subcriticalContrastLaw
  have hv : AEMeasurable (fun s : Fin n → ObsHistory => fun i =>
      subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))
      (Measure.pi (fun _ : Fin n => observedLaw P)) :=
    aemeasurable_pi_lambda _ (fun i =>
      ha.comp_quasiMeasurePreserving
        (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving)
  have hr := AEMeasurable.map_map_of_aemeasurable
    (g := fun y : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y)
    ((Causalean.Stat.measurable_iidRowSum n).const_mul _).aemeasurable hv
  rw [← hp, hr]
  congr 1
  funext s
  simp [Function.comp_def, Causalean.Stat.iidRowSum, div_eq_mul_inv, mul_comm]

/-- The normalized actual influence contrast converges to the centered
Gaussian with the exact positive subcritical variance, as in roadmap (30). -/
-- @node: subcriticalInfluence_normalizedSum_gaussian
lemma subcriticalInfluence_normalizedSum_gaussian (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : c.kappa < 1) :
    ConvergesInLaw (fun n : ℕ => (sampleLaw P n).map (fun s =>
      (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
        subcriticalInfluence c P false (s i))) / Real.sqrt n))
      (gaussianReal 0 (Real.toNNReal (subcriticalVariance c P))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (subcriticalContrastLaw c P) :=
    Measure.isProbabilityMeasure_map (aemeasurable_subcriticalContrast c P hP hk)
  have hm := subcriticalContrastLaw_moments c P hP hk
  have hvar := (subcriticalVariance_pos c P hP hk).le
  have hclt := Causalean.Stat.iidRowNormalizedSumLaw_tendsto_gaussian
    (fun _ => subcriticalContrastLaw c P) (Real.toNNReal (subcriticalVariance c P))
    (fun _ => hm.1) (fun _ => hm.2.1)
    (by simpa only [hm.2.2, Real.coe_toNNReal _ hvar] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => subcriticalVariance c P)
        atTop (nhds (subcriticalVariance c P))))
    (fun ε hε => subcriticalContrastLaw_lindeberg c P hP hk ε hε)
  intro f hf hb
  obtain ⟨M, hM⟩ := hb
  let F : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨f, hf⟩, ⟨2 * M, fun x y => by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hM x, hM y])⟩⟩
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hclt) F
  simpa [Causalean.Stat.iidRowNormalizedSumLaw, F,
    ← subcriticalInfluence_normalizedSumLaw_eq c P hP hk] using ht

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
