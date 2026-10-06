module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.TMinimaxFrontier
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.THonestIntervalFrontier
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedBoundaryNull
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Causalean.Mathlib.Probability.Poisson.Moments

/-!
# Converse transfer to the relaxed causal class

The relaxed class contains the smooth Poisson model and inherits minimax and
honest-length lower bounds, with class constants fixed across sample sizes.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: RecurConfig.countLE_le_count
lemma RecurConfig.countLE_le_count (s : RecurConfig) (t : ℝ) :
    s.countLE t ≤ s.count := by
  have hsum :
    (∑ i : Fin s.count, if (s.points i).1 ≤ t then 1 else 0) ≤
        s.count := by
    calc
      _ ≤ ∑ _i : Fin s.count, 1 :=
        Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
      _ = s.count := by simp
  convert hsum using 1
  simp [RecurConfig.countLE, RecurConfig.paddedCountLE,
    finiteSamplePaddedStream]
  congr 1

-- @node: clinicalCount_le_recurCount
lemma clinicalCount_le_recurCount (z : LatentSubject) (a : Arm) (t : ℝ) :
    clinicalCount z a t ≤ (z.recur a).count := by
  exact RecurConfig.countLE_le_count (z.recur a) (min t (z.death a))

-- @node: RecurConfig.countLE_min_eventually_eq_horizon
lemma RecurConfig.countLE_min_eventually_eq_horizon (s : RecurConfig)
    (d : ℝ) (hNoEndpoint : ∀ i : Fin s.count, (s.points i).1 ≠ 1) :
    ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1),
      s.countLE (min t d) = s.countLE (min 1 d) := by
  have hi (i : Fin s.count) :
      ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1),
        (if (s.points i).1 ≤ min t d then 1 else 0) =
          (if (s.points i).1 ≤ min 1 d then 1 else 0) := by
    by_cases hx : (s.points i).1 ≤ min 1 d
    · have hlt : (s.points i).1 < 1 :=
        lt_of_le_of_ne (le_trans hx (min_le_left _ _)) (hNoEndpoint i)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Ioi_mem_nhds hlt)] with t ht'
      have htd : (s.points i).1 ≤ min t d :=
        le_min ht'.le (le_trans hx (min_le_right _ _))
      simp [hx, htd]
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      have hnot : ¬ (s.points i).1 ≤ min t d := by
        intro h
        exact hx (le_trans h (min_le_min_right d ht.le))
      simp [hx, hnot]
  have hall : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ i : Fin s.count,
        (if (s.points i).1 ≤ min t d then 1 else 0) =
          (if (s.points i).1 ≤ min 1 d then 1 else 0) :=
    Filter.eventually_all.mpr hi
  filter_upwards [hall] with t ht
  simpa only [RecurConfig.countLE, RecurConfig.paddedCountLE,
    finiteSamplePaddedStream, Fin.is_lt, dite_true] using
    Finset.sum_congr rfl (fun i _ => ht i)

-- @node: recurCount_sq_integrable
lemma recurCount_sq_integrable (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) :
    Integrable (fun z : LatentSubject => ((z.recur a).count : ℝ) ^ 2) P.latent := by
  obtain ⟨_, _, hν, hdist⟩ := hP.poissonRecurrence a
  have hmap : Measure.map FiniteSample.count (@canonicalRecurrenceLaw P a hν) =
      ProbabilityTheory.poissonMeasure (finiteMeasureMass (recurrenceIntensity P a)) := by
    simpa [canonicalRecurrenceLaw, canonicalRecurrenceLawOf] using
      finiteMeasureMarkedPoissonLaw_map_count
        (recurrenceIntensity P a) (Measure.dirac 0) (Measure.dirac 0) 1
  have hpoisson :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
      (finiteMeasureMass (recurrenceIntensity P a))).integrable_sq
  rw [← hmap] at hpoisson
  have hconfig : Integrable
      (fun s : RecurConfig => (s.count : ℝ) ^ 2)
      (@canonicalRecurrenceLaw P a hν) := by
    exact hpoisson.comp_measurable (by fun_prop)
  rw [← hdist] at hconfig
  exact hconfig.comp_measurable (measurable_latentSubject_recur a)

-- @node: prop:endpoint-relaxed-superclass-converse
theorem endpoint_relaxed_superclass_converse (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) :
    (∀ P : SubjectLaw, ModelClass c P →
      RelaxedClass c P ∧ relaxedTarget P = causalTarget P) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 3 ≤ n →
      ENNReal.ofReal (c₀ * riskScale c n) ≤ relaxedMinimaxRisk c n) ∧
    (∀ alpha : ℝ, 0 < alpha → alpha < 1 / 2 →
      ∃ cAlpha : ℝ, 0 < cAlpha ∧ ∀ n : ℕ, 3 ≤ n →
        ∀ lo hi : (Fin n → ObsHistory) → ℝ,
          Measurable lo → Measurable hi →
          (∀ P : SubjectLaw, RelaxedClass c P →
            1 - alpha ≤ (sampleLaw P n).real
              {s | lo s ≤ relaxedTarget P ∧ relaxedTarget P ≤ hi s}) →
          ∃ P : SubjectLaw, RelaxedClass c P ∧
            ENNReal.ofReal (cAlpha * Real.sqrt (riskScale c n)) ≤
              ∫⁻ s, ENNReal.ofReal (hi s - lo s) ∂sampleLaw P n) := by
  have hIncl : ∀ P : SubjectLaw, ModelClass c P →
      RelaxedClass c P ∧ relaxedTarget P = causalTarget P := by
    intro P hP
    refine ⟨?_, rfl⟩
    refine ⟨hP.iid, hP.randomAssignment, hP.assignmentLaw,
      hP.treatmentOverlap, hP.independentCensoring, hP.endpointRetention,
      hP.tailEnvelopeSmall, hP.endpointCoefficientBounds,
      hP.interiorRetention, ?_, ?_⟩
    · intro a
      have hcount : Measurable (fun z : LatentSubject => clinicalCount z a 1) := by
        unfold clinicalCount
        exact RecurConfig.measurable_countLE.comp
          ((measurable_const.min (measurable_latentSubject_death a)).prodMk
            (measurable_latentSubject_recur a))
      have hmeas : Measurable
          (fun z : LatentSubject => (clinicalCount z a 1 : ℝ) ^ 2) := by
        exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hcount).pow_const 2
      apply (recurCount_sq_integrable P hP a).mono' hmeas.aestronglyMeasurable
      filter_upwards with z
      have hle : (clinicalCount z a 1 : ℝ) ≤ ((z.recur a).count : ℝ) :=
        Nat.cast_le.mpr (clinicalCount_le_recurCount z a 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (by positivity) hle 2
    · -- A stopped Poisson path has no jump at the fixed horizon almost surely,
      -- and the second moment supplies domination for mean continuity.
      intro a
      have hcountInt : Integrable
          (fun z : LatentSubject => ((z.recur a).count : ℝ)) P.latent := by
        have hmeas : Measurable
            (fun z : LatentSubject => ((z.recur a).count : ℝ)) := by fun_prop
        apply (recurCount_sq_integrable P hP a).mono' hmeas.aestronglyMeasurable
        filter_upwards with z
        have hnat : (z.recur a).count = 0 ∨ 1 ≤ (z.recur a).count := by omega
        rcases hnat with hzero | hone
        · simp [hzero]
        · rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
          have hn : (1 : ℝ) ≤ ((z.recur a).count : ℝ) := by exact_mod_cast hone
          nlinarith
      apply tendsto_integral_filter_of_dominated_convergence
        (bound := fun z : LatentSubject => ((z.recur a).count : ℝ))
      · filter_upwards with t
        have hmeas : Measurable
            (fun z : LatentSubject => (clinicalCount z a t : ℝ)) := by
          have hc : Measurable (fun z : LatentSubject => clinicalCount z a t) := by
            unfold clinicalCount
            exact RecurConfig.measurable_countLE.comp
              ((measurable_const.min (measurable_latentSubject_death a)).prodMk
                (measurable_latentSubject_recur a))
          exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hc
        exact hmeas.aestronglyMeasurable
      · filter_upwards with t
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast clinicalCount_le_recurCount z a t
      · exact hcountInt
      · filter_upwards [hP.ae_no_recurrence_at_horizon a] with z hz
        have hlim := RecurConfig.countLE_min_eventually_eq_horizon
          (z.recur a) (z.death a) hz
        exact tendsto_nhds_of_eventually_eq
          (show ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1),
            (clinicalCount z a t : ℝ) = (clinicalCount z a 1 : ℝ) by
              filter_upwards [hlim] with t ht
              exact congrArg Nat.cast ht)
  refine ⟨hIncl, ?_, ?_⟩
  · obtain ⟨c₀, C, hc₀, _hstrict, hrisk, _⟩ :=
      minimax_frontier c hNonempty
    refine ⟨c₀, hc₀, ?_⟩
    intro n hn
    have hmono :
        (Causalean.Stat.minimaxValueENNReal
          (fun (f : {f : (Fin n → ObsHistory) → ℝ // Measurable f})
            (P : {P : SubjectLaw // ModelClass c P}) =>
            Causalean.Stat.sqRiskLIntegral (sampleLaw P.1 n) f.1 (causalTarget P.1))) ≤
        relaxedMinimaxRisk c n := by
      unfold relaxedMinimaxRisk
      apply Causalean.Stat.minimaxValueENNReal_mono_class
        (fun P : {P : SubjectLaw // ModelClass c P} =>
          ⟨P.1, (hIncl P.1 P.2).1⟩)
      intro f P
      simp only [relaxedTarget, le_refl]
    have hlow := (hrisk n hn).1
    apply le_trans (ENNReal.ofReal_le_ofReal hlow)
    exact (ENNReal.ofReal_toReal_le).trans hmono
  · intro alpha hAlpha hAlphaHalf
    obtain ⟨_hUpper, cAlpha, hcAlpha, hLower⟩ :=
      honest_interval_frontier c hNonempty alpha hAlpha hAlphaHalf
    refine ⟨cAlpha, hcAlpha, ?_⟩
    intro n hn lo hi hlo hhi hCoverage
    have hCoverageSmooth : ∀ P : SubjectLaw, ModelClass c P →
        1 - alpha ≤ (sampleLaw P n).real
          {s | lo s ≤ causalTarget P ∧ causalTarget P ≤ hi s} := by
      intro P hP
      simpa only [(hIncl P hP).2] using hCoverage P (hIncl P hP).1
    obtain ⟨P, hP, hLength⟩ := hLower n hn lo hi hlo hhi hCoverageSmooth
    exact ⟨P, (hIncl P hP).1, hLength⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
