module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalBiasScale
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalDeathRemainder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalProjectionProbability

/-!
# Critical recurrence approximation

Roadmap (22)--(26): the exact decomposition, negligible death and extinction
terms, continuation bias, and projection inactivity reduce the observable
critical contrast to its genuine recurrence-martingale contrast along arbitrary
triangular model sequences. The recurrence CLT remains a separate obligation.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Subtraction preserves negligible probability tails on the actual sample rows. -/
-- @node: triangularSampleLaw_negligible_sub
lemma triangularSampleLaw_negligible_sub (Pseq : ℕ → SubjectLaw)
    (X Y : (n : ℕ) → (Fin n → ObsHistory) → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < |X n s|}) atTop (nhds 0))
    (hY : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | ε < |Y n s|}) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s | ε < |X n s - Y n s|})
      atTop (nhds 0) := by
  have ht := (hX (ε / 2) (half_pos hε)).add (hY (ε / 2) (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using ht)
  apply Eventually.of_forall
  intro n
  let P := Pseq n
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  have hs : {s | ε < |X n s - Y n s|} ⊆
      {s | ε / 2 < |X n s|} ∪ {s | ε / 2 < |Y n s|} := by
    intro s hs
    by_contra hn
    have h := not_or.mp hn
    have hx : |X n s| ≤ ε / 2 := le_of_not_gt h.1
    have hy : |Y n s| ≤ ε / 2 := le_of_not_gt h.2
    have ha := abs_sub (X n s) (Y n s)
    change ε < |X n s - Y n s| at hs
    linarith
  exact (measureReal_mono hs (by finiteness)).trans (measureReal_union_le _ _)

/-- The actual continued arm error differs negligibly from its recurrence term
at the critical normalization, uniformly along triangular model laws. -/
-- @node: critical_muTilde_recurrence_triangular_probability_tendsto_zero
lemma critical_muTilde_recurrence_triangular_probability_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |Real.sqrt ((n : ℝ) / Real.log n) *
        (muTildeAt c (bandwidth c n) a s - armMean (Pseq n) a -
          recurrenceError c (Pseq n) a s (bandwidth c n))|}) atTop (nhds 0) := by
  let q := fun n : ℕ => Real.sqrt ((n : ℝ) / Real.log n)
  let B := fun n : ℕ => q n *
    (truncatedMean c (Pseq n) a (bandwidth c n) - armMean (Pseq n) a)
  let D := fun n (s : Fin n → ObsHistory) =>
    q n * deathError c (Pseq n) a s (bandwidth c n)
  let E := fun n (s : Fin n → ObsHistory) =>
    q n * extinctionError c (Pseq n) a s (bandwidth c n)
  have hB : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | δ < |B n|}) atTop (nhds 0) := by
    intro δ hδ
    have hb := critical_continuation_bias_triangular_tendsto_zero c hk Pseq hP a
    apply tendsto_const_nhds.congr'
    filter_upwards [hb.eventually (gt_mem_nhds hδ)] with n hn
    have hbn : |B n| < δ := by
      simpa only [B, q, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
    have he : {s : Fin n → ObsHistory | δ < |B n|} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge hbn.le
    simp only [he, measureReal_empty]
  have hD : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | δ < |D n s|}) atTop (nhds 0) := fun _ hδ =>
    critical_deathError_triangular_probability_tendsto_zero c hk Pseq hP a hδ
  have hE : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw (Pseq n) n).real
      {s | δ < |E n s|}) atTop (nhds 0) := fun _ hδ =>
    critical_extinctionError_triangular_probability_tendsto_zero c hk Pseq hP a hδ
  have ht := triangularSampleLaw_negligible_sub Pseq
    (fun n s => B n - D n s) E
    (fun _ hδ => triangularSampleLaw_negligible_sub Pseq (fun n _ => B n) D hB hD hδ)
    hE hε
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  apply measureReal_congr
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  filter_upwards [(exact_error_decomposition c (Pseq n) (hP n).iid
    (hP n).randomAssignment (hP n).poissonRecurrence (hP n).deathHazard
    (hP n).recurrenceDeathIndependence (hP n).independentCensoring
    (hP n).deathBounds (hP n).assignmentLaw).1 n hn] with s hs
  have he := hs a (bandwidth c n) hh.1.le hh.2
  change (ε < |B n - D n s - E n s|) =
    (ε < |q n * (muTildeAt c (bandwidth c n) a s - armMean (Pseq n) a -
      recurrenceError c (Pseq n) a s (bandwidth c n))|)
  have hid : B n - D n s - E n s = q n *
      (muTildeAt c (bandwidth c n) a s - armMean (Pseq n) a -
        recurrenceError c (Pseq n) a s (bandwidth c n)) := by
    dsimp [B, D, E]
    have hm : muTildeAt c (bandwidth c n) a s =
        truncatedMean c (Pseq n) a (bandwidth c n) +
        recurrenceError c (Pseq n) a s (bandwidth c n) -
        deathError c (Pseq n) a s (bandwidth c n) -
        extinctionError c (Pseq n) a s (bandwidth c n) := by linarith [he]
    rw [hm]
    ring
  rw [hid]

/-- The unprojected critical contrast has only a negligible nonrecurrence error. -/
-- @node: critical_rawContrast_recurrence_triangular_probability_tendsto_zero
lemma critical_rawContrast_recurrence_triangular_probability_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |Real.sqrt ((n : ℝ) / Real.log n) *
        (muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s -
          causalTarget (Pseq n) - (recurrenceError c (Pseq n) true s (bandwidth c n) -
            recurrenceError c (Pseq n) false s (bandwidth c n)))|}) atTop (nhds 0) := by
  have ht := triangularSampleLaw_negligible_sub Pseq
    (fun n s => Real.sqrt ((n : ℝ) / Real.log n) *
      (muTildeAt c (bandwidth c n) true s - armMean (Pseq n) true -
        recurrenceError c (Pseq n) true s (bandwidth c n)))
    (fun n s => Real.sqrt ((n : ℝ) / Real.log n) *
      (muTildeAt c (bandwidth c n) false s - armMean (Pseq n) false -
        recurrenceError c (Pseq n) false s (bandwidth c n)))
    (fun _ hδ => critical_muTilde_recurrence_triangular_probability_tendsto_zero
      c hk Pseq hP true hδ)
    (fun _ hδ => critical_muTilde_recurrence_triangular_probability_tendsto_zero
      c hk Pseq hP false hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq]
  rw [(hP n).causalTarget_eq_survival_intensity_contrast,
    intervalIntegral.integral_sub ((hP n).armMean_integrand_intervalIntegrable true)
      ((hP n).armMean_integrand_intervalIntegrable false)]
  unfold armMean
  ring_nf

/-- Projection inactivity transfers the genuine recurrence approximation to the
observable critical estimator, completing the nonrecurrence part of (26). -/
-- @node: critical_observable_recurrence_triangular_probability_tendsto_zero
lemma critical_observable_recurrence_triangular_probability_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |Real.sqrt ((n : ℝ) / Real.log n) *
        (observableEstimator c s - causalTarget (Pseq n) -
          (recurrenceError c (Pseq n) true s (bandwidth c n) -
            recurrenceError c (Pseq n) false s (bandwidth c n)))|}) atTop (nhds 0) := by
  have ht := (continuedProjectionActivity_critical_triangular_tendsto_zero c hk Pseq hP).add
    (critical_rawContrast_recurrence_triangular_probability_tendsto_zero c hk Pseq hP hε)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using ht)
  apply Eventually.of_forall
  intro n
  let P := Pseq n
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  apply (measureReal_mono ?_ (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_cases hp : observableEstimator c s ≠
      muTildeAt c (bandwidth c n) true s - muTildeAt c (bandwidth c n) false s
  · exact Or.inl hp
  · apply Or.inr
    simp only [Set.mem_ofPred_eq] at hs ⊢
    simpa only [not_not.mp hp] using hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
