module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedDeathOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.OrdinaryRecurrenceOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalEstimatorTightness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceAssembly

/-!
# Actual subcritical influence expansion

Roadmap (23), (27)--(28): combine the full-horizon recurrence and death
oracle replacements with negligible extinction and the exact decomposition.
The oracle identity and projection inactivity give the observable contrast
expansion, without additional moment or linearity assumptions.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Subtraction preserves negligible probability tails on the actual sample rows. -/
-- @node: sampleLaw_negligible_sub
lemma sampleLaw_negligible_sub (P : SubjectLaw)
    (X Y : (n : ℕ) → (Fin n → ObsHistory) → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real
      {s | ε < |X n s|}) atTop (nhds 0))
    (hY : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real
      {s | ε < |Y n s|}) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (sampleLaw P n).real {s | ε < |X n s - Y n s|})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have ht := (hX (ε / 2) (half_pos hε)).add (hY (ε / 2) (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using ht)
  apply Eventually.of_forall
  intro n
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

/-- The raw ordinary arm mean has the exact paper influence expansion at
root-n scale, by the actual oracle replacements and negligible extinction. -/
-- @node: subcritical_ordinaryMuTilde_influence_probability_tendsto_zero
lemma subcritical_ordinaryMuTilde_influence_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a) -
        (∑ i : Fin n, subcriticalInfluence c P a (s i)) / Real.sqrt n|})
      atTop (nhds 0) := by
  let R := fun n (s : Fin n → ObsHistory) => Real.sqrt n * recurrenceError c P a s 0 -
    observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
      (P.p a * Real.sqrt n)
  let D := fun n (s : Fin n → ObsHistory) => Real.sqrt n * deathError c P a s 0 -
    aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
      (observedDeathSample a s) / Real.sqrt n
  let E := fun n (s : Fin n → ObsHistory) => Real.sqrt n * extinctionError c P a s 0
  have hR : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw P n).real
      {s | δ < |R n s|}) atTop (nhds 0) := fun _ hδ =>
    recurrenceError_zero_oracle_difference_probability_tendsto_zero c P hP hk a hδ
  have hD : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw P n).real
      {s | δ < |D n s|}) atTop (nhds 0) := fun _ hδ =>
    deathError_zero_oracle_difference_probability_tendsto_zero c P hP hk a hδ
  have hE : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw P n).real
      {s | δ < |E n s|}) atTop (nhds 0) := fun _ hδ =>
    subcritical_extinctionError_rootn_probability_tendsto_zero c P hP hk a hδ
  have ht := sampleLaw_negligible_sub P (fun n s => R n s - D n s) E
    (fun _ hδ => sampleLaw_negligible_sub P R D hR hD hδ) hE hε
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  apply measureReal_congr
  filter_upwards [ordinaryMuTilde_error_decomposition_ae c P hP a hn,
    observedSubcriticalArmOracle_ae_eq_influence_sum c P hP hk a n] with s hs ho
  change (ε < |R n s - D n s - E n s|) =
    (ε < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a) -
      (∑ i : Fin n, subcriticalInfluence c P a (s i)) / Real.sqrt n|)
  rw [← ho, hs]
  dsimp [R, D, E]
  congr 2
  simp only [sub_div, div_div]
  ring

/-- Subtracting the two raw arm expansions gives the unprojected causal
contrast expansion with the paper's subject-level influence contrast. -/
-- @node: subcritical_rawContrast_influence_probability_tendsto_zero
lemma subcritical_rawContrast_influence_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryMuTilde true s - ordinaryMuTilde false s -
        causalTarget P) - (∑ i : Fin n,
          (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
            Real.sqrt n|}) atTop (nhds 0) := by
  have ht := sampleLaw_negligible_sub P
    (fun n s => Real.sqrt n * (ordinaryMuTilde true s - armMean P true) -
      (∑ i : Fin n, subcriticalInfluence c P true (s i)) / Real.sqrt n)
    (fun n s => Real.sqrt n * (ordinaryMuTilde false s - armMean P false) -
      (∑ i : Fin n, subcriticalInfluence c P false (s i)) / Real.sqrt n)
    (fun _ hδ => subcritical_ordinaryMuTilde_influence_probability_tendsto_zero
      c P hP hk true hδ)
    (fun _ hδ => subcritical_ordinaryMuTilde_influence_probability_tendsto_zero
      c P hP hk false hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  rw [hP.causalTarget_eq_survival_intensity_contrast,
    intervalIntegral.integral_sub (hP.armMean_integrand_intervalIntegrable true)
      (hP.armMean_integrand_intervalIntegrable false)]
  simp only [Finset.sum_sub_distrib, sub_div]
  unfold armMean
  congr 2
  ring

/-- The actual observable ordinary estimator is root-n asymptotically
linear, since projection is inactive with probability tending to one. -/
-- @node: subcritical_ordinaryEstimator_influence_probability_tendsto_zero
lemma subcritical_ordinaryEstimator_influence_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryEstimator c s - causalTarget P) -
        (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
          subcriticalInfluence c P false (s i))) / Real.sqrt n|})
      atTop (nhds 0) := by
  have ht := sampleLaw_negligible_sub P
    (fun n s => Real.sqrt n * (ordinaryMuTilde true s - ordinaryMuTilde false s -
      causalTarget P) - (∑ i : Fin n,
        (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
          Real.sqrt n)
    (fun n s => -(Real.sqrt n *
      (ordinaryEstimator c s - (ordinaryMuTilde true s - ordinaryMuTilde false s))))
    (fun _ hδ => subcritical_rawContrast_influence_probability_tendsto_zero c P hP hk hδ)
    (fun _ hδ => by simpa only [abs_neg] using
      subcritical_projection_rootn_probability_tendsto_zero c P hP hk hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  congr 2
  ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
