module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceMeasurability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalRemainingMeanGrid

/-!
# Probability control for the future-mark death plug-in

A lower risk fraction at the localization horizon controls every earlier death
mark. The finite-sum comparison and finite-grid convergence then give the
probability-level plug-in replacement in roadmap (38). Pointwise remaining-mean
consistency and the probability of the lower-risk event remain explicit inputs.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Risk sets decrease as the observation horizon advances. -/
-- @node: riskSet_antitone
lemma riskSet_antitone {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    Antitone (riskSet a s) := by
  classical
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, huv.trans hi.2⟩

/-- All iid observed exits lie in the study window almost surely. -/
-- @node: sample_exit_mem_Icc_ae
lemma sample_exit_mem_Icc_ae (P : SubjectLaw) (hD : DeathHazard P) (n : ℕ) :
    ∀ᵐ s ∂sampleLaw P n, ∀ i : Fin n, (s i).exit ∈ Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  rw [Filter.eventually_all]
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving.ae (observed_exit_mem_Icc_ae P hD)

/-- The death plug-in error probability is bounded by the failed horizon-risk
event plus the uniform remaining-mean error event. Dependence between the
future marks and death variation does not enter this union bound. -/
-- @node: localizedDeathVariation_plugin_probability_le
lemma localizedDeathVariation_plugin_probability_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T η q : ℝ} (hT : T ≤ 1)
    (hη : 0 ≤ η) (hq : 0 < q) :
    (sampleLaw P n).real {s |
      2 * c.lambdaMax * η * q⁻¹ ^ 2 <
        |localizedDeathVariation a s T (remainingMeanHat c a s) -
          localizedDeathVariation a s T (remainingTarget c P a 0)|} ≤
      (sampleLaw P n).real {s | (riskSet a s T : ℝ) < (n : ℝ) * q} +
      (sampleLaw P n).real {s | ∃ u ∈ Icc (0 : ℝ) T,
        η < |remainingMeanHat c a s u - remainingTarget c P a 0 u|} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E : Set (Fin n → ObsHistory) := {s |
    2 * c.lambdaMax * η * q⁻¹ ^ 2 <
      |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|}
  have heq : (sampleLaw P n).real E =
      (sampleLaw P n).real (E ∩ {s | ∀ i, 0 ≤ (s i).exit}) := by
    apply measureReal_congr
    filter_upwards [sample_exit_mem_Icc_ae P hP.deathHazard n] with s hs
    change (s ∈ E) = (s ∈ E ∧ ∀ i, 0 ≤ (s i).exit)
    exact propext (and_iff_left (fun i => (hs i).1)).symm
  change (sampleLaw P n).real E ≤ _
  rw [heq]
  apply (measureReal_mono (show E ∩ {s | ∀ i, 0 ≤ (s i).exit} ⊆
      {s | (riskSet a s T : ℝ) < (n : ℝ) * q} ∪
      {s | ∃ u ∈ Icc (0 : ℝ) T,
        η < |remainingMeanHat c a s u - remainingTarget c P a 0 u|} from ?_)
    (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_contra hbad
  have hr : (n : ℝ) * q ≤ riskSet a s T := by
    by_contra h
    exact hbad (Or.inl (lt_of_not_ge h))
  have he : ∀ u ∈ Icc (0 : ℝ) T,
      |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤ η := by
    intro u hu
    by_contra h
    exact hbad (Or.inr ⟨u, hu, lt_of_not_ge h⟩)
  have hb := localizedDeathVariation_plugin_error_le_of_riskFraction_lower
    c P hP a hn s hT hη hq hs.2 he (fun i _ _ hi =>
      hr.trans (by exact_mod_cast riskSet_antitone a s hi))
  exact (not_lt_of_ge hb) hs.1

/-- Uniform remaining-mean consistency and a positive horizon-risk event
imply the localized death plug-in replacement in probability. -/
-- @node: localizedDeathVariation_plugin_probability_tendsto_of_uniform
lemma localizedDeathVariation_plugin_probability_tendsto_of_uniform
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T q : ℝ} (hT : T ≤ 1) (hq : 0 < q)
    (hrisk : Tendsto (fun n => (sampleLaw P n).real
      {s | (riskSet a s T : ℝ) < (n : ℝ) * q}) atTop (nhds 0))
    (huniform : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (sampleLaw P n).real {s | ∃ u ∈ Icc (0 : ℝ) T,
        η < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
        atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|}) atTop (nhds 0) := by
  intro ε hε
  let C := 2 * c.lambdaMax * q⁻¹ ^ 2
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) (c.lambdaMin_pos.trans c.lambdaMin_lt))
      (sq_pos_of_pos (inv_pos.mpr hq))
  have hη : 0 < ε / C := div_pos hε hC
  have hcoef : 2 * c.lambdaMax * (ε / C) * q⁻¹ ^ 2 = ε := by
    calc
      _ = C * (ε / C) := by dsimp [C]; ring
      _ = ε := mul_div_cancel₀ _ hC.ne'
  have hbound := Filter.eventually_atTop.2 ⟨1, fun n hn => by
    simpa only [hcoef] using localizedDeathVariation_plugin_probability_le
      c P hP a (by omega : 0 < n) hT hη.le hq⟩
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
    hbound (by simpa only [add_zero] using hrisk.add (huniform (ε / C) hη))

/-- The finite-grid upgrade supplies the uniform input to the localized
future-mark plug-in comparison from pointwise remaining-mean consistency. -/
-- @node: localizedDeathVariation_plugin_probability_tendsto_of_pointwise
lemma localizedDeathVariation_plugin_probability_tendsto_of_pointwise
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T q : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hq : 0 < q)
    (hrisk : Tendsto (fun n => (sampleLaw P n).real
      {s | (riskSet a s T : ℝ) < (n : ℝ) * q}) atTop (nhds 0))
    (hpoint : ∀ u ∈ Icc (0 : ℝ) T, ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (sampleLaw P n).real {s |
        η < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
        atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|}) atTop (nhds 0) := by
  exact localizedDeathVariation_plugin_probability_tendsto_of_uniform c P hP a hT1 hq
    hrisk (remainingMeanHat_uniform_probability_tendsto_of_pointwise c P hP a hT0 hT1 hpoint)

/-- The full plug-in error event is controlled by the localized error event
and a deterministic terminal-envelope event. This step is a pathwise union
bound, so the future marks need no predictability or independence premise. -/
-- @node: fullDeathVariation_plugin_probability_le_local_and_tail
lemma fullDeathVariation_plugin_probability_le_local_and_tail
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T ε : ℝ} (hT : T ≤ 1) :
    (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s 1 (remainingMeanHat c a s) -
        localizedDeathVariation a s 1 (remainingTarget c P a 0)|} ≤
    (sampleLaw P n).real {s |
      ε / 2 < |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|} +
    (sampleLaw P n).real {s |
      ε / 2 < tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E : Set (Fin n → ObsHistory) := {s |
    ε < |localizedDeathVariation a s 1 (remainingMeanHat c a s) -
      localizedDeathVariation a s 1 (remainingTarget c P a 0)|}
  have heq : (sampleLaw P n).real E =
      (sampleLaw P n).real (E ∩ {s | ∀ i, 0 ≤ (s i).exit}) := by
    apply measureReal_congr
    filter_upwards [sample_exit_mem_Icc_ae P hP.deathHazard n] with s hs
    change (s ∈ E) = (s ∈ E ∧ ∀ i, 0 ≤ (s i).exit)
    exact propext (and_iff_left (fun i => (hs i).1)).symm
  change (sampleLaw P n).real E ≤ _
  rw [heq]
  apply (measureReal_mono (show E ∩ {s | ∀ i, 0 ≤ (s i).exit} ⊆
      {s | ε / 2 < |localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)|} ∪
      {s | ε / 2 < tailDeathVariation a s T 1
        (fun t => c.lambdaMax * (1 - t))} from ?_)
    (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_contra hbad
  have hl : |localizedDeathVariation a s T (remainingMeanHat c a s) -
      localizedDeathVariation a s T (remainingTarget c P a 0)| ≤ ε / 2 := by
    by_contra h
    exact hbad (Or.inl (lt_of_not_ge h))
  have ht : tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t)) ≤ ε / 2 := by
    by_contra h
    exact hbad (Or.inr (lt_of_not_ge h))
  have hb := fullDeathVariation_plugin_error_le_local_and_tail c P hP a s hT hs.2
  have he : ε < |localizedDeathVariation a s 1 (remainingMeanHat c a s) -
      localizedDeathVariation a s 1 (remainingTarget c P a 0)| := hs.1
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
