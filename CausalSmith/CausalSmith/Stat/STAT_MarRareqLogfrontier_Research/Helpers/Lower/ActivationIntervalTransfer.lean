module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationMixture
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationModel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TOneCellTestingFamily

/-! Averaging randomized interval lengths in the actual activated experiment
and comparing the prior average with the model-class worst-case length. -/

public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,f), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_integral
lemma activatedAugmentedMixture_integral (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ} (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (f : (Fin n → Bool × ObsRecord d) → ℝ) :
    (∫ s, f s ∂activatedAugmentedMixture η n d q π) =
      ∫ z, (∫ s, f s ∂activatedAugmentedSample η n d q z)
        ∂Measure.pi (fun _ : Fin d => π) := by
  classical
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice hπ
  rw [integral_fintype Integrable.of_finite]
  simp_rw [activatedAugmentedMixture_real_singleton, smul_eq_mul,
    ← integral_mul_const]
  rw [← integral_finsetSum _ (fun s _ => finiteReciprocalPrior_pi_integrable hπ d _)]
  apply integral_congr_ae
  filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
  rw [activatedAugmentedSample, dif_pos hz]
  let := augmentedOneRecord_isProbabilityMeasure η n d q z hn hd hb hq hslice hz
  simpa only [smul_eq_mul] using (integral_fintype (f := f)
    (μ := Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz))
    Integrable.of_finite).symm

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,f), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_projected_integral
lemma activatedAugmentedMixture_projected_integral (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (f : (Fin n → ObsRecord d) → ℝ) :
    (∫ s, f s ∂((activatedAugmentedMixture η n d q π).map
      (fun s i => (s i).2))) =
      ∫ z, (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        ∫ s, f s ∂sampleLaw n (activatedFullLaw η n d q z hd hb hq hslice hz)
        else 0) ∂Measure.pi (fun _ : Fin d => π) := by
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
    fun_prop
  rw [integral_map hf.aemeasurable (by fun_prop), activatedAugmentedMixture_integral η n d q hn hd hb hq hslice hπ]
  apply integral_congr_ae
  filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
  rw [dif_pos hz, activatedAugmentedSample, dif_pos hz]
  rw [← activated_sample_projection η n d q z hn hd hb hq hslice hz,
    integral_map hf.aemeasurable (by fun_prop)]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,T), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_intervalRisk_average
lemma activatedAugmentedMixture_intervalRisk_average (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (T : IntervalProcedure n d) :
    (∫ s, (∫ I : ConnectedInterval, I.hi - I.lo ∂T.1 s)
      ∂((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2))) =
      ∫ z, (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        intervalRisk T (activatedFullLaw η n d q z hd hb hq hslice hz)
        else 0) ∂Measure.pi (fun _ : Fin d => π) := by
  exact activatedAugmentedMixture_projected_integral η n d q hn hd hb hq hslice hπ _

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,T), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_intervalRisk_le_worst
lemma activatedAugmentedMixture_intervalRisk_le_worst (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (T : IntervalProcedure n d) :
    (∫ s, (∫ I : ConnectedInterval, I.hi - I.lo ∂T.1 s)
      ∂((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2))) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          intervalRisk T P.1) () := by
  let := hπ.1
  rw [activatedAugmentedMixture_intervalRisk_average η n d q hn hd hb hq hslice hπ T]
  have hbdd : BddAbove (Set.range (fun P : {P : FullLaw d // RareArrivalModelClass n d q P} =>
      intervalRisk T P.1)) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact (intervalRisk_bounds T P.1).2
  have hle : ∀ᵐ z ∂Measure.pi (fun _ : Fin d => π),
      (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        intervalRisk T (activatedFullLaw η n d q z hd hb hq hslice hz) else 0) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          intervalRisk T P.1) () := by
    filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
    rw [dif_pos hz]
    exact Causalean.Stat.le_worstCaseRisk
      (risk := fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
        intervalRisk T P.1) (e := ()) hbdd ⟨_, activatedFullLaw_model η n d q z hd hb hq hslice hz hn⟩
  simpa using integral_mono_ae (finiteReciprocalPrior_pi_integrable hπ d _)
    (integrable_const _) hle

end CausalSmith.Stat.MarRareqLogfrontier
