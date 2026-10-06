module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationCalibration
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.FuzzyRisk
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TOneCellTestingRisk

/-! Prior averaging and centered-risk transfer for randomized estimators in
 equations (14)--(16) of the activated point-risk lower bound. -/

public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:n,d,f,P,θ), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_deterministic_centered_risk_le
lemma activated_deterministic_centered_risk_le {n d : ℕ}
    (f : (Fin n → ObsRecord d) → ℝ) (P : FullLaw d) (θ : ℝ) :
    (∫ s, (f s - θ) ^ 2 ∂sampleLaw n P) ≤
      2 * deterministicRisk f P + 2 * (ate P - θ) ^ 2 := by
  let := P.2
  let := Measure.isProbabilityMeasure_map (show Measurable obs by fun_prop).aemeasurable
    (μ := P.1)
  letI : IsProbabilityMeasure (sampleLaw n P) := by unfold sampleLaw; infer_instance
  have h := activated_centered_risk_le (sampleLaw n P) f (fun _ => ate P) θ
    Integrable.of_finite Integrable.of_finite Integrable.of_finite
  simpa [deterministicRisk] using h

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_full_prior_target_second_moment_le
lemma activated_full_prior_target_second_moment_le
    (η : ℝ) (n d : ℕ) (q : ℝ) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    (∫ z, (rareMass η n q * (∑ x : Fin d,
      if x.val < rareCount η n d q then (z x)⁻¹ else 0) -
      (rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π)) ^ 2
      ∂Measure.pi (fun _ : Fin d => π)) ≤
        (rareCount η n d q : ℝ) * (rareMass η n q) ^ 2 / 4 := by
  let := hπ.1
  let J := rareCount η n d q
  have hJ : J ≤ d := (min_le_left _ _).trans (Nat.sub_le d 1)
  let restrict : (Fin d → ℝ) → (Fin J → ℝ) := fun z x => z (x.castLE hJ)
  have hr : Measurable restrict := by fun_prop
  have hmap := intervalPrior_initial_coordinates_map d J hJ (π := π)
  have hm : Measurable (intervalPriorTarget J (rareMass η n q)) := by
    unfold intervalPriorTarget
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    fun_prop
  have hv := intervalPriorTarget_variance_le hπ J (rareMass η n q)
  rw [variance_eq_integral hm.aemeasurable,
    intervalPriorTarget_integral hπ] at hv
  rw [← hmap, integral_map hr.aemeasurable ((hm.sub_const _).pow_const 2).aestronglyMeasurable] at hv
  simpa only [intervalPriorTarget, activation_sum_initial_cells d J hJ, restrict, J]
    using hv

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,T), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_prior_squaredRisk_le_worst
lemma activated_prior_squaredRisk_le_worst (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) (T : Estimator n d) :
    (∫ z, (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
      squaredRisk T (activatedFullLaw η n d q z hd hb hq hslice hz) else 0)
      ∂Measure.pi (fun _ : Fin d => π)) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          squaredRisk T P.1) () := by
  let := hπ.1
  have hbdd : BddAbove (Set.range (fun P : {P : FullLaw d // RareArrivalModelClass n d q P} =>
      squaredRisk T P.1)) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact (unrestricted_squaredRisk_bounds T P.1).2
  have hle : ∀ᵐ z ∂Measure.pi (fun _ : Fin d => π),
      (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        squaredRisk T (activatedFullLaw η n d q z hd hb hq hslice hz) else 0) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          squaredRisk T P.1) () := by
    filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
    rw [dif_pos hz]
    exact Causalean.Stat.le_worstCaseRisk
      (risk := fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
        squaredRisk T P.1) (e := ()) hbdd
      ⟨_, activatedFullLaw_model η n d q z hd hb hq hslice hz hn⟩
  simpa using integral_mono_ae (finiteReciprocalPrior_pi_integrable hπ d _)
    (integrable_const _) hle

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,T), [the stated mathematical conclusion holds](goal). -/
lemma activatedAugmentedMixture_centered_risk_le_worst
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) (T : Estimator n d) :
    (∫ s, (Causalean.Stat.kernelMean T.toBoundedKernel.1 clip s -
      (rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π)) ^ 2
      ∂((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2))) ≤
      2 * Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          squaredRisk T P.1) () +
        (rareCount η n d q : ℝ) * (rareMass η n q) ^ 2 / 2 := by
  classical
  let := hπ.1
  let f := Causalean.Stat.kernelMean T.toBoundedKernel.1 clip
  let θ := (rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π)
  let r := fun z : Fin d → ℝ => if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)
    then squaredRisk T (activatedFullLaw η n d q z hd hb hq hslice hz) else 0
  let v := fun z : Fin d → ℝ => (rareMass η n q * (∑ x : Fin d,
    if x.val < rareCount η n d q then (z x)⁻¹ else 0) - θ) ^ 2
  rw [activatedAugmentedMixture_projected_integral η n d q hn hd hb hq hslice hπ]
  have hpoint : ∀ᵐ z ∂Measure.pi (fun _ : Fin d => π),
      (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        ∫ s, (f s - θ) ^ 2 ∂sampleLaw n
          (activatedFullLaw η n d q z hd hb hq hslice hz) else 0) ≤ 2 * r z + 2 * v z := by
    filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
    simp only [r, dif_pos hz]
    let P := activatedFullLaw η n d q z hd hb hq hslice hz
    have h := activated_deterministic_centered_risk_le f P θ
    have hj := complete_arrival_kernel_mean_risk_le T P
    have ht : ate P = rareMass η n q * (∑ x : Fin d,
      if x.val < rareCount η n d q then (z x)⁻¹ else 0) := by
      exact activatedLaw_target_integral η n d q z hb hq hslice hz
    dsimp only [v]
    rw [← ht]
    linarith
  have havg := integral_mono_ae (finiteReciprocalPrior_pi_integrable hπ d _)
    (finiteReciprocalPrior_pi_integrable hπ d _) hpoint
  rw [integral_add ((finiteReciprocalPrior_pi_integrable hπ d r).const_mul 2)
    ((finiteReciprocalPrior_pi_integrable hπ d v).const_mul 2),
    integral_const_mul, integral_const_mul] at havg
  have hr := activated_prior_squaredRisk_le_worst η n d q hn hd hb hq hslice hπ T
  have hv := activated_full_prior_target_second_moment_le η n d q hπ
  change (∫ z, v z ∂Measure.pi (fun _ : Fin d => π)) ≤ _ at hv
  change (∫ z, r z ∂Measure.pi (fun _ : Fin d => π)) ≤ _ at hr
  dsimp only [f, θ] at havg
  linarith

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,hgap,hJ,htv,T), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_squaredRisk_lower
lemma activatedAugmentedMixture_squaredRisk_lower
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (hgap : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|)
    (hJ : 2048 ≤ rareCount η n d q)
    (htv : Causalean.Stat.tvDist
      ((activatedAugmentedMixture η n d q π₀).map (fun s i => (s i).2))
      ((activatedAugmentedMixture η n d q π₁).map (fun s i => (s i).2)) ≤ 1 / 8)
    (T : Estimator n d) :
    (1 / 4096) * ((rareCount η n d q : ℝ) * rareMass η n q) ^ 2 ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          squaredRisk T P.1) () := by
  let := T.toBoundedKernel.2.1
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice h₀
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice h₁
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
    fun_prop
  let := Measure.isProbabilityMeasure_map hf.aemeasurable
    (μ := activatedAugmentedMixture η n d q π₀)
  let := Measure.isProbabilityMeasure_map hf.aemeasurable
    (μ := activatedAugmentedMixture η n d q π₁)
  have hclip : Measurable clip := by unfold clip; fun_prop
  have hm := Causalean.Stat.measurable_kernelMean T.toBoundedKernel.1 hclip
  have hsep : (rareCount η n d q : ℝ) * rareMass η n q / 12 ≤
      |(rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π₁) -
        (rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π₀)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hgap
      (show 0 ≤ (rareCount η n d q : ℝ) * rareMass η n q by positivity)]
  exact activated_fuzzy_risk_lower_of_center_comparison _ _ _ hm _ _ _ _ _
    hJ hb.le hsep htv Integrable.of_finite Integrable.of_finite
    (activatedAugmentedMixture_centered_risk_le_worst η n d q hn hd hb hq hslice h₀ T)
    (activatedAugmentedMixture_centered_risk_le_worst η n d q hn hd hb hq hslice h₁ T)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,hgap,hJ,htv), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_minimaxRisk_lower
lemma activatedAugmentedMixture_minimaxRisk_lower
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (hgap : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|)
    (hJ : 2048 ≤ rareCount η n d q)
    (htv : Causalean.Stat.tvDist
      ((activatedAugmentedMixture η n d q π₀).map (fun s i => (s i).2))
      ((activatedAugmentedMixture η n d q π₁).map (fun s i => (s i).2)) ≤ 1 / 8) :
    (1 / 4096) * ((rareCount η n d q : ℝ) * rareMass η n q) ^ 2 ≤ minimaxRisk n d q := by
  let T₀ : Estimator n d :=
    Estimator.ofMap (fun _ => 0) ⟨measurable_const, by intro s; norm_num⟩
  letI : Nonempty (Estimator n d) := ⟨T₀⟩
  unfold minimaxRisk
  apply Causalean.Stat.le_minimaxValue
  intro T
  exact activatedAugmentedMixture_squaredRisk_lower η n d q hn hd hb hq hslice
    h₀ h₁ hgap hJ htv T

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hslice,π₀,π₁,h₀,h₁,hm,hgap,hJ,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_minimaxRisk_calibrated
lemma activatedAugmentedMixture_minimaxRisk_calibrated
    (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (hm : ∀ v : ℕ, v ≤ lowerDegree n q → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (hgap : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|)
    (hJ : 2048 ≤ rareCount (Real.exp (-32)) n d q)
    (hlarge : Real.exp ((32 - Real.log ((2 : ℝ) / 16)) / 28) ≤ effectiveSize n q) :
    (1 / 4096) * ((rareCount (Real.exp (-32)) n d q : ℝ) *
      rareMass (Real.exp (-32)) n q) ^ 2 ≤ minimaxRisk n d q := by
  have hN : 0 < effectiveSize n q := by unfold effectiveSize; positivity
  have hell : 0 < logScale n q := by
    unfold logScale
    apply Real.log_pos
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hb : 0 < rareMass (Real.exp (-32)) n q := by
    unfold rareMass
    positivity
  let := activatedAugmentedMixture_isProbabilityMeasure (Real.exp (-32)) n d q
    hn hd hb hq hslice h₀
  let := activatedAugmentedMixture_isProbabilityMeasure (Real.exp (-32)) n d q
    hn hd hb hq hslice h₁
  have htv := activation_projected_tv_le_bad_event
    (activatedAugmentedMixture (Real.exp (-32)) n d q π₀)
    (activatedAugmentedMixture (Real.exp (-32)) n d q π₁)
    {s | ∀ x : Fin d, x.val < rareCount (Real.exp (-32)) n d q →
      (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
        if (s i).1 then 1 else 0) ≤ lowerDegree n q}
    (by
      intro s hs
      rw [activatedAugmentedMixture_real_singleton, activatedAugmentedMixture_real_singleton]
      exact activatedAugmentedSample_prior_singleton_eq (Real.exp (-32)) n d q
        hn hd hb hq hslice h₀ h₁ (lowerDegree n q) hm s hs)
    (fun s i => (s i).2) (by fun_prop)
  have htail := activatedAugmentedMixture_cutoff_budget 2 n d q (by norm_num)
    hn hd hq hslice h₀ hlarge
  apply activatedAugmentedMixture_minimaxRisk_lower (Real.exp (-32)) n d q
    hn hd hb hq hslice h₀ h₁ hgap hJ
  exact htv.trans (by simpa only [Set.compl_setOf, show (2 : ℝ) / 16 = 1 / 8 by norm_num] using htail)

end CausalSmith.Stat.MarRareqLogfrontier
