module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationSampleMass

/-! Construct the augmented prior mixture from its averaged atoms, with
normalization and event probabilities derived from the supported experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,J,f), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_pi_integrable
lemma finiteReciprocalPrior_pi_integrable {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (J : ℕ) (f : (Fin J → ℝ) → ℝ) :
    Integrable f (Measure.pi (fun _ : Fin J => π)) := by
  let := hπ.1
  obtain ⟨s, hs, _⟩ := hπ.2
  have hae : ∀ᵐ z ∂π, z ∈ (s : Set ℝ) :=
    (ae_mem_iff_measure_eq s.measurableSet.nullMeasurableSet).2 (by simpa using hs)
  have hprod : ∀ᵐ z ∂Measure.pi (fun _ : Fin J => π), ∀ x, z x ∈ (s : Set ℝ) := by
    rw [ae_all_iff]
    intro x
    exact Measure.tendsto_eval_ae_ae.eventually hae
  have hfinite : {z : Fin J → ℝ | ∀ x, z x ∈ (s : Set ℝ)}.Finite :=
    Set.Finite.pi' (fun _ => s.finite_toSet)
  have hres : (Measure.pi (fun _ : Fin J => π)).restrict
      {z : Fin J → ℝ | ∀ x, z x ∈ (s : Set ℝ)} =
        Measure.pi (fun _ : Fin J => π) :=
    Measure.restrict_eq_self_of_ae_mem hprod
  have hi : IntegrableOn f {z : Fin J → ℝ | ∀ x, z x ∈ (s : Set ℝ)}
      (Measure.pi (fun _ : Fin J => π)) := IntegrableOn.of_finite hfinite
  simpa only [IntegrableOn, hres] using hi

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,π), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activatedAugmentedMixture
noncomputable def activatedAugmentedMixture (η : ℝ) (n d : ℕ) (q : ℝ)
    (π : Measure ℝ) : Measure (Fin n → Bool × ObsRecord d) :=
  ∑ s, ENNReal.ofReal (∫ z, (activatedAugmentedSample η n d q z).real {s}
    ∂Measure.pi (fun _ : Fin d => π)) • Measure.dirac s

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,π,s), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_real_singleton
lemma activatedAugmentedMixture_real_singleton (η : ℝ) (n d : ℕ) (q : ℝ)
    (π : Measure ℝ) (s : Fin n → Bool × ObsRecord d) :
    (activatedAugmentedMixture η n d q π).real {s} =
      ∫ z, (activatedAugmentedSample η n d q z).real {s}
        ∂Measure.pi (fun _ : Fin d => π) := by
  classical
  unfold activatedAugmentedMixture Measure.real
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => measureReal_nonneg))

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_isProbabilityMeasure
lemma activatedAugmentedMixture_isProbabilityMeasure (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    IsProbabilityMeasure (activatedAugmentedMixture η n d q π) := by
  classical
  let := hπ.1
  have hsum : (∑ s : Fin n → Bool × ObsRecord d,
      ∫ z, (activatedAugmentedSample η n d q z).real {s}
        ∂Measure.pi (fun _ : Fin d => π)) = 1 := by
    rw [← integral_finsetSum _ (fun s _ => finiteReciprocalPrior_pi_integrable hπ d _)]
    calc
      (∫ z, ∑ s : Fin n → Bool × ObsRecord d,
          (activatedAugmentedSample η n d q z).real {s}
          ∂Measure.pi (fun _ : Fin d => π)) = ∫ _z, (1 : ℝ)
            ∂Measure.pi (fun _ : Fin d => π) := by
        apply integral_congr_ae
        filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
        rw [activatedAugmentedSample, dif_pos hz]
        let := augmentedOneRecord_isProbabilityMeasure η n d q z hn hd hb hq hslice hz
        rw [sum_measureReal_singleton]
        simp
      _ = 1 := by simp
  constructor
  unfold activatedAugmentedMixture
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun s _ => integral_nonneg (fun _ => measureReal_nonneg)), hsum]
  simp

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,A), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_real_event
lemma activatedAugmentedMixture_real_event (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (A : Set (Fin n → Bool × ObsRecord d)) :
    (activatedAugmentedMixture η n d q π).real A =
      ∫ z, (activatedAugmentedSample η n d q z).real A
        ∂Measure.pi (fun _ : Fin d => π) := by
  classical
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice hπ
  rw [← Set.coe_toFinset A, ← sum_measureReal_singleton]
  simp_rw [activatedAugmentedMixture_real_singleton]
  rw [← integral_finsetSum _ (fun s _ => finiteReciprocalPrior_pi_integrable hπ d _)]
  apply integral_congr_ae
  filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
  rw [activatedAugmentedSample, dif_pos hz]
  let := augmentedOneRecord_isProbabilityMeasure η n d q z hn hd hb hq hslice hz
  exact sum_measureReal_singleton _

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j'), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_grid_tv_le_bad_event
lemma activatedAugmentedMixture_grid_tv_le_bad_event (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1)) :
    Causalean.Stat.tvDist
      (activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M)))
      (activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M))) ≤
      (activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).real
        {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
          (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
            if (s i).1 then 1 else 0) ≤ K} := by
  have hgrid := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice
    (hgrid j).1
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice
    (hgrid j').1
  exact activatedAugmentedSample_grid_tv_le_bad_event η n d q hn hd hb hq hslice
    h₀ h₁ K hm M hM j j' _ _
    (activatedAugmentedMixture_real_singleton η n d q _)
    (activatedAugmentedMixture_real_singleton η n d q _)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,A), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_projected_real_event
lemma activatedAugmentedMixture_projected_real_event (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (A : Set (Fin n → ObsRecord d)) :
    ((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2)).real A =
      ∫ z, (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        (sampleLaw n (activatedFullLaw η n d q z hd hb hq hslice hz)).real A
        else 0) ∂Measure.pi (fun _ : Fin d => π) := by
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
    fun_prop
  have hA : MeasurableSet A := A.toFinite.measurableSet
  rw [map_measureReal_apply hf hA,
    activatedAugmentedMixture_real_event η n d q hn hd hb hq hslice hπ]
  apply integral_congr_ae
  filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
  rw [dif_pos hz, activatedAugmentedSample, dif_pos hz]
  rw [← activated_sample_projection η n d q z hn hd hb hq hslice hz,
    map_measureReal_apply hf hA]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j'), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_projected_grid_tv_le_bad_event
lemma activatedAugmentedMixture_projected_grid_tv_le_bad_event
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1)) :
    Causalean.Stat.tvDist
      ((activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).map (fun s i => (s i).2))
      ((activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M))).map (fun s i => (s i).2)) ≤
      (activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).real
        {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
          (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
            if (s i).1 then 1 else 0) ≤ K} := by
  have hgrid := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice
    (hgrid j).1
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice
    (hgrid j').1
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
    fun_prop
  apply activation_projected_tv_le_bad_event _ _ _ _ _ hf
  intro s hs
  rw [activatedAugmentedMixture_real_singleton, activatedAugmentedMixture_real_singleton]
  exact activatedAugmentedSample_grid_singleton_eq η n d q hn hd hb hq hslice
    h₀ h₁ K hm M hM j j' s hs

end CausalSmith.Stat.MarRareqLogfrontier
