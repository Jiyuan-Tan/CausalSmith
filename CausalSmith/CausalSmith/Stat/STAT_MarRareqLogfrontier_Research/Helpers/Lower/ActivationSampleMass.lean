module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationProbability
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationSampleLikelihood
public import Causalean.Stat.Minimax.TotalVariation

/-! Atomic probabilities of the actual augmented fixed-horizon experiment and
matched-prior cancellation on the activation cutoff event in equation (6). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hz,r), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_singleton
lemma augmentedOneRecord_singleton (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))
    (r : Bool × ObsRecord d) :
    augmentedOneRecord η n d q z hz {r} =
      if r.2.S then 0 else
        ENNReal.ofReal (baselineMass η n d q r.2.X / 2 *
          bernWeight (q * lowerEndpoint n q) r.1 *
          augmentedOutcomeWeight η n d q z r.2.X r.2.A r.1 r.2.R r.2.RY) := by
  classical
  rcases r with ⟨flag, x, a, s, arrival, one⟩
  simp only [augmentedOneRecord, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply, Prod.mk.injEq, ObsRecord.mk.injEq]
  simp only [mul_ite, mul_one, mul_zero, ite_and]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
    Finset.sum_const_zero]


/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hb,hq,hslice,hz,r), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_weight_nonneg
lemma augmentedOneRecord_weight_nonneg (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))
    (r : Bool × ObsRecord d) :
    0 ≤ baselineMass η n d q r.2.X / 2 *
      bernWeight (q * lowerEndpoint n q) r.1 *
      augmentedOutcomeWeight η n d q z r.2.X r.2.A r.1 r.2.R r.2.RY := by
  have hH : 0 ≤ lowerEndpoint n q := by unfold lowerEndpoint; positivity
  have hp : 0 ≤ q * lowerEndpoint n q ∧ q * lowerEndpoint n q ≤ 1 :=
    ⟨mul_nonneg hq.le hH, lower_activation_probability_le_one n q hq.le hslice⟩
  have hbern : 0 ≤ bernWeight (q * lowerEndpoint n q) r.1 := by
    cases r.1 <;> simp [bernWeight] <;> linarith [hp.1, hp.2]
  exact mul_nonneg
    (mul_nonneg (div_nonneg (baselineMass_nonneg η n d q hb r.2.X) (by norm_num))
      hbern)
    (augmentedOutcomeWeight_nonneg η n d q z _ _ _ _ _ (hz r.2.X))

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hb,hq,hslice,hz,r), [the stated mathematical conclusion holds](goal). -/
-- @node: augmentedOneRecord_real_singleton
lemma augmentedOneRecord_real_singleton (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))
    (r : Bool × ObsRecord d) :
    (augmentedOneRecord η n d q z hz).real {r} =
      if r.2.S then 0 else
        baselineMass η n d q r.2.X / 2 * bernWeight (q * lowerEndpoint n q) r.1 *
          augmentedOutcomeWeight η n d q z r.2.X r.2.A r.1 r.2.R r.2.RY := by
  rw [Measure.real, augmentedOneRecord_singleton]
  split_ifs
  · simp
  · exact ENNReal.toReal_ofReal
      (augmentedOneRecord_weight_nonneg η n d q z hb hq hslice hz r)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hn,hd,hb,hq,hslice,hz,s), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_sample_real_singleton
lemma activated_sample_real_singleton (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hb : 0 < rareMass η n q) (hq : 0 < q) (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))
    (s : Fin n → Bool × ObsRecord d) :
    (Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz)).real {s} =
      ∏ i, if (s i).2.S then 0 else
        baselineMass η n d q (s i).2.X / 2 *
          bernWeight (q * lowerEndpoint n q) (s i).1 *
          augmentedOutcomeWeight η n d q z (s i).2.X (s i).2.A (s i).1
            (s i).2.R (s i).2.RY := by
  let := augmentedOneRecord_isProbabilityMeasure η n d q z hn hd hb hq hslice hz
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ =>
    augmentedOneRecord_real_singleton η n d q z hb hq hslice hz (s i))

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activatedAugmentedSample
noncomputable def activatedAugmentedSample (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) : Measure (Fin n → Bool × ObsRecord d) :=
  if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
    Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz)
  else 0

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,s), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedSample_prior_singleton
lemma activatedAugmentedSample_prior_singleton (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q)
    {π : Measure ℝ} (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (s : Fin n → Bool × ObsRecord d) :
    (∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => π)) =
      if ∀ i, (s i).2.S = false then
        ∫ z, ∏ i, (baselineMass η n d q (s i).2.X / 2 *
          bernWeight (q * lowerEndpoint n q) (s i).1 *
          augmentedOutcomeWeight η n d q z (s i).2.X (s i).2.A (s i).1
            (s i).2.R (s i).2.RY) ∂Measure.pi (fun _ : Fin d => π)
      else 0 := by
  classical
  by_cases hs : ∀ i, (s i).2.S = false
  · rw [if_pos hs]
    apply integral_congr_ae
    filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
    rw [activatedAugmentedSample, dif_pos hz,
      activated_sample_real_singleton η n d q z hn hd hb hq hslice hz]
    exact Finset.prod_congr rfl (fun i _ => by simp only [hs i, Bool.false_eq_true, if_false])
  · rw [if_neg hs]
    calc
      (∫ z, (activatedAugmentedSample η n d q z).real {s}
        ∂Measure.pi (fun _ : Fin d => π)) = ∫ _z, (0 : ℝ)
          ∂Measure.pi (fun _ : Fin d => π) := by
        apply integral_congr_ae
        filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
        rw [activatedAugmentedSample, dif_pos hz,
          activated_sample_real_singleton η n d q z hn hd hb hq hslice hz]
        obtain ⟨i, hi⟩ := not_forall.mp hs
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        have hi' : (s i).2.S = true := by cases h : (s i).2.S <;> simp_all
        simp only [hi', if_true]
      _ = 0 := by simp

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,s,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedSample_prior_singleton_eq
lemma activatedAugmentedSample_prior_singleton_eq (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (s : Fin n → Bool × ObsRecord d)
    (hcount : ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
        if (s i).1 then 1 else 0) ≤ K) :
    (∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => π₀)) =
    ∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => π₁) := by
  rw [activatedAugmentedSample_prior_singleton η n d q hn hd hb hq hslice h₀,
    activatedAugmentedSample_prior_singleton η n d q hn hd hb hq hslice h₁]
  split_ifs
  · exact activationSampleWeight_integral_eq Finset.univ η n d q
      (fun i => (s i).2.X) h₀ h₁ K hm
      (fun i => (s i).2.A) (fun i => (s i).1)
      (fun i => (s i).2.R) (fun i => (s i).2.RY) hcount
  · rfl

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j',s,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedSample_grid_singleton_eq
lemma activatedAugmentedSample_grid_singleton_eq (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1))
    (s : Fin n → Bool × ObsRecord d)
    (hcount : ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
        if (s i).1 then 1 else 0) ≤ K) :
    (∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))) =
    ∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M)) := by
  have hgrid := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  exact activatedAugmentedSample_prior_singleton_eq η n d q hn hd hb hq hslice
    (hgrid j).1 (hgrid j').1 K ((hgrid j).2.1 j') s hcount

/-- Given [the specified inputs and assumptions](hyp:Ω,μ,ν,G,A,hatom), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_good_event_real_eq
lemma activation_good_event_real_eq {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G A : Set Ω) (hatom : ∀ s ∈ G, μ.real {s} = ν.real {s}) :
    μ.real (A ∩ G) = ν.real (A ∩ G) := by
  classical
  rw [← Set.coe_toFinset (A ∩ G), ← sum_measureReal_singleton,
    ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl (fun s hs => hatom s (Set.mem_toFinset.mp hs).2)

/-- Given [the specified inputs and assumptions](hyp:Ω,μ,ν,G,hatom), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_tv_le_bad_event
lemma activation_tv_le_bad_event {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set Ω) (hatom : ∀ s ∈ G, μ.real {s} = ν.real {s}) :
    Causalean.Stat.tvDist μ ν ≤ μ.real Gᶜ := by
  classical
  have hG : MeasurableSet G := G.toFinite.measurableSet
  have hgood : μ.real G = ν.real G := by
    simpa using activation_good_event_real_eq μ ν G Set.univ hatom
  have hbad : μ.real Gᶜ = ν.real Gᶜ := by
    rw [measureReal_compl hG, measureReal_compl hG, probReal_univ,
      probReal_univ, hgood]
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hsplit (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      ρ.real A = ρ.real (A ∩ G) + ρ.real (A ∩ Gᶜ) := by
    rw [← measureReal_union (Set.disjoint_left.mpr (by
      intro s hs ht
      exact ht.2 hs.2)) (hA.inter hG.compl)]
    congr 1
    exact (Set.inter_union_compl A G).symm
  rw [hsplit μ, hsplit ν, activation_good_event_real_eq μ ν G A hatom]
  have hμ := measureReal_mono (μ := μ) (Set.inter_subset_right : A ∩ Gᶜ ⊆ Gᶜ)
  have hν := measureReal_mono (μ := ν) (Set.inter_subset_right : A ∩ Gᶜ ⊆ Gᶜ)
  rw [← hbad] at hν
  have hμ0 : 0 ≤ μ.real (A ∩ Gᶜ) := measureReal_nonneg
  have hν0 : 0 ≤ ν.real (A ∩ Gᶜ) := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- Given [the specified inputs and assumptions](hyp:Ω,Ξ,μ,ν,G,hatom,f,hf), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_projected_tv_le_bad_event
lemma activation_projected_tv_le_bad_event {Ω Ξ : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [MeasurableSpace Ξ]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set Ω) (hatom : ∀ s ∈ G, μ.real {s} = ν.real {s})
    (f : Ω → Ξ) (hf : Measurable f) :
    Causalean.Stat.tvDist (μ.map f) (ν.map f) ≤ μ.real Gᶜ := by
  have htv := activation_tv_le_bad_event μ ν G hatom
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  rw [map_measureReal_apply hf hA, map_measureReal_apply hf hA]
  exact (Causalean.Stat.abs_measureReal_sub_le_tvDist (hf hA)).trans htv

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j',Q,Q',hQ,hQ'), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedSample_grid_tv_le_bad_event
lemma activatedAugmentedSample_grid_tv_le_bad_event (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1))
    (Q Q' : Measure (Fin n → Bool × ObsRecord d))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hQ : ∀ s, Q.real {s} = ∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M)))
    (hQ' : ∀ s, Q'.real {s} = ∫ z, (activatedAugmentedSample η n d q z).real {s}
      ∂Measure.pi (fun _ : Fin d => intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M))) :
    Causalean.Stat.tvDist Q Q' ≤ Q.real
      {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
        (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
          if (s i).1 then 1 else 0) ≤ K} := by
  apply activation_tv_le_bad_event
  intro s hs
  rw [hQ s, hQ' s]
  exact activatedAugmentedSample_grid_singleton_eq η n d q hn hd hb hq hslice
    h₀ h₁ K hm M hM j j' s hs

end CausalSmith.Stat.MarRareqLogfrontier
