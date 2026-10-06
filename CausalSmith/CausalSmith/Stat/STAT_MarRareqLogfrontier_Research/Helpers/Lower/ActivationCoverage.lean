module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalNeighborhood
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationIntervalTransfer
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationTail

/-! Uniform honesty transfers to neighborhood hits in the actual activated
prior mixture. The target concentration budget is kept separate from coverage,
so equations (13)--(16) and the minimax reduction are assembled without
assuming averaged honesty. The actual activation-cutoff tail remains a
separate input to the lower-bound assembly. -/

public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:t,θ,w,hnear), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalContains_subset_neighborhood
lemma intervalContains_subset_neighborhood (t θ w : ℝ) (hnear : |t - θ| ≤ w) :
    {I : ConnectedInterval | intervalContains I t} ⊆
      {I | ∃ x : ℝ, I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w} := by
  intro I hI
  have hlo : I.lo ≤ t := by
    have h := hI.1
    change (if I.closedLeft then I.lo ≤ t else I.lo < t) at h
    split at h
    · exact h
    · exact h.le
  have hhi : t ≤ I.hi := by
    have h := hI.2
    change (if I.closedRight then t ≤ I.hi else t < I.hi) at h
    split at h
    · exact h
    · exact h.le
  exact ⟨t, hlo, hhi, hnear⟩

/-- Given [the specified inputs and assumptions](hyp:n,d,T,μ,A,hA), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalProcedure_real_event
lemma intervalProcedure_real_event {n d : ℕ} (T : IntervalProcedure n d)
    (μ : Measure (Fin n → ObsRecord d)) [IsProbabilityMeasure μ]
    (A : Set ConnectedInterval) (hA : MeasurableSet A) :
    (T.1 ∘ₘ μ).real A = ∫ s, (T.1 s).real A ∂μ := by
  let := T.2
  rw [measureReal_def, Measure.bind_apply hA T.1.aemeasurable, ←
    integral_toReal (T.1.measurable_coe hA).aemeasurable
      (Filter.Eventually.of_forall fun s =>
        (lt_top_iff_ne_top).2 (measure_ne_top (T.1 s) A))]
  rfl

/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,T,hT,hα,P,hP,θ,w), [the stated mathematical conclusion holds](goal). -/
-- @node: honestInterval_neighborhood_coverage
lemma honestInterval_neighborhood_coverage {n d : ℕ} {q α : ℝ}
    (T : IntervalProcedure n d) (hT : HonestInterval n d q α T)
    (hα : 0 ≤ α) (P : FullLaw d) (hP : RareArrivalModelClass n d q P)
    (θ w : ℝ) :
    1 - α - (if w < |ate P - θ| then 1 else 0) ≤
      ∫ s, (T.1 s).real {I | ∃ x : ℝ,
        I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w} ∂sampleLaw n P := by
  classical
  let := T.2
  let := P.2
  let : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    let : IsProbabilityMeasure (P.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    infer_instance
  by_cases hbad : w < |ate P - θ|
  · simp only [if_pos hbad]
    have hnonneg : 0 ≤ ∫ s, (T.1 s).real {I | ∃ x : ℝ,
        I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w} ∂sampleLaw n P :=
      integral_nonneg (fun _ => measureReal_nonneg)
    linarith
  · simp only [if_neg hbad, sub_zero]
    apply (hT P hP).trans
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro s
    exact measureReal_mono (intervalContains_subset_neighborhood (ate P) θ w
      (le_of_not_gt hbad)) (measure_ne_top (T.1 s) _)

/-- Given [the specified inputs and assumptions](hyp:π,d,J,hJ), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalPrior_initial_coordinates_map
lemma intervalPrior_initial_coordinates_map {π : Measure ℝ} [IsProbabilityMeasure π]
    (d J : ℕ) (hJ : J ≤ d) :
    (Measure.pi (fun _ : Fin d => π)).map
      (fun z : Fin d → ℝ => fun x : Fin J => z (x.castLE hJ)) =
        Measure.pi (fun _ : Fin J => π) := by
  have hind : iIndepFun (fun x : Fin d => fun z : Fin d → ℝ => z x)
      (Measure.pi (fun _ : Fin d => π)) :=
    iIndepFun_pi (X := fun _ (z : ℝ) => z) (fun _ => measurable_id.aemeasurable)
  have hrestrict := hind.precomp (Fin.castLE_injective hJ)
  rw [hrestrict.map_fun_eq_pi_map (fun x => (measurable_pi_apply _).aemeasurable)]
  simp_rw [(measurePreserving_eval (fun _ : Fin d => π) _).map_eq]

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,d,J,M,hJd,b,Δ,u,hb,hΔ,hu,hM,hgap,hJ), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalPrior_full_alphabet_concentration_budget
lemma intervalPrior_full_alphabet_concentration_budget {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (d J M : ℕ) (hJd : J ≤ d)
    (b Δ u : ℝ) (hb : 0 < b) (hΔ : 0 < Δ) (hu : 0 < u) (hM : 1 ≤ M)
    (hgap : (J : ℝ) * b / 12 ≤ Δ)
    (hJ : 18432 * (M : ℝ) ^ 2 / u ≤ (J : ℝ)) :
    (Measure.pi (fun _ : Fin d => π)).real
      {z | Δ / (8 * M) < |b * (∑ x : Fin d,
        if x.val < J then (z x)⁻¹ else 0) - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} ≤ u / 8 := by
  let := hπ.1
  let restrict : (Fin d → ℝ) → (Fin J → ℝ) :=
    fun z x => z (x.castLE hJd)
  have hr : Measurable restrict := by fun_prop
  have hevent : MeasurableSet {z : Fin J → ℝ | Δ / (8 * M) <
      |intervalPriorTarget J b z - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} := by
    have hf : Measurable (intervalPriorTarget J b) := by
      unfold intervalPriorTarget
      fun_prop
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      (measurableSet_lt measurable_const (measurable_norm.comp (hf.sub_const _)))
  have hmap := intervalPrior_initial_coordinates_map d J hJd (π := π)
  have hprob := map_measureReal_apply (μ := Measure.pi (fun _ : Fin d => π)) hr hevent
  rw [hmap] at hprob
  have htail := intervalPriorTarget_concentration_budget hπ J M b Δ u hb hΔ hu hM hgap hJ
  rw [hprob] at htail
  simpa only [Set.preimage_ofPred_eq, intervalPriorTarget,
    activation_sum_initial_cells d J hJd, restrict] using htail

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,α,θ,w,ε,hn,hd,hb,hq,hslice,π,hπ,T,hT,hα,htail), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_neighborhood_coverage
lemma activatedAugmentedMixture_neighborhood_coverage
    (η : ℝ) (n d : ℕ) (q α θ w ε : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (T : IntervalProcedure n d) (hT : HonestInterval n d q α T) (hα : 0 ≤ α)
    (htail : (Measure.pi (fun _ : Fin d => π)).real
      {z | w < |rareMass η n q * (∑ x : Fin d,
        if x.val < rareCount η n d q then (z x)⁻¹ else 0) - θ|} ≤ ε) :
    1 - α - ε ≤
      ∫ s, (T.1 s).real {I | ∃ x : ℝ,
        I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w}
        ∂((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2)) := by
  classical
  let := hπ.1
  let μ := Measure.pi (fun _ : Fin d => π)
  let target : (Fin d → ℝ) → ℝ := fun z => rareMass η n q *
    ∑ x : Fin d, if x.val < rareCount η n d q then (z x)⁻¹ else 0
  let bad : Set (Fin d → ℝ) := {z | w < |target z - θ|}
  have hmeas : Measurable target := by
    dsimp [target]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro x hx
    by_cases h : x.val < rareCount η n d q <;> simp only [h, if_true, if_false]
    · fun_prop
    · fun_prop
  have hbad : MeasurableSet bad := by
    simpa only [bad, Function.comp_def, Real.norm_eq_abs] using
      (measurableSet_lt measurable_const (measurable_norm.comp (hmeas.sub_const θ)))
  rw [activatedAugmentedMixture_projected_integral η n d q hn hd hb hq hslice hπ]
  have hle : ∀ᵐ z ∂μ, 1 - α - bad.indicator (fun _ => (1 : ℝ)) z ≤
      (if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
        ∫ s, (T.1 s).real {I | ∃ x : ℝ,
          I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w}
          ∂sampleLaw n (activatedFullLaw η n d q z hd hb hq hslice hz)
        else 0) := by
    filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
    rw [dif_pos hz]
    have htarget : ate (activatedFullLaw η n d q z hd hb hq hslice hz) = target z := by
      change (∫ r : FullRecord d,
        ((if r.Y1 then (1 : ℝ) else 0) - (if r.Y0 then (1 : ℝ) else 0))
          ∂activatedLaw η n d q z hz) = target z
      exact activatedLaw_target_integral η n d q z hb hq hslice hz
    have h := honestInterval_neighborhood_coverage T hT hα
      (activatedFullLaw η n d q z hd hb hq hslice hz)
      (activatedFullLaw_model η n d q z hd hb hq hslice hz hn) θ w
    simpa only [htarget, Set.indicator_apply, Set.mem_ofPred_eq, bad, Pi.one_apply]
      using h
  have hbound := integral_mono_ae (finiteReciprocalPrior_pi_integrable hπ d _)
    (finiteReciprocalPrior_pi_integrable hπ d _) hle
  have heq : (∫ z, 1 - α - bad.indicator (fun _ => (1 : ℝ)) z ∂μ) =
      1 - α - μ.real bad := by
    rw [integral_sub (integrable_const _) (finiteReciprocalPrior_pi_integrable hπ d _),
      integral_const, integral_indicator_const 1 hbad]
    simp [μ]
  rw [heq] at hbound
  exact (sub_le_sub_left htail (1 - α)).trans hbound

/-- Given [the specified inputs and assumptions](hyp:η,n,d,M,q,α,Δ,hn,hd,hb,hq,hslice,π,hπ,T,hT,hα,hα1,hΔ,hM,hgap,hJ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_neighborhood_coverage_budget
lemma activatedAugmentedMixture_neighborhood_coverage_budget
    (η : ℝ) (n d M : ℕ) (q α Δ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (T : IntervalProcedure n d) (hT : HonestInterval n d q α T)
    (hα : 0 ≤ α) (hα1 : α < 1) (hΔ : 0 < Δ) (hM : 1 ≤ M)
    (hgap : (rareCount η n d q : ℝ) * rareMass η n q / 12 ≤ Δ)
    (hJ : 18432 * (M : ℝ) ^ 2 / (1 - α) ≤ (rareCount η n d q : ℝ)) :
    7 * (1 - α) / 8 ≤
      (T.1 ∘ₘ ((activatedAugmentedMixture η n d q π).map
        (fun s i => (s i).2))).real {I | ∃ x : ℝ,
          I.lo ≤ x ∧ x ≤ I.hi ∧
            |x - ((rareCount η n d q : ℝ) * rareMass η n q * ∫ z, z⁻¹ ∂π)| ≤
              Δ / (8 * M)} := by
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice hπ
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
    fun_prop
  let := Measure.isProbabilityMeasure_map hf.aemeasurable
    (μ := activatedAugmentedMixture η n d q π)
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  rw [intervalProcedure_real_event T _ _
    (connectedInterval_measurableSet_neighborhood _ _ (by positivity))]
  have htail := intervalPrior_full_alphabet_concentration_budget hπ d
    (rareCount η n d q) M ((min_le_left _ _).trans (Nat.sub_le d 1))
    (rareMass η n q) Δ (1 - α) hb hΔ (by linarith) hM hgap hJ
  have h := activatedAugmentedMixture_neighborhood_coverage η n d q α
    ((rareCount η n d q : ℝ) * rareMass η n q * ∫ z, z⁻¹ ∂π)
    (Δ / (8 * M)) ((1 - α) / 8) hn hd hb hq hslice hπ T hT hα htail
  convert h using 1
  ring


/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,T), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_reported_length_le_worst
lemma activatedAugmentedMixture_reported_length_le_worst
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (T : IntervalProcedure n d) :
    (∫ I : ConnectedInterval, I.hi - I.lo ∂(T.1 ∘ₘ
      ((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2)))) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          intervalRisk T P.1) () := by
  let := T.2
  let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice hπ
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
    fun_prop
  let := Measure.isProbabilityMeasure_map hf.aemeasurable
    (μ := activatedAugmentedMixture η n d q π)
  have hF : Measurable (fun I : ConnectedInterval =>
      (I.lo, I.hi, I.closedLeft, I.closedRight)) := by
    exact (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_const.prodMk measurable_const))
  have hlen : Measurable (fun I : ConnectedInterval => I.hi - I.lo) := by
    first
    | fun_prop
    | exact (measurable_connectedInterval_hi).sub
        (measurable_connectedInterval_lo)
  have hint : Integrable (fun I : ConnectedInterval => I.hi - I.lo)
      (T.1 ∘ₘ ((activatedAugmentedMixture η n d q π).map (fun s i => (s i).2))) :=
    Integrable.of_bound hlen.aestronglyMeasurable 2
      (Eventually.of_forall fun I => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr I.ordered)]
        linarith [I.lower, I.upper])
  rw [Causalean.Mathlib.MeasureTheory.integral_bind T.1.measurable hint]
  exact activatedAugmentedMixture_intervalRisk_le_worst η n d q hn hd hb hq hslice hπ T

/-- Given [the specified inputs and assumptions](hyp:η,n,d,M,q,α,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,hgap,hα,hα1,hM,hgrid,hJ,htv,T,hT), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_grid_length_le_worst
lemma activatedAugmentedMixture_grid_length_le_worst
    (η : ℝ) (n d M : ℕ) (q α : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (hgap : 1 / 12 ≤ (∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)
    (hα : 0 ≤ α) (hα1 : α < 1) (hM : 1 ≤ M)
    (hgrid : 8 / (1 - α) ≤ (M : ℝ))
    (hJ : 18432 * (M : ℝ) ^ 2 / (1 - α) ≤ (rareCount η n d q : ℝ))
    (htv : ∀ j : Fin (M + 1), Causalean.Stat.tvDist
      ((activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((0 : ℝ) / M))).map (fun s i => (s i).2))
      ((activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).map (fun s i => (s i).2)) ≤
          (1 - α) / 16)
    (T : IntervalProcedure n d) (hT : HonestInterval n d q α T) :
    (21 * (1 - α) / 32) * ((rareCount η n d q : ℝ) * rareMass η n q *
      ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          intervalRisk T P.1) () := by
  let J : ℝ := rareCount η n d q
  let b := rareMass η n q
  let Δ := J * b * ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)
  let θ := J * b * ∫ z, z⁻¹ ∂π₀
  let Q : Fin (M + 1) → Measure (Fin n → ObsRecord d) := fun j =>
    (activatedAugmentedMixture η n d q
      (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).map (fun s i => (s i).2)
  let ν : Fin (M + 1) → Measure ConnectedInterval := fun j => T.1 ∘ₘ Q j
  have hpriors := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  let := T.2
  have hQ (j : Fin (M + 1)) : IsProbabilityMeasure (Q j) := by
    let := activatedAugmentedMixture_isProbabilityMeasure η n d q hn hd hb hq hslice
      (hpriors j).1
    apply Measure.isProbabilityMeasure_map
    have hf : Measurable (fun s : Fin n → Bool × ObsRecord d => fun i => (s i).2) := by
      fun_prop
    exact hf.aemeasurable
  have hν (j : Fin (M + 1)) : IsProbabilityMeasure (ν j) := by
    dsimp [ν]
    infer_instance
  have hu : 0 < 1 - α := by linarith
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hJpos : 0 < J := lt_of_lt_of_le (by positivity) hJ
  have hΔ : 0 < Δ := by dsimp [Δ, b]; positivity
  have hΔgap : J * b / 12 ≤ Δ := by
    dsimp [Δ]
    nlinarith [mul_le_mul_of_nonneg_left hgap (mul_nonneg hJpos.le hb.le)]
  have hlength := connectedInterval_many_prior_length_floor (ν 0) M ν θ Δ (1 - α)
    hΔ hu hgrid (fun j => ?_) (fun j => ?_)
  · exact hlength.trans (activatedAugmentedMixture_reported_length_le_worst η n d q
      hn hd hb hq hslice (hpriors 0).1 T)
  · have h := activatedAugmentedMixture_neighborhood_coverage_budget η n d M q α Δ
      hn hd hb hq hslice (hpriors j).1 T hT hα hα1 hΔ hM hΔgap hJ
    have hcenter : J * b * (∫ z, z⁻¹ ∂intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M)) =
        θ + (j : ℝ) * (Δ / M) := by
      rw [(hpriors j).2.2]
      dsimp [θ, Δ]
      ring
    change 7 * (1 - α) / 8 ≤ (ν j).real {I | ∃ x : ℝ,
      I.lo ≤ x ∧ x ≤ I.hi ∧
      |x - (J * b * ∫ z, z⁻¹ ∂intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))| ≤
        Δ / (8 * M)} at h
    rw [hcenter] at h
    exact h
  · exact (Causalean.Stat.tvDist_bind_le (Q 0) (Q j) T.1).trans (by simpa [Q] using htv j)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,hα), [the stated mathematical conclusion holds](goal). -/
-- @node: honestInterval_nonempty
lemma honestInterval_nonempty (n d : ℕ) (q α : ℝ) (hα : 0 ≤ α) :
    Nonempty {T : IntervalProcedure n d // HonestInterval n d q α T} := by
  let I : ConnectedInterval := ⟨(-1, 1), by norm_num, by norm_num, by norm_num⟩
  let T : IntervalProcedure n d := ⟨Kernel.const _ (Measure.dirac I), inferInstance⟩
  refine ⟨⟨T, ?_⟩⟩
  intro P hP
  let := P.2
  let := Measure.isProbabilityMeasure_map (show Measurable obs by fun_prop).aemeasurable
    (μ := P.1)
  letI : IsProbabilityMeasure (sampleLaw n P) := by unfold sampleLaw; infer_instance
  have hmem : I ∈ {I | intervalContains I (ate P)} := by
    exact ate_mem_unit_interval P
  have heq (s : Fin n → ObsRecord d) :
      (T.1 s).real {I | intervalContains I (ate P)} = 1 := by
    rw [Kernel.const_apply, Measure.real, Measure.dirac_apply_of_mem hmem]
    simp
  simp_rw [heq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith

/-- Given [the specified inputs and assumptions](hyp:η,n,d,M,q,α,hn,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,K,hm,hgap,hα,hα1,hM,hgrid,hJ,hbad), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_interval_minimax_of_cutoff
lemma activatedAugmentedMixture_interval_minimax_of_cutoff
    (η : ℝ) (n d M : ℕ) (q α : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (hgap : 1 / 12 ≤ (∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)
    (hα : 0 ≤ α) (hα1 : α < 1) (hM : 1 ≤ M)
    (hgrid : 8 / (1 - α) ≤ (M : ℝ))
    (hJ : 18432 * (M : ℝ) ^ 2 / (1 - α) ≤ (rareCount η n d q : ℝ))
    (hbad : (activatedAugmentedMixture η n d q
      (intervalInterpolatedPrior π₀ π₁ ((0 : ℝ) / M))).real
        {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
          (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
            if (s i).1 then 1 else 0) ≤ K} ≤ (1 - α) / 16) :
    (21 * (1 - α) / 32) * ((rareCount η n d q : ℝ) * rareMass η n q *
      ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀)) ≤ intervalLengthRisk n d q α := by
  have htv (j : Fin (M + 1)) :=
    activatedAugmentedMixture_projected_grid_tv_le_bad_event η n d q hn hd hb hq hslice
      h₀ h₁ K hm M hM 0 j
  have htvbudget (j : Fin (M + 1)) : Causalean.Stat.tvDist
      ((activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((0 : ℝ) / M))).map (fun s i => (s i).2))
      ((activatedAugmentedMixture η n d q
        (intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).map (fun s i => (s i).2)) ≤
          (1 - α) / 16 := by
    simpa only [Fin.val_zero, Nat.cast_zero] using (htv j).trans
      (by simpa only [Fin.val_zero, Nat.cast_zero] using hbad)
  letI := honestInterval_nonempty n d q α hα
  unfold intervalLengthRisk
  apply Causalean.Stat.le_minimaxValue
  intro T
  exact activatedAugmentedMixture_grid_length_le_worst η n d M q α hn hd hb hq hslice
    h₀ h₁ K hm hgap hα hα1 hM hgrid hJ htvbudget T.1 T.2

end CausalSmith.Stat.MarRareqLogfrontier
