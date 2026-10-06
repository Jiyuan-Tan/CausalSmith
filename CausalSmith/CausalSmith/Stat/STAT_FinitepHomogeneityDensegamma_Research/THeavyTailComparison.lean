module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TBoundedSubmodelComparison
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TOriginalRecordAttainableRate
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TTailEssentialFullRecordConverse
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TWholeNullCalibrationResolved

/-! Finite-moment homogeneity testing: THeavyTailComparison. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Frontiercompactuniformity: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def FrontierCompactUniformity : Prop :=
  (∀ K : Set Params, IsCompact K → (∀ v ∈ K, v.Valid) → ∃ c C N : ℝ, 0 < c ∧
    ∀ v ∈ K, c ≤ cLower v ∧ CAtt v ≤ C ∧ (NAtt v:ℝ) ≤ N) ∧
  (∀ K : Set Smooth3, IsCompact K → (∀ w ∈ K, w.Valid) → ∃ c C N : ℝ, 0 < c ∧
    ∀ w ∈ K, c ≤ cLowerBounded w ∧ CAttBounded w ≤ C ∧ (NAttBounded w:ℝ) ≤ N)
/-- Frontierat: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def FrontierAt (v : Params) : Prop :=
  0 < cLower v ∧ 0 < CAtt v ∧
  (∀ n : ℕ, 2 ≤ n →
    0 < rho n v ∧ 0 < rhoBounded n v.toSmooth3 ∧
    cLower v*rho n v ≤ criticalRadius n v ∧ criticalRadius n v ≤ CAtt v*rho n v ∧
    cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ boundedCriticalRadius n v.toSmooth3 ∧
    boundedCriticalRadius n v.toSmooth3=binaryCriticalRadius n v.toSmooth3 ∧
    boundedCriticalRadius n v.toSmooth3 ≤ CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 ∧
    0 < cLower v*rho n v ∧ cLower v*rho n v < maxDist v ∧
    0 < cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 ∧ cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 < maxDistBounded v.toSmooth3 ∧
    1/10 < testingRisk n v (cLower v*rho n v) ∧
    1/10 < boundedTestingRisk n v.toSmooth3 (cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3) ∧
    (∀ law, InNull v law → rejectProb n law.P (phistar n v) ≤ 1/10) ∧
    (∀ law, InBoundedNull v.toSmooth3 law → rejectProb n law.P (phistarBounded n v.toSmooth3) ≤ 1/10) ∧
    (CAtt v*rho n v < maxDist v → ∀ law, InModel v law → CAtt v*rho n v ≤ hetDist law → 1-rejectProb n law.P (phistar n v) ≤ 1/10) ∧
    (CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 < maxDistBounded v.toSmooth3 → ∀ law, InBoundedModel v.toSmooth3 law →
      CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ hetDist law → 1-rejectProb n law.P (phistarBounded n v.toSmooth3) ≤ 1/10) ∧
    (cLower v/CAttBounded v.toSmooth3)*(n:ℝ)^(Eexp (v.withP 2)-Eexp v) ≤ radiusRatio n v ∧
    radiusRatio n v ≤ (CAtt v/cLowerBounded v.toSmooth3)*(n:ℝ)^(Eexp (v.withP 2)-Eexp v) ∧ 1 ≤ radiusRatio n v) ∧
  Filter.Tendsto (fun n : ℕ => rho n v) Filter.atTop (nhds 0) ∧
  Filter.Tendsto (fun n : ℕ => rhoBounded n v.toSmooth3) Filter.atTop (nhds 0) ∧
  (∀ n : ℕ, NAtt v ≤ n → CAtt v*rho n v < d0) ∧
  (∀ n : ℕ, NAttBounded v.toSmooth3 ≤ n → CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 < d0) ∧
  E4 v-E0 v=(2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v))*(Fphase v-1) ∧
  (1 ≤ Fphase v → Eexp v=E0 v) ∧ (Fphase v < 1 → Eexp v=E4 v) ∧
  Eexp (v.withP 2)-Eexp v=phaseDifference v ∧
  (v.p < 2 → Eexp v < Eexp (v.withP 2) ∧
    Filter.Tendsto (fun n : ℕ => rho n v/rhoBounded n v.toSmooth3) Filter.atTop Filter.atTop ∧ BoundedTailEssentiality v ∧
    Filter.Tendsto (fun n : ℕ => magnitude n v) Filter.atTop Filter.atTop ∧
    (∀ n : ℕ, 2 ≤ n →
      PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
      PriorSupported (conversePrior false n v) {law | InNull v law ∧ ArmSupport law (magnitude n v)} ∧
      PriorSupported (conversePrior true n v) {law | InModel v law ∧ ArmSupport law (magnitude n v) ∧
        cLower v*rho n v ≤ hetDist law ∧ hetDist law < maxDist v} ∧
      Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/2))
/-- A continuous positive lower envelope removes the threshold ceiling and phase switch. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
-- @node: compactLowerEnvelope
def compactLowerEnvelope (v : Params) : ℝ :=
  min (cOracle v) (min (kLow v)
    (cOracle v*(max 2 ((32:ℝ)^(Dp v*v.γ/(2*sumReg v)))+1)^(-|E0 v-E4 v|)))

/-- The continuous envelope is positive throughout the public parameter domain. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: compactLowerEnvelope_pos
lemma compactLowerEnvelope_pos (v : Params) (hv : v.Valid) :
    0 < compactLowerEnvelope v := by
  unfold compactLowerEnvelope cOracle kLow Hfine
  positivity

/-- Upward ceiling rounding and exponent monotonicity put the envelope below either lower branch. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: compactLowerEnvelope_le
lemma compactLowerEnvelope_le (v : Params) (hv : v.Valid) :
    compactLowerEnvelope v ≤ cLower v := by
  let T : ℝ := max 2 ((32:ℝ)^(Dp v*v.γ/(2*sumReg v)))+1
  have hN : (1:ℝ) ≤ Nlow v := by
    have : (2:ℝ) ≤ Nlow v := (le_max_left _ _).trans (Nat.le_ceil _)
    linarith
  have hNT : (Nlow v:ℝ) ≤ T := by
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hpow : T^(-|E0 v-E4 v|) ≤ (Nlow v:ℝ)^(-(E0 v-E4 v)) := by
    calc
      _ ≤ (Nlow v:ℝ)^(-|E0 v-E4 v|) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hNT (neg_nonpos.mpr (abs_nonneg _))
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (le_abs_self _))
  unfold cLower
  split
  · exact min_le_left _ _
  · apply le_min
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left hpow (by unfold cOracle; positivity)))

/-- All lower-envelope factors are continuous on the valid exponent domain. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: continuousAt_compactLowerEnvelope
lemma continuousAt_compactLowerEnvelope (v : Params) (hv : v.Valid) :
    ContinuousAt compactLowerEnvelope v := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hα := hv.2.1.1
  have hβ := hv.2.2.1.1
  simp only [qExp, Dp, sumReg] at hq he hd
  have cp := continuous_params_p.continuousAt (x := v)
  have ca := continuous_params_alpha.continuousAt (x := v)
  have cb := continuous_params_beta.continuousAt (x := v)
  have cg := continuous_params_gamma.continuousAt (x := v)
  have hc : ContinuousAt cOracle v := by
    unfold cOracle
    exact ((continuousAt_const.rpow cg.neg (Or.inl (by norm_num))).div_const _)
  have hk : ContinuousAt kLow v := by
    unfold kLow
    apply continuousAt_const.mul
    exact continuousAt_const.rpow (ca.add cb).neg (Or.inl (by unfold Hfine; positivity))
  have htarget : ContinuousAt (fun v => max 2 ((32:ℝ)^(Dp v*v.γ/(2*sumReg v)))+1) v := by
    unfold Dp qExp sumReg
    apply ContinuousAt.add_const
    apply continuousAt_const.max
    apply continuousAt_const.rpow
    · fun_prop (disch := first | positivity | assumption)
    · left; norm_num
  have hgap : ContinuousAt (fun v => -|E0 v-E4 v|) v := by
    unfold E0 E4 Dp qExp sumReg
    fun_prop (disch := first | positivity | assumption)
  unfold compactLowerEnvelope
  apply hc.min
  apply hk.min
  apply hc.mul
  exact htarget.rpow hgap (Or.inl (by positivity))

/-- The lower envelope attains a positive minimum on every compact valid parameter set. This statement assumes [the hK condition](hyp:hK), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: cLower_compact_uniformity
lemma cLower_compact_uniformity (K : Set Params) (hK : IsCompact K)
    (hv : ∀ v ∈ K, v.Valid) : ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ cLower v := by
  by_cases hne : K.Nonempty
  · obtain ⟨v0, hv0, hmin⟩ := hK.exists_isMinOn hne
      (fun v h => (continuousAt_compactLowerEnvelope v (hv v h)).continuousWithinAt)
    exact ⟨compactLowerEnvelope v0, compactLowerEnvelope_pos v0 (hv v0 hv0),
      fun v h => (hmin h).trans (compactLowerEnvelope_le v (hv v h))⟩
  · exact ⟨1, by norm_num, fun v h => (hne ⟨v,h⟩).elim⟩

/-- Inserting moment exponent two continuously embeds bounded parameter sets. [This is the stated conclusion](goal). -/
-- @node: continuous_ofBounded
@[fun_prop] lemma continuous_ofBounded : Continuous Params.ofBounded := by
  apply continuous_induced_rng.mpr
  have h : Continuous (fun w : Smooth3 => (w.α,w.β,w.γ)) := continuous_induced_dom
  exact continuous_const.prodMk h

/-- Compact uniformity includes both phase boundaries and the second-moment face. [This is the stated conclusion](goal). -/
-- @node: frontier_compact_uniformity
lemma frontier_compact_uniformity : FrontierCompactUniformity := by
  have hparams : ∀ K : Set Params, IsCompact K → (∀ v ∈ K, v.Valid) →
      ∃ c C N : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ cLower v ∧ CAtt v ≤ C ∧ (NAtt v:ℝ) ≤ N := by
    intro K hK hv
    obtain ⟨c, hc, hl⟩ := cLower_compact_uniformity K hK hv
    obtain ⟨C, N, e, he, hu⟩ := attainment_compact_uniformity K hK hv
    exact ⟨c, C, N, hc, fun v h => ⟨hl v h, (hu v h).1, (hu v h).2.1⟩⟩
  refine ⟨hparams, ?_⟩
  intro K hK hw
  have hvalid : ∀ v ∈ Params.ofBounded '' K, v.Valid := by
    rintro v ⟨w, hwK, rfl⟩
    exact ⟨by norm_num [Params.ofBounded], hw w hwK⟩
  obtain ⟨c, C, N, hc, hu⟩ := hparams (Params.ofBounded '' K)
    (hK.image continuous_ofBounded) hvalid
  exact ⟨c, C, N, hc, fun w h => hu _ ⟨w,h,rfl⟩⟩

/-- The lower multiplier never exceeds the pure paired-tent multiplier. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: cLower_le_cOracle
lemma cLower_le_cOracle (v : Params) (hv : v.Valid) : cLower v ≤ cOracle v := by
  unfold cLower
  split
  · exact le_rfl
  · rename_i hf
    have hgap : 0 ≤ E0 v-E4 v := by
      have h := phase_channel_difference v hv
      have hp := phase_denominators v hv
      have hc : 0 < 2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v) := by
        obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := hp
        positivity
      have hphase : Fphase v < 1 := lt_of_not_ge hf
      have hh : E4 v-E0 v < 0 := by rw [h]; exact mul_neg_of_pos_of_neg hc (by linarith)
      linarith
    have hN : (1:ℝ) ≤ Nlow v := by
      have : (2:ℝ) ≤ Nlow v := (le_max_left _ _).trans (Nat.le_ceil _)
      linarith
    exact (min_le_right _ _).trans (by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hgap)
      have hc : 0 ≤ cOracle v := by unfold cOracle; positivity
      simpa using mul_le_mul_of_nonneg_left hh hc)

/-- Every prescribed lower separation is strictly below the shared witness distance. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: matched_lower_separation
lemma matched_lower_separation (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    0 < cLower v*rho n v ∧ cLower v*rho n v < d0 := by
  have hr := (matched_scales_pos n (by omega) v).1
  have hr1 : rho n v ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (by omega : 1 ≤ n)
    · exact neg_nonpos.mpr (exponent_phase_algebra v hv).2.2.1.le
  have hc : cOracle v < d0 := by
    have hp : (4:ℝ)^(-v.γ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [hv.2.2.2.1])
    have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hs3 : 0 < Real.sqrt 3 := by positivity
    unfold cOracle d0
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hh : Real.sqrt 2 < 2*Real.sqrt 3 := by nlinarith
    nlinarith
  refine ⟨mul_pos (cLower_pos v hv) hr, ?_⟩
  exact ((mul_le_mul_of_nonneg_left hr1 (cLower_pos v hv).le).trans
    (by simpa using cLower_le_cOracle v hv)).trans_lt hc

/-- A normalized finite prior has a positive-weight support atom. This statement assumes [the hπ condition](hyp:hπ). [This is the stated conclusion](goal). -/
-- @node: normalized_prior_positive_atom
lemma normalized_prior_positive_atom (π : FinitePrior) (hπ : PriorNormalized π) :
    ∃ i, 0 < priorWeight π i := by
  by_contra h
  have hz : ∀ i, priorWeight π i = 0 := fun i =>
    le_antisymm (le_of_not_gt (fun hi => h ⟨i,hi⟩)) (hπ.1 i)
  have hs := hπ.2
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

/-- The bounded lower uses its own legal rough or signed-binary witnesses. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: bounded_matched_lower
lemma bounded_matched_lower (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (∃ law, InBoundedModel w law ∧ cLowerBounded w*rhoBounded n w ≤ hetDist law) ∧
    2/5 ≤ boundedTestingRisk n w (cLowerBounded w*rhoBounded n w) := by
  let v := Params.ofBounded w
  have hv : v.Valid := ⟨by norm_num [v, Params.ofBounded], hw⟩
  by_cases hf : Fphase v < 1
  · have hl := rough_full_record_sharp_lower.2 w hw hf n hn
    obtain ⟨i, hi⟩ := normalized_prior_positive_atom _ hl.2.1
    have he := (phase_channel_selection v hv).2 hf
    have hscale : rhoBounded n w = (n:ℝ)^(-E4 v) := by rw [rhoBounded, rho, he]
    rw [hscale]
    exact ⟨⟨_, (hl.2.2.2.1 i hi).1, (hl.2.2.2.1 i hi).2.1⟩, hl.2.2.2.2.2⟩
  · have hf' : 1 ≤ Fphase v := le_of_not_gt hf
    have he := (phase_channel_selection v hv).1 hf'
    obtain ⟨P0, π, hnull, he0, hnorm, ⟨i,hi⟩, halt, hD, htv, hr⟩ :=
      paired_tent_full_record_lower.2 w hw n hn
    have hscale : cLowerBounded w*rhoBounded n w = cOracle v*rhoOracle n v := by
      simp only [cLowerBounded, rhoBounded, cLower, if_pos hf', rho, he, rhoOracle, v]
    rw [hscale]
    exact ⟨⟨_, binaryModel_inBoundedModel w _ (halt i hi).1, (halt i hi).2.2.1⟩, hr⟩

/-- A strict failure with a nonempty alternative bounds the capped radius below. This statement assumes [the hr condition](hyp:hr), [the hne condition](hyp:hne), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: cappedRadius_lower_of_nonempty_failure
lemma cappedRadius_lower_of_nonempty_failure (n : ℕ) (Null Alt : Set ObservedLaw)
    (D r : ℝ) (hr : 0 < r ∧ r < D) (hne : ∃ law ∈ Alt, r ≤ hetDist law)
    (hf : 1/10 < testingRiskOn n r Null Alt) :
    r ≤ cappedRadius D (fun t => testingRiskOn n t Null Alt) := by
  apply le_csInf ⟨D, Or.inr (Set.mem_singleton _)⟩
  intro t ht
  rcases ht with ht | ht
  · by_contra hrt
    have hanti := testingRiskOn_antitone n Null Alt t r (le_of_not_ge hrt) hne
    exact (not_le_of_gt hf) (hanti.trans ht.2.2)
  · exact hr.2.le.trans (le_of_eq (Set.mem_singleton_iff.mp ht).symm)

/-- Dividing the matched radius bounds yields the complete ratio comparison. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hlo condition](hyp:hlo), [the hhi condition](hyp:hhi), [the hblo condition](hyp:hblo), [the hbhi condition](hyp:hbhi). [This is the stated conclusion](goal). -/
-- @node: matched_radius_ratio_bounds
lemma matched_radius_ratio_bounds (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (hlo : cLower v*rho n v ≤ criticalRadius n v)
    (hhi : criticalRadius n v ≤ CAtt v*rho n v)
    (hblo : cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ boundedCriticalRadius n v.toSmooth3)
    (hbhi : boundedCriticalRadius n v.toSmooth3 ≤ CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3) :
    (cLower v/CAttBounded v.toSmooth3)*(n:ℝ)^(Eexp (v.withP 2)-Eexp v) ≤ radiusRatio n v ∧
    radiusRatio n v ≤ (CAtt v/cLowerBounded v.toSmooth3)*(n:ℝ)^(Eexp (v.withP 2)-Eexp v) ∧
    1 ≤ radiusRatio n v := by
  have hv2 : (Params.ofBounded v.toSmooth3).Valid := ⟨by norm_num [Params.ofBounded], hv.2⟩
  have hc := cLower_pos v hv
  have hcb := cLower_pos _ hv2
  have hs := matched_scales_pos n (by omega) v
  have hbp : 0 < boundedCriticalRadius n v.toSmooth3 := (mul_pos hcb hs.2).trans_le hblo
  have hscale := matched_scale_ratio_eq n (by omega) v
  change rho n v/rhoBounded n v.toSmooth3 = (n:ℝ)^(Eexp (v.withP 2)-Eexp v) at hscale
  rw [← hscale]
  have hid (a b : ℝ) : (a/b)*(rho n v/rhoBounded n v.toSmooth3) =
      (a*rho n v)/(b*rhoBounded n v.toSmooth3) := by ring
  rw [hid, hid]
  refine ⟨?_, ?_, ?_⟩
  · exact div_le_div₀ ((mul_pos hc hs.1).le.trans hlo) hlo hbp hbhi
  · exact div_le_div₀ ((mul_pos hc hs.1).le.trans (hlo.trans hhi)) hhi (mul_pos hcb hs.2) hblo
  · exact (one_le_div hbp).mpr ((bounded_submodel_comparison v hv).2.2.2.2.2.2.1 n hn).2.2

/-- The lower and upper receipts assemble every finite-sample and phase comparison. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: frontier_at
lemma frontier_at (v : Params) (hv : v.Valid) : FrontierAt v := by
  have hv2 : (Params.ofBounded v.toSmooth3).Valid := ⟨by norm_num [Params.ofBounded], hv.2⟩
  have hatt := original_record_attainable_rate.1 v hv
  have hconv := tail_essential_full_record_converse v hv
  have hphase := exponent_phase_algebra v hv
  refine ⟨cLower_pos v hv, hatt.1, ?_, rho_tendsto_zero v hv,
    rhoBounded_tendsto_zero v hv, hatt.2.2.1, ?_, phase_channel_difference v hv,
    (phase_channel_selection v hv).1, (phase_channel_selection v hv).2,
    phase_difference_eq v hv, ?_⟩
  · intro n hn
    have hc := hconv.1 n hn
    have hb := bounded_matched_lower v.toSmooth3 hv.2 n hn
    have hsep := matched_lower_separation (Params.ofBounded v.toSmooth3) hv2 n hn
    have hcomp := bounded_submodel_comparison v hv
    have hDb : d0 ≤ maxDistBounded v.toSmooth3 := by rw [hcomp.2.2.2.1]; exact hcomp.2.2.2.2.1
    have hbsep : cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 < maxDistBounded v.toSmooth3 :=
      hsep.2.trans_le hDb
    obtain ⟨i, hi⟩ := normalized_prior_positive_atom _ hc.2.1
    have hsupp := hc.2.2.2.1 i hi
    have hlo : cLower v*rho n v ≤ criticalRadius n v :=
      cappedRadius_lower_of_nonempty_failure n _ _ _ _
        ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1⟩ ⟨_, hsupp.1, hsupp.2.2.1⟩
        (by change 1/10 < testingRisk n v (cLower v*rho n v); linarith [hc.2.2.2.2.2.2.2])
    have hblo : cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ boundedCriticalRadius n v.toSmooth3 :=
      cappedRadius_lower_of_nonempty_failure n _ _ _ _ ⟨hsep.1, hbsep⟩ hb.1 (by change 1/10 < boundedTestingRisk n v.toSmooth3 _; linarith [hb.2])
    have hu := hatt.2.1 n hn
    have hbu := (original_record_attainable_rate.2.2 v.toSmooth3 hv.2).2 n hn
    have hr := matched_radius_ratio_bounds v hv n hn hlo hu.2.2 hblo hbu.2.2
    have heq := (hcomp.2.2.2.2.2.2.1 n hn).2.1.symm
    refine ⟨(matched_scales_pos n (by omega) v).1, (matched_scales_pos n (by omega) v).2,
      hlo, hu.2.2, hblo, heq, hbu.2.2,
      hc.2.2.2.2.1, hc.2.2.2.2.2.1, hsep.1, hbsep,
      by linarith [hc.2.2.2.2.2.2.2], by linarith [hb.2], ?_, ?_, ?_, ?_, hr⟩
    · intro law hm; exact (hu.1 law hm).trans (by norm_num)
    · intro law hm; exact (hbu.1 law hm).trans (by norm_num)
    · intro hlegal law hm hd; exact (hu.2.1 hlegal law hm hd).trans (by norm_num)
    · intro hlegal law hm hd; exact (hbu.2.1 hlegal law hm hd).trans (by norm_num)
  · exact attainment_threshold _ hv2
  · intro hp
    refine ⟨hphase.2.2.2.2.2.2.2.2.2 hp, (hconv.2.2.1 hp).1,
      (hconv.2.2.1 hp).2, hconv.2.1, ?_⟩
    intro n hn
    have h := hconv.1 n hn
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- The assembled comparison supplies both ratio bounds at every legal sample size. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: frontier_ratio_bounds
lemma frontier_ratio_bounds (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (cLower v/CAttBounded v.toSmooth3)*(n:ℝ)^(Eexp (v.withP 2)-Eexp v) ≤ radiusRatio n v ∧
    radiusRatio n v ≤ (CAtt v/cLowerBounded v.toSmooth3)*(n:ℝ)^(Eexp (v.withP 2)-Eexp v) := by
  obtain ⟨hs, hbs, hlo, hhi, hblo, heq, hbhi, hpos, hcap, hbpos, hbcap,
    hf, hbf, hsize, hbsize, hpower, hbpower, hlr, hur, h1⟩ := (frontier_at v hv).2.2.1 n hn
  exact ⟨hlr, hur⟩

/-- The positive strict exponent gap forces divergence of the entire-record radius ratio. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: radiusRatio_tendsto_atTop
lemma radiusRatio_tendsto_atTop (v : Params) (hv : v.Valid) (hp : v.p < 2) :
    Filter.Tendsto (fun n : ℕ => radiusRatio n v) Filter.atTop Filter.atTop := by
  have hgap : 0 < Eexp (v.withP 2)-Eexp v :=
    sub_pos.mpr ((exponent_phase_algebra v hv).2.2.2.2.2.2.2.2.2 hp)
  have hv2 : (Params.ofBounded v.toSmooth3).Valid := ⟨by norm_num [Params.ofBounded], hv.2⟩
  have hC : 0 < CAttBounded v.toSmooth3 := by
    change 0 < CAtt (Params.ofBounded v.toSmooth3)
    linarith [CAtt_ge_256 _ hv2]
  have h := ((tendsto_rpow_atTop hgap).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n:ℝ))
      Filter.atTop Filter.atTop)).const_mul_atTop (div_pos (cLower_pos v hv) hC)
  simp only [Function.comp_def] at h
  apply Filter.tendsto_atTop_mono' _ ?_ h
  filter_upwards [Filter.eventually_ge_atTop (2:ℕ)] with n hn
  exact (frontier_ratio_bounds v hv n hn).1

/-- On the second-moment face the exponent gap vanishes, giving a uniform ratio bound. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: second_moment_radiusRatio_bounded
lemma second_moment_radiusRatio_bounded (v : Params) (hv : v.Valid) (hp : v.p = 2) :
    BddAbove ((fun n : ℕ => radiusRatio n v) '' {n | 2 ≤ n}) := by
  refine ⟨CAtt v/cLowerBounded v.toSmooth3, ?_⟩
  rintro _ ⟨n, hn, rfl⟩
  have heq : v.withP 2 = v := by
    change Params.ofBounded v.toSmooth3 = v
    exact ofBounded_toSmooth3_of_p_eq_two v hp
  simpa only [heq, sub_self, Real.rpow_zero, mul_one] using
    (frontier_ratio_bounds v hv n hn).2

/-- Every strict moment exponent belongs to the strict region, and only these do. [This is the stated conclusion](goal). -/
-- @node: tailRegion_characterization
lemma tailRegion_characterization : tailRegion = {v | v.Valid ∧ v.p < 2} := by
  ext v
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, radiusRatio_tendsto_atTop v h.1 h.2⟩

/-- Divergence rules out a bounded ratio off the second-moment face. [This is the stated conclusion](goal). -/
-- @node: equalityRegion_characterization
lemma equalityRegion_characterization : equalityRegion = {v | v.Valid ∧ v.p = 2} := by
  ext v
  constructor
  · rintro ⟨hv, ⟨C, hC⟩⟩
    refine ⟨hv, ?_⟩
    by_contra hp
    have hp' : v.p < 2 := lt_of_le_of_ne hv.1.2 hp
    have ht := (radiusRatio_tendsto_atTop v hv hp').eventually
      (Filter.eventually_gt_atTop C)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ht
    have hn := hN (max 2 N) (le_max_right _ _)
    have hb := hC ⟨max 2 N, (show 2 ≤ max 2 N from le_max_left _ _), rfl⟩
    exact (not_le_of_gt hn) hb
  · exact fun h => ⟨h.1, second_moment_radiusRatio_bounded v h.1 h.2⟩

/-- A public strict-moment neighborhood intersects the domain in a nonempty tail region. [This is the stated conclusion](goal). -/
-- @node: tailRegion_nonempty_open
lemma tailRegion_nonempty_open : ∃ U : Set Params, IsOpen U ∧
    (U ∩ {v | v.Valid}).Nonempty ∧ (U ∩ {v | v.Valid}) ⊆ tailRegion := by
  refine ⟨{v | v.p < 2}, isOpen_lt continuous_params_p continuous_const, ?_, ?_⟩
  · refine ⟨⟨3/2,1/2,1/2,1/2⟩, ?_⟩
    norm_num [Params.Valid]
  · intro v hv
    rw [tailRegion_characterization]
    exact ⟨hv.2, hv.1⟩

/-- Matched entire-class frontiers, phase comparisons, and calibrated total rules. [This is the stated conclusion](goal). -/
-- @node: thm:heavy-tail-comparison
theorem heavy_tail_comparison :
    (∀ v : Params, v.Valid → FrontierAt v) ∧
    tailRegion={v | v.Valid ∧ v.p < 2} ∧ equalityRegion={v | v.Valid ∧ v.p=2} ∧
    (∃ U : Set Params, IsOpen U ∧ (U ∩ {v | v.Valid}).Nonempty ∧ (U ∩ {v | v.Valid}) ⊆ tailRegion) ∧
    FrontierCompactUniformity := by
  exact ⟨frontier_at, tailRegion_characterization, equalityRegion_characterization,
    tailRegion_nonempty_open, frontier_compact_uniformity⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
