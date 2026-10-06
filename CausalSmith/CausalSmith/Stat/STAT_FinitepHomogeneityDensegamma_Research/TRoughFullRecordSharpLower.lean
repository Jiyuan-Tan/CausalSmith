module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BoundedRoughCalibration
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ConversePriors
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TailRoughCalibration
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TwoPrior
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TFullRecordCopulaComponentBound
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TPairedTentFullRecordLower

/-! Finite-moment homogeneity testing: TRoughFullRecordSharpLower. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- In the rough phase the tail exponent is strictly larger than the rough exponent. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: rough_exponent_gap_pos
lemma rough_exponent_gap_pos (v : Params) (hv : v.Valid) (hf : Fphase v < 1) :
    0 < E0 v-E4 v := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hfactor : 0 < 2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v) := by positivity
  have hneg := mul_neg_of_pos_of_neg hfactor (sub_neg.mpr hf)
  rw [← phase_channel_difference v hv] at hneg
  linarith

/-- The public multiplier bridges the paired-tent separation at every sample below the threshold. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hsmall condition](hyp:hsmall). [This is the stated conclusion](goal). -/
-- @node: rough_small_sample_separation
lemma rough_small_sample_separation (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) (hsmall : n < Nlow v) :
    cLower v*(n:ℝ)^(-E4 v) ≤ cOracle v*rhoOracle n v := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hle : (n:ℝ) ≤ Nlow v := by exact_mod_cast hsmall.le
  have hgap := rough_exponent_gap_pos v hv hf
  have hc : 0 ≤ cOracle v := by unfold cOracle; positivity
  have hbridge : cLower v ≤ cOracle v*(Nlow v:ℝ)^(-(E0 v-E4 v)) := by
    simp only [cLower, if_neg (not_le.mpr hf)]
    exact min_le_right _ _
  calc
    _ ≤ (cOracle v*(Nlow v:ℝ)^(-(E0 v-E4 v)))*(n:ℝ)^(-E4 v) :=
      mul_le_mul_of_nonneg_right hbridge (Real.rpow_nonneg hnpos.le _)
    _ ≤ (cOracle v*(n:ℝ)^(-(E0 v-E4 v)))*(n:ℝ)^(-E4 v) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hnpos hle (neg_nonpos.mpr hgap.le)) hc)
        (Real.rpow_nonneg hnpos.le _)
    _ = cOracle v*rhoOracle n v := by
      rw [mul_assoc, ← Real.rpow_add hnpos]
      congr 1
      congr 1
      ring

/-- All binary null indices describe the same balanced zero-effect original law. [This is the stated conclusion](goal). -/
-- @node: binaryTentPrior_false_mixture
lemma binaryTentPrior_false_mixture (n : ℕ) (w : Smooth3) :
    priorMixture n (binaryTentPrior false n w) =
      Measure.pi (fun _ : Fin n => (binaryTentLaw false n w (fun _ => false)).P) := by
  apply priorMixture_eq_iid_of_constant _ _ _ (binaryTentPrior_normalized false n w).1
  intro i
  change binaryTentLaw false n w _ = binaryTentLaw false n w _
  simp only [binaryTentLaw, Bool.false_eq_true, if_false]

/-- The paired-tent fallback supplies all entire-class small-sample rough lower conclusions. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hsmall condition](hyp:hsmall). [This is the stated conclusion](goal). -/
-- @node: rough_small_sample_lower
lemma rough_small_sample_lower (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) (hsmall : n < Nlow v) :
    PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
    PriorSupported (conversePrior false n v) {law | InNull v law} ∧
    PriorSupported (conversePrior true n v) {law | InModel v law ∧
      cLower v*(n:ℝ)^(-E4 v) ≤ hetDist law ∧ hetDist law < d0} ∧ d0 ≤ maxDist v ∧
    Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/2 ∧
    2/5 ≤ testingRisk n v (cLower v*(n:ℝ)^(-E4 v)) := by
  have hb : ¬roughBranch n v := fun h => (not_le.mpr hsmall) h.2
  have hsep := rough_small_sample_separation v hv hf n hn hsmall
  have hr := tent_canonical_lower_receipt v hv n hn
  have hnull := hr.2.1
  have halt := hr.2.2.2.2.2.2.2.1
  have hD := hr.2.2.2.2.2.2.2.2.1
  have htv := hr.2.2.2.2.2.2.2.2.2.1
  have hrisk := hr.2.2.2.2.2.2.2.2.2.2.2
  have hne : ∃ law ∈ {law | InModel v law}, cOracle v*rhoOracle n v ≤ hetDist law := by
    obtain ⟨i, hi⟩ := hr.2.2.2.2.2.2.1
    exact ⟨_, (halt i hi).1, (halt i hi).2.2.2.1⟩
  have hanti := testingRiskOn_antitone n {law | InNull v law} {law | InModel v law}
    _ _ hsep hne
  simp only [conversePrior, if_neg hb]
  refine ⟨(tentPrior_normalized false n v).1, (tentPrior_normalized true n v).1,
    ?_, ?_, hD, ?_, hrisk.trans hanti⟩
  · intro i hi
    have heq : priorLaw (tentPrior false n v) i = tentLaw false n v (fun _ => false) := by
      change tentLaw false n v _ = tentLaw false n v _
      rw [tentLaw_false_eq_zero_table, tentLaw_false_eq_zero_table]
    rw [heq]
    exact hnull
  · intro i hi
    have hs := halt i hi
    exact ⟨hs.1, hsep.trans hs.2.2.2.1, hs.2.2.2.2.1⟩
  · simpa only [converseMixture, conversePrior, if_neg hb, tentPrior_false_mixture] using htv

/-- The separate signed-binary fallback supplies the bounded small-sample rough lower. This statement assumes [the hw condition](hyp:hw), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hsmall condition](hyp:hsmall). [This is the stated conclusion](goal). -/
-- @node: bounded_rough_small_sample_lower
lemma bounded_rough_small_sample_lower (w : Smooth3) (hw : w.Valid)
    (hf : Fphase (Params.ofBounded w) < 1) (n : ℕ) (hn : 2 ≤ n)
    (hsmall : n < Nlow (Params.ofBounded w)) :
    PriorNormalized (boundedConversePrior false n w) ∧ PriorNormalized (boundedConversePrior true n w) ∧
    PriorSupported (boundedConversePrior false n w) {law | InBoundedNull w law} ∧
    PriorSupported (boundedConversePrior true n w) {law | InBoundedModel w law ∧
      cLowerBounded w*(n:ℝ)^(-E4 (Params.ofBounded w)) ≤ hetDist law ∧ hetDist law < d0} ∧
    Causalean.Stat.tvDist (boundedConverseMixture false n w) (boundedConverseMixture true n w) < 1/2 ∧
    2/5 ≤ boundedTestingRisk n w (cLowerBounded w*(n:ℝ)^(-E4 (Params.ofBounded w))) := by
  have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
  have hb : ¬roughBranch n (Params.ofBounded w) := fun h => (not_le.mpr hsmall) h.2
  have hsep := rough_small_sample_separation (Params.ofBounded w) hv hf n hn hsmall
  have hr := binary_tent_canonical_lower_receipt w hw n hn
  have hnull := hr.1
  have halt := hr.2.2.2.2.1
  have htv := hr.2.2.2.2.2.2.1
  have hrisk := hr.2.2.2.2.2.2.2
  have hne : ∃ law ∈ {law | InBoundedModel w law},
      cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w) ≤ hetDist law := by
    obtain ⟨i, hi⟩ := hr.2.2.2.1
    exact ⟨_, binaryModel_inBoundedModel w _ (halt i hi).1, (halt i hi).2.2.1⟩
  have hanti := testingRiskOn_antitone n {law | InBoundedNull w law} {law | InBoundedModel w law}
    _ _ hsep hne
  simp only [boundedConversePrior, if_neg hb]
  refine ⟨(binaryTentPrior_normalized false n w).1, (binaryTentPrior_normalized true n w).1,
    ?_, ?_, ?_, hrisk.trans hanti⟩
  · intro i hi
    change InBoundedNull w (binaryTentLaw false n w _)
    have h := binaryTentLaw_false_inBinaryNull w hw n hn
      ((Fintype.equivFin (Fin (tentRank n (Params.ofBounded w)/2) → Bool)).symm i)
    have hm : InBinaryModel w (binaryTentLaw false n w _) :=
      ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
        h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment, h.signedBinaryOutcome⟩
    have hbm := binaryModel_inBoundedModel w _ hm
    exact ⟨hbm.uniform, hbm.overlap, hbm.propensitySmooth, hbm.baselineSmooth,
      hbm.effectSmooth, hbm.baselineCap, hbm.effectCap, hbm.rawMoment, hbm.boundedOutcome,
      h.nullConstancy⟩
  · intro i hi
    have hs := halt i hi
    exact ⟨binaryModel_inBoundedModel w _ hs.1, hsep.trans hs.2.2.1, hs.2.2.2⟩
  · simpa only [boundedConverseMixture, boundedConversePrior, if_neg hb,
      binaryTentPrior_false_mixture] using htv

/-- The branchwise rare-mark probability equals the legality tuning at the rough fine rank. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: tail_rough_rarity_eq_legality
lemma tail_rough_rarity_eq_legality (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) (hlarge : Nlow v ≤ n) :
    rarity n v = legalityRarity v (roughK n v) := by
  have hb : roughBranch n v := ⟨hf, hlarge⟩
  have hk : (0:ℝ) < roughK n v := by
    have := (rough_fine_rank_bounds v hv hf n hn).2.2
    exact_mod_cast (by omega : 0 < roughK n v)
  rw [rarity, if_pos hb]
  unfold legalityRarity legalityB
  rw [show (16:ℝ)*((roughK n v:ℝ)^(-v.β)/256) =
      (16:ℝ)^(-1:ℝ)*(roughK n v:ℝ)^(-v.β) by norm_num; ring,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16), ← Real.rpow_mul hk.le]
  congr 1 <;> congr 1 <;> ring

/-- The moment-normalized tail copula tuning closes the large-sample branch using the full-record component comparison and finite-prior testing inequality. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: tail_rough_large_sample_lower
lemma tail_rough_large_sample_lower (v : Params) (hv : v.Valid)
    (hf : Fphase v < 1) (n : ℕ) (hn : 2 ≤ n)
    (hlarge : Nlow v ≤ n) :
    PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
    PriorSupported (conversePrior false n v) {law | InNull v law} ∧
    PriorSupported (conversePrior true n v) {law | InModel v law ∧
      cLower v*(n:ℝ)^(-E4 v) ≤ hetDist law ∧ hetDist law < d0} ∧
    Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/8 ∧
    2/5 ≤ testingRisk n v (cLower v*(n:ℝ)^(-E4 v)) := by
  let K := roughK n v
  let M := roughM n v
  have hb : roughBranch n v := ⟨hf, hlarge⟩
  have hr := (rough_rank_legality v hv hf n hn hlarge).1
  have hd2 := (legality_copula_domains v hv K M hr).1
  have hd : CopulaDomain n K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K) :=
    ⟨hn, hd2.2⟩
  have hnorm (ν : Bool) := copula_prior_normalized n K M _ _ _ _ hd ν v
  have hlegal := copula_frame_legality.1 v hv hf K M hr
  have hsep := rough_rank_separation v hv hf n hn
  have hsupp0 : PriorSupported (copulaPrior false v K M (legalityA v K)
      (1/16) (legalityRarity v K) (legalityMagnitude v K)) {law | InNull v law} := by
    intro i hi
    exact (hlegal.1 _).1
  have hsupp1 : PriorSupported (copulaPrior true v K M (legalityA v K)
      (1/16) (legalityRarity v K) (legalityMagnitude v K)) {law | InModel v law ∧
        cLower v*(n:ℝ)^(-E4 v) ≤ hetDist law ∧ hetDist law < d0} := by
    intro i hi
    have hh := hlegal.2 ((Fintype.equivFin (CopulaIndex K M)).symm i)
    exact ⟨hh.1, hsep.trans hh.2.1.2.2.1, hh.2.1.2.2.2.2⟩
  have hbud := tail_rough_activity_budgets v hv hf n hn hlarge
  have hsum : activityBudgetA n K (legalityA v K) (1/16) (legalityRarity v K)+
      activityBudgetB n K M (legalityA v K) (1/16) (legalityRarity v K) ≤ (2:ℝ)^(-16:ℤ) := by
    have hh := add_le_add hbud.1 hbud.2
    exact hh.trans (by norm_num [Hfine])
  obtain ⟨μ, P0, P1, Q, A, B, hμ, hdesign, hmarks, hdisclosure, hlegitimate, hmap0, hmap1,
      hfst0, hfst1, hQ, hcond, hAm, hBm, hAi, hBi, hAb, hBb, htv⟩ :=
    full_record_copula_component_bound v n K M _ _ _ _ hd
      (rough_fine_rank_bounds v hv hf n hn).2.2
  have htv8 := htv hsum
  have htv2 : Causalean.Stat.tvDist
      (copulaMixture false n v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K))
      (copulaMixture true n v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K)) < 1/2 :=
    htv8.trans (by norm_num)
  have hrisk := finite_two_prior_testing_lower n {law | InNull v law}
    {law | InModel v law} (cLower v*(n:ℝ)^(-E4 v))
    _ _ (hnorm false) (hnorm true) hsupp0 (fun i hi => ⟨(hsupp1 i hi).1, (hsupp1 i hi).2.1⟩)
  have hlower : 2/5 ≤ testingRisk n v (cLower v*(n:ℝ)^(-E4 v)) := by
    change 2/5 ≤ testingRiskOn n _ _ _
    change 9/10-Causalean.Stat.tvDist
      (copulaMixture false n v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K))
      (copulaMixture true n v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K)) ≤ _ at hrisk
    linarith
  have hrary : rarity n v = legalityRarity v K :=
    tail_rough_rarity_eq_legality v hv hf n hn hlarge
  have hmagn : magnitude n v = legalityMagnitude v K := by
    simp only [magnitude, if_pos hb, hrary, legalityMagnitude]
  have heq (ν : Bool) : conversePrior ν n v =
      copulaPrior ν v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K) := by
    simp only [conversePrior, show roughBranch n v from hb,
      if_true, legalityA, K, M, hrary, hmagn]
  rw [heq false, heq true]
  refine ⟨hnorm false, hnorm true, hsupp0, hsupp1, ?_, hlower⟩
  simpa only [converseMixture, heq, copulaMixture] using htv8

/-- The separate bounded copula tuning closes the large-sample branch using the full-record component comparison and finite-prior testing inequality. This statement assumes [the hw condition](hyp:hw), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: bounded_rough_large_sample_lower
lemma bounded_rough_large_sample_lower (w : Smooth3) (hw : w.Valid)
    (hf : Fphase (Params.ofBounded w) < 1) (n : ℕ) (hn : 2 ≤ n)
    (hlarge : Nlow (Params.ofBounded w) ≤ n) :
    PriorNormalized (boundedConversePrior false n w) ∧ PriorNormalized (boundedConversePrior true n w) ∧
    PriorSupported (boundedConversePrior false n w) {law | InBoundedNull w law} ∧
    PriorSupported (boundedConversePrior true n w) {law | InBoundedModel w law ∧
      cLowerBounded w*(n:ℝ)^(-E4 (Params.ofBounded w)) ≤ hetDist law ∧ hetDist law < d0} ∧
    Causalean.Stat.tvDist (boundedConverseMixture false n w) (boundedConverseMixture true n w) < 1/2 ∧
    2/5 ≤ boundedTestingRisk n w (cLowerBounded w*(n:ℝ)^(-E4 (Params.ofBounded w))) := by
  let v := Params.ofBounded w
  let K := roughK n v
  let M := roughM n v
  have hv : v.Valid := ⟨by norm_num [v, Params.ofBounded], hw⟩
  have hb : roughBranch n v := ⟨hf, hlarge⟩
  have hr := (rough_rank_legality v hv hf n hn hlarge).1
  have hd2 := (legality_copula_domains v hv K M hr).2
  have hd : CopulaDomain n K M (legalityA v K) (2*legalityB v K) (1/2) 1 :=
    ⟨hn, hd2.2⟩
  have hnorm (ν : Bool) := copula_prior_normalized n K M _ _ _ _ hd ν v
  have hlegal := copula_frame_legality.2 w hw hf K M hr
  have hsep := rough_rank_separation v hv hf n hn
  have hsupp0 : PriorSupported (copulaPrior false v K M (legalityA v K)
      (2*legalityB v K) (1/2) 1) {law | InBoundedNull w law} := by
    intro i hi
    exact (hlegal.1 _).1
  have hsupp1 : PriorSupported (copulaPrior true v K M (legalityA v K)
      (2*legalityB v K) (1/2) 1) {law | InBoundedModel w law ∧
        cLowerBounded w*(n:ℝ)^(-E4 v) ≤ hetDist law ∧ hetDist law < d0} := by
    intro i hi
    have hh := hlegal.2 ((Fintype.equivFin (CopulaIndex K M)).symm i)
    exact ⟨hh.1, hsep.trans hh.2.1.2.2.1, hh.2.1.2.2.2.2⟩
  have hbud := bounded_rough_activity_budgets w hw hf n hn hlarge
  have hsum : activityBudgetA n K (legalityA v K) (2*legalityB v K) (1/2)+
      activityBudgetB n K M (legalityA v K) (2*legalityB v K) (1/2) ≤ (2:ℝ)^(-16:ℤ) := by
    have hh := add_le_add hbud.1 hbud.2
    exact hh.trans (by norm_num [Hfine])
  obtain ⟨μ, P0, P1, Q, A, B, hμ, hdesign, hmarks, hdisclosure, hlegitimate, hmap0, hmap1,
      hfst0, hfst1, hQ, hcond, hAm, hBm, hAi, hBi, hAb, hBb, htv⟩ :=
    full_record_copula_component_bound v n K M _ _ _ _ hd
      (rough_fine_rank_bounds v hv hf n hn).2.2
  have htv8 := htv hsum
  have htv2 : Causalean.Stat.tvDist
      (copulaMixture false n v K M (legalityA v K) (2*legalityB v K) (1/2) 1)
      (copulaMixture true n v K M (legalityA v K) (2*legalityB v K) (1/2) 1) < 1/2 :=
    htv8.trans (by norm_num)
  have hrisk := finite_two_prior_testing_lower n {law | InBoundedNull w law}
    {law | InBoundedModel w law} (cLowerBounded w*(n:ℝ)^(-E4 v))
    _ _ (hnorm false) (hnorm true) hsupp0 (fun i hi => ⟨(hsupp1 i hi).1, (hsupp1 i hi).2.1⟩)
  have hlower : 2/5 ≤ boundedTestingRisk n w (cLowerBounded w*(n:ℝ)^(-E4 v)) := by
    change 2/5 ≤ testingRiskOn n _ _ _
    change 9/10-Causalean.Stat.tvDist
      (copulaMixture false n v K M (legalityA v K) (2*legalityB v K) (1/2) 1)
      (copulaMixture true n v K M (legalityA v K) (2*legalityB v K) (1/2) 1) ≤ _ at hrisk
    linarith
  have heq (ν : Bool) : boundedConversePrior ν n w =
      copulaPrior ν v K M (legalityA v K) (2*legalityB v K) (1/2) 1 := by
    simp only [boundedConversePrior, show roughBranch n (Params.ofBounded w) from hb,
      if_true, legalityA, legalityB, v, K, M, mul_div_assoc]
  rw [heq false, heq true]
  refine ⟨hnorm false, hnorm true, hsupp0, hsupp1, ?_, hlower⟩
  simpa only [boundedConverseMixture, heq, copulaMixture] using htv2

/-- [Rough full record sharp lower](goal).
Use Definition \(\mathrm{def:sharp\mbox{-}frontier\mbox{-}scales}\). If \(F(p)<1\), then for
every \(n\ge2\) there are finite null and alternative mixtures on the entire original class such
that \[  c_v n^{-E_4(p)}\le d(P)<d_0\le D_v  \quad\text{on every alternative support law},\qquad
\operatorname{TV}(\mathbb P_0,\mathbb P_1)<1/2,  \qquad B_n(v,c_vn^{-E_4(p)})\ge2/5. \] For
\(n\ge N_{\mathrm{low}}(v)\), take \(K\) to be the least power of two at least
\(H_{\mathrm{fine}}n^{2/D_p}\), and \[  M=2^{\lfloor\log_2(K^{S/\gamma}/16)\rfloor}. \] Use the
tail tuning of Lemma \(\mathrm{lem:copula\mbox{-}frame\mbox{-}legality}\). These mixtures have
total variation below \(1/8\). For \(n<N_{\mathrm{low}}(v)\), use the established paired-tent
mixtures. At \(p=2\), the same tuning of ranks with the separate bounded version of that
legality lemma proves \[  B_n^{\mathrm b}(w,c_w^{\mathrm b}n^{-E_4(2)})\ge2/5
\quad\text{whenever }F(2)<1, \] with legal nonempty bounded alternatives for every \(n\).
-/
-- @node: lem:rough-full-record-sharp-lower
lemma rough_full_record_sharp_lower :
    (∀ v : Params, v.Valid → Fphase v < 1 → ∀ n : ℕ, 2 ≤ n →
      PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
      PriorSupported (conversePrior false n v) {law | InNull v law} ∧
      PriorSupported (conversePrior true n v) {law | InModel v law ∧
        cLower v*(n:ℝ)^(-E4 v) ≤ hetDist law ∧ hetDist law < d0} ∧ d0 ≤ maxDist v ∧
      Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/2 ∧
      2/5 ≤ testingRisk n v (cLower v*(n:ℝ)^(-E4 v)) ∧
      (Nlow v ≤ n → LegalityRanks v (roughK n v) (roughM n v) ∧
        2^40*n ≤ roughK n v ∧
        activityBudgetA n (roughK n v) (legalityA v (roughK n v)) (1/16) (rarity n v) ≤ (2:ℝ)^(-10:ℤ)/Hfine ∧
        activityBudgetB n (roughK n v) (roughM n v) (legalityA v (roughK n v)) (1/16) (rarity n v) ≤ 2^13/Hfine^2 ∧
        Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/8)) ∧
    (∀ w : Smooth3, w.Valid → Fphase (Params.ofBounded w) < 1 → ∀ n : ℕ, 2 ≤ n →
      PriorNormalized (boundedConversePrior false n w) ∧ PriorNormalized (boundedConversePrior true n w) ∧
      PriorSupported (boundedConversePrior false n w) {law | InBoundedNull w law} ∧
      PriorSupported (boundedConversePrior true n w) {law | InBoundedModel w law ∧
        cLowerBounded w*(n:ℝ)^(-E4 (Params.ofBounded w)) ≤ hetDist law ∧ hetDist law < d0} ∧
      Causalean.Stat.tvDist (boundedConverseMixture false n w) (boundedConverseMixture true n w) < 1/2 ∧
      2/5 ≤ boundedTestingRisk n w (cLowerBounded w*(n:ℝ)^(-E4 (Params.ofBounded w)))) := by
  constructor
  · intro v hv hf n hn
    by_cases hsmall : n < Nlow v
    · have hr := rough_small_sample_lower v hv hf n hn hsmall
      refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ?_⟩
      intro hlarge
      exact False.elim ((not_le.mpr hsmall) hlarge)
    · have hlarge : Nlow v ≤ n := by omega
      have hr := tail_rough_large_sample_lower v hv hf n hn hlarge
      have hD := (tent_canonical_lower_receipt v hv n hn).2.2.2.2.2.2.2.2.1
      refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hD,
        hr.2.2.2.2.1.trans (by norm_num), hr.2.2.2.2.2, ?_⟩
      intro _
      have hranks := rough_rank_legality v hv hf n hn hlarge
      have hbud := tail_rough_activity_budgets v hv hf n hn hlarge
      rw [← tail_rough_rarity_eq_legality v hv hf n hn hlarge] at hbud
      exact ⟨hranks.1, (rough_fine_rank_bounds v hv hf n hn).2.2,
        hbud.1, hbud.2, hr.2.2.2.2.1⟩
  · intro w hw hf n hn
    by_cases hsmall : n < Nlow (Params.ofBounded w)
    · exact bounded_rough_small_sample_lower w hw hf n hn hsmall
    · exact bounded_rough_large_sample_lower w hw hf n hn (by omega)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
