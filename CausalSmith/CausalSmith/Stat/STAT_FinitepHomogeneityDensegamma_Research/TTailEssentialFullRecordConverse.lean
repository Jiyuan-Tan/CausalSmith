module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseLimits
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TBoundedSubmodelComparison
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TOriginalRecordAttainableRate
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TRoughFullRecordSharpLower

/-! Finite-moment homogeneity testing: TTailEssentialFullRecordConverse. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- All bounded finite-prior pairs eventually fail the required distance comparison. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def BoundedTailEssentiality (v : Params) : Prop := ∃ N : ℕ, 2 ≤ N ∧
  ∀ n : ℕ, N ≤ n → ∀ π0 π1 : FinitePrior,
    PriorNormalized π0 → PriorNormalized π1 →
    PriorSupported π0 {law | InBoundedNull v.toSmooth3 law} →
    PriorSupported π1 {law | InBoundedModel v.toSmooth3 law ∧ cLower v*rho n v ≤ hetDist law} →
    1/2 ≤ Causalean.Stat.tvDist (priorMixture n π0) (priorMixture n π1)
/-- A calibrated test bounds the minimax risk at every separation where its power guarantee holds. This statement assumes [the hδ condition](hyp:hδ), [the hlevel condition](hyp:hlevel), [the hpower condition](hyp:hpower). [This is the stated conclusion](goal). -/
-- @node: testingRiskOn_le_of_uniform_test
lemma testingRiskOn_le_of_uniform_test (n : ℕ) (Null Alt : Set ObservedLaw)
    (r δ : ℝ) (hδ : 0 ≤ δ) (φ : Test n) (hlevel : LevelValid n Null φ)
    (hpower : ∀ law ∈ Alt, r ≤ hetDist law → 1-rejectProb n law.P φ ≤ δ) :
    testingRiskOn n r Null Alt ≤ δ := by
  unfold testingRiskOn
  refine ciInf_le_of_le (f := fun ψ : {ψ : Test n // LevelValid n Null ψ} =>
    ⨆ law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law},
      1-rejectProb n law.1.P ψ.1) ?_ ⟨φ, hlevel⟩ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact worstError_nonneg n Alt r ψ.1
  · by_cases hA : Nonempty {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law}
    · have := hA
      apply ciSup_le
      intro law
      exact hpower law.1 law.2.1 law.2.2
    · have := not_nonempty_iff.mp hA
      rw [Real.iSup_of_isEmpty]
      exact hδ

/-- The bounded attaining rule precludes bounded finite-prior converses at the larger finite-moment scale. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: bounded_tail_essentiality
lemma bounded_tail_essentiality (v : Params) (hv : v.Valid) (hp : v.p < 2) :
    BoundedTailEssentiality v := by
  have hw : v.toSmooth3.Valid := hv.2
  have hv2 : (Params.ofBounded v.toSmooth3).Valid :=
    ⟨by norm_num [Params.ofBounded], hw⟩
  have hdom := finite_scale_eventually_dominates_bounded v hv hp (CAttBounded v.toSmooth3)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hdom
  refine ⟨max 2 (max N (NAtt (Params.ofBounded v.toSmooth3))), le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnAtt : NAtt (Params.ofBounded v.toSmooth3) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hsep := hN n hnN
  have hsmall := (original_record_attainable_rate.1 _ hv2).2.2.1 n hnAtt
  have hcomp := bounded_submodel_comparison v hv
  have hD : d0 ≤ maxDistBounded v.toSmooth3 := by
    rw [hcomp.2.2.2.1]
    exact hcomp.2.2.2.2.1
  have hlegal : CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 < maxDistBounded v.toSmooth3 :=
    hsmall.trans_le hD
  have hatt := (original_record_attainable_rate.2.2 _ hw).2 n hn2
  have hrisk : boundedTestingRisk n v.toSmooth3 (cLower v*rho n v) ≤ 0.0075 := by
    apply testingRiskOn_le_of_uniform_test n _ _ _ _ (by norm_num)
      (phistarBounded n v.toSmooth3)
    · intro law hnull
      exact (hatt.1 law hnull).trans (by norm_num)
    · intro law hm hd
      exact hatt.2.1 hlegal law hm (hsep.trans hd)
  intro π0 π1 h0 h1 hnull halt
  have hlow := finite_two_prior_testing_lower n
    {law | InBoundedNull v.toSmooth3 law} {law | InBoundedModel v.toSmooth3 law}
    (cLower v*rho n v) π0 π1 h0 h1 hnull halt
  change 9/10-Causalean.Stat.tvDist (priorMixture n π0) (priorMixture n π1) ≤
    boundedTestingRisk n v.toSmooth3 (cLower v*rho n v) at hlow
  linarith

/-- Dyadic upward rounding preserves divergence of the positive rough-rank target. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: roughK_tendsto_atTop
lemma roughK_tendsto_atTop (v : Params) (hv : v.Valid) :
    Filter.Tendsto (fun n : ℕ => (roughK n v : ℝ)) Filter.atTop Filter.atTop := by
  have hd := (phase_denominators v hv).2.2.2.2.2.2.2
  have ht := ((tendsto_rpow_atTop (div_pos (by norm_num : (0:ℝ) < 2) hd)).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n:ℝ))
      Filter.atTop Filter.atTop)).const_mul_atTop (show 0 < Hfine by norm_num [Hfine])
  simp only [Function.comp_def] at ht
  apply Filter.tendsto_atTop_mono' _ ?_ ht
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ Hfine*(n:ℝ)^(2/Dp v) := by
    have hr := Real.one_le_rpow hn' (div_pos (by norm_num : (0:ℝ) < 2) hd).le
    have hh : 1 ≤ Hfine := by norm_num [Hfine]
    nlinarith
  rw [roughK, leastPow2Ge_eq_dyadUp hx]
  exact le_dyadUp (by linarith)

/-- Moment normalization rewrites the rough mark as a positive power of the fine rank. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: rough_magnitude_power
lemma rough_magnitude_power (n : ℕ) (v : Params) (hv : v.Valid)
    (h : roughBranch n v) :
    magnitude n v = (16:ℝ)^(1/(v.p*qExp v)) *
      (roughK n v:ℝ)^(v.β/(v.p*qExp v)) := by
  have hp := (phase_denominators v hv).1
  have hq := (phase_denominators v hv).2.2.2.2.1
  have hk : (0:ℝ) ≤ roughK n v := by positivity
  simp only [magnitude, if_pos h, rarity]
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hk _),
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16), ← Real.rpow_mul hk]
  congr 1 <;> field_simp <;> ring

/-- The rough rare marks diverge on every tuple, independently of the phase selection. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: rough_mark_power_tendsto_atTop
lemma rough_mark_power_tendsto_atTop (v : Params) (hv : v.Valid) :
    Filter.Tendsto (fun n : ℕ => (16:ℝ)^(1/(v.p*qExp v)) *
      (roughK n v:ℝ)^(v.β/(v.p*qExp v))) Filter.atTop Filter.atTop := by
  have hp := (phase_denominators v hv).1
  have hq := (phase_denominators v hv).2.2.2.2.1
  have he : 0 < v.β/(v.p*qExp v) := div_pos hv.2.2.1.1 (mul_pos hp hq)
  exact ((tendsto_rpow_atTop he).comp (roughK_tendsto_atTop v hv)).const_mul_atTop
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The public threshold changes only finitely many marks in the rough phase. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: magnitude_tendsto_atTop
lemma magnitude_tendsto_atTop (v : Params) (hv : v.Valid) :
    Filter.Tendsto (fun n : ℕ => magnitude n v) Filter.atTop Filter.atTop := by
  by_cases hf : Fphase v < 1
  · apply (rough_mark_power_tendsto_atTop v hv).congr'
    filter_upwards [Filter.eventually_ge_atTop (Nlow v)] with n hn
    exact (rough_magnitude_power n v hv ⟨hf, hn⟩).symm
  · apply (tentMagnitude_tendsto_atTop v hv).congr'
    exact Filter.Eventually.of_forall (fun n => by simp [magnitude, roughBranch, hf])

/-- At second moment reinserting the bounded exponent recovers the public tuple. This statement assumes [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: ofBounded_toSmooth3_of_p_eq_two
lemma ofBounded_toSmooth3_of_p_eq_two (v : Params) (hp : v.p = 2) :
    Params.ofBounded v.toSmooth3 = v := by
  cases v
  simp_all [Params.ofBounded, Params.toSmooth3]

/-- The bounded constant null is a legal constant null in the original model. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: boundedNull_inNull
lemma boundedNull_inNull (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (h : InBoundedNull v.toSmooth3 law) : InNull v law := by
  have hb : InBoundedModel v.toSmooth3 law :=
    ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth, h.effectSmooth,
      h.baselineCap, h.effectCap, h.rawMoment, h.boundedOutcome⟩
  have hm := boundedModel_inModel v hv law hb
  exact ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
    hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, h.nullConstancy⟩

/-- Constant primitives in the prescribed envelope satisfy every Hölder exponent. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: holderBall_const_of_cap
lemma holderBall_const_of_cap (s c : ℝ) (hc : |c| ≤ 20) :
    holderBall s (ContinuousMap.const unitInterval c) := by
  refine ⟨continuous_const, fun _ => hc, ?_⟩
  intro x z
  simp only [ContinuousMap.const_apply, sub_self, abs_zero]
  positivity

/-- The balanced zero-effect signed-binary tent null satisfies all original primitive predicates. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_false_inNull
lemma binaryTentLaw_false_inNull (v : Params) (hv : v.Valid) (n : ℕ)
    (σ : Fin (tentRank n (Params.ofBounded v.toSmooth3)/2) → Bool) :
    InNull v (binaryTentLaw false n v.toSmooth3 σ) := by
  let e : Nuisance := ContinuousMap.const unitInterval (1/2)
  let law := deterministicLaw e 0 0
  have her : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun _ => by norm_num [e]
  have hc := deterministicLaw_primitives e 0 0 her
  have hm : InModel v law := by
    apply deterministicLaw_inModel v hv e 0 0
    · intro x; norm_num [e]
    · exact holderBall_const_of_cap _ _ (by norm_num)
    · exact holderBall_const_of_cap _ 0 (by norm_num)
    · exact holderBall_const_of_cap _ 0 (by norm_num)
    · intro x; norm_num
    · intro x; norm_num
  have hconv : binaryConversion law = binaryTentLaw false n v.toSmooth3 σ := by
    simp only [binaryConversion, binaryTentLaw, Bool.false_eq_true, if_false]
    change binaryRealization law.e law.m0 law.tau = binaryRealization e 0 0
    rw [hc.1, hc.2.1, hc.2.2.1]
  have hb := binaryConversion_inBinaryModel v law hm
  have hm' := boundedModel_inModel v hv _ (binaryModel_inBoundedModel _ _ hb)
  have hnull : NullConstancy (binaryConversion law) := by
    rw [(binaryConversion_preserves_effect law hm.baselineCap hm.effectCap).2]
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    intro x
    change (deterministicLaw e 0 0).tau x = 0
    rw [hc.2.2.1]
    rfl
  rw [← hconv]
  exact ⟨hm'.uniform, hm'.overlap, hm'.propensitySmooth, hm'.baselineSmooth,
    hm'.effectSmooth, hm'.baselineCap, hm'.effectCap, hm'.rawMoment, hnull⟩

/-- Every enumerated paired-tent null support is legal, including the nonrough branch. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: binaryTentPrior_false_supported
lemma binaryTentPrior_false_supported (v : Params) (hv : v.Valid) (n : ℕ) :
    PriorSupported (binaryTentPrior false n v.toSmooth3) {law | InNull v law} := by
  intro i hi
  exact binaryTentLaw_false_inNull v hv n _

/-- The bounded lower transfers at the matched scale on the entire second-moment face. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: second_moment_testingRisk_lower
lemma second_moment_testingRisk_lower (v : Params) (hv : v.Valid) (hp : v.p = 2)
    (n : ℕ) (hn : 2 ≤ n) : 2/5 ≤ testingRisk n v (cLower v*rho n v) := by
  have heq := ofBounded_toSmooth3_of_p_eq_two v hp
  have hbounded : 2/5 ≤ boundedTestingRisk n v.toSmooth3 (cLower v*rho n v) := by
    by_cases hf : Fphase v < 1
    · have hr := rough_full_record_sharp_lower.2 v.toSmooth3 hv.2
        (by simpa only [heq] using hf) n hn
      have he := (phase_channel_selection v hv).2 hf
      simpa only [cLowerBounded, heq, rho, he] using hr.2.2.2.2.2
    · have hf' : 1 ≤ Fphase v := le_of_not_gt hf
      have he := (phase_channel_selection v hv).1 hf'
      obtain ⟨P0, π1, hnull, he0, hnorm, hmass, halt, hD, htv, hr⟩ :=
        paired_tent_full_record_lower.2 v.toSmooth3 hv.2 n hn
      simpa only [heq, cLower, if_pos hf', rho, he, rhoOracle] using hr
  exact hbounded.trans (boundedTestingRisk_le_testingRisk v hv n _)

/-- Rough-phase bounded priors retain their null and separated supports in the original model. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp), [the hf condition](hyp:hf), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: second_moment_rough_prior_support
lemma second_moment_rough_prior_support (v : Params) (hv : v.Valid) (hp : v.p = 2)
    (hf : Fphase v < 1) (n : ℕ) (hn : 2 ≤ n) :
    PriorSupported (boundedConversePrior false n v.toSmooth3) {law | InNull v law} ∧
    PriorSupported (boundedConversePrior true n v.toSmooth3)
      {law | InModel v law ∧ cLower v*rho n v ≤ hetDist law} := by
  have heq := ofBounded_toSmooth3_of_p_eq_two v hp
  have hr := rough_full_record_sharp_lower.2 v.toSmooth3 hv.2
      (by simpa only [heq] using hf) n hn
  have he := (phase_channel_selection v hv).2 hf
  constructor
  · intro i hi
    exact boundedNull_inNull v hv _ (hr.2.2.1 i hi)
  · intro i hi
    have hs := hr.2.2.2.1 i hi
    refine ⟨boundedModel_inModel v hv _ hs.1, ?_⟩
    simpa only [cLowerBounded, heq, rho, he] using hs.2.1

/-- Every valid copula table retains the three-point arm support before mixing. [This is the stated conclusion](goal). -/
-- @node: copulaLaw_armSupport
lemma copulaLaw_armSupport (n K M : ℕ) (v : Params) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (ν : Bool) (idx : CopulaIndex K M) :
    ArmSupport (copulaLaw ν v K M a u ε L idx) L := by
  have ht := copula_table_valid n K M a u ε L h ν idx
  intro arm
  filter_upwards [] with x
  simp only [copulaLaw, tableObservedLaw, dif_pos ht]
  exact tableArm_three_atom_support _ _ _ _ _ ht arm x

/-- The public rough rarity is precisely the tail tuning in the legality lemma. This statement assumes [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: rough_rarity_eq_legality
lemma rough_rarity_eq_legality (n : ℕ) (v : Params) (hb : roughBranch n v) :
    rarity n v = legalityRarity v (roughK n v) := by
  have hk : (0 : ℝ) ≤ roughK n v := by positivity
  simp only [rarity, if_pos hb, legalityRarity, legalityB]
  rw [show 16*((roughK n v : ℝ)^(-v.β)/256) =
    (16:ℝ)⁻¹*(roughK n v : ℝ)^(-v.β) by ring]
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hk _),
    ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_mul hk]
  congr 1 <;> ring

/-- All branchwise prior supports retain the actual public mark size. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: conversePrior_armSupport
lemma conversePrior_armSupport (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (ν : Bool) :
    PriorSupported (conversePrior ν n v) {law | ArmSupport law (magnitude n v)} := by
  by_cases hb : roughBranch n v
  · have hr := rough_full_record_sharp_lower.1 v hv hb.1 n hn
    have hranks := (hr.2.2.2.2.2.2.2 hb.2).1
    have hd := (legality_copula_domains v hv _ _ hranks).1
    have he := rough_rarity_eq_legality n v hb
    have hL : magnitude n v = legalityMagnitude v (roughK n v) := by
      simp only [magnitude, if_pos hb, he, legalityMagnitude]
    simp only [conversePrior, if_pos hb, he, hL]
    intro i hi
    exact copulaLaw_armSupport 2 _ _ v _ _ _ _ hd ν _
  · simp only [conversePrior, if_neg hb, magnitude, if_neg hb]
    intro i hi
    cases ν
    · exact (tentLaw_false_arm_properties v hv n hn _).1
    · exact (tentLaw_true_arm_properties v hv n hn _).1

/-- In the rough phase the established lower lemma supplies the full converse ledger, including the finite paired-tent branch below the public threshold. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: rough_phase_converse_assembly
lemma rough_phase_converse_assembly (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
    PriorSupported (conversePrior false n v) {law | InNull v law ∧ ArmSupport law (magnitude n v)} ∧
    PriorSupported (conversePrior true n v) {law | InModel v law ∧ ArmSupport law (magnitude n v) ∧
      cLower v*rho n v ≤ hetDist law ∧ hetDist law < maxDist v} ∧
    0 < cLower v*rho n v ∧ cLower v*rho n v < maxDist v ∧
    Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/2 ∧
    2/5 ≤ testingRisk n v (cLower v*rho n v) := by
  have hr := rough_full_record_sharp_lower.1 v hv hf n hn
  have he := (phase_channel_selection v hv).2 hf
  have hscale : rho n v = (n:ℝ)^(-E4 v) := by rw [rho, he]
  rw [← hscale] at hr
  have h0 := conversePrior_armSupport v hv n hn false
  have h1 := conversePrior_armSupport v hv n hn true
  have hsep : cLower v*rho n v < maxDist v := by
    have hpw : 0 < ∑ i, priorWeight (conversePrior true n v) i := by
      rw [hr.2.1.2]; norm_num
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun i _ => hr.2.1.1 i)).mp hpw
    exact (hr.2.2.2.1 i hi).2.1.trans_lt
      ((hr.2.2.2.1 i hi).2.2.trans_le hr.2.2.2.2.1)
  refine ⟨hr.1, hr.2.1, ?_, ?_,
    mul_pos (cLower_pos v hv) (matched_scales_pos n (by omega) v).1,
    hsep, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩
  · intro i hi
    exact ⟨hr.2.2.1 i hi, h0 i hi⟩
  · intro i hi
    have hs := hr.2.2.2.1 i hi
    exact ⟨hs.1, h1 i hi, hs.2.1, hs.2.2.trans_le hr.2.2.2.2.1⟩

/-- In the nonrough phase the canonical paired-tent receipt supplies the full converse ledger. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: nonrough_phase_converse_assembly
lemma nonrough_phase_converse_assembly (v : Params) (hv : v.Valid)
    (hf : 1 ≤ Fphase v) (n : ℕ) (hn : 2 ≤ n) :
    PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
    PriorSupported (conversePrior false n v) {law | InNull v law ∧ ArmSupport law (magnitude n v)} ∧
    PriorSupported (conversePrior true n v) {law | InModel v law ∧ ArmSupport law (magnitude n v) ∧
      cLower v*rho n v ≤ hetDist law ∧ hetDist law < maxDist v} ∧
    0 < cLower v*rho n v ∧ cLower v*rho n v < maxDist v ∧
    Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/2 ∧
    2/5 ≤ testingRisk n v (cLower v*rho n v) := by
  have hb : ¬ roughBranch n v := fun h => (not_lt_of_ge hf) h.1
  have he := (phase_channel_selection v hv).1 hf
  have hs : cLower v*rho n v = cOracle v*rhoOracle n v := by
    simp only [cLower, if_pos hf, rho, he, rhoOracle]
  have hr := tent_canonical_lower_receipt v hv n hn
  have hnull := hr.2.1
  have halt := hr.2.2.2.2.2.2.2.1
  have hD := hr.2.2.2.2.2.2.2.2.1
  have htv := hr.2.2.2.2.2.2.2.2.2.1
  have hrisk := hr.2.2.2.2.2.2.2.2.2.2.2
  have hsep : cOracle v*rhoOracle n v < maxDist v := by
    obtain ⟨i, hi⟩ := hr.2.2.2.2.2.2.1
    have hi' := halt i hi
    exact hi'.2.2.2.1.trans_lt (hi'.2.2.2.2.1.trans_le hD)
  simp only [conversePrior, if_neg hb, magnitude, if_neg hb]
  refine ⟨(tentPrior_normalized false n v).1, (tentPrior_normalized true n v).1,
    ?_, ?_, mul_pos (cLower_pos v hv) (matched_scales_pos n (by omega) v).1,
    hs.symm ▸ hsep, ?_, hs.symm ▸ hrisk⟩
  · intro i hi
    have heq : priorLaw (tentPrior false n v) i = tentLaw false n v (fun _ => false) := by
      change tentLaw false n v _ = tentLaw false n v _
      rw [tentLaw_false_eq_zero_table, tentLaw_false_eq_zero_table]
    rw [heq]
    exact ⟨hnull, hr.2.2.2.1⟩
  · intro i hi
    have hi' := halt i hi
    exact ⟨hi'.1, hi'.2.2.1, hs.symm ▸ hi'.2.2.2.1, hi'.2.2.2.2.1.trans_le hD⟩
  · simpa only [converseMixture, conversePrior, if_neg hb, tentPrior_false_mixture] using htv

/-- The established bounded lower receipts certify the exact branchwise witness pair. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma second_moment_bounded_receipt (v : Params) (hv : v.Valid) (hp : v.p = 2)
    (n : ℕ) (hn : 2 ≤ n) :
    PriorNormalized (boundedConversePrior false n v.toSmooth3) ∧
    PriorNormalized (boundedConversePrior true n v.toSmooth3) ∧
    PriorSupported (boundedConversePrior false n v.toSmooth3) {law | InBoundedNull v.toSmooth3 law} ∧
    PriorSupported (boundedConversePrior true n v.toSmooth3)
      {law | InBoundedModel v.toSmooth3 law ∧ cLower v*rho n v ≤ hetDist law ∧ hetDist law < d0} ∧
    Causalean.Stat.tvDist (boundedConverseMixture false n v.toSmooth3)
      (boundedConverseMixture true n v.toSmooth3) < 1/2 ∧
    2/5 ≤ boundedTestingRisk n v.toSmooth3 (cLower v*rho n v) := by
  have heq := ofBounded_toSmooth3_of_p_eq_two v hp
  by_cases hf : Fphase v < 1
  · have hr := rough_full_record_sharp_lower.2 v.toSmooth3 hv.2
      (by simpa only [heq] using hf) n hn
    have he := (phase_channel_selection v hv).2 hf
    simpa only [cLowerBounded, heq, rho, he] using hr
  · have hf' : 1 ≤ Fphase v := le_of_not_gt hf
    have he := (phase_channel_selection v hv).1 hf'
    have hb : ¬ roughBranch n (Params.ofBounded v.toSmooth3) := by
      rw [heq]
      exact fun h => hf h.1
    have hs : cLower v*rho n v =
        cOracle (Params.ofBounded v.toSmooth3)*rhoOracle n (Params.ofBounded v.toSmooth3) := by
      simp only [heq, cLower, if_pos hf', rho, he, rhoOracle]
    have hr := binary_tent_canonical_lower_receipt v.toSmooth3 hv.2 n hn
    have hnull := hr.1
    have hm0 : InBinaryModel v.toSmooth3 (binaryTentLaw false n v.toSmooth3 (fun _ => false)) :=
      ⟨hnull.uniform, hnull.overlap, hnull.propensitySmooth, hnull.baselineSmooth,
        hnull.effectSmooth, hnull.baselineCap, hnull.effectCap, hnull.rawMoment, hnull.signedBinaryOutcome⟩
    have hm0b := binaryModel_inBoundedModel _ _ hm0
    have hnullb : InBoundedNull v.toSmooth3 (binaryTentLaw false n v.toSmooth3 (fun _ => false)) :=
      ⟨hm0b.uniform, hm0b.overlap, hm0b.propensitySmooth, hm0b.baselineSmooth,
        hm0b.effectSmooth, hm0b.baselineCap, hm0b.effectCap, hm0b.rawMoment,
        hm0b.boundedOutcome, hnull.nullConstancy⟩
    simp only [boundedConversePrior, if_neg hb, boundedConverseMixture]
    refine ⟨(binaryTentPrior_normalized false n v.toSmooth3).1,
      (binaryTentPrior_normalized true n v.toSmooth3).1, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hconst : priorLaw (binaryTentPrior false n v.toSmooth3) i =
          binaryTentLaw false n v.toSmooth3 (fun _ => false) := by
        change binaryTentLaw false n v.toSmooth3 _ = binaryTentLaw false n v.toSmooth3 _
        simp only [binaryTentLaw, Bool.false_eq_true, if_false]
      rw [hconst]
      exact hnullb
    · intro i hi
      have ha := hr.2.2.2.2.1 i hi
      exact ⟨binaryModel_inBoundedModel _ _ ha.1, hs.symm ▸ ha.2.2.1, ha.2.2.2⟩
    · simpa only [boundedConversePrior, if_neg hb, binaryTentPrior_false_mixture] using
        hr.2.2.2.2.2.2.1
    · simpa only [hs] using hr.2.2.2.2.2.2.2

/-- Nonnegative normalized weights give a nonempty positive support with total mass one. Adding weights of coincident law values leaves this positive-support mass unchanged. This statement assumes [the hπ condition](hyp:hπ). [This is the stated conclusion](goal). -/
lemma finite_prior_positive_mass (π : FinitePrior) (hπ : PriorNormalized π) :
    (∃ i, 0 < priorWeight π i) ∧
    (∑ i ∈ Finset.univ.filter (fun i => 0 < priorWeight π i), priorWeight π i) = 1 := by
  constructor
  · have hs : 0 < ∑ i, priorWeight π i := by rw [hπ.2]; norm_num
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hπ.1 i)).mp hs
    exact ⟨i, hi⟩
  · rw [Finset.sum_filter]
    convert hπ.2 using 1
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · exact (le_antisymm (le_of_not_gt h) (hπ.1 i)).symm

/-- A failed test problem with a legal alternative bounds its capped radius below. This statement assumes [the hr condition](hyp:hr), [the hne condition](hyp:hne), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
lemma second_moment_capped_lower (n : ℕ) (Null Alt : Set ObservedLaw)
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

/-- The existing ceiling and scale identity gives the half-witness threshold bound. This is the unchanged calculation already used inside attainment_threshold. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma second_moment_attainment_half (v : Params) (hv : v.Valid) (n : ℕ) (hn : NAtt v ≤ n) :
    CAtt v*rho n v ≤ d0/2 := by
  have he : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have hc : 0 < CAtt v := (original_record_attainable_rate.1 v hv).1
  have hd : 0 < d0 := by unfold d0; positivity
  have ht : 0 < 2*CAtt v/d0 := by positivity
  have hceil : max 4 ((2*CAtt v/d0)^(1/Eexp v)) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have htarget := (le_max_right (4:ℝ) ((2*CAtt v/d0)^(1/Eexp v))).trans hceil
  have hpower := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (2*CAtt v/d0)^(1/Eexp v))
    htarget (neg_nonpos.mpr he.le)
  rw [← Real.rpow_mul ht.le] at hpower
  have hid : (1/Eexp v)*(-Eexp v) = -1 := by field_simp
  rw [hid, Real.rpow_neg_one] at hpower
  calc
    _ ≤ CAtt v*(2*CAtt v/d0)⁻¹ := mul_le_mul_of_nonneg_left hpower hc.le
    _ = d0/2 := by field_simp

/-- The complete second-moment face uses the existing bounded branch selector and rules. It records normalized nonempty supports, mass one, bounded support and full-record TV, risk transfer, identical scales and constants, matching capped radii, size, conditional nonempty power, the half-witness threshold and the small-sample zero rule. This statement assumes [the v parameter](hyp:v), [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def SecondMomentFacePackage (v : Params) (n : ℕ) : Prop :=
  (∀ ν : Bool, PriorNormalized (boundedConversePrior ν n v.toSmooth3) ∧
    (∃ i, 0 < priorWeight (boundedConversePrior ν n v.toSmooth3) i) ∧
    (∑ i ∈ Finset.univ.filter (fun i => 0 < priorWeight (boundedConversePrior ν n v.toSmooth3) i),
      priorWeight (boundedConversePrior ν n v.toSmooth3) i) = 1) ∧
  PriorSupported (boundedConversePrior false n v.toSmooth3) {law | InBoundedNull v.toSmooth3 law} ∧
  PriorSupported (boundedConversePrior true n v.toSmooth3)
    {law | InBoundedModel v.toSmooth3 law ∧ cLower v*rho n v ≤ hetDist law ∧ hetDist law < d0} ∧
  Causalean.Stat.tvDist (boundedConverseMixture false n v.toSmooth3)
    (boundedConverseMixture true n v.toSmooth3) < 1/2 ∧
  2/5 ≤ boundedTestingRisk n v.toSmooth3 (cLower v*rho n v) ∧
  boundedTestingRisk n v.toSmooth3 (cLower v*rho n v) ≤ testingRisk n v (cLower v*rho n v) ∧
  rho n v = rhoBounded n v.toSmooth3 ∧ cLower v = cLowerBounded v.toSmooth3 ∧
  CAtt v = CAttBounded v.toSmooth3 ∧ NAtt v = NAttBounded v.toSmooth3 ∧
  maxDist v = maxDistBounded v.toSmooth3 ∧
  cLower v*rho n v ≤ criticalRadius n v ∧ criticalRadius n v ≤ CAtt v*rho n v ∧
  cLowerBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ boundedCriticalRadius n v.toSmooth3 ∧
  boundedCriticalRadius n v.toSmooth3 = binaryCriticalRadius n v.toSmooth3 ∧
  boundedCriticalRadius n v.toSmooth3 ≤ CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 ∧
  (∀ law, InNull v law → rejectProb n law.P (phistar n v) ≤ 0.0075) ∧
  (∀ law, InBoundedNull v.toSmooth3 law → rejectProb n law.P (phistarBounded n v.toSmooth3) ≤ 0.0075) ∧
  (CAtt v*rho n v < maxDist v →
    (∃ law, InModel v law ∧ CAtt v*rho n v ≤ hetDist law) ∧
    (∃ law, InBoundedModel v.toSmooth3 law ∧ CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ hetDist law) ∧
    (∀ law, InModel v law → CAtt v*rho n v ≤ hetDist law →
      1-rejectProb n law.P (phistar n v) ≤ 0.0075) ∧
    (∀ law, InBoundedModel v.toSmooth3 law → CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ hetDist law →
      1-rejectProb n law.P (phistarBounded n v.toSmooth3) ≤ 0.0075)) ∧
  (NAtt v ≤ n → CAtt v*rho n v ≤ d0/2 ∧ CAtt v*rho n v < maxDist v ∧
    CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 < maxDistBounded v.toSmooth3) ∧
  (n = 2 ∨ n = 3 → ∀ z, (phistar n v).1 z = 0 ∧ (phistarBounded n v.toSmooth3).1 z = 0)

/-- Existing bounded lower and original-record attainment receipts assemble the full face. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma second_moment_face_package (v : Params) (hv : v.Valid) (hp : v.p = 2)
    (n : ℕ) (hn : 2 ≤ n) : SecondMomentFacePackage v n := by
  have heq := ofBounded_toSmooth3_of_p_eq_two v hp
  have hs : rho n v = rhoBounded n v.toSmooth3 := by simp only [rhoBounded, heq]
  have hc : cLower v = cLowerBounded v.toSmooth3 := by simp only [cLowerBounded, heq]
  have hC : CAtt v = CAttBounded v.toSmooth3 := by simp only [CAttBounded, heq]
  have hN : NAtt v = NAttBounded v.toSmooth3 := by simp only [NAttBounded, heq]
  have hD : maxDistBounded v.toSmooth3 = maxDist v := maxDistBounded_eq_maxDist v
  obtain ⟨h0, h1, hnull, halt, htv, hrisk⟩ := second_moment_bounded_receipt v hv hp n hn
  obtain ⟨i, hi⟩ := (finite_prior_positive_mass _ h1).1
  have ha := halt i hi
  have hd : d0 ≤ maxDistBounded v.toSmooth3 := hD.symm ▸ model_distance_lower v hv
  have hsep : 0 < cLower v*rho n v ∧ cLower v*rho n v < maxDistBounded v.toSmooth3 :=
    ⟨mul_pos (cLower_pos v hv) (matched_scales_pos n (by omega) v).1,
      ha.2.1.trans_lt (ha.2.2.trans_le hd)⟩
  have hblo : cLower v*rho n v ≤ boundedCriticalRadius n v.toSmooth3 :=
    second_moment_capped_lower n _ _ _ _ hsep ⟨_, ha.1, ha.2.1⟩ (by
      change 1/10 < boundedTestingRisk n v.toSmooth3 (cLower v*rho n v)
      linarith)
  have hcomp := bounded_submodel_comparison v hv
  have hatt := (original_record_attainable_rate.1 v hv).2.1 n hn
  have hbatt := (original_record_attainable_rate.2.2 v.toSmooth3 hv.2).2 n hn
  refine ⟨?_, hnull, halt, htv, hrisk, boundedTestingRisk_le_testingRisk v hv n _,
    hs, hc, hC, hN, hD.symm,
    hblo.trans (hcomp.2.2.2.2.2.2.1 n hn).2.2, hatt.2.2,
    ?_, (hcomp.2.2.2.2.2.2.1 n hn).2.1.symm, hbatt.2.2,
    hatt.1, hbatt.1, ?_, ?_, ?_⟩
  · intro ν
    have hnorm : PriorNormalized (boundedConversePrior ν n v.toSmooth3) := by
      cases ν
      · exact h0
      · exact h1
    exact ⟨hnorm, finite_prior_positive_mass _ hnorm⟩
  · simpa only [← hc, ← hs] using hblo
  · intro hpower
    have hpowerb : CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 < maxDistBounded v.toSmooth3 := by
      simpa only [← hC, ← hs, hD] using hpower
    have hnonempty : ∃ law, InBoundedModel v.toSmooth3 law ∧
        CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 ≤ hetDist law := by
      by_contra hh
      have hbound : ∀ law, InBoundedModel v.toSmooth3 law →
          hetDist law ≤ CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 := by
        intro law hm
        exact le_of_lt (lt_of_not_ge (fun h => hh ⟨law, hm, h⟩))
      have hmax : maxDistBounded v.toSmooth3 ≤ CAttBounded v.toSmooth3*rhoBounded n v.toSmooth3 := by
        change sSup (hetDist '' {law | InBoundedModel v.toSmooth3 law}) ≤ _
        refine csSup_le ?_ ?_
        · exact ⟨hetDist (priorLaw (boundedConversePrior true n v.toSmooth3) i), _, ha.1, rfl⟩
        · rintro t ⟨law, hm, rfl⟩
          exact hbound law hm
      exact (not_le_of_gt hpowerb) hmax
    obtain ⟨law, hm, hdist⟩ := hnonempty
    refine ⟨⟨law, boundedModel_inModel v hv law hm, ?_⟩, ⟨law, hm, hdist⟩,
      hatt.2.1 hpower, hbatt.2.1 hpowerb⟩
    simpa only [← hC, ← hs] using hdist
  · intro hthreshold
    have hhalf := second_moment_attainment_half v hv n hthreshold
    have hsmall := (original_record_attainable_rate.1 v hv).2.2.1 n hthreshold
    have hsmallD := hsmall.trans_le (model_distance_lower v hv)
    exact ⟨hhalf, hsmallD, by simpa only [← hC, ← hs, hD] using hsmallD⟩
  · intro hsmall z
    have hn4 : n < 4 := by omega
    simp [phistar, phistarBounded, ledgerTest, ledgerRule, hn4]

/-- [Tail essential full record converse](goal). Use the explicit scales and constants of Definition \(\mathrm{def:sharp\mbox{-}frontier\mbox{-}scales}\). For every \(v\in\mathcal V\) and every \(n\ge2\), there are the following explicit finite mixing laws and rare-mark parameters satisfying \[ \pi_{0,n,v}(H_0(v))=1,\quad \pi_{1,n,v}\{P\in\mathcal M_v:c_v\rho_n(v)\le d(P)<D_v\}=1, \quad0<c_v\rho_n(v)<D_v, \] \[ \operatorname{TV}(\mathbb P_{0,n,v},\mathbb P_{1,n,v})<1/2, \qquad B_n(v,c_v\rho_n(v))\ge2/5>1/10. \] When \(F(p)<1\) and \(n\ge N_{\mathrm{low}}(v)\), use the dyadic \(K,M\) and tail copula priors of Lemma \(\mathrm{lem:rough\mbox{-}full\mbox{-}record\mbox{-}sharp\mbox{-}lower}\), with \[ \varepsilon_{n,v}=16^{-1/q}K^{-\beta/q},\qquad L_{n,v}=\varepsilon_{n,v}^{-1/p}. \] Otherwise use the established opposite paired-tent family, with \[ N=2\lceil n^{2q/(2\gamma+q)}\rceil,\quad h=1/N,\quad \varepsilon_{n,v}=h^{\gamma/q},\qquad L_{n,v}=h^{-\gamma/(p-1)}. \] All arm supports are contained in \(\{0,-L_{n,v},L_{n,v}\}\), all support laws satisfy every original primitive predicate separately, and \(L_{n,v}\to\infty\). Every alternative has a deterministic \(\gamma\)-smooth original mean effect conditional on its latent coefficients. The complete-record likelihood bound retains zero marks, both treatment labels, all occupancies, and the odd overlap tensors. Throughout \(p<2\), \(\rho_n(v)/\rho_n^{\mathrm b}(w)\to\infty\). A normalized finite prior means a probability measure \(\pi=\sum_{j=1}^{k}\omega_j\delta_{P_j}\) on original-record laws, with \(k\ge1\), \(\omega_j\ge0\) and \(\sum_j\omega_j=1\). Its positive-weight support is \(\operatorname{supp}_+(\pi)=\{P_j:\omega_j>0\}\), and its complete-record mixture is \[ \mathbb P_{\pi,n}=\int P^{\otimes n}\,\pi(dP). \] Write \(w=(\alpha,\beta,\gamma)\). For each fixed \(v\in\mathcal V\) with \(p<2\), there exists an integer \(N(v)\ge2\) such that for every \(n\ge N(v)\) and every pair of normalized finite priors \(\pi_0,\pi_1\), \[ \left. \begin{gathered} \operatorname{supp}_+(\pi_0)\subseteq H_0^{\mathrm b}(w),\\ \operatorname{supp}_+(\pi_1)\subseteq \{P\in\mathcal M_w^{\mathrm b}:c_v\rho_n(v)\le d(P)\} \end{gathered} \right\} \quad\Longrightarrow\quad \operatorname{TV}(\mathbb P_{\pi_0,n},\mathbb P_{\pi_1,n})\ge\frac12. \] Thus the exclusion quantifies over all such finite prior pairs, separately for each fixed tuple. This statement assumes [the hv condition](hyp:hv).

On
the complementary face \(p=2\), for every \(n\ge2\), take the branchwise bounded witness pair
\(\pi^{\mathrm b}_{0,n,v},\pi^{\mathrm b}_{1,n,v}\): use the signed-binary paired-tent package when
\(F(2)\ge1\), the bounded rough package when \(F(2)<1\) and \(n\ge N_{\mathrm{low}}(v)\), and the
signed-binary paired-tent fallback otherwise. Both priors are normalized finite probability laws
with nonempty positive-weight supports. Define \(\mathbb P^{\mathrm b}_{\nu,n,v}=\mathbb
P_{\pi^{\mathrm b}_{\nu,n,v},n}\), \(\nu\in\{0,1\}\). They satisfy
\[
 \begin{gathered}
\sum_{P\in\operatorname{supp}_+(\pi^{\mathrm b}_{\nu,n,v})}
       \pi^{\mathrm
b}_{\nu,n,v}(\{P\})=1,\qquad \nu\in\{0,1\},\\
  \operatorname{supp}_+(\pi^{\mathrm
b}_{0,n,v})\subseteq H_0^{\mathrm b}(w),\\
  \operatorname{supp}_+(\pi^{\mathrm b}_{1,n,v})\subseteq
\{P\in\mathcal M_w^{\mathrm b}:c_v\rho_n(v)\le d(P)<d_0\},\\
  \operatorname{TV}(\mathbb P^{\mathrm
b}_{0,n,v},
                    \mathbb P^{\mathrm b}_{1,n,v})<\frac12,\\
  \frac25\le B_n^{\mathrm
b}(w,c_v\rho_n(v))
          \le B_n(v,c_v\rho_n(v)).
 \end{gathered}
\]
The unchanged scales and
multipliers agree on this face:
\[
 \rho_n(v)=\rho_n^{\mathrm b}(w),\qquad
 c_v=c_w^{\mathrm
b},\qquad C_v=C_w^{\mathrm b}.
\]
The bounded lower witnesses and the established original-record
attainable theorem therefore give, for every \(n\ge2\),
\[
 \begin{gathered}
 c_v\rho_n(v)\le
r_n^*(v)\le C_v\rho_n(v),\\
 c_w^{\mathrm b}\rho_n^{\mathrm b}(w)
 \le r_n^{*,\mathrm
b}(w)=r_n^{*,\mathrm{bin}}(w)
 \le C_w^{\mathrm b}\rho_n^{\mathrm b}(w).
 \end{gathered}
\]
The
upper inequalities use the existing total original and bounded rules and retain their finite-sample
conditions:
\[
 \sup_{P\in H_0(v)}\mathsf R_n(P,\phi^*_{n,v})\le0.0075,
 \qquad
 \sup_{P\in
H_0^{\mathrm b}(w)}
      \mathsf R_n(P,\phi^{*,\mathrm b}_{n,w})\le0.0075.
\]
Only when
\(C_v\rho_n(v)<D_v=D_w^{\mathrm b}\), the alternatives are nonempty and
\[
 \begin{gathered}
\sup_{P\in\mathcal M_v:\ d(P)\ge C_v\rho_n(v)}
     \{1-\mathsf R_n(P,\phi^*_{n,v})\}\le0.0075,\\
\sup_{P\in\mathcal M_w^{\mathrm b}:\ d(P)\ge
                        C_w^{\mathrm b}\rho_n^{\mathrm
b}(w)}
     \{1-\mathsf R_n(P,\phi^{*,\mathrm b}_{n,w})\}\le0.0075.
 \end{gathered}
\]
The existing
public thresholds satisfy \(N_v=N_w^{\mathrm b}\) on \(p=2\), and for \(n\ge N_v\) the common power
separation is at most \(d_0/2\), hence strictly below both maxima. Before that threshold the rules
remain calibrated, with their zero branch at \(n=2,3\); a nominal level at or above the common
maximum asserts only saturation. All constructions, constants and conclusions are the existing ones
assembled on this face. -/
-- @node: thm:tail-essential-full-record-converse
theorem tail_essential_full_record_converse (v : Params) (hv : v.Valid) :
    (∀ n : ℕ, 2 ≤ n →
      PriorNormalized (conversePrior false n v) ∧ PriorNormalized (conversePrior true n v) ∧
      PriorSupported (conversePrior false n v) {law | InNull v law ∧ ArmSupport law (magnitude n v)} ∧
      PriorSupported (conversePrior true n v) {law | InModel v law ∧ ArmSupport law (magnitude n v) ∧
        cLower v*rho n v ≤ hetDist law ∧ hetDist law < maxDist v} ∧
      0 < cLower v*rho n v ∧ cLower v*rho n v < maxDist v ∧
      Causalean.Stat.tvDist (converseMixture false n v) (converseMixture true n v) < 1/2 ∧
      2/5 ≤ testingRisk n v (cLower v*rho n v)) ∧
    Filter.Tendsto (fun n : ℕ => magnitude n v) Filter.atTop Filter.atTop ∧
    (v.p < 2 → Filter.Tendsto (fun n : ℕ => rho n v/rhoBounded n v.toSmooth3) Filter.atTop Filter.atTop ∧ BoundedTailEssentiality v) ∧
    (v.p=2 → ∀ n : ℕ, 2 ≤ n →
      PriorSupported (boundedConversePrior false n v.toSmooth3) {law | InNull v law} ∧
      PriorSupported (boundedConversePrior true n v.toSmooth3) {law | InModel v law ∧ cLower v*rho n v ≤ hetDist law} ∧
      2/5 ≤ testingRisk n v (cLower v*rho n v) ∧
      SecondMomentFacePackage v n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    by_cases hf : Fphase v < 1
    · exact rough_phase_converse_assembly v hv hf n hn
    · exact nonrough_phase_converse_assembly v hv (le_of_not_gt hf) n hn
  · exact magnitude_tendsto_atTop v hv
  · intro hp
    exact ⟨matched_scale_ratio_tendsto v hv hp, bounded_tail_essentiality v hv hp⟩
  · intro hp n hn
    refine ⟨?_, ?_, second_moment_testingRisk_lower v hv hp n hn,
      second_moment_face_package v hv hp n hn⟩
    · by_cases hf : Fphase v < 1
      · exact (second_moment_rough_prior_support v hv hp hf n hn).1
      · have heq := ofBounded_toSmooth3_of_p_eq_two v hp
        have hbranch : ¬ roughBranch n (Params.ofBounded v.toSmooth3) := by
          simp only [roughBranch, heq]
          exact fun h => hf h.1
        simpa only [boundedConversePrior, if_neg hbranch] using
          binaryTentPrior_false_supported v hv n
    · by_cases hf : Fphase v < 1
      · exact (second_moment_rough_prior_support v hv hp hf n hn).2
      · have heq := ofBounded_toSmooth3_of_p_eq_two v hp
        have hbranch : ¬ roughBranch n (Params.ofBounded v.toSmooth3) := by
          simp only [roughBranch, heq]
          exact fun h => hf h.1
        have he := (phase_channel_selection v hv).1 (le_of_not_gt hf)
        have hbranchv : ¬ roughBranch n v := fun h => hf h.1
        simpa only [boundedConversePrior, if_neg hbranch, heq, if_neg hbranchv, cLower,
          if_pos (le_of_not_gt hf), rho, he, rhoOracle] using
          binaryTentPrior_true_supported v hv n hn

end CausalSmith.Stat.FinitepHomogeneityDensegamma
