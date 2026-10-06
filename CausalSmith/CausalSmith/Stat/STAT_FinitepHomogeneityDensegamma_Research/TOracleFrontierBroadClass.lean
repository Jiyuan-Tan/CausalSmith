module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TOracleFrontierResolved

/-! Supplied-propensity testing on the broader continuous-representative model. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The broader oracle model is nonempty and retains the universal effect-distance cap. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
lemma oracle_model_distance_bounds (v : Params) (hv : v.Valid) :
    d0 ≤ maxDistOracle v ∧ maxDistOracle v ≤ 1/2 := by
  have hw : InOracleModel v separatedWitness :=
    (separatedWitness_inModel v hv).toInOracleModel
  have hb : ∀ r ∈ hetDist '' {law | InOracleModel v law}, r ≤ (1/2:ℝ) := by
    rintro r ⟨law, hm, rfl⟩
    exact hetDist_le_half law hm.effectCap
  constructor
  · rw [← separatedWitness_distance]
    exact le_csSup ⟨1/2, hb⟩ ⟨separatedWitness, hw, rfl⟩
  · exact csSup_le ⟨hetDist separatedWitness, separatedWitness, hw, rfl⟩ hb

/-- [Oracle frontier on the broader continuous-carrier class](goal).
For every valid public tuple, d0 <= maxDistOracle <= 1/2. For every n >= 2 the broader
oracle radius lies between cOracle * rhoOracle and COr * rhoOracle, with testing risk
at least 2/5 at the lower separation. The unchanged total jointly Borel oracleTest,
with its dyadic clipped inverse-propensity score and independent-block centered histogram
vectors, has size at most 0.01 on the entire broader null and type-II error at most 0.01
at the upper separation whenever it is below maxDistOracle. For n >= NOr that separation
is at most d0/2; saturated separations carry no power claim.
The converse supplies a same-class null and a normalized nonempty finite prior of alternatives
that belong to both the original and broader classes, with the same entire constant propensity 1/2, distances in
[cOracle * rhoOracle,d0), full original-record mixture TV below 1/2, and a positive-weight
alternative of type-II error at least 2/5 for every allowed level-valid OracleTest.
The untruncated original inverse-propensity score still has conditional mean law.tau.
The exponent has a positive lower bound on each valid compact set, cOracle >= 1/(64 sqrt 3),
and COr is the fixed constant 3(120 + 128 sqrt(160 sqrt 2)); no logarithm is needed.
All continuous representatives and the six retained model atoms remain unchanged.
Neither deleted quantitative nuisance Hölder restriction is consumed by the upper proof.
-/
-- @node: thm:oracle-frontier-broad-class
theorem oracle_frontier_broad_class :
    (∀ v : Params, v.Valid →
      d0 ≤ maxDistOracle v ∧ maxDistOracle v ≤ 1/2 ∧
      1/(64*Real.sqrt 3) ≤ cOracle v ∧ 0 < COr ∧
      (∀ n : ℕ, 2 ≤ n → cOracle v*rhoOracle n v ≤ oracleBroadCriticalRadius n v ∧
        oracleBroadCriticalRadius n v ≤ COr*rhoOracle n v ∧
        (∀ law, InOracleNull v law → oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
        (COr*rhoOracle n v < maxDistOracle v → ∀ law, InOracleModel v law →
          COr*rhoOracle n v ≤ hetDist law →
          1-oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
        2/5 ≤ oracleBroadTestingRisk n v (cOracle v*rhoOracle n v) ∧
        (∃ f : Nuisance, ∃ P0 : ObservedLaw, ∃ π1 : FinitePrior,
          InNull v P0 ∧ InOracleNull v P0 ∧ P0.e = f ∧
          (∀ x, f x = 1/2) ∧ PriorNormalized π1 ∧
          (∃ i, 0 < priorWeight π1 i) ∧
          PriorSupported π1 {law | InModel v law ∧ InOracleModel v law ∧ law.e = f ∧
            cOracle v*rhoOracle n v ≤ hetDist law ∧ hetDist law < d0} ∧
          Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π1) < 1/2 ∧
          (∀ φ : OracleTest n,
            (∀ law, InOracleNull v law → oracleRejectProb n law φ ≤ 1/10) →
            ∃ i, 0 < priorWeight π1 i ∧
              2/5 ≤ 1-oracleRejectProb n (priorLaw π1 i) φ))) ∧
      (∀ n : ℕ, NOr v ≤ n → COr*rhoOracle n v ≤ d0/2) ∧
      (∀ law, InOracleModel v law → ∀ᵐ x ∂design,
        law.e x*(∫ y, ipwUntruncated law.e (x,true,y) ∂law.Q true x)+
          (1-law.e x)*(∫ y, ipwUntruncated law.e (x,false,y) ∂law.Q false x)=law.tau x)) ∧
    OracleCompactUniformity := by
  refine ⟨?_, oracle_compact_uniformity⟩
  intro v hv
  refine ⟨(oracle_model_distance_bounds v hv).1,
    (oracle_model_distance_bounds v hv).2, cOracle_uniform_lower v hv, COr_pos, ?_,
    fun n hn => oracle_attainment_threshold v hv n hn,
    fun law hm => oracle_untruncated_mean_identity v hv law hm⟩
  intro n hn
  obtain ⟨L, hLlim, hpriors⟩ := paired_tent_full_record_lower.1 v hv
  obtain ⟨P0, π1, hL, hnull, he0, hsupport0, hmoment0, hnorm, hpos,
    hsupport, hd, htv, hrisk, hrawrisk⟩ := hpriors n hn
  have hdOracle := oracle_model_distance_bounds v hv
  have hlegal : PriorSupported π1 {law | InModel v law ∧ InOracleModel v law ∧
      law.e = P0.e ∧ cOracle v*rhoOracle n v ≤ hetDist law ∧ hetDist law < d0} := by
    intro i hi
    obtain ⟨hm, he, hs, hlo, hhi, hmom⟩ := hsupport i hi
    refine ⟨hm, hm.toInOracleModel, ?_, hlo, hhi⟩
    ext x
    rw [he x, he0 x]
  obtain ⟨i, hi⟩ := hpos
  have hip := hlegal i hi
  have hsep : 0 < cOracle v*rhoOracle n v := by
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    unfold cOracle rhoOracle
    positivity
  have hriskBroad : 2/5 ≤ oracleBroadTestingRisk n v (cOracle v*rhoOracle n v) := by
    let zeroOracleTest : OracleTest n :=
      ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
    have hz : ∀ law, InOracleNull v law →
        oracleRejectProb n law zeroOracleTest ≤ 1/10 := by
      intro law _
      simp [oracleRejectProb, zeroOracleTest]
    let : Nonempty {φ : OracleTest n // ∀ law, InOracleNull v law →
        oracleRejectProb n law φ ≤ 1/10} := ⟨⟨zeroOracleTest, hz⟩⟩
    unfold oracleBroadTestingRisk
    apply le_ciInf
    intro φ
    obtain ⟨j, hj, herr⟩ := oracle_single_null_prior_error_witness n P0 π1 hnorm
      (fun j hj => (hlegal j hj).2.2.1) htv φ.1 (φ.2 P0 hnull.toInOracleNull)
    have hb : BddAbove (Set.range (fun law :
        {law : ObservedLaw // InOracleModel v law ∧
          cOracle v*rhoOracle n v ≤ hetDist law} =>
        1-oracleRejectProb n law.1 φ.1)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨law, rfl⟩
      linarith [(oracleRejectProb_bounds n law.1 φ.1).1]
    exact herr.trans (le_ciSup hb
      ⟨priorLaw π1 j, (hlegal j hj).2.1, (hlegal j hj).2.2.2.1⟩)
  have hlower : cOracle v*rhoOracle n v ≤ oracleBroadCriticalRadius n v :=
    oracleBroadCriticalRadius_ge_of_failed n v _
      ⟨hsep, hip.2.2.2.1.trans_lt (hip.2.2.2.2.trans_le hdOracle.1)⟩
      ⟨priorLaw π1 i, hip.2.1, hip.2.2.2.1⟩ (by linarith)
  have hattain : oracleBroadCriticalRadius n v ≤ COr*rhoOracle n v ∧
      (∀ law, InOracleNull v law → oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
      (COr*rhoOracle n v < maxDistOracle v → ∀ law, InOracleModel v law →
        COr*rhoOracle n v ≤ hetDist law →
        1-oracleRejectProb n law (oracleTest n v) ≤ 0.01) := by
    have hcal : (∀ law, InOracleNull v law →
        oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
        (∀ law, InOracleModel v law →
          20*(oracleJ n v:ℝ)^(-v.γ)+5*oracleBias n v+
            128*Real.sqrt (Real.sqrt (oracleJ n v)*oracleCov n v) ≤ hetDist law →
          1-oracleRejectProb n law (oracleTest n v) ≤ 0.01) := by
      constructor
      · exact fun law hnull => oracle_whole_null_size_le n v hn hv law hnull
      · intro law hm hdist
        have hpopulation : hetDist law-20*(oracleJ n v:ℝ)^(-v.γ)-oracleBias n v ≤
            ‖∫ data, oracleBlockVec n v law.e false data
              ∂Measure.pi (fun _ : Fin n => law.P)‖ :=
          oracle_alternative_population_norm_ge n v hn hv law hm
        apply oracle_power_of_mean_bound n v hn hv law hm
        linarith
    have hpower : COr*rhoOracle n v < maxDistOracle v →
        ∀ law, InOracleModel v law → COr*rhoOracle n v ≤ hetDist law →
          1-oracleRejectProb n law (oracleTest n v) ≤ 0.01 := by
      intro hsat law hm hdist
      exact hcal.2 law hm ((oracle_attaining_separation_le n v hn hv).trans hdist)
    have hr : 0 < COr*rhoOracle n v := by
      have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact mul_pos COr_pos (Real.rpow_pos_of_pos hnpos _)
    have hD : 0 ≤ maxDistOracle v :=
      (show 0 ≤ d0 by unfold d0; positivity).trans hdOracle.1
    refine ⟨oracleBroadCriticalRadius_le_of_test n v _ hD hr (oracleTest n v)
      (fun law hnull => (hcal.1 law hnull).trans (by norm_num))
      (fun hsat law hm hdist => (hpower hsat law hm hdist).trans (by norm_num)),
      hcal.1, hpower⟩
  refine ⟨hlower, hattain.1, hattain.2.1, hattain.2.2, hriskBroad,
    P0.e, P0, π1, hnull, hnull.toInOracleNull, rfl, he0, hnorm, ⟨i, hi⟩, hlegal, htv, ?_⟩
  intro φ hsize
  exact oracle_single_null_prior_error_witness n P0 π1 hnorm
    (fun j hj => (hlegal j hj).2.2.1) htv φ (hsize P0 hnull.toInOracleNull)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
