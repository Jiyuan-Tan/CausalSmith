module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleTuning
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OraclePopulation
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ProjectionGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TwoPrior
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TCausalNonempty
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TPairedTentFullRecordLower

/-! Finite-moment homogeneity testing: TOracleFrontierResolved. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Oraclecompactuniformity: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def OracleCompactUniformity : Prop := ∀ K : Set Params, IsCompact K → (∀ v ∈ K, v.Valid) →
  ∃ e : ℝ, 0 < e ∧ ∀ v ∈ K, e ≤ E0 v
/-- The positive continuous oracle exponent has a positive minimum on each valid compact set.  the stated setting, [the asserted mathematical result holds](goal). -/
-- @node: oracle_compact_uniformity
lemma oracle_compact_uniformity : OracleCompactUniformity := by
  have hc : Continuous (fun v : Params => (v.p,v.α,v.β,v.γ)) := continuous_induced_dom
  have hcp : Continuous (fun v : Params => v.p) := hc.fst
  have hcg : Continuous (fun v : Params => v.γ) := hc.snd.snd.snd
  have hcont (v : Params) (hv : v.Valid) : ContinuousAt E0 v := by
    obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
    have hqcont : ContinuousAt qExp v := by
      unfold qExp
      exact (hcp.continuousAt.sub continuousAt_const).div hcp.continuousAt hp.ne'
    unfold E0
    exact ((continuousAt_const.mul hcg.continuousAt).mul hqcont).div
      ((continuousAt_const.mul hcg.continuousAt).add hqcont) he.ne'
  intro K hK hv
  by_cases hne : K.Nonempty
  · obtain ⟨v, hvK, hmin⟩ := hK.exists_isMinOn hne
      (fun v hvK => (hcont v (hv v hvK)).continuousWithinAt)
    exact ⟨E0 v, E0_pos v (hv v hvK), fun w hw => hmin hw⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro v hvK
    exact (hne ⟨v, hvK⟩).elim

/-- [Oracle frontier resolved](goal).
The supplied-propensity frontier is resolved independently of the unknown-propensity rough
converse. For every public tuple let \[  q=(p-1)/p,\quad E_0=2\gamma q/(2\gamma+q),\quad
\rho_n^{\mathrm e}(v)=n^{-E_0},\quad  c^{\mathrm e}_v=4^{-\gamma}/(16\sqrt3),\quad  C^{\mathrm
e}_v=3\{120+128\sqrt{160\sqrt2}\}. \] For every \(n\ge2\), \[  c^{\mathrm e}_v\rho_n^{\mathrm
e}(v)\le r_n^{*,\mathrm e}(v)                       \le C^{\mathrm e}_v\rho_n^{\mathrm e}(v). \]
Here is a total attaining rule. Put \(s=\lfloor n/2\rfloor\), \(a=s^{-E_0}\),
\(T=2^{\lceil\log_2(a^{-1/(p-1)})\rceil}\), and let \(J\) be the least power of two at least
\(a^{-1/\gamma}\). Put \(u=J^{-1/2}(1,\ldots,1)^T\), \(C_J=I_J-uu^T\), and \[
R_i=\frac{A_i\ell_T(Y_i)}{e_P(X_i)}        -\frac{(1-A_i)\ell_T(Y_i)}{1-e_P(X_i)},\quad
V_b=s^{-1}\sum_{i\in\mathcal I_b}C_JF_J(X_i)R_i. \] Set \(b=20T^{1-p}\),
\(\Lambda=80T^{2-p}/s\), and reject when \(\langle V_1,V_2\rangle>2b^2+1024\sqrt J\Lambda\).
Extend this Borel map to a supplied continuous function outside \([1/4,3/4]\) by first clipping
it into that interval. This rule is \(\phi^{*,\mathrm e}_{n,v}\). Its size is at most \(0.01\)
on the entire unknown-constant original-mean null, and its type-II error is at most \(0.01\) at
the displayed separation whenever that separation is below \(D_v\). A public nonempty-power
threshold is \[  N^{\mathrm e}_v=\left\lceil\max\{2,(2C^{\mathrm
e}_v/d_0)^{1/E_0}\}\right\rceil. \] Before that threshold the finite rule remains calibrated; a
level at or above \(D_v\) records only saturation. The converse has nonempty alternatives and
identical entire supplied propensity for every \(n\). Constants are locally uniform including
\(p=2\) and \(\gamma=1/4\). No logarithm is necessary.
-/
-- @node: thm:oracle-frontier-resolved
theorem oracle_frontier_resolved :
    (∀ v : Params, v.Valid →
      1/(64*Real.sqrt 3) ≤ cOracle v ∧ 0 < COr ∧
      (∀ n : ℕ, 2 ≤ n → cOracle v*rhoOracle n v ≤ oracleCriticalRadius n v ∧
        oracleCriticalRadius n v ≤ COr*rhoOracle n v ∧
        (∀ law, InNull v law → oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
        (COr*rhoOracle n v < maxDist v → ∀ law, InModel v law → COr*rhoOracle n v ≤ hetDist law → 1-oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
        2/5 ≤ oracleTestingRisk n v (cOracle v*rhoOracle n v) ∧
        (∃ f : Nuisance, ∃ P0 : ObservedLaw, ∃ π1 : FinitePrior,
          InNull v P0 ∧ P0.e = f ∧ PriorNormalized π1 ∧ (∃ i, 0 < priorWeight π1 i) ∧
          PriorSupported π1 {law | InModel v law ∧ law.e = f ∧
            cOracle v*rhoOracle n v ≤ hetDist law ∧ hetDist law < maxDist v} ∧
          Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π1) < 1/2 ∧
          (∀ φ : OracleTest n, (∀ law, InNull v law → oracleRejectProb n law φ ≤ 1/10) →
            ∃ i, 0 < priorWeight π1 i ∧ 2/5 ≤ 1-oracleRejectProb n (priorLaw π1 i) φ))) ∧
      (∀ n : ℕ, NOr v ≤ n → COr*rhoOracle n v ≤ d0/2) ∧
      (∀ law, InModel v law → ∀ᵐ x ∂design,
        law.e x*(∫ y, ipwUntruncated law.e (x,true,y) ∂law.Q true x)+
          (1-law.e x)*(∫ y, ipwUntruncated law.e (x,false,y) ∂law.Q false x)=law.tau x)) ∧
    OracleCompactUniformity := by
  refine ⟨?_, oracle_compact_uniformity⟩
  intro v hv
  refine ⟨cOracle_uniform_lower v hv, COr_pos, ?_,
    fun n hn => oracle_attainment_threshold v hv n hn,
    fun law hm => oracle_untruncated_mean_identity v hv law hm⟩
  intro n hn
  obtain ⟨L, hLlim, hpriors⟩ := paired_tent_full_record_lower.1 v hv
  obtain ⟨P0, π1, hL, hnull, he0, hsupport0, hmoment0, hnorm, hpos,
    hsupport, hd, htv, hrisk, hrawrisk⟩ := hpriors n hn
  have hlegal : PriorSupported π1 {law | InModel v law ∧ law.e = P0.e ∧
      cOracle v*rhoOracle n v ≤ hetDist law ∧ hetDist law < maxDist v} := by
    intro i hi
    obtain ⟨hm, he, hs, hlo, hhi, hmom⟩ := hsupport i hi
    refine ⟨hm, ?_, hlo, hhi.trans_le hd⟩
    ext x
    rw [he x, he0 x]
  obtain ⟨i, hi⟩ := hpos
  have hip := hlegal i hi
  have hsep : 0 < cOracle v*rhoOracle n v := by
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    unfold cOracle rhoOracle
    positivity
  have hlower : cOracle v*rhoOracle n v ≤ oracleCriticalRadius n v :=
    oracleCriticalRadius_ge_of_failed n v _ ⟨hsep, hip.2.2.1.trans_lt hip.2.2.2⟩
      ⟨priorLaw π1 i, hip.1, hip.2.2.1⟩ (by linarith)
  have hattain : oracleCriticalRadius n v ≤ COr*rhoOracle n v ∧
      (∀ law, InNull v law → oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
      (COr*rhoOracle n v < maxDist v → ∀ law, InModel v law →
        COr*rhoOracle n v ≤ hetDist law →
        1-oracleRejectProb n law (oracleTest n v) ≤ 0.01) := by
    have hcal : (∀ law, InNull v law → oracleRejectProb n law (oracleTest n v) ≤ 0.01) ∧
        (∀ law, InModel v law →
          20*(oracleJ n v:ℝ)^(-v.γ)+5*oracleBias n v+
            128*Real.sqrt (Real.sqrt (oracleJ n v)*oracleCov n v) ≤ hetDist law →
          1-oracleRejectProb n law (oracleTest n v) ≤ 0.01) := by
      constructor
      · exact fun law hnull => oracle_whole_null_size_le n v hn hv law hnull
      · intro law hm hdist
        have hpopulation : hetDist law-20*(oracleJ n v:ℝ)^(-v.γ)-oracleBias n v ≤
            ‖∫ data, oracleBlockVec n v law.e false data
              ∂Measure.pi (fun _ : Fin n => law.P)‖ := by
          exact oracle_alternative_population_norm_ge n v hn hv law hm
        apply oracle_power_of_mean_bound n v hn hv law hm
        linarith
    have hpower : COr*rhoOracle n v < maxDist v → ∀ law, InModel v law →
        COr*rhoOracle n v ≤ hetDist law →
        1-oracleRejectProb n law (oracleTest n v) ≤ 0.01 := by
      intro hsat law hm hdist
      exact hcal.2 law hm ((oracle_attaining_separation_le n v hn hv).trans hdist)
    have hr : 0 < COr*rhoOracle n v := by
      have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact mul_pos COr_pos (Real.rpow_pos_of_pos hnpos _)
    refine ⟨oracleCriticalRadius_le_of_test n v _ (hsep.le.trans (hip.2.2.1.trans hip.2.2.2.le)) hr (oracleTest n v)
      (fun law hnull => (hcal.1 law hnull).trans (by norm_num))
      (fun hsat law hm hdist => (hpower hsat law hm hdist).trans (by norm_num)),
      hcal.1, hpower⟩
  refine ⟨hlower, hattain.1, hattain.2.1, hattain.2.2, hrisk,
    P0.e, P0, π1, hnull, rfl, hnorm, ⟨i, hi⟩, hlegal, htv, ?_⟩
  intro φ hsize
  exact oracle_single_null_prior_error_witness n P0 π1 hnorm
    (fun j hj => (hlegal j hj).2.1) htv φ (hsize P0 hnull)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
