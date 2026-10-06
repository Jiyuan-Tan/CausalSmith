module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainIndependence
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainSquareIntegrability
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CorrectedMeanAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyBudgets
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyProjection
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.TMultibandCovariance

/-!
Independent-chain energy identities, signal-dependent envelopes and conditional probability and
first-moment guarantees.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Conditional energy identities and guarantees with the rule's exact public moment constant. -/
-- @node: energy_envelope_public_constant
lemma energy_envelope_public_constant :
    ∀ C0 : ℝ, 0 < C0 → -- @realizes C0(arbitrary positive public pilot constant)
    ∀ P : ObsLaw, Model P → ∀ m, 1 ≤ m → ∀ mx my K L T J q kt,
    ∀ train : Fin m → Omega, ∀ ν : Measure (SampleSpace (13 * m)),
    SamplingLaw P (13 * m) ν →
    let C : ℝ := 2 ^ 24
    let μ := contrastMean P train mx my L T J q kt
    let sigma := contrastCovariance P train mx my L T J q kt
    let Z := energy train mx my L T J q kt
    let B := BAllow C (hAllow C0 m mx my) m K L T q kt
    let W := WAllow C m T kt
    let V := VAllow C m J L T kt
    (∫ eval, Z eval ∂evalLaw P m) = ‖μ‖ ^ 2 ∧
    variance Z (evalLaw P m) = 2 * covarianceForm sigma μ + covarianceSquareTrace sigma ∧
    (MeanRanks mx my K L T J q kt → q ≤ m →
      GoodPilot P train C0 mx my → hAllow C0 m mx my ≤ 1 →
      |(∫ eval, Z eval ∂evalLaw P m) - Psi P| ≤
        2 * B * Real.sqrt (Psi P) + B ^ 2 + 400 * (J : ℝ) ^ (-2 : ℤ) ∧
      variance Z (evalLaw P m) ≤ 2 * W * (Real.sqrt (Psi P) + B) ^ 2 + V ∧
      (19 / 20 : ℝ) ≤ (evalLaw P m).real
        {eval | |Z eval - Psi P| ≤ aci B W * Real.sqrt (Psi P) + dci B W V J} ∧
      (∫ eval, |Z eval - Psi P| ∂evalLaw P m) ≤
        aci B W * Real.sqrt (Psi P) + dci B W V J) := by
  have hcovBudget := multiband_covariance_public_constant
  let C : ℝ := 2 ^ 24
  have hC : 0 < C := by positivity
  intro C0 hC0 P hModel m hm mx my K L T J q kt train ν hSampling
  letI : MeasurableSpace (Hj J) := borel (Hj J)
  letI : BorelSpace (Hj J) := ⟨rfl⟩
  -- Fixed-training chains use disjoint iid six-role blocks and bounded finite histograms.
  have chain_inputs :
      IndepFun (fun eval => coefficientChain train mx my L T J q kt eval 0)
        (fun eval => coefficientChain train mx my L T J q kt eval 1) (evalLaw P m) ∧
      IdentDistrib (fun eval => coefficientChain train mx my L T J q kt eval 0)
        (fun eval => coefficientChain train mx my L T J q kt eval 1)
        (evalLaw P m) (evalLaw P m) ∧
      MemLp (fun eval => coefficientChain train mx my L T J q kt eval 0) 2 (evalLaw P m) := by
    exact ⟨indepFun_coefficientChain P train mx my L T J q kt,
      identDistrib_coefficientChain P train mx my L T J q kt,
      memLp_coefficientChain P train mx my L T J q kt 0 2⟩
  obtain ⟨hind, hid, hchainL2⟩ := chain_inputs
  have hMeas : Measurable (energy train mx my L T J q kt) :=
    measurable_energy train mx my L T J q kt
  obtain ⟨hL2, hmean, hvariance⟩ :=
    energy_moments_of_independent_chains P train mx my L T q kt hind hid hchainL2
  refine ⟨hmean, hvariance, ?_⟩
  intro hRanks hq hGood hh
  obtain ⟨hmx, hmy, hL, hK, hqd, hkt, hJ, hmyL, hk0, hdiv, hdivq⟩ := hRanks
  have hJpos : 0 < J := by
    rw [hJ]
    obtain ⟨l, hl⟩ := hL
    rw [hl]
    positivity
  obtain ⟨hp, hprojection⟩ := model_delta_projection_budgets P hModel J hJpos
  have hRanks' : MeanRanks mx my K L T J q kt :=
    ⟨hmx, hmy, hL, hK, hqd, hkt, hJ, hmyL, hk0, hdiv, hdivq⟩
  have hmu := (corrected_mean_public_constant C0 hC0 P hModel m hm mx my K L T J q kt hRanks'
    train ν hSampling).2 hGood hh
  have hnonneg := hAllow_nonneg C0 hC0.le m mx my
  have hb : ‖contrastMean P train mx my L T J q kt - coefficients J (delta P)‖ ≤
      BAllow C (hAllow C0 m mx my) m K L T q kt :=
    hmu
  have hcov := hcovBudget P hModel m hm mx my L T J q kt hmx hmy hL hJ hqd hq hkt
    train ν hSampling
  have hop : covarianceOpNorm (contrastCovariance P train mx my L T J q kt) ≤
      WAllow C m T kt := hcov.2.2.2.1
  have htrace : covarianceSquareTrace (contrastCovariance P train mx my L T J q kt) ≤
      VAllow C m J L T kt := hcov.2.2.2.2
  have hbias : |(∫ eval, energy train mx my L T J q kt eval ∂evalLaw P m) - Psi P| ≤
      2 * BAllow C (hAllow C0 m mx my) m K L T q kt * Real.sqrt (Psi P) +
        (BAllow C (hAllow C0 m mx my) m K L T q kt) ^ 2 + 400 * (J : ℝ) ^ (-2 : ℤ) := by
    rw [hmean]
    exact energy_bias_of_projection_budget _ _ _ _ _ hp hb hprojection
  have hvar : variance (energy train mx my L T J q kt) (evalLaw P m) ≤
      2 * WAllow C m T kt *
        (Real.sqrt (Psi P) + BAllow C (hAllow C0 m mx my) m K L T q kt) ^ 2 +
        VAllow C m J L T kt :=
    energy_variance_of_covariance_budgets _ _ _ _ _ _ _ _ hp hb
      (WAllow_nonneg C hC.le m T kt) hop htrace hvariance
  refine ⟨hbias, hvar, ?_⟩
  letI : IsProbabilityMeasure (evalLaw P m) := by
    unfold evalLaw
    infer_instance
  exact energy_scalar_guarantees (evalLaw P m) _ hMeas hL2 (Psi P) _ _ _ J
    (BAllow_nonneg C _ hC.le hnonneg m K L T q kt)
    (WAllow_nonneg C hC.le m T kt) (VAllow_nonneg C m J L T kt) hbias hvar

-- @node: lem:energy-envelope
/-- Independent identically distributed chains give the exact energy mean and variance;
on good pilots the corrected mean and multiband covariance give both conditional guarantees. -/
lemma energy_envelope :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(universal positive energy-envelope constant)
    ∀ C0 : ℝ, 0 < C0 → -- @realizes C0(arbitrary positive public pilot constant)
    ∀ P : ObsLaw, Model P → ∀ m, 1 ≤ m → ∀ mx my K L T J q kt,
    ∀ train : Fin m → Omega, ∀ ν : Measure (SampleSpace (13 * m)),
    SamplingLaw P (13 * m) ν →
    let μ := contrastMean P train mx my L T J q kt
    let sigma := contrastCovariance P train mx my L T J q kt
    let Z := energy train mx my L T J q kt
    let B := BAllow C (hAllow C0 m mx my) m K L T q kt
    let W := WAllow C m T kt
    let V := VAllow C m J L T kt
    (∫ eval, Z eval ∂evalLaw P m) = ‖μ‖ ^ 2 ∧
    variance Z (evalLaw P m) = 2 * covarianceForm sigma μ + covarianceSquareTrace sigma ∧
    (MeanRanks mx my K L T J q kt → q ≤ m →
      GoodPilot P train C0 mx my → hAllow C0 m mx my ≤ 1 →
      |(∫ eval, Z eval ∂evalLaw P m) - Psi P| ≤
        2 * B * Real.sqrt (Psi P) + B ^ 2 + 400 * (J : ℝ) ^ (-2 : ℤ) ∧
      variance Z (evalLaw P m) ≤ 2 * W * (Real.sqrt (Psi P) + B) ^ 2 + V ∧
      (19 / 20 : ℝ) ≤ (evalLaw P m).real
        {eval | |Z eval - Psi P| ≤ aci B W * Real.sqrt (Psi P) + dci B W V J} ∧
      (∫ eval, |Z eval - Psi P| ∂evalLaw P m) ≤
        aci B W * Real.sqrt (Psi P) + dci B W V J) := by
  exact ⟨2 ^ 24, by positivity, energy_envelope_public_constant⟩

end CausalSmith.Stat.DensityEffectRoughNull
