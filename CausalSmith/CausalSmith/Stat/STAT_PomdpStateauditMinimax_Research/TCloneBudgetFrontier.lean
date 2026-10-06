module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.FrontierWitness

/-! # Collision envelope, critical clone budget, and capped two-point converse. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory Filter

-- @node: thm:clone-budget-frontier
/-- The exact feasible worst-case distance is the explicit binomial collision
probability. Its least sufficient budget has sharp exponential bounds and a
large-audit asymptotic; at that budget signed-depth atoms certify a capped lower rate
without any additional order-horizon feasibility floor. -/
theorem clone_budget_frontier :
    (∀ (T n k m : Nat) (eta : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m),
      eta ∈ Set.Icc (0 : ℝ) 1 → T ≤ n * m →
      (∀ (M : PomdpModel T 1 n k),
        FullFiltrationPomdp M → FullFiltrationRandomization M → StationaryStart M →
        Causalean.Stat.tvDist (permutationMixture M hm eta)
          (freshLabelLaw M hn hm eta) ≤
          collisionEnvelope T eta m) ∧
      (∃ M : PomdpModel T 1 n k,
        FullFiltrationPomdp M ∧ FullFiltrationRandomization M ∧ StationaryStart M ∧
        (∃ s0 : JointState 1 n, M.law {w | ∀ t : Fin T, currentState w t = s0} = 1) ∧
        Causalean.Stat.tvDist (permutationMixture M hm eta)
          (freshLabelLaw M hn hm eta) =
            collisionEnvelope T eta m)) ∧
    (∀ (T : Nat) (eta delta : ℝ), eta ∈ Set.Icc (0 : ℝ) 1 →
      ∀ hdelta : delta ∈ Set.Ioo (0 : ℝ) 1,
      1 ≤ cloneBudget T eta delta hdelta ∧
      collisionEnvelope T eta (cloneBudget T eta delta hdelta) ≤ delta ∧
      (∀ m : Nat, 1 ≤ m → m < cloneBudget T eta delta hdelta →
        delta < collisionEnvelope T eta m)) ∧
    (∀ (T m : Nat) (eta : ℝ), 1 ≤ m → eta ∈ Set.Icc (0 : ℝ) 1 →
      collisionLowerEnvelope T eta m ≤ collisionEnvelope T eta m ∧
      collisionEnvelope T eta m ≤
        min 1 (collisionScale T eta / (m : ℝ))) ∧
    (∀ (delta : ℝ), ∀ hdelta : delta ∈ Set.Ioo (0 : ℝ) 1,
      ∀ (Tseq : Nat → Nat) (etaseq : Nat → ℝ),
        (∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1) →
        Tendsto (fun j => (Tseq j : ℝ) * etaseq j) atTop atTop →
        Tendsto (fun j =>
          (cloneBudget (Tseq j) (etaseq j) delta hdelta : ℝ) /
            (collisionScale (Tseq j) (etaseq j) / (-Real.log (1 - delta))))
          atTop (nhds 1)) ∧
    (∀ (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta),
      ∃ B0 : ℝ, 1 ≤ B0 ∧
        (∀ (T Q : Nat) (hQ : 1 ≤ Q),
          let Mp := signedDepthModel T Q t0 zeta 2 true ht0 hzeta (by norm_num) hQ
          let Mm := signedDepthModel T Q t0 zeta 2 false ht0 hzeta (by norm_num) hQ
          InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≤
            ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
              policyFactor zeta ^ (-(Q : ℤ)))) ∧
        (∀ delta0 : ℝ, ∀ hdelta0 : delta0 ∈ Set.Ioo (0 : ℝ) (3 / 8),
          ∃ c : ℝ, 0 < c ∧ ∀ (T N : Nat) (eta : ℝ), 1 ≤ T →
            eta ∈ Set.Icc (0 : ℝ) 1 →
            signedDepthCardinality T t0 zeta B0 * cloneBudget T eta delta0
              ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩ ≤ N →
              c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
                cappedMinimaxRisk T N t0 zeta eta)) ∧
    (∀ (T n k m : Nat) (Mp Mm : PomdpModel T 1 n k)
      (hn : 1 ≤ n) (hm : 1 ≤ m) (t0 zeta C eta a : ℝ),
      1 ≤ C → FixedOverlapClass t0 zeta C Mp → FixedOverlapClass t0 zeta C Mm →
      Mp.b = Mm.b → Mp.e = Mm.e → eta ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ a → targetValue Mp = a → targetValue Mm = -a →
      Causalean.Stat.tvDist (permutationMixture Mp hm eta)
        (permutationMixture Mm hm eta) ≤
        Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
          2 * collisionEnvelope T eta m ∧
      Causalean.Stat.tvDist (permutationMixture Mp hm eta)
        (permutationMixture Mm hm eta) ≤
        Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) +
          eta ^ 2 * T * (T - 1) / (m : ℝ) ∧
      (∀ est : AuditedRecord T 1 (n * m) k → ℝ, Measurable est →
        ∃ (v : Bool) (π : Fin n × Fin m ≃ Fin (n * m)),
          FixedOverlapClass t0 zeta C
            (cloneModel (if v then Mp else Mm) hm π) ∧
          ENNReal.ofReal ((a ^ 2 / 2) *
            (1 - Causalean.Stat.tvDist (permutationMixture Mp hm eta)
              (permutationMixture Mm hm eta))) ≤
            Causalean.Stat.sqRiskLIntegral
              (auditedLaw eta (cloneModel (if v then Mp else Mm) hm π)) est
              (targetValue (cloneModel (if v then Mp else Mm) hm π)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T n k m eta hn hk hm heta hcard
    constructor
    · intro M hK hA hStart
      exact frontier_fixed_permutation_tv_upper M hn hm hK hA hStart eta heta
    · exact probe_exact_witness hn hk hm eta heta hcard
  · intro T eta delta heta hdelta
    exact cloneBudget_minimal_of_exists T eta delta hdelta
      (frontier_cloneBudget_exists T eta delta heta hdelta.1)
  · intro T m eta hm heta
    constructor
    · exact collisionLowerEnvelope_le_collisionEnvelope T m hm eta heta
    · exact frontier_collisionEnvelope_upper T m hm eta heta
  · intro delta hdelta Tseq etaseq heta hmean
    simpa only [cloneBudget_eq_birthdayMStar,
      collisionScale_eq_birthdayPairScale,
      Causalean.Mathlib.Probability.Birthday.mean] using
      Causalean.Mathlib.Probability.Birthday.mStar_div_calibratedScale_tendsto_one
        Tseq etaseq heta hmean hdelta
  · intro t0 zeta ht0 hzeta
    obtain ⟨B0, hconst⟩ := signedDepthConstantAtTwo_exists ht0 hzeta
    obtain ⟨hB0, hwitness⟩ := signedDepthConstantAtTwo_spec hconst
    refine ⟨B0, hB0, ?_, ?_⟩
    · intro T Q hQ
      exact (hwitness T Q hQ ht0 hzeta).2.2.2.2.2.2
    · intro delta0 hdelta0
      obtain ⟨c, hc, hconv⟩ :=
        capped_signedDepth_converse ht0 hzeta hconst delta0 hdelta0
      refine ⟨c, hc, ?_⟩
      intro T N eta hT heta hcap
      have hdelta : delta0 ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨hdelta0.1, lt_trans hdelta0.2 (by norm_num)⟩
      have hbudget := cloneBudget_minimal_of_exists T eta delta0 hdelta
        (frontier_cloneBudget_exists T eta delta0 heta hdelta0.1)
      exact hconv T N (cloneBudget T eta delta0 hdelta) eta hT heta
        hbudget.1 hbudget.2.1 hcap
  · intro T n k m Mp Mm hn hm t0 zeta C eta a hC hMp hMm hb he heta ha hp hmval
    exact overflow_safe_all_procedure_transfer Mp Mm hn hm hC hMp hMm
      ⟨hb, he⟩ eta a heta ha hp hmval

end CausalSmith.Stat.PomdpStateauditMinimax
