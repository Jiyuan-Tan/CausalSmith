module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.ConsistencyFrontier
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerFiniteAlphabet
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerDenseFullCounts
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerHistogramTransfer
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerPriorTransfer
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerRateSplice
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseFullCounts
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerTransfer
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketResponseLower
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedDualCompletion
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedUpperOrder
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TObservableUpper
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TIdentification
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Weighted moment-prior separation and the minimax frontier
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory Filter
open scoped BigOperators Topology

/-- The full weighted approximation comparison and its explicit completed Jackson-packet witness, with a common universal lower constant. The optimal finite dual proves E ≤ Delta; the packet proves the lower order and supplies the required supported, mean-one, moment-matched witness. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
theorem weighted_approximation_and_packet :
    (∃ (c C : ℝ) (A₀ : ℕ), 0 < c ∧ c < C ∧ 1 ≤ A₀ ∧
      ∀ (K : ℕ) (M ε : ℝ),
        (hK : 2 ≤ K) → (hM : 2 ≤ M) → (hMhi : M ≤ (K : ℝ) ^ 2) →
        (hε : 0 ≤ ε) → (hεhi : ε ≤ 1 / 2) →
        c * Real.sqrt M / K ≤ weightedApproxError K M ε ∧
        weightedApproxError K M ε ≤ constrainedPriorSeparation K M ε hK hM hMhi hε hεhi ∧
        constrainedPriorSeparation K M ε hK hM hMhi hε hεhi ≤ 4 * weightedApproxError K M ε ∧
        4 * weightedApproxError K M ε ≤ C * Real.sqrt M / K ∧
        (∃ (p : ConstrainedPriorPair K M),
          ∃ hdom : CommonAtomDomain
            (packetPositive A₀ K M) (packetNegative A₀ K M),
          ((packetPositive A₀ K M) Set.univ).toReal ≤ 1 / 2 ∧
          (1 / 2 : ℝ) ≤
            (1 - ∫ z, z ∂packetPositive A₀ K M) /
              (1 - ((packetPositive A₀ K M) Set.univ).toReal) ∧
          (1 - ∫ z, z ∂packetPositive A₀ K M) /
              (1 - ((packetPositive A₀ K M) Set.univ).toReal) ≤ 2 ∧
          commonAtomCompletion
            (packetPositive A₀ K M) (packetNegative A₀ K M) hdom =
              (p.ν₀, p.ν₁) ∧
          c * Real.sqrt M / K ≤
            |(∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀)|)) := by
  obtain ⟨ce, hce, he⟩ := packetWeightedApproxError_lower
  obtain ⟨cp, A, hcp, hA, hpacket⟩ := packetCompletion_separation_lower
  let c := min (min ce cp) 1
  have hc : 0 < c := lt_min (lt_min hce hcp) (by norm_num)
  have hce' : c ≤ ce := (min_le_left _ _).trans (min_le_left _ _)
  have hcp' : c ≤ cp := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨c, 257, A, hc, lt_of_le_of_lt (min_le_right _ _) (by norm_num), hA, ?_⟩
  intro K M ε hK hM hMhi hε hεhi
  have hscale : 0 ≤ Real.sqrt M / (K : ℝ) := by positivity
  have hlower : c * Real.sqrt M / K ≤ weightedApproxError K M ε := by
    calc
      _ ≤ ce * Real.sqrt M / K := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hce' hscale
      _ ≤ _ := he K M ε hK hM hMhi hε hεhi
  refine ⟨hlower, weightedApproxError_le_constrainedPriorSeparation hK hM hMhi hε hεhi,
    constrainedPriorSeparation_le_four_weightedApproxError K M ε (by linarith), ?_, ?_⟩
  · have hu := weightedApproxError_upper hK (M := M) (by linarith) hε hεhi
    have h := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 4)
    calc
      _ ≤ 4 * (64 * Real.sqrt M / K) := h
      _ = 256 * Real.sqrt M / K := by ring
      _ ≤ 257 * Real.sqrt M / K := by
        simpa only [mul_div_assoc] using
          mul_le_mul_of_nonneg_right (by norm_num : (256 : ℝ) ≤ 257) hscale
  · obtain ⟨p, hdom, ht, hzlo, hzhi, hcompletion, hgap⟩ :=
      hpacket K M ε hK hM hMhi hε hεhi
    refine ⟨p, hdom, ht, hzlo, hzhi, hcompletion, le_trans ?_ hgap⟩
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hcp' hscale

-- @node: thm:weighted-separation-and-frontier
/-- [The weighted approximation error, constrained-prior separation, and an explicit completed packet pair all have the square-root mass scale; universal constants then match the observed and causal minimax risks to the vanishing-overlap rate, and an estimator sequence is uniformly consistent exactly when the alphabet-to-effective-sample-size ratio tends to zero](goal). -/
theorem weighted_separation_and_frontier :
    (∃ (c C : ℝ) (A₀ : ℕ), 0 < c ∧ c < C ∧ 1 ≤ A₀ ∧
      ∀ (K : ℕ) (M ε : ℝ),
        (hK : 2 ≤ K) → (hM : 2 ≤ M) → (hMhi : M ≤ (K : ℝ) ^ 2) →
        (hε : 0 ≤ ε) → (hεhi : ε ≤ 1 / 2) →
        c * Real.sqrt M / K ≤ weightedApproxError K M ε ∧
        weightedApproxError K M ε ≤ constrainedPriorSeparation K M ε hK hM hMhi hε hεhi ∧
        constrainedPriorSeparation K M ε hK hM hMhi hε hεhi ≤ 4 * weightedApproxError K M ε ∧
        4 * weightedApproxError K M ε ≤ C * Real.sqrt M / K ∧
        (∃ (p : ConstrainedPriorPair K M),
          ∃ hdom : CommonAtomDomain
            (packetPositive A₀ K M) (packetNegative A₀ K M),
          ((packetPositive A₀ K M) Set.univ).toReal ≤ 1 / 2 ∧
          (1 / 2 : ℝ) ≤
            (1 - ∫ z, z ∂packetPositive A₀ K M) /
              (1 - ((packetPositive A₀ K M) Set.univ).toReal) ∧
          (1 - ∫ z, z ∂packetPositive A₀ K M) /
              (1 - ((packetPositive A₀ K M) Set.univ).toReal) ≤ 2 ∧
          commonAtomCompletion
            (packetPositive A₀ K M) (packetNegative A₀ K M) hdom =
              (p.ν₀, p.ν₁) ∧
          c * Real.sqrt M / K ≤
            |(∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀)|)) ∧
    (∃ (cstar Cstar H₀ κ : ℝ) (D₀ : ℕ),
      ∃ hH₀ : 0 < H₀, ∃ hκ : 0 < κ, ∃ hD₀ : 2 ≤ D₀,
      0 < cstar ∧ cstar ≤ Cstar ∧
      ∀ (n d : ℕ) (ε : ℝ),
        1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
        cstar * rateScale n d ε ≤ minimaxRisk n d ε ∧
        minimaxRisk n d ε ≤ armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ∧
        armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ≤ Cstar * rateScale n d ε ∧
        cstar * rateScale n d ε ≤ causalMinimaxRisk n d ε ∧
        causalMinimaxRisk n d ε ≤ Cstar * rateScale n d ε) ∧
    (∀ (N d : ℕ → ℕ) (ε : ℕ → ℝ),
      Tendsto N atTop atTop →
      (∀ k, 2 ≤ d k ∧ 0 < ε k ∧ ε k ≤ 1 / 2) →
      ((∃ est : ∀ k, Estimator (N k) (d k),
          Tendsto
            (fun k => Causalean.Stat.worstCaseRiskReal
              (observedRisk (N k) (d := d k) (ε := ε k)) (est k))
            atTop (𝓝 0)) ↔
        Tendsto (fun k => (d k : ℝ) /
          ((N k : ℝ) * ε k * logAlphabet (d k))) atTop (𝓝 0))) := by
  refine ⟨weighted_approximation_and_packet, ?_⟩
  obtain ⟨cl, hcl, hlower⟩ := allAlphabet_minimaxRisk_lower
  obtain ⟨H₀, κ, Cu, D₀, hH₀, hκ, hD₀, hCu, hupper⟩ := observable_upper
  let cstar := min cl Cu
  have hcstar : 0 < cstar := lt_min hcl hCu
  have hl : ∀ n d ε, 1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
      cstar * rateScale n d ε ≤ minimaxRisk n d ε := by
    intro n d ε hn hd hε hεhi
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (rateScale_nonneg (by omega) hε.le)).trans (hlower n d ε hn hd hε hεhi)
  have hu : ∀ n d ε, 1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
      armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ≤ Cu * rateScale n d ε := by
    intro n d ε hn hd hε hεhi
    exact (hupper n d ε hn hd hε hεhi).2 (fun P => productLaw P.1 n) (fun _ => rfl)
  constructor
  · refine ⟨cstar, Cu, H₀, κ, D₀, hH₀, hκ, hD₀, hcstar, min_le_right _ _, ?_⟩
    intro n d ε hn hd hε hεhi
    have hlo := hl n d ε hn hd hε hεhi
    have hmid := minimaxRisk_le_armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε
    have hhi := hu n d ε hn hd hε hεhi
    have hcausal := causalMinimaxRisk_bounds_of_observed hd hε hεhi hlo (hmid.trans hhi)
    exact ⟨hlo, hmid, hhi, hcausal⟩
  · intro N d ε hN hlegal
    exact uniformConsistency_iff_of_frontier cstar Cu H₀ κ D₀ hcstar hH₀ hκ hD₀
      hl hu N d ε hN hlegal
  -- @realizes \(c_w\)(universal weighted lower constant)
  -- @realizes \(K_0\)(full range begins at degree two)
  -- @realizes \(c_\star\)(universal lower risk constant)
  -- @realizes \(C_\star\)(universal upper risk constant)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
