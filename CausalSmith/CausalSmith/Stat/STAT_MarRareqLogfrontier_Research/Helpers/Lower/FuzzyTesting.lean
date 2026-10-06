module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationLikelihood
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationRiskTransfer
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.MomentPriors
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TOneCellTestingFamily

/-! Fuzzy testing comparison in the original fixed-sample experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:u,hu), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_min_one_sq
lemma activated_min_one_sq (u : ℝ) (hu : 0 ≤ u) :
    (min 1 u) ^ 2 = min 1 (u ^ 2) := by
  by_cases h : u ≤ 1
  · rw [min_eq_right h, min_eq_right (by nlinarith : u ^ 2 ≤ 1)]
  · have h' : 1 ≤ u := le_of_not_ge h
    rw [min_eq_left h', min_eq_left (by nlinarith : 1 ≤ u ^ 2)]
    norm_num

-- @node: activated_fuzzy_lower
/-- [the stated mathematical conclusion holds](goal). -/
lemma activated_fuzzy_lower
    : ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
        RareArrivalSlice n q → Real.sqrt (effectiveSize n q) ≤ d →
          c * min 1 (((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2) ≤
            minimaxRisk n d q := by
  let η := Real.exp (-32)
  let T := max 1 (max (Real.exp 2) (max (4 * η)
    (max (2 * η * 2048) (Real.exp ((32 - Real.log ((2 : ℝ) / 16)) / 28)))))
  let c := min (1 / (256 * T)) (min (1 / (256 * (2048 : ℝ) ^ 2)) (η ^ 2 / 16384))
  have hT : 1 ≤ T := le_max_left _ _
  have hη : 0 < η := Real.exp_pos _
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n d q hn hd hq hq1 hslice _hdim
  let N := effectiveSize n q
  let L := logScale n q
  let u := (d : ℝ) / (N * L)
  have hN : 0 < N := by dsimp [N, effectiveSize]; positivity
  have hL : 1 ≤ L := by
    dsimp [L, logScale]
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
      (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
    simpa using h
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hcap : 0 ≤ min 1 (u ^ 2) := le_min (by norm_num) (sq_nonneg _)
  have hone := (oneCell_minimax_risk_floors q hn hd hq hq1 hslice).1
  have hcT : c ≤ 1 / (256 * T) := min_le_left _ _
  have hcD : c ≤ 1 / (256 * (2048 : ℝ) ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcη : c ≤ η ^ 2 / 16384 :=
    (min_le_right _ _).trans (min_le_right _ _)
  change c * min 1 (u ^ 2) ≤ minimaxRisk n d q
  by_cases hlarge : T ≤ N
  · have hN1 : 1 ≤ N := hT.trans hlarge
    have hTexp : Real.exp 2 ≤ N :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
    have hTmass : 4 * η ≤ N :=
      (le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans hlarge))
    have hTcapacity : 2 * η * 2048 ≤ N :=
      (le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge)))
    have hTtail : Real.exp ((32 - Real.log ((2 : ℝ) / 16)) / 28) ≤ N :=
      (le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge)))
    have hcapacity := interval_capacity_of_large_size η 2048 n q hη hN hL hTcapacity
    by_cases hJ : 2048 ≤ rareCount η n d q
    · have hK : 2 ≤ lowerDegree n q := by
        have hlog := Real.log_le_log (Real.exp_pos (2 : ℝ))
          (hTexp.trans (show N ≤ Real.exp 1 + N by linarith [Real.exp_pos (1 : ℝ)]))
        rw [Real.log_exp] at hlog
        have hceil := Nat.le_ceil (logScale n q)
        have : (2 : ℝ) ≤ (lowerDegree n q : ℝ) := hlog.trans hceil
        exact_mod_cast this
      obtain ⟨π₀, π₁, h₀, h₁, hm, hgap⟩ :=
        interval_ordered_reciprocal_priors n q hK
      have hgapabs : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀| :=
        hgap.trans (le_abs_self _)
      have hrisk := activatedAugmentedMixture_minimaxRisk_calibrated n d q
        hn hd hq hslice h₀ h₁ hm hgapabs hJ hTtail
      have hb : 0 < rareMass η n q := by unfold rareMass; positivity
      have hbsmall : rareMass η n q ≤ 1 / 4 := by
        unfold rareMass
        apply (div_le_iff₀ (by positivity : 0 < effectiveSize n q * logScale n q)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hL hN.le]
      have hηsmall : η ≤ 1 / 2 := by
        dsimp [η]
        rw [Real.exp_neg, inv_eq_one_div]
        apply (div_le_iff₀ (Real.exp_pos 32)).mpr
        linarith [Real.add_one_le_exp (32 : ℝ)]
      have hd2 : 2 ≤ d := by
        have hjd : rareCount η n d q ≤ d - 1 := min_le_left _ _
        omega
      have hwidth := interval_prior_segment_width_lower η
        ((rareCount η n d q : ℝ) * rareMass η n q / 12) n d q
        hη hηsmall hd2 hN (by linarith) hbsmall le_rfl
      have hmass : η / 2 * min 1 u ≤ (rareCount η n d q : ℝ) * rareMass η n q := by
        change η / 24 * min 1 u ≤ _ at hwidth
        linarith
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ η / 2 * min 1 u)
        (by positivity : 0 ≤ (rareCount η n d q : ℝ) * rareMass η n q)).2 hmass
      rw [mul_pow, activated_min_one_sq u hu] at hsq
      have hbound : c * min 1 (u ^ 2) ≤
          (1 / 4096) * ((rareCount η n d q : ℝ) * rareMass η n q) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hcη hcap]
      exact hbound.trans hrisk
    · have hdsmall := rareCount_small_dimension η n d 2048 q hd hcapacity (by omega)
      have hscale := interval_small_dimension_scale n d 2048 q hN1 hL hdsmall
      change min 1 u ≤ (2048 : ℝ) * (Real.sqrt N)⁻¹ at hscale
      have hs := (sq_le_sq₀ (le_min (by norm_num) hu) (by positivity)).2 hscale
      rw [activated_min_one_sq u hu, mul_pow, inv_pow, Real.sq_sqrt hN.le] at hs
      have hmin : min 1 N⁻¹ = N⁻¹ := min_eq_right (inv_le_one_of_one_le₀ hN1)
      change (1 / 256 : ℝ) * min 1 N⁻¹ ≤ _ at hone
      rw [hmin] at hone
      have hbnd := mul_le_mul_of_nonneg_left hs hc.le
      have hcoef : c * (2048 : ℝ) ^ 2 ≤ 1 / 256 := by
        nlinarith [mul_le_mul_of_nonneg_right hcD (by positivity : 0 ≤ (2048 : ℝ) ^ 2)]
      have hbound := mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr hN.le)
      exact hbnd.trans (by simpa only [mul_assoc] using hbound.trans hone)
  · have hsmall : N ≤ T := le_of_not_ge hlarge
    have hrecip : T⁻¹ ≤ min 1 N⁻¹ := by
      apply le_min (inv_le_one_of_one_le₀ hT)
      exact (inv_le_inv₀ (show 0 < T by linarith [hT]) hN).mpr hsmall
    have hc' : c ≤ (1 / 256 : ℝ) * T⁻¹ := by
      convert hcT using 1
      ring
    have hbound := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1 / 256)
    have hcap1 := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (u ^ 2)) hc.le
    exact hcap1.trans (by simpa only [mul_one] using (hc'.trans hbound).trans hone)


end CausalSmith.Stat.MarRareqLogfrontier
