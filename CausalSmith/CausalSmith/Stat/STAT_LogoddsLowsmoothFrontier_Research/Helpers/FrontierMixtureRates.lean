module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedPriorTesting
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FrontierElbows
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.LowerRankRates

/-! # Uniform mixture lower rates

A single absolute ceiling multiplier controls occupancy and the two mixture
Hellinger budgets. The mixed and fair testing bounds then give the numerator
and radius rates with the roadmap's uniform square-root ceiling factor.
-/
public section
noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The amplitude product is the power at the sum of the native exponents.](goal) Under [the stated assumptions](hyp:hk). -/
-- @node: lower_amplitude_product
lemma lower_amplitude_product (ε α β : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (ε*(k : ℝ)^(-α))*(ε*(k : ℝ)^(-β)) = ε^2*(k : ℝ)^(-(α+β)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  rw [neg_add, Real.rpow_add hk0]
  ring

/-- [The squared amplitude product and the pair-count factor combine into
the balanced Hellinger power budget. [the documented result](goal) Under [the stated assumptions](hyp:hk). -/
-- @node: lower_mixed_budget_identity
lemma lower_mixed_budget_identity (C ε α β : ℝ) (n k : ℕ) (hk : 1 ≤ k) :
    C*(n : ℝ)^2/(k : ℝ)*(ε*(k : ℝ)^(-α))^2*(ε*(k : ℝ)^(-β))^2 =
      C*ε^4*((n : ℝ)^2*(k : ℝ)^(-(2*(α+β)+1))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have he : (ε*(k : ℝ)^(-α))^2*(ε*(k : ℝ)^(-β))^2 =
      ε^4*(k : ℝ)^(-2*(α+β)) := by
    have hp2 : ((k : ℝ)^(-(α+β)))^2 = (k : ℝ)^(-2*(α+β)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
      congr 1
      ring
    rw [← mul_pow, lower_amplitude_product ε α β k hk, mul_pow, hp2]
    ring
  rw [mul_assoc (C*(n : ℝ)^2/(k : ℝ)), he]
  have hp : (k : ℝ)^(-(2*(α+β)+1)) =
      (k : ℝ)^(-2*(α+β)) / (k : ℝ) := by
    rw [show -(2*(α+β)+1) = -2*(α+β)-1 by ring,
      Real.rpow_sub hk0, Real.rpow_one]
  rw [hp]
  ring

/-- Both lower rates use one absolute multiplier and the same original
record mixture lemma, with no restrictions beyond the paper's domain. [the documented result](goal) -/
-- @node: frontier_mixture_lower_rates
lemma frontier_mixture_lower_rates :
    ∃ cMix cRadius : ℝ, 0 < cMix ∧ 0 < cRadius ∧
      (∀ α β r : ℝ, ExponentDomain α β → α+β ≤ 1/2 →
        r ∈ Set.Icc (0 : ℝ) (1/2) →
        ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
          cMix*(n : ℝ)^(-exponentA α β) ≤ worstLength n α β r I) ∧
      (∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Ioc (0 : ℝ) (1/2) →
        ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
          cRadius*(r*(n : ℝ)^(-exponentB β)) ≤ worstLength n α β r I) := by
  obtain ⟨hκ, hC, hMixtures⟩ := original_record_mixtures
  let L : ℝ := (⌈max 1 (max (1/mixtureKappa) (100*mixtureConstant*calibEps^4))⌉₊ : ℝ)
  have hmax : max 1 (max (1/mixtureKappa) (100*mixtureConstant*calibEps^4)) ≤ L :=
    Nat.le_ceil _
  have hL : 1 ≤ L := (le_max_left _ _).trans hmax
  have hL0 : 0 < L := by linarith
  have hκL : 1/L ≤ mixtureKappa := by
    have h := (le_max_left (1/mixtureKappa) _).trans ((le_max_right _ _).trans hmax)
    apply (div_le_iff₀ hL0).2
    have h' := (div_le_iff₀ hκ).1 h
    nlinarith
  have hCL : mixtureConstant*calibEps^4/L ≤ 1/100 := by
    have h := (le_max_right (1/mixtureKappa) _).trans ((le_max_right _ _).trans hmax)
    apply (div_le_iff₀ hL0).2
    linarith
  let D := (L+1)^(-(1/2 : ℝ))
  have hε := calib_constants_spec.1
  have hD : 0 < D := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨(7/10)*32*calibEps^2*D, (7/10)*(3/2)*calibEps^2*D,
    by positivity, by positivity, ?_, ?_⟩
  · intro α β r hab hs hr n hn I hI
    have hs0 : 0 < α+β := by linarith [hab.1, hab.2.2.1]
    obtain ⟨k, hk, hkl, hku⟩ := lower_rank_ceiling_bounds L (α+β) hL hs0 n hn
    obtain ⟨hOccupancy, hBudget⟩ := lower_rank_budget L (α+β) hL hs0 hs n k hn hk hkl
    have hSep := lower_rank_separation L (α+β) hL hs0 hs n k hn hk hku
    have hη := calibrated_amplitude_abs_le calibEps α calib_constants_spec.1.le
      (by linarith [hab.1, hab.2.2.1]) k hk
    have hζ := calibrated_amplitude_abs_le calibEps β calib_constants_spec.1.le hab.1.le k hk
    have hH := (hMixtures n k hn hk (hOccupancy.trans hκL)
      (calibEps*(k : ℝ)^(-α)) (calibEps*(k : ℝ)^(-β)) 0 hη hζ
      (by simpa using calib_constants_spec.1.le)).1
    rw [lower_mixed_budget_identity mixtureConstant calibEps α β n k hk] at hH
    have hHscaled := hH.trans (mul_le_mul_of_nonneg_left hBudget
      (by positivity : 0 ≤ mixtureConstant*calibEps^4))
    rw [← mul_div_assoc, mul_one] at hHscaled
    have hHsmall := hHscaled.trans hCL
    have hTest := mixed_prior_length_lower α β r n k hab hr.1 hk I hI hHsmall
    rw [mul_assoc 32, lower_amplitude_product calibEps α β k hk] at hTest
    rw [exponentA_low_branch α β hab hs]
    have h := mul_le_mul_of_nonneg_left hSep
      (by positivity : 0 ≤ (7/10 : ℝ)*32*calibEps^2)
    dsimp only [D] at *
    ring_nf at hTest h ⊢
    exact h.trans hTest
  · intro α β r hab hr n hn I hI
    have hrpos := hr.1
    have hs0 : 0 < 2*β := by linarith [hab.1]
    have hs : 2*β ≤ 1/2 := by linarith [hab.2.1]
    obtain ⟨k, hk, hkl, hku⟩ := lower_rank_ceiling_bounds L (2*β) hL hs0 n hn
    obtain ⟨hOccupancy, hBudget⟩ := lower_rank_budget L (2*β) hL hs0 hs n k hn hk hkl
    have hSep := lower_rank_separation L (2*β) hL hs0 hs n k hn hk hku
    have hδ := calibrated_amplitude_abs_le calibEps β calib_constants_spec.1.le hab.1.le k hk
    have ht : r/2 ∈ Set.Icc (0 : ℝ) (1/4) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hH := (hMixtures n k hn hk (hOccupancy.trans hκL) 0 0
      (calibEps*(k : ℝ)^(-β)) (by simpa using calib_constants_spec.1.le)
      (by simpa using calib_constants_spec.1.le) hδ).2 (r/2) ht
    have hId := lower_mixed_budget_identity mixtureConstant calibEps β β n k hk
    have hEq : (calibEps*(k : ℝ)^(-β))^2*(calibEps*(k : ℝ)^(-β))^2 =
        (calibEps*(k : ℝ)^(-β))^4 := by ring
    rw [mul_assoc (mixtureConstant*(n : ℝ)^2/(k : ℝ)), hEq] at hId
    rw [hId, ← two_mul β] at hH
    have hHscaled := hH.trans (mul_le_mul_of_nonneg_left hBudget
      (by positivity : 0 ≤ mixtureConstant*calibEps^4))
    rw [← mul_div_assoc, mul_one] at hHscaled
    have hHsmall := hHscaled.trans hCL
    have hTest := fair_prior_length_lower α β r n k hab ⟨hr.1.le, hr.2⟩ hk I hI hHsmall
    have hAmp := lower_amplitude_product calibEps β β k hk
    have hAmp' : (calibEps*(k : ℝ)^(-β))^2 = calibEps^2*(k : ℝ)^(-(2*β)) := by
      simpa only [← sq, ← two_mul] using hAmp
    rw [hAmp'] at hTest
    have h := mul_le_mul_of_nonneg_left hSep
      (by positivity : 0 ≤ (7/10 : ℝ)*(3/2)*r*calibEps^2)
    dsimp only [D, exponentB] at *
    ring_nf at hTest h ⊢
    exact h.trans hTest

end CausalSmith.Stat.LogoddsLowsmoothFrontier
