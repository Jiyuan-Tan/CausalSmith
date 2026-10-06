module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.Assembly
public import Causalean.Stat.Minimax.ChiSquared

/-! # Finite sign-mixture chi-square and total-variation estimates -/

public section

open Set MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The legal uniform mixture has an absolutely continuous likelihood with
an integrable squared real density deviation relative to the center experiment. Under [the displayed assumptions and inputs](hyp:a,n,cStar,hn,ha,hc,hτ), [the stated conclusion holds](goal). -/
-- @node: legal_mixture_finite_chiSquare
lemma legal_mixture_finite_chiSquare (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    (lowerMixture a n cStar τ) ≪ (dataLaw (mixtureCenter a n) n n) ∧
    MeasureTheory.Integrable (fun ω : TwoSample n n =>
      (((lowerMixture a n cStar τ).rnDeriv
        (dataLaw (mixtureCenter a n) n n) ω).toReal - 1) ^ 2)
      (dataLaw (mixtureCenter a n) n n) := by
  exact legal_mixture_finite_chiSquare_support a n cStar τ hτ hn ha hc
/-- Given [the supplied inputs](hyp:α,a,n,cStar,hn,ha,hα,hc,hτ), [the stated result about legal mixture distance holds](goal). -/

lemma legal_mixture_distance (α a : ℝ) (n : ℕ)
    (cStar τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : threshold ≤ n) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hα : 0 < α ∧ α < 1)
    (hc : 0 < cStar ∧ cStar ≤ 1 / 100 ∧
      Real.exp (mixConstant * cStar ^ 4) ≤
        1 + (1 - α) ^ 2) :
    1 + Causalean.Stat.chiSqDiv
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n) ≤
        Real.exp (mixConstant * cStar ^ 4) ∧
    Causalean.Stat.tvDist
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n) ≤ (1 - α) / 2 := by
  have hsmall : 0 < cStar ∧ cStar ≤ 1 / 100 := ⟨hc.1, hc.2.1⟩
  have hchi := legal_chi_exp_bound a n cStar τ hτ hn ha hsmall
  refine ⟨hchi, ?_⟩
  have htv := legal_tv_le_half_sqrt_chi a n cStar τ hτ hn ha hsmall
  have hchi' : Causalean.Stat.chiSqDiv
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n) ≤ (1 - α) ^ 2 := by
    linarith [hc.2.2]
  have hsqrt : Real.sqrt (Causalean.Stat.chiSqDiv
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n)) ≤ 1 - α := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith [hα.2], hchi'⟩
  calc
    Causalean.Stat.tvDist
        (lowerMixture a n cStar τ)
        (dataLaw (mixtureCenter a n) n n) ≤
        (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv
          (lowerMixture a n cStar τ)
          (dataLaw (mixtureCenter a n) n n)) := htv
    _ ≤ (1 - α) / 2 := by nlinarith

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
