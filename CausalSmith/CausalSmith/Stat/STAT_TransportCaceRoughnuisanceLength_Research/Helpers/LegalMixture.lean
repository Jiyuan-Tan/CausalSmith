module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.Membership
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ChiSquare
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.SeparationIdentity

/-! # Legal full-elbow monotone-IV mixture -/

public section

open Set Filter MeasureTheory
open scoped Topology
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Choose an amplitude below any positive membership ceiling while satisfying
the exponential distance calibration in roadmap (29).  Under [the displayed assumptions and inputs](hyp:α,cap,hα,hcap), [the stated conclusion holds](goal). -/
-- @node: calibrated_mixture_amplitude
lemma calibrated_mixture_amplitude (α cap : ℝ) (hα : α < 1) (hcap : 0 < cap) :
    ∃ c : ℝ, 0 < c ∧ c ≤ cap ∧ c ≤ 1 / 100 ∧
      Real.exp (mixConstant * c ^ 4) ≤ 1 + (1 - α) ^ 2 := by
  have hgap : Real.exp (mixConstant * (0 : ℝ) ^ 4) < 1 + (1 - α) ^ 2 := by
    simp only [zero_pow (by norm_num : 4 ≠ 0), mul_zero, Real.exp_zero]
    nlinarith [sq_pos_of_pos (show 0 < 1 - α by linarith)]
  have hcont : ContinuousAt (fun c : ℝ => Real.exp (mixConstant * c ^ 4)) 0 := by
    fun_prop
  have hevent := hcont.tendsto.eventually (gt_mem_nhds hgap)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let c := min cap (min (1 / 100 : ℝ) (δ / 2))
  have hc : 0 < c := lt_min hcap (lt_min (by norm_num) (half_pos hδ))
  refine ⟨c, hc, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  apply le_of_lt (hnear ?_)
  rw [Real.dist_eq, sub_zero, abs_of_pos hc]
  have := (min_le_right cap (min (1 / 100 : ℝ) (δ / 2))).trans
    (min_le_right (1 / 100 : ℝ) (δ / 2))
  change c < δ
  linarith

-- @node: lem:legal-iv-mixture-full-elbow
/-- Given [the supplied inputs](hyp:α,c_f,C_f,L,hα,hf,hF,hL), [the stated result about legal iv mixture full elbow holds](goal). -/
lemma legal_iv_mixture_full_elbow (α c_f C_f L : ℝ)
    (hα : 0 < α ∧ α < 1) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) :
    ∃ cStar : ℝ, 0 < cStar ∧ cStar < 1 ∧ -- @realizes c_{\star}(chosen amplitude in (0,1))
      (∀ n : ℕ, threshold ≤ n →
        ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
          LowerAdmissible n a cStar) ∧
      ∀ n : ℕ, threshold ≤ n →
      ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
      (∀ τ : ℝ, τ ∈ Icc (-1 : ℝ) 1 →
        (∀ sgn : Fin (lowerCells n) → Bool,
          legalIVComponent a n cStar τ sgn ∈ StrengthSlice c_f C_f L a n ∧
          (∀ s : Bool,
            (∀ x ∈ covariateSpace,
              lowerPointwiseMean a n cStar τ sgn s complier x =
                actualStrength a n ∧
              lowerPointwiseMean a n cStar τ sgn s
                (fun o => (outcome1 o - outcome0 o) * complier o) x =
                -(tiledPerturbation cStar n sgn x *
                  coupledPerturbation cStar τ n sgn x) /
                  (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) ∧
            ConditionalMean (legalIVComponent a n cStar τ sgn) s complier
              (fun _ => actualStrength a n) ∧
            ConditionalMean (legalIVComponent a n cStar τ sgn) s
              (fun o => (outcome1 o - outcome0 o) * complier o)
              (fun x =>
                -(tiledPerturbation cStar n sgn x *
                  coupledPerturbation cStar τ n sgn x) /
                  (1 / 4 - tiledPerturbation cStar n sgn x ^ 2))) ∧
          firstStage (legalIVComponent a n cStar τ sgn) =
            actualStrength a n ∧
          targetCACE (legalIVComponent a n cStar τ sgn) =
            -(τ * separation cStar n) / actualStrength a n) ∧
        1 + Causalean.Stat.chiSqDiv
          (lowerMixture a n cStar τ)
          (dataLaw (mixtureCenter a n) n n) ≤
            Real.exp (mixConstant * cStar ^ 4) ∧
        Causalean.Stat.tvDist
          (lowerMixture a n cStar τ)
          (dataLaw (mixtureCenter a n) n n) ≤ (1 - α) / 2 ∧
        (lowerMixture a n cStar τ) ≪ (dataLaw (mixtureCenter a n) n n) ∧
        MeasureTheory.Integrable (fun ω : TwoSample n n =>
          (((lowerMixture a n cStar τ).rnDeriv
            (dataLaw (mixtureCenter a n) n n) ω).toReal - 1) ^ 2)
          (dataLaw (mixtureCenter a n) n n)) ∧
      mixtureCenter a n ∈ StrengthSlice c_f C_f L a n ∧
      firstStage (mixtureCenter a n) = actualStrength a n ∧
      targetCACE (mixtureCenter a n) = 0 ∧
      2 ^ ((3 : ℝ) / 4) * cStar ^ 2 *
        (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ separation cStar n ∧
      separation cStar n ≤ 4 * cStar ^ 2 *
        (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨cMax, hcMax, hcMax1, hmember⟩ :=
    legal_mixture_membership α c_f C_f L hα hf hF hL
  obtain ⟨cStar, hcStar, hcap, hsmall, hcal⟩ :=
    calibrated_mixture_amplitude α cMax hα.2 hcMax
  have hc : 0 < cStar ∧ cStar ≤ 1 / 100 := ⟨hcStar, hsmall⟩
  have hcStar1 : cStar < 1 := lt_of_le_of_lt hcap hcMax1
  refine ⟨cStar, hcStar, hcStar1, ?_, ?_⟩
  · intro n hn a ha ha4
    exact lower_admissible_of_small_amplitude n a cStar hn ⟨ha, ha4⟩ hc
  · intro n hn a ha ha4
    have hmem := hmember cStar hcStar hcap n hn a ha ha4
    have hmargin := legal_mixture_margins a n cStar 0 (fun _ => false)
      hn ⟨ha, ha4⟩ hc (by norm_num)
    have hsep := legal_mixture_separation n hn cStar hc
    refine ⟨?_, hmem.2, hmargin.2.2.2.1, hmargin.2.2.2.2, hsep.1, hsep.2⟩
    intro τ hτ
    have hdist := legal_mixture_distance α a n cStar τ hτ hn
      ⟨ha, ha4⟩ hα ⟨hcStar, hsmall, hcal⟩
    have hfinite := legal_mixture_finite_chiSquare a n cStar τ hτ hn ⟨ha, ha4⟩ hc
    refine ⟨?_, hdist.1, hdist.2, hfinite.1, hfinite.2⟩
    intro sgn
    have hm := legal_mixture_margins a n cStar τ sgn hn ⟨ha, ha4⟩ hc hτ
    have hDomain : LowerExperimentDomain n a cStar :=
      ⟨by have : 256 ≤ n := hn; omega,
        lower_admissible_of_small_amplitude n a cStar hn ⟨ha, ha4⟩ hc⟩
    have hcomponent :
        (legalIVMixture a n cStar τ hn ⟨ha, ha4⟩ hDomain hcStar1 hτ sgn).1 ∈
          StrengthSlice c_f C_f L a n := hmem.1 τ hτ sgn
    refine ⟨hcomponent, ?_, hm.2.1, hm.2.2.1⟩
    intro s
    refine ⟨?_, (hm.1 s).1, (hm.1 s).2⟩
    intro x _
    exact lowerPointwiseMean_complier_margins a n cStar τ sgn s x
      (actualStrength_bounds a n hn ⟨ha, ha4⟩).1.ne'


end CausalSmith.Stat.TransportCaceRoughnuisanceLength
