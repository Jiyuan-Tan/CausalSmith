module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Regions

/-! # Continuity substrate for the three-output region

This file provides the positivity facts and affine stationarity coefficient used
to construct local certificates for the three-mask support regime. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

/-- Every staircase-pattern mass is positive at interior trial parameters. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp0,hp1,hμ00,hμ01,hμ10,hμ11), [the pattern Mass pos of interior](goal).

Under the stated assumptions, the pattern Mass pos of interior. -/
lemma patternMass_pos_of_interior (p μ0 μ1 ε : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ00 : 0 < μ0) (hμ01 : μ0 < 1)
    (hμ10 : 0 < μ1) (hμ11 : μ1 < 1) (s : Fin 14) :
    0 < patternMass (fun k => if k = 0 then μ0 else μ1) p ε s := by
  have hr (j : Fin 4) : 0 < patternRay ε s j := by
    simp only [patternRay, privacyIncrement, privacyRatio]
    split <;> simp_all <;> positivity
  have hpi (j : Fin 4) :
      0 ≤ piTheta (fun k => if k = 0 then μ0 else μ1) p j := by
    fin_cases j <;> simp only [piTheta, controlProb] <;> simp_all <;> try positivity
    all_goals linarith
  unfold patternMass
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hpi j) (hr j).le
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    change 0 < ((1 - p) * (1 - μ0)) * patternRay ε s 0
    exact mul_pos (mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hμ01)) (hr 0)

/-- The canonical weights on masks 0, 5, and 7. The stated result follows. [The r3 Weight](goal) is determined by [the displayed parameters](hyp:ε). -/
def r3Weight (ε : ℝ) : StaircaseWeight :=
  fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then (Real.exp ε + 2)⁻¹ else 0

/-- The stationarity equation evaluated at the canonical three-mask weights. For the displayed inputs and conditions, the stated result follows. [The r3 Stationarity](goal) is determined by [the displayed parameters](hyp:p,μ0,μ1,ε,t). -/
def r3Stationarity (p μ0 μ1 ε t : ℝ) : ℝ :=
  ∑ s : Fin 14, r3Weight ε s *
    patternInformationSlope (fun k => if k = 0 then μ0 else μ1) p ε s t

/-- The linear coefficient of the canonical three-mask stationarity equation. For the displayed inputs and conditions, the stated result follows. [The r3 Stationarity Coeff](goal) is determined by [the displayed parameters](hyp:p,μ0,μ1,ε). -/
def r3StationarityCoeff (p μ0 μ1 ε : ℝ) : ℝ :=
  r3Stationarity p μ0 μ1 ε 1 - r3Stationarity p μ0 μ1 ε 0

/-- The unit finite difference of a pattern's information slope is its positive
quadratic coefficient. For [the displayed inputs and conditions](hyp:p), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:s), these specify the stated inputs. -/
lemma patternInformationSlope_one_sub_zero (θ : TrialParameter) (p ε : ℝ)
    (s : Fin 14) :
    patternInformationSlope θ p ε s 1 - patternInformationSlope θ p ε s 0 =
      2 * (patternGradient p ε s 0 + patternGradient p ε s 1) ^ 2 /
        patternMass θ p ε s := by
  simp [patternInformationSlope, projectedGradient, direction, Fin.sum_univ_succ]
  ring

/-- The canonical three-mask stationarity equation has positive linear coefficient at interior trial parameters and positive privacy budget. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp0,hp1,hμ00,hμ01,hμ10,hμ11,hε), [the r3 Stationarity Coeff pos](goal).

Under the stated assumptions, the r3 Stationarity Coeff pos. -/
lemma r3StationarityCoeff_pos (p μ0 μ1 ε : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ00 : 0 < μ0) (hμ01 : μ0 < 1)
    (hμ10 : 0 < μ1) (hμ11 : μ1 < 1) (hε : 0 < ε) :
    0 < r3StationarityCoeff p μ0 μ1 ε := by
  have hm (s : Fin 14) :
      0 < patternMass (fun k => if k = 0 then μ0 else μ1) p ε s :=
    patternMass_pos_of_interior p μ0 μ1 ε hp0 hp1 hμ00 hμ01 hμ10 hμ11 s
  rw [show r3StationarityCoeff p μ0 μ1 ε =
      ∑ s : Fin 14, r3Weight ε s *
        (patternInformationSlope (fun k => if k = 0 then μ0 else μ1) p ε s 1 -
          patternInformationSlope (fun k => if k = 0 then μ0 else μ1) p ε s 0) by
    unfold r3StationarityCoeff r3Stationarity
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  simp_rw [patternInformationSlope_one_sub_zero]
  apply Finset.sum_pos'
  · intro s _
    apply mul_nonneg
    · simp only [r3Weight]
      split <;> positivity
    · exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hm s).le
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    apply mul_pos
    · simp [r3Weight]
      positivity
    · apply div_pos
      · apply mul_pos
        · norm_num
        · simp +decide [patternGradient, controlProb, privacyIncrement, privacyRatio]
          have : 1 < Real.exp ε := (Real.one_lt_exp_iff).2 hε
          positivity
      · exact hm 0

end CausalSmith.Stat.LdpAteEfficiencySurface
