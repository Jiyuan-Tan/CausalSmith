module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.CenterMembership
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.SeparationIdentity

/-! # Monotone-IV component and center membership

The roadmap (9) provides an amplitude ceiling: every smaller positive
amplitude satisfies the same model conditions. Keeping this quantifier
explicit allows the assembly to impose the independent distance calibration (29).
-/

public section

open Set MeasureTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: legal_mixture_membership
/-- Given [the supplied inputs](hyp:α,c_f,C_f,L,hα,hf,hF,hL), [the stated result about legal mixture membership holds](goal). -/
lemma legal_mixture_membership (α c_f C_f L : ℝ)
    (hα : 0 < α ∧ α < 1) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) :
    ∃ cMax : ℝ, 0 < cMax ∧ cMax < 1 ∧
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ cMax →
      ∀ n : ℕ, threshold ≤ n →
      ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
      (∀ τ : ℝ, τ ∈ Icc (-1 : ℝ) 1 →
        ∀ sgn : Fin (lowerCells n) → Bool,
          legalIVComponent a n cStar τ sgn ∈ StrengthSlice c_f C_f L a n) ∧
      mixtureCenter a n ∈ StrengthSlice c_f C_f L a n := by
  obtain ⟨cap, hcap, hcap1, hsmall, hlo, hhi, htarget, harm⟩ :=
    exists_membership_amplitude_ceiling c_f C_f L hf.2 hF hL
  refine ⟨cap, hcap, hcap1, ?_⟩
  intro cStar hc hccap n hn a ha ha4
  have hgeometry := fun τ hτ sgn =>
    legalIVComponent_density_overlap_of_ceiling a c_f C_f cStar τ n sgn
      hf hF hn ⟨ha, ha4⟩ ⟨hc, hccap.trans hsmall⟩
      (hccap.trans hlo) (hccap.trans hhi) hτ
  have hholders (τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1)
      (sgn : Fin (lowerCells n) → Bool) :
      SourceDensityHolder L (legalIVComponent a n cStar τ sgn) ∧
      TargetDensityHolder L (legalIVComponent a n cStar τ sgn) ∧
      PropensityHolder L (legalIVComponent a n cStar τ sgn) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [SourceDensityHolder, legalIVComponent, lawFromMass] using
        const_holderOn 1 L hL (by norm_num; linarith)
    · simpa [TargetDensityHolder, legalIVComponent, lawFromMass] using
        one_add_tiledPerturbation_holderOn cStar L n sgn hc.le
          (hccap.trans htarget) hn hL
    · simpa [PropensityHolder, legalIVComponent, lawFromMass] using
        half_add_tiledPerturbation_holderOn cStar L n sgn hc.le
          (hccap.trans htarget) hn hL
  have hcenterHolders :
      SourceDensityHolder L (mixtureCenter a n) ∧
      TargetDensityHolder L (mixtureCenter a n) ∧
      PropensityHolder L (mixtureCenter a n) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [SourceDensityHolder, mixtureCenter, lawFromMass] using
        const_holderOn 1 L hL (by norm_num; linarith)
    · simpa [TargetDensityHolder, mixtureCenter, lawFromMass] using
        const_holderOn 1 L hL (by norm_num; linarith)
    · simpa [PropensityHolder, mixtureCenter, lawFromMass] using
        const_holderOn (1 / 2) L hL (by norm_num; linarith)
  have harmHolders (τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1)
      (sgn : Fin (lowerCells n) → Bool) :=
    legalIVComponent_arm_means_holder a cStar τ L n sgn ⟨ha, ha4⟩ hc.le
      (hccap.trans hsmall) (hccap.trans harm) hτ hn hL
  have harmRegular (τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1)
      (sgn : Fin (lowerCells n) → Bool) :=
    legalIVComponent_arm_means_regular a cStar τ n sgn ⟨ha, ha4⟩ hc.le
      (hccap.trans hsmall) hτ hn
  have hcenterArmHolders := mixtureCenter_arm_means_holder a L n ⟨ha, ha4⟩ hn hL
  have hcenterArmRegular := mixtureCenter_arm_means_regular a n ⟨ha, ha4⟩ hn
  have hb := actualStrength_bounds a n hn ⟨ha, ha4⟩
  have hAdm := lower_admissible_of_small_amplitude n a cStar hn ⟨ha, ha4⟩
    ⟨hc, hccap.trans hsmall⟩
  have hnpos : 0 < n := by have : 256 ≤ n := hn; omega
  have hobs : Measurable observeSource := by unfold observeSource covariate; fun_prop
  constructor
  · intro τ hτ sgn
    let P := legalIVComponent a n cStar τ sgn
    have hgeom := hgeometry τ hτ sgn
    have hhold := hholders τ hτ sgn
    have hass := legalIVComponent_assignment_conditions a n cStar τ sgn hb hAdm hτ hnpos
    have : IsProbabilityMeasure P.assignedLaw := hass.2.2.1
    have : IsProbabilityMeasure (sourceObsLaw P) :=
      Measure.isProbabilityMeasure_map hobs.aemeasurable
    have : IsProbabilityMeasure (targetXLaw P) := ⟨by
      rw [hgeom.2.1.1]
      apply targetDensity_univ cStar n sgn hnpos
      intro x
      have hu := (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc.le).trans hAdm.2.1
      linarith [neg_abs_le (tiledPerturbation cStar n sgn x)]⟩
    have hsampling := @lawFromMass_sampling_conditions
      (fun _ => 1) (fun x => 1 + tiledPerturbation cStar n sgn x)
      (fun x => 1 / 2 + tiledPerturbation cStar n sgn x)
      (lowerMass a n cStar τ sgn)
      (inferInstanceAs (IsProbabilityMeasure (sourceObsLaw P)))
      (inferInstanceAs (IsProbabilityMeasure (targetXLaw P))) n n
    have hmarg := legal_mixture_margins a n cStar τ sgn hn ⟨ha, ha4⟩
      ⟨hc, hccap.trans hsmall⟩ hτ
    have hmodel : ModelClass c_f C_f L P n := {
      sourceIid := hsampling.1
      targetIid := hsampling.2.1
      independence := hsampling.2.2
      sourceBounds := hgeom.1
      targetBounds := hgeom.2.1
      sourceHolder := hhold.1
      targetHolder := hhold.2.1
      overlap := hgeom.2.2
      propensityHolder := hhold.2.2
      armHolder := ⟨harmHolders τ hτ sgn, harmRegular τ hτ sgn,
        legalIVComponent_arm_setIntegral a cStar τ n sgn ⟨ha, ha4⟩
          ⟨hc, hccap.trans hsmall⟩ hn hτ⟩
      receipt := hass.1
      outcome := hass.2.1
      randomized := hass.2.2
      exclusion := legalIVComponent_exclusion a n cStar τ sgn
      monotone := legalIVComponent_monotonicity a n cStar τ sgn
      outcomeTransport := ⟨_, (hmarg.1 false).2, (hmarg.1 true).2⟩
      shareTransport := ⟨_, (hmarg.1 false).1, (hmarg.1 true).1⟩
      strength := by change 0 < firstStage P; rw [hmarg.2.1]; exact hb.1 }
    refine ⟨ha, ha4, hmodel, ?_, ?_⟩
    · rw [hmarg.2.1]; exact le_max_left _ _
    · rw [hmarg.2.1]; exact hb.2
  · let P := mixtureCenter a n
    have hass := mixtureCenter_assignment_conditions a n hb
    have : IsProbabilityMeasure P.assignedLaw := hass.2.2.1
    have : IsProbabilityMeasure (sourceObsLaw P) :=
      Measure.isProbabilityMeasure_map hobs.aemeasurable
    have : IsProbabilityMeasure (targetXLaw P) := ⟨by
      rw [(mixtureCenter_targetDensityBounds a c_f C_f n hf hF hb).1]
      simp [P, mixtureCenter, lawFromMass, covariateSpace]⟩
    have hsampling := @lawFromMass_sampling_conditions
      (fun _ => 1) (fun _ => 1) (fun _ => 1 / 2)
      (fun _ => primitiveMass (actualStrength a n) 0 0)
      (inferInstanceAs (IsProbabilityMeasure (sourceObsLaw P)))
      (inferInstanceAs (IsProbabilityMeasure (targetXLaw P))) n n
    have hstage := mixtureCenter_firstStage a n (ne_of_gt hb.1)
    have hmodel : ModelClass c_f C_f L P n := {
      sourceIid := hsampling.1
      targetIid := hsampling.2.1
      independence := hsampling.2.2
      sourceBounds := mixtureCenter_sourceDensityBounds a c_f C_f n hf hF hb
      targetBounds := mixtureCenter_targetDensityBounds a c_f C_f n hf hF hb
      sourceHolder := hcenterHolders.1
      targetHolder := hcenterHolders.2.1
      overlap := by intro x hx; norm_num [P, mixtureCenter, lawFromMass]
      propensityHolder := hcenterHolders.2.2
      armHolder := ⟨hcenterArmHolders, hcenterArmRegular, mixtureCenter_arm_setIntegral a n hb⟩
      receipt := hass.1
      outcome := hass.2.1
      randomized := hass.2.2
      exclusion := mixtureCenter_exclusion a n
      monotone := mixtureCenter_monotonicity a n
      outcomeTransport := ⟨_, (mixtureCenter_conditional_complier_margins a n hb false).2,
        (mixtureCenter_conditional_complier_margins a n hb true).2⟩
      shareTransport := ⟨_, (mixtureCenter_conditional_complier_margins a n hb false).1,
        (mixtureCenter_conditional_complier_margins a n hb true).1⟩
      strength := by change 0 < firstStage P; rw [hstage]; exact hb.1 }
    refine ⟨ha, ha4, hmodel, ?_, ?_⟩
    · rw [hstage]; exact le_max_left _ _
    · rw [hstage]; exact hb.2

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
