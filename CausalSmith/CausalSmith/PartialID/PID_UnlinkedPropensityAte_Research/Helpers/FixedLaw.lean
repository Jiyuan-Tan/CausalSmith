module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TCompatibility
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawConvexity

/-! Sharp potential-outcome means and ATE interval at a fixed released law. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: lem:fixed-released-law-baseline
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hOverlap,hg,hcomp), this result [establishes the stated mathematical conclusion](goal). -/
lemma fixedReleasedLaw_sharp {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J))
    (hOverlap : Overlap ε) (hg : Measurable g)
    (hcomp : (CompatibleLaws H g Prel).Nonempty) :
    (∀ a : ArmSpace,
      {v : ℝ | ∃ P ∈ CompatibleLaws H g Prel,
        v = ∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ) ∂P} =
        Set.Icc
          (muLower H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) a)
          (muUpper H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) a)) ∧
    {v : ℝ | ∃ P ∈ CompatibleLaws H g Prel, v = ate P} =
      sharpATESet H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) ∧
    (∃ Pminus ∈ CompatibleLaws H g Prel,
      ∃ Pplus ∈ CompatibleLaws H g Prel,
        ate Pminus =
          muLower H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) true -
          muUpper H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) false ∧
        ate Pplus =
          muUpper H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) true -
          muLower H g Prel (compatibleCellMasses_of_nonempty H g Prel hcomp) false) := by
  let hMass := compatibleCellMasses_of_nonempty H g Prel hcomp
  let Plo := endpointFullLaw H g Prel hMass hOverlap false false
  let Phi := endpointFullLaw H g Prel hMass hOverlap true true
  let Pminus := endpointFullLaw H g Prel hMass hOverlap true false
  let Pplus := endpointFullLaw H g Prel hMass hOverlap false true
  have hlo : CompatibleCausalLaw H g Prel Plo :=
    endpointFullLaw_compatibleCausalLaw H g Prel hMass hOverlap false false
  have hhi : CompatibleCausalLaw H g Prel Phi :=
    endpointFullLaw_compatibleCausalLaw H g Prel hMass hOverlap true true
  have hminus : CompatibleCausalLaw H g Prel Pminus :=
    endpointFullLaw_compatibleCausalLaw H g Prel hMass hOverlap true false
  have hplus : CompatibleCausalLaw H g Prel Pplus :=
    endpointFullLaw_compatibleCausalLaw H g Prel hMass hOverlap false true
  have hloMem : Plo ∈ CompatibleLaws H g Prel := ⟨hlo.probability, hlo⟩
  have hhiMem : Phi ∈ CompatibleLaws H g Prel := ⟨hhi.probability, hhi⟩
  have hminusMem : Pminus ∈ CompatibleLaws H g Prel :=
    ⟨hminus.probability, hminus⟩
  have hplusMem : Pplus ∈ CompatibleLaws H g Prel :=
    ⟨hplus.probability, hplus⟩
  have hminusAte : ate Pminus =
      muLower H g Prel hMass true - muUpper H g Prel hMass false := by
    letI : IsProbabilityMeasure Pminus := hminus.probability
    rw [ate_eq_potentialOutcomeMeans_sub]
    have h1 := endpointFullLaw_armMean H g Prel hMass hOverlap true false true
    have h0 := endpointFullLaw_armMean H g Prel hMass hOverlap true false false
    simpa [Pminus] using congrArg₂ (· - ·) h1 h0
  have hplusAte : ate Pplus =
      muUpper H g Prel hMass true - muLower H g Prel hMass false := by
    letI : IsProbabilityMeasure Pplus := hplus.probability
    rw [ate_eq_potentialOutcomeMeans_sub]
    have h1 := endpointFullLaw_armMean H g Prel hMass hOverlap false true true
    have h0 := endpointFullLaw_armMean H g Prel hMass hOverlap false true false
    simpa [Pplus] using congrArg₂ (· - ·) h1 h0
  refine ⟨?_, ?_, ?_⟩
  · intro a
    ext v
    constructor
    · rintro ⟨P, hP, rfl⟩
      exact compatible_armMean_mem_endpoints H g Prel P hP.2 hMass hOverlap a
    · intro hv
      rcases Icc_subset_segment hv with ⟨c, d, hc, hd, hcd, hv⟩
      let cE : ENNReal := ENNReal.ofReal c
      let dE : ENNReal := ENNReal.ofReal d
      let Pmix := compatibleMixture cE dE Plo Phi
      have hsumE : cE + dE = 1 := by
        dsimp [cE, dE]
        rw [← ENNReal.ofReal_add hc hd, hcd]
        norm_num
      have hmix := compatibleCausalLaw_mixture H g Prel Plo Phi hlo hhi
        cE dE ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hsumE
      refine ⟨Pmix, ⟨hmix.probability, hmix⟩, ?_⟩
      letI : IsProbabilityMeasure Plo := hlo.probability
      letI : IsProbabilityMeasure Phi := hhi.probability
      have hint := integral_compatibleMixture Plo Phi cE dE
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        (fun ω => ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ))
        (by
          cases a
          · simp only [Bool.false_eq_true, ↓reduceIte]
            unfold outcome0
            fun_prop
          · simp only [↓reduceIte]
            unfold outcome1
            fun_prop) 1 (by
            intro ω
            cases a
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rw [Real.norm_eq_abs, abs_of_nonneg (outcome0 ω).property.1]
              exact (outcome0 ω).property.2
            · simp only [↓reduceIte]
              rw [Real.norm_eq_abs, abs_of_nonneg (outcome1 ω).property.1]
              exact (outcome1 ω).property.2)
      have hL := endpointFullLaw_armMean H g Prel hMass hOverlap false false a
      have hU := endpointFullLaw_armMean H g Prel hMass hOverlap true true a
      change v = ∫ ω, ((if a then outcome1 ω else outcome0 ω : OutcomeSpace) : ℝ)
        ∂Pmix
      rw [hint, hL, hU]
      dsimp [cE, dE]
      rw [ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd]
      simpa [smul_eq_mul] using hv.symm
  · ext v
    constructor
    · rintro ⟨P, hP, rfl⟩
      exact compatibleLaw_ate_mem_sharpATESet H g Prel hOverlap hcomp P hP
    · intro hv
      unfold sharpATESet at hv
      rcases Icc_subset_segment hv with ⟨c, d, hc, hd, hcd, hv⟩
      let cE : ENNReal := ENNReal.ofReal c
      let dE : ENNReal := ENNReal.ofReal d
      let Pmix := compatibleMixture cE dE Pminus Pplus
      have hsumE : cE + dE = 1 := by
        dsimp [cE, dE]
        rw [← ENNReal.ofReal_add hc hd, hcd]
        norm_num
      have hmix := compatibleCausalLaw_mixture H g Prel Pminus Pplus
        hminus hplus cE dE ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hsumE
      refine ⟨Pmix, ⟨hmix.probability, hmix⟩, ?_⟩
      letI : IsProbabilityMeasure Pminus := hminus.probability
      letI : IsProbabilityMeasure Pplus := hplus.probability
      have hint := integral_compatibleMixture Pminus Pplus cE dE
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        (fun ω => (outcome1 ω : ℝ) - (outcome0 ω : ℝ))
        (by unfold outcome0 outcome1; fun_prop) 1 (by
          intro ω
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by
            linarith [(outcome0 ω).property.2, (outcome1 ω).property.1], by
            linarith [(outcome1 ω).property.2, (outcome0 ω).property.1]⟩)
      change v = ate Pmix
      rw [show ate Pmix = _ from hint]
      change v = cE.toReal * ate Pminus + dE.toReal * ate Pplus
      rw [hminusAte, hplusAte]
      dsimp [cE, dE]
      rw [ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd]
      simpa [smul_eq_mul] using hv.symm
  · exact ⟨Pminus, hminusMem, Pplus, hplusMem, hminusAte, hplusAte⟩

end CausalSmith.PartialID.UnlinkedPropensityAte
