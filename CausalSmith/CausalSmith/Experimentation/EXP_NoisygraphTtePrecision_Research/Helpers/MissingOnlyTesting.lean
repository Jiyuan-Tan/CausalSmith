module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLaw
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TBlockTestingScale

/-!
# Supported block testing in the comparison channel

The bounded-baseline block construction is transported through the exact
comparison-record law, preserving every graph label, assignment, and response.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hs,hsd,hB,h,hh,hfit,hp,ha,hhu), [The inherited concrete bounded-baseline block priors give separated constant targets
and full detailed-record TV at most one half in the no-false-positive channel.](goal) -/
-- @node: lem:missing-only-supported-testing
lemma missing_only_supported_testing (n d s B : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (hs : 1 ≤ s) (hsd : s ≤ d) (hB : 1 ≤ B) (hfit : 2*(B*s) ≤ n)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (μZ : Measure (Assign (Fin n)))
    (ha : AssignmentLaw (fun η => μZ.prod (acquisitionLaw η p 0)))
    (h : ℝ) (hh : 0 < h) (hhu : h ≤ (100*Real.pi)⁻¹ * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s p) :
    let Dc := fun η => μZ.prod (acquisitionLaw η p 0)
    (∀ σ : Bool, ∀ᵐ ξ ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s,
      ScheduleClass (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ) d ∧
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ) = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*(B*s : ℕ)*h/n) ∧
    Causalean.Stat.tvDist
      ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s).bind (fun ξ =>
        (Dc (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s true h ξ)).map (recordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s true h ξ))))
      ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s).bind (fun ξ =>
        (Dc (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s false h ξ)).map (recordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s false h ξ)))) ≤ 1/2 := by
  let η₀ : Schedule (Fin n) :=
    ⟨fun _ _ => False, inferInstance, fun _ => not_false, fun _ => 0,
      fun _ => 0, fun _ _ => 0⟩
  have hassign := ha η₀
  let := acquisitionLaw_probability p 0 ⟨le_rfl, hp.1, hp.2⟩ η₀
  rw [Measure.map_fst_prod, measure_univ, one_smul] at hassign
  subst μZ
  have hscale :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale_pos_le_one
      B s p hB hs
  have hsmall : h ∈ Set.Icc (0 : ℝ) (1/4) := by
    refine ⟨hh.le, hhu.trans ?_⟩
    calc
      (100*Real.pi)⁻¹ *
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s p
          ≤ (100*Real.pi)⁻¹ :=
        mul_le_of_le_one_right (by positivity) hscale.2
      _ ≤ 1/4 := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ (by positivity : 0 < 100*Real.pi)).mpr
        nlinarith [Real.pi_gt_three]
  dsimp only
  constructor
  · intro σ
    have hsupp :=
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.block_support
        n B s σ h hB hs hfit hsmall
    filter_upwards [hsupp] with ξ hξ
    exact ⟨((scheduleClass_iff_thin _ s).mpr hξ.1).mono hsd, hξ.2⟩
  · have hbridge (σ : Bool) :
        ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s).bind
          (fun ξ =>
            ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli
              (Fin n)).prod (acquisitionLaw
                (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule
                  n B s σ h ξ) p 0)).map
              (recordOf
                (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule
                  n B s σ h ξ)))) =
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockMixtureLawOf
          n B s
          (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.thinnedDesign
            (Fin n) p) σ h := by
      unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockMixtureLawOf
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.mixtureLaw
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.thinnedDesign
      congr 1
      funext ξ
      exact comparison_record_law_eq_thin _ p hp _
    rw [hbridge true, hbridge false]
    exact (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.block_testing_scale
      n B s p
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.thinnedDesign (Fin n) p)
      hn hB hs hfit hp
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.thinnedDesign_assignment p hp)
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.thinnedDesign_audit p hp)
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.thinnedDesign_independent p hp)).1
        h hh.le hhu

end CausalSmith.Experimentation.NoisygraphTtePrecision
