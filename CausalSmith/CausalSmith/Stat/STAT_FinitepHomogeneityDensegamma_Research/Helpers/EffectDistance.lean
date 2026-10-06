module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Basic
public import Mathlib.Probability.Moments.Variance

/-! Bounds on centered effect distance from the original effect envelope. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Centering cannot increase the root second moment beyond a uniform envelope. This statement assumes [the hB condition](hyp:hB), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: hetDist_le_effect_envelope
lemma hetDist_le_effect_envelope (law : ObservedLaw) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, |law.tau x| ≤ B) : hetDist law ≤ B := by
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  have hm : AEMeasurable law.tau design := by fun_prop
  have hv := variance_le_sq_of_bounded
    (Filter.Eventually.of_forall (fun x => abs_le.mp (hb x))) hm
  have he : variance law.tau design = ∫ x, (law.tau x-meanTau law)^2 ∂design := by
    simpa only [meanTau] using variance_eq_integral hm
  rw [he] at hv
  have hi : (∫ x, (law.tau x-meanTau law)^2 ∂design) ≤ B^2 := by
    convert hv using 1 <;> ring
  exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_sq hB)

/-- The fixed tent amplitude is strictly below the nonempty witness distance. [This is the stated conclusion](goal). -/
-- @node: one_sixteenth_lt_d0
lemma one_sixteenth_lt_d0 : (1:ℝ)/16 < d0 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  unfold d0
  apply (lt_div_iff₀ (by positivity : 0 < 8*Real.sqrt 2)).2
  nlinarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
