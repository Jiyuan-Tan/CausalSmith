module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import Causalean.Stat.Concentration.Matrix.IidSums

/-! The fair product prior on binary cell outcome parameters for the large-alphabet converse. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def binaryCellPrior (d : ℕ) : Measure (Fin d → Bool) :=
  Measure.pi (fun _ : Fin d =>
    (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true)

/-- For [the specified inputs and assumptions](hyp:d,ξ), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def cellPriorTarget {d : ℕ} (ξ : Fin d → Bool) : ℝ :=
  (∑ x : Fin d, if ξ x then (1 : ℝ) else 0) / d

/-- Given [the specified inputs and assumptions](hyp:f), [the stated mathematical conclusion holds](goal). -/
-- @node: fairBinary_integral
lemma fairBinary_integral (f : Bool → ℝ) :
    (∫ b, f b ∂((1 / 2 : ℝ≥0∞) • Measure.dirac false +
      (1 / 2 : ℝ≥0∞) • Measure.dirac true)) = (f false + f true) / 2 := by
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure]
  simp
  ring

/-- [the stated mathematical conclusion holds](goal). -/
-- @node: fairBinary_probability
lemma fairBinary_probability :
    IsProbabilityMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac false +
      (1 / 2 : ℝ≥0∞) • Measure.dirac true) := by
  constructor
  norm_num
  exact ENNReal.inv_two_add_inv_two

-- @node: binaryCellPrior_target_concentration
/-- Given [the specified inputs and assumptions](hyp:d,hd,h,hh), [the stated mathematical conclusion holds](goal). -/
lemma binaryCellPrior_target_concentration (d : ℕ) (hd : 1 ≤ d) (h : ℝ) (hh : 0 < h) :
    (binaryCellPrior d).real {ξ | h < |cellPriorTarget ξ - 1 / 2|} ≤
      1 / (4 * (d : ℝ) * h ^ 2) := by
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let g : Bool → ℝ := fun b => if b then 1 else 0
  have hg : MemLp g 2 μ := MemLp.of_discrete
  have hmean : (∫ b, g b ∂μ) = 1 / 2 := by
    rw [show μ = _ from rfl, fairBinary_integral]
    norm_num [g]
  have hvar : variance g μ = 1 / 4 := by
    rw [variance_eq_integral hg.aemeasurable, hmean]
    rw [show μ = _ from rfl, fairBinary_integral]
    norm_num [g]
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hcheb := Causalean.Stat.Concentration.iid_sum_chebyshev
    (N := d) μ g hg (mul_pos hdpos hh)
  rw [hmean, hvar] at hcheb
  have hsub : {ξ | h < |cellPriorTarget ξ - 1 / 2|} ⊆
      {ξ : Fin d → Bool | (d : ℝ) * h ≤ |(∑ x, g (ξ x)) - d * (1 / 2)|} := by
    intro ξ hξ
    have heq : (∑ x, g (ξ x)) - d * (1 / 2) =
        (d : ℝ) * (cellPriorTarget ξ - 1 / 2) := by
      dsimp [cellPriorTarget, g]
      field_simp
    change (d : ℝ) * h ≤ |(∑ x, g (ξ x)) - d * (1 / 2)|
    rw [heq, abs_mul, abs_of_pos hdpos]
    exact le_of_lt (mul_lt_mul_of_pos_left hξ hdpos)
  have hprob := (measure_mono hsub).trans hcheb
  have hreal := ENNReal.toReal_mono (by simp) hprob
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  change (binaryCellPrior d).real {ξ | h < |cellPriorTarget ξ - 1 / 2|} ≤ _ at hreal
  have halg : (d : ℝ) * (1 / 4) / ((d : ℝ) * h) ^ 2 =
      1 / (4 * (d : ℝ) * h ^ 2) := by
    field_simp
  simpa only [halg] using hreal

end CausalSmith.Stat.MarRareqLogfrontier
