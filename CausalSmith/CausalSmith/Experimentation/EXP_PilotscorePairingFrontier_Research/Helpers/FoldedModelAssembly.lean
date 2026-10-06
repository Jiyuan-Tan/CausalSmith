module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedRegularPushforward

/-! # Bernoulli regular-score model assembly -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma bernoulliUnitLaw_covariateDensity
    {d : ℕ} {g : XSpace d -> ℝ} {cX CX : ℝ}
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1)
    (hcX : cX ≤ 1) (hCX : 1 ≤ CX) :
    CovariateDensity (bernoulliUnitLaw g) cX CX := by
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  have hmap := bernoulliUnitLaw_map_fst g hg hrange
  constructor
  · exact bernoulliUnitLaw_isProbabilityMeasure g hg hrange
  constructor
  · rw [hmap]
  · rw [hmap]
    filter_upwards [Measure.rnDeriv_self (cubeMeasure d)] with x hx
    rw [hx, ENNReal.toReal_one]
    exact ⟨hcX, hCX⟩

/-- The generic Bernoulli witness helpers reduce model membership to the
Hölder estimate and regular score-pushforward calculation. -/
lemma bernoulliUnitLaw_regularScoreModel
    {d : ℕ} {beta L cX CX cg Cg : ℝ}
    (hpars : ValidClassParameters d beta L cX CX cg Cg)
    {g : XSpace d -> ℝ}
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1)
    (hholder : HolderScore g L beta)
    (hregular : RegularScorePushforward (bernoulliUnitLaw g) g cg Cg) :
    RegularScoreModel (bernoulliUnitLaw g) g L beta cX CX cg Cg := by
  rcases hpars with ⟨hd, hbeta0, hbeta1, hL0, hcX0, hcX1, hCX1,
    hcg0, hcg2, hCg2⟩
  refine
    { parameters := ⟨hd, hbeta0, hbeta1, hL0, hcX0, hcX1, hCX1,
        hcg0, hcg2, hCg2⟩
      half_sum_version := bernoulliUnitLaw_isHalfSumVersion g hg hrange
      covariate_density := bernoulliUnitLaw_covariateDensity hg hrange hcX1 hCX1
      bounded_outcomes := bernoulliUnitLaw_boundedOutcomes g hg
      holder_score := hholder
      regular_score_pushforward := hregular }

end CausalSmith.Experimentation.PilotscorePairingFrontier
