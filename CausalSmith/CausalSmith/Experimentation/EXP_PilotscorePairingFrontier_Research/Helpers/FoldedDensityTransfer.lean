module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BernoulliHypercube

/-! # Transfer of an explicit folded-score density to the model predicate -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

/-- Once the geometric calculation identifies the score pushforward as an
explicit density, this lemma performs the Bernoulli-law and Radon--Nikodym
bookkeeping required by `RegularScorePushforward`. -/
lemma regularScorePushforward_of_cube_map_withDensity {d : ℕ}
    {g : XSpace d → ℝ} {p : ℝ → ℝ} {cg Cg : ℝ}
    (hg : Measurable g) (hrange : ∀ x ∈ cube d, 0 ≤ g x ∧ g x ≤ 1)
    (hp : Measurable p) (hp0 : ∀ t, 0 ≤ p t)
    (hpbounds : ∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
      cg ≤ p t ∧ p t ≤ Cg)
    (hmap : (cubeMeasure d).map g =
      ((volume : Measure ℝ).restrict scoreInterval).withDensity
        (fun t => ENNReal.ofReal (p t))) :
    RegularScorePushforward (bernoulliUnitLaw g) g cg Cg := by
  let ρ := (volume : Measure ℝ).restrict scoreInterval
  have hfst := bernoulliUnitLaw_map_fst g hg hrange
  have hscore :
      (bernoulliUnitLaw g).map (fun u => g u.1) =
        ρ.withDensity (fun t => ENNReal.ofReal (p t)) := by
    calc
      (bernoulliUnitLaw g).map (fun u => g u.1) =
          ((bernoulliUnitLaw g).map Prod.fst).map g := by
        simpa [Function.comp_def] using
          (Measure.map_map (μ := bernoulliUnitLaw g) hg measurable_fst).symm
      _ = (cubeMeasure d).map g := by rw [hfst]
      _ = ρ.withDensity (fun t => ENNReal.ofReal (p t)) := hmap
  change (bernoulliUnitLaw g).map (fun u => g u.1) ≪ ρ ∧ _
  rw [hscore]
  constructor
  · exact withDensity_absolutelyContinuous _ _
  · filter_upwards [Measure.rnDeriv_withDensity ρ hp.ennreal_ofReal, hpbounds]
      with t ht hb
    rw [ht, ENNReal.toReal_ofReal (hp0 t)]
    exact hb

end CausalSmith.Experimentation.PilotscorePairingFrontier
