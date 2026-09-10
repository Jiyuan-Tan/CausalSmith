import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ConfidenceUnion
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Set-theoretic confidence-union coverage

Honest-slot simultaneous covariance coverage implies inclusion of the true structural matrix in
the compatibility union, with a measurability-conditional probability corollary.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open MeasureTheory Set

/-- The simultaneous honest-slot coverage event at a fixed region realization. -/
def coverageEvent {p m c : ℕ} (W : BackshiftSystem p m c)
    (C : Environment m → Set (RealMatrix p)) : Prop :=
  ∀ e ∈ W.honest, W.covariance e ∈ C e

-- @node: thm:confidence-union-coverage
/-- For arbitrary nonempty PSD covariance regions, honest-slot coverage places the true
structural matrix in the set-theoretic confidence union. [Under the stated hypotheses](hyp:honest_covariance_model) [this conclusion](goal) applies. -/
theorem confidence_union_coverage {p m c : ℕ}
    (W : BackshiftSystem p m c) (V : InferenceWorld p m)
    (backshift_normalization : BackshiftNormalization W)
    (nonnegative_shifts : NonnegativeShifts W)
    (honest_covariance_model : HonestCovarianceModel W)
    (invariant_noise_psd : W.invariantNoise.PosSemidef) :
    coverageEvent W V.currentRegions →
      W.structural ∈ confidenceUnion c V := by
  intro covered
  classical
  let Gamma : Environment m → RealMatrix p := fun e ↦
    if he : e ∈ W.honest then W.covariance e
    else Classical.choose (V.regions_nonempty V.sampleSize e)
  have hGamma : ∀ e, Gamma e ∈ V.currentRegions e := by
    intro e
    by_cases he : e ∈ W.honest
    · simpa [Gamma, he] using covered e he
    · simpa [Gamma, he, InferenceWorld.currentRegions] using
        (Classical.choose_spec (V.regions_nonempty V.sampleSize e))
  refine Set.mem_iUnion_of_mem Gamma (Set.mem_iUnion_of_mem hGamma ?_)
  refine ⟨backshift_normalization, W.honest, ?_, W.invariantNoise,
    invariant_noise_psd, W.shifts, nonnegative_shifts, ?_⟩
  · simp [W.honest_card]
  · intro e he
    simpa [Gamma, he] using honest_covariance_model e he

-- keep: public probability-transfer corollary stated by the paper, not an internal proof helper.
/-- Measurable honest coverage transfers its probability lower bound to measurable confidence-
union coverage. [Under the stated hypotheses](hyp:sample_size_fixed,alpha_fixed,honest_covariance_model,h_measurable_good,h_measurable_union,h_coverage) [this conclusion](goal) applies. -/
lemma confidence_union_probability_coverage {Ωsample : Type*} [MeasurableSpace Ωsample]
    (μ : Measure Ωsample) {p m c n : ℕ} {alpha : ℝ}
    (W : BackshiftSystem p m c)
    (V : Ωsample → InferenceWorld p m)
    (sample_size_fixed : ∀ ω, (V ω).sampleSize.1 = n)
    (alpha_fixed : ∀ ω, (V ω).alpha = alpha)
    (backshift_normalization : BackshiftNormalization W)
    (nonnegative_shifts : NonnegativeShifts W)
    (honest_covariance_model : HonestCovarianceModel W)
    (invariant_noise_psd : W.invariantNoise.PosSemidef)
    (h_measurable_good : MeasurableSet {ω | coverageEvent W (V ω).currentRegions})
    (h_measurable_union :
      MeasurableSet {ω | W.structural ∈ confidenceUnion c (V ω)})
    (h_coverage : 1 - ENNReal.ofReal alpha ≤
      μ {ω | coverageEvent W (V ω).currentRegions}) :
    1 - ENNReal.ofReal alpha ≤
      μ {ω | W.structural ∈ confidenceUnion c (V ω)} := by
  calc
    1 - ENNReal.ofReal alpha ≤
        μ {ω | coverageEvent W (V ω).currentRegions} := h_coverage
    _ ≤ μ {ω | W.structural ∈ confidenceUnion c (V ω)} := by
      apply measure_mono
      intro ω hω
      exact confidence_union_coverage W (V ω) backshift_normalization
        nonnegative_shifts honest_covariance_model invariant_noise_psd hω

end CausalSmith.ExactID.RobustBackshiftUniformDistance
