module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.StreamBridge

/-! Transfer of ideal risk between a marked Poisson sample and independent streams. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

attribute [local instance] markedObsLaw_isProbabilityMeasure
attribute [local instance] map_obs_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,θ,P), [the stated mathematical conclusion holds](goal). -/
lemma integral_sq_poissonAuxiliaryMixedValue_eq_streams
    (n d : ℕ) (q θ : ℝ) (P : FullLaw d) :
    (∫ s, (poissonAuxiliaryMixedValue n d q s - θ) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      ∫ s, (streamAuxiliaryMixedValue n d q s - θ) ^ 2
        ∂Measure.pi (fun _ : Fin 3 ↦
          finitePoissonSampleLaw (P.1.map obs)
            (((n : ℝ≥0) / 2) * (1 / 3))) := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (P.1.map obs) := map_obs_isProbabilityMeasure P
  rw [← map_unshuffle_markedObsLaw P ((n : ℝ≥0) / 2)]
  let f : (Fin 3 → FiniteSample (ObsRecord d)) → ℝ := fun s ↦
    (streamAuxiliaryMixedValue n d q s - θ) ^ 2
  have hf : Measurable f :=
    ((measurable_streamAuxiliaryMixedValue n d q).sub measurable_const).pow_const 2
  change _ = ∫ s, f s ∂Measure.map unshuffle
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))
  rw [integral_map measurable_unshuffle.aemeasurable hf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with s
  dsimp [f]
  rw [streamAuxiliaryMixedValue_unshuffle]

end CausalSmith.Stat.MarRareqLogfrontier
