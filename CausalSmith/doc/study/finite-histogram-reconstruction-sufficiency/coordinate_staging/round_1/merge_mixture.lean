
namespace Causalean.Stat.Minimax.MomentMatchedMixture

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Given [a probability prior](hyp:pi), [an experiment Markov
kernel](hyp:K), and [a common post-processing Markov kernel](hyp:R), mixing the
composed experiment [equals post-processing the prior-predictive mixture](goal). -/
theorem kernel_comp_priorPredictive
    {Theta A B : Type*} [MeasurableSpace Theta]
    [MeasurableSpace A] [MeasurableSpace B]
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (K : Kernel Theta A) [IsMarkovKernel K]
    (R : Kernel A B) [IsMarkovKernel R] :
    priorPredictive pi (R ∘ₖ K) = R ∘ₘ priorPredictive pi K := by
  unfold priorPredictive
  exact Measure.comp_assoc.symm

end Causalean.Stat.Minimax.MomentMatchedMixture
