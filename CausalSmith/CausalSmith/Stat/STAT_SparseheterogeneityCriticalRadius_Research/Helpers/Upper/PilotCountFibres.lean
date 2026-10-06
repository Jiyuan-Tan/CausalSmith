module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.PilotPostSplit

/-! Count-fibre form of the retained-pilot prefix product law. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

lemma smul_map_pilotTau_fixedPrefixSamples_eq_countFibres {n u v : ℕ}
    (M : ℝ) (P : Law n) (lam : ℝ≥0) (h : u + v ≤ postPilotSize n)
    (hlam : lam = Real.toNNReal (blockMean n)) :
    ((poissonMeasure lam {u}) * (poissonMeasure lam {v})) •
        Measure.map (fun sample =>
          (pilotTau n M sample, fixedPrefixSamples n u v h sample))
          (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.map (pilotTau n M)
        (DiscreteAteHeterogeneityFrontier.productLaw n P)).prod
        (((finitePoissonSampleLaw P.observedLaw lam).restrict
          (FiniteSample.count ⁻¹' ({u} : Set ℕ))).prod
         ((finitePoissonSampleLaw P.observedLaw lam).restrict
          (FiniteSample.count ⁻¹' ({v} : Set ℕ)))) := by
  subst lam
  rw [map_pilotTau_fixedPrefixSamples_productLaw M P h,
    finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [mul_comm]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
