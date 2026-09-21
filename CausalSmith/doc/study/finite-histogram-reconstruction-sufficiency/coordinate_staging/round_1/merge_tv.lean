
namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Given [two probability laws](hyp:mu,nu) and [one common Markov
kernel](hyp:K), applying that channel to both laws [cannot increase their total
variation distance](goal). -/
theorem tvDist_bind_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K] :
    tvDist (K ∘ₘ mu) (K ∘ₘ nu) ≤ tvDist mu nu := by
  let _ : IsProbabilityMeasure (K ∘ₘ mu) := by infer_instance
  let _ : IsProbabilityMeasure (K ∘ₘ nu) := by infer_instance
  unfold tvDist
  apply ciSup_le
  rintro ⟨S, hS⟩
  have hreal (rho : Measure A) [IsProbabilityMeasure rho] :
      (K ∘ₘ rho).real S = ∫ x, (K x S).toReal ∂rho := by
    rw [measureReal_def, Measure.bind_apply hS (Kernel.aemeasurable K), ←
      integral_toReal (K.measurable_coe hS).aemeasurable]
    filter_upwards with x
    exact measure_lt_top (K x) S
  rw [hreal mu, hreal nu]
  have hrange : ∀ x, (K x S).toReal ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle := ENNReal.toReal_mono (measure_ne_top (K x) _)
        (measure_mono (Set.subset_univ S))
      simpa using hle
  simpa only [zero_add, mul_one, tvDist] using
    tvDist_integral_range mu nu
      (fun x => (K x S).toReal) (K.measurable_coe hS).ennreal_toReal
      0 1 (by norm_num) (by simpa using hrange)

end Causalean.Stat
