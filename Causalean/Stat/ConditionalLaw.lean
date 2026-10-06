module
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Chosen conditional laws for real doses

This module packages an explicitly supplied Markov kernel that disintegrates a
full observation law given a real-valued dose. It supplies pointwise conditional
moments from that one chosen kernel, without asserting that such a kernel exists.
-/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Causalean.Stat.ConditionalLaw

variable {Obs : Type*} [MeasurableSpace Obs] {P : Measure Obs}
  [IsProbabilityMeasure P] {A : Obs → ℝ}

/-- A [measurable observation space](hyp:Obs), [probability law](hyp:P), and
[measurable real-valued dose map](hyp:A) determine a chosen continuous-dose
conditional law. Its [measurable dose map](hyp:measurable_dose), [conditional
kernel](hyp:K), [Markov property](hyp:markov), and [coherence identity](hyp:coherence)
record the supplied disintegration of the joint dose--observation law. -/
structure ContinuousDoseConditionalLaw (Obs : Type*) [MeasurableSpace Obs]
    (P : Measure Obs) [IsProbabilityMeasure P] (A : Obs → ℝ) where
  measurable_dose : Measurable A
  K : Kernel ℝ Obs
  markov : IsMarkovKernel K
  coherence : (letI : IsMarkovKernel K := markov
    (P.map A) ⊗ₘ K = P.map (fun ω ↦ (A ω, ω)))

namespace ContinuousDoseConditionalLaw

/-- The [chosen conditional law](hyp:L) assigns [a probability distribution to
the specified dose](hyp:a), so [its kernel fiber has total mass one](goal). -/
theorem kernel_probability (L : ContinuousDoseConditionalLaw Obs P A) (a : ℝ) :
    IsProbabilityMeasure (L.K a) := by
  haveI : IsMarkovKernel L.K := L.markov
  infer_instance

/-- The [chosen conditional law](hyp:L) makes [the marginal distribution of
the dose a probability measure](goal). -/
theorem dose_probability (L : ContinuousDoseConditionalLaw Obs P A) :
    IsProbabilityMeasure (P.map A) := by
  exact Measure.isProbabilityMeasure_map L.measurable_dose.aemeasurable

/-- A [chosen conditional law](hyp:L), [joint real-valued quantity](hyp:f),
and [integrability under the joint dose--observation law](hyp:hf) imply [that
joint integration equals first averaging within each dose and then averaging
over the dose distribution](goal). -/
theorem integral_graph (L : ContinuousDoseConditionalLaw Obs P A)
    (f : ℝ × Obs → ℝ)
    (hf : Integrable f (P.map (fun ω ↦ (A ω, ω)))) :
    ∫ z, f z ∂(P.map (fun ω ↦ (A ω, ω))) =
      ∫ a, ∫ ω, f (a, ω) ∂L.K a ∂(P.map A) := by
  haveI : IsMarkovKernel L.K := L.markov
  rw [← L.coherence]
  exact Measure.integral_compProd (L.coherence ▸ hf)

/-- The [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) determine [the pointwise conditional mean](goal),
given by integration against the selected kernel fiber. -/
noncomputable def mean (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) : ℝ := ∫ ω, f ω ∂L.K a

/-- The [chosen conditional law](hyp:L), [real observation](hyp:f),
[dose-indexed prediction](hyp:g), and [specified dose](hyp:a) determine [the
pointwise squared prediction risk](goal), given by the kernel-fiber average of
squared prediction error. -/
noncomputable def squaredRisk (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ ω, (f ω - g a) ^ 2 ∂L.K a

/-- The [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) determine [the conditional second moment](goal), given
by the kernel-fiber average of the squared observation. -/
noncomputable def secondMoment (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) : ℝ := ∫ ω, (f ω) ^ 2 ∂L.K a

/-- The [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) determine [the conditional variance](goal), given by
the squared risk of the conditional mean under the same kernel fiber. -/
noncomputable def variance (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) : ℝ :=
  L.squaredRisk f (L.mean f) a

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) satisfy [the defining integral formula for its
conditional mean](goal). -/
theorem mean_eq_integral (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) : L.mean f a = ∫ ω, f ω ∂L.K a := rfl

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f),
[dose-indexed prediction](hyp:g), and [specified dose](hyp:a) satisfy [the
defining integral formula for their squared prediction risk](goal). -/
theorem squaredRisk_eq_integral (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (g : ℝ → ℝ) (a : ℝ) :
    L.squaredRisk f g a = ∫ ω, (f ω - g a) ^ 2 ∂L.K a := rfl

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) satisfy [the defining integral formula for their
conditional second moment](goal). -/
theorem secondMoment_eq_integral (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) :
    L.secondMoment f a = ∫ ω, (f ω) ^ 2 ∂L.K a := rfl

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) satisfy [the defining integral formula for their
conditional variance](goal). -/
theorem variance_eq_integral (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) :
    L.variance f a = ∫ ω, (f ω - L.mean f a) ^ 2 ∂L.K a := rfl

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f),
[dose-indexed prediction](hyp:g), and [specified dose](hyp:a) have [a
nonnegative squared prediction risk](goal). -/
theorem squaredRisk_nonneg (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (g : ℝ → ℝ) (a : ℝ) :
    0 ≤ L.squaredRisk f g a := by
  simp only [squaredRisk]
  exact integral_nonneg fun ω ↦ sq_nonneg _

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) have [a nonnegative conditional second moment](goal). -/
theorem secondMoment_nonneg (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) :
    0 ≤ L.secondMoment f a := by
  simp only [secondMoment]
  exact integral_nonneg fun ω ↦ sq_nonneg _

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f), and
[specified dose](hyp:a) have [a nonnegative conditional variance](goal). -/
theorem variance_nonneg (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ) :
    0 ≤ L.variance f a := L.squaredRisk_nonneg f (L.mean f) a

/-- A [chosen conditional law](hyp:L) and [measurable real observation](hyp:hf)
give [a measurable pointwise conditional mean](goal). -/
theorem measurable_mean (L : ContinuousDoseConditionalLaw Obs P A)
    {f : Obs → ℝ} (hf : Measurable f) : Measurable (L.mean f) := by
  haveI : IsMarkovKernel L.K := L.markov
  exact hf.stronglyMeasurable.integral_kernel.measurable

/-- A [chosen conditional law](hyp:L), [measurable real observation](hyp:hf),
and [measurable dose-indexed prediction](hyp:hg) give [a measurable pointwise
squared prediction risk](goal). -/
theorem measurable_squaredRisk (L : ContinuousDoseConditionalLaw Obs P A)
    {f : Obs → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (L.squaredRisk f g) := by
  haveI : IsMarkovKernel L.K := L.markov
  have h : Measurable (fun p : ℝ × Obs ↦ (f p.2 - g p.1) ^ 2) :=
    ((hf.comp measurable_snd).sub (hg.comp measurable_fst)).pow_const 2
  exact (h.stronglyMeasurable.integral_kernel_prod_right').measurable

/-- A [chosen conditional law](hyp:L) and [measurable real observation](hyp:hf)
give [a measurable conditional second moment](goal). -/
theorem measurable_secondMoment (L : ContinuousDoseConditionalLaw Obs P A)
    {f : Obs → ℝ} (hf : Measurable f) :
    Measurable (L.secondMoment f) := by
  haveI : IsMarkovKernel L.K := L.markov
  exact (hf.pow_const 2).stronglyMeasurable.integral_kernel.measurable

/-- A [chosen conditional law](hyp:L) and [measurable real observation](hyp:hf)
give [a measurable conditional variance](goal). -/
theorem measurable_variance (L : ContinuousDoseConditionalLaw Obs P A)
    {f : Obs → ℝ} (hf : Measurable f) : Measurable (L.variance f) := by
  exact L.measurable_squaredRisk hf (L.measurable_mean hf)

/-- A [chosen conditional law](hyp:L), [real observation](hyp:f), [specified
dose](hyp:a), [integrable observation on its kernel fiber](hyp:hf), and
[integrable squared observation on that fiber](hyp:hf2) imply [that conditional
variance equals the conditional second moment minus the squared conditional
mean](goal). -/
theorem variance_eq_secondMoment_sub_sq_mean
    (L : ContinuousDoseConditionalLaw Obs P A)
    (f : Obs → ℝ) (a : ℝ)
    (hf : Integrable f (L.K a))
    (hf2 : Integrable (fun ω ↦ (f ω) ^ 2) (L.K a)) :
    L.variance f a = L.secondMoment f a - (L.mean f a) ^ 2 := by
  haveI : IsMarkovKernel L.K := L.markov
  letI : IsProbabilityMeasure (L.K a) := L.kernel_probability a
  have hlinear : Integrable (fun ω ↦ 2 * L.mean f a * f ω) (L.K a) :=
    hf.const_mul _
  calc
    L.variance f a =
        ∫ ω, ((f ω) ^ 2 - 2 * L.mean f a * f ω + (L.mean f a) ^ 2) ∂L.K a := by
      rw [L.variance_eq_integral]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    _ = (∫ ω, (f ω) ^ 2 - 2 * L.mean f a * f ω ∂L.K a) +
        (∫ _ω, (L.mean f a) ^ 2 ∂L.K a) := by
      simpa only [Pi.sub_apply, Pi.add_apply] using
        (integral_add (hf2.sub hlinear) (integrable_const (L.mean f a ^ 2)))
    _ = L.secondMoment f a - (L.mean f a) ^ 2 := by
      rw [integral_sub hf2 hlinear, integral_const, probReal_univ, one_smul,
        integral_const_mul]
      simp only [L.secondMoment_eq_integral, L.mean_eq_integral]
      ring

end ContinuousDoseConditionalLaw
end Causalean.Stat.ConditionalLaw
