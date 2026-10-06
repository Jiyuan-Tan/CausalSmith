/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bilinear remainder bound for `GeneralMoment`

* `BilinearRemainder M C` — `|∫ m(η, ·, θ₀) dP_Z| ≤ C · ρ₁(η, η₀) · ρ₂(η, η₀)`
  for every `η ∈ M.H_ε`.
* `bilinear_remainder_of_smoothness` — a sufficient condition for
  `BilinearRemainder` from Neyman orthogonality plus a uniform second-order
  envelope on the linearization residual.

-/

module
public import Causalean.Estimation.OrthogonalMoments.NeymanOrthogonal
public import Causalean.Stat.Limit.StochasticOrderEnvelope

/-! # Bilinear Remainder Bounds

This file formalizes the product-rate remainder condition for abstract
orthogonal moments. It also gives a smoothness bridge showing that Neyman
orthogonality plus a uniform second-order envelope implies such a bilinear
population bias bound. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- For [a general moment system](hyp:M) and [a real constant](hyp:C), the
[bilinear-remainder condition](goal) requires that, for every nuisance value in
the system's admissible perturbation set, the absolute population moment at the
true scalar target is at most $C$ times the product of its two seminorm
distances from the true nuisance. -/
def BilinearRemainder (M : GeneralMoment Ω μ Z P_Z H) (C : ℝ) : Prop :=
  ∀ η ∈ M.H_ε,
    |∫ z, M.m η z M.θ₀ ∂P_Z|
      ≤ C * ((M.ρ₁ η M.η₀ : ℝ)) * ((M.ρ₂ η M.η₀ : ℝ))

/-- **Integrated smoothness bridge to a bilinear remainder bound.** For [a general moment
system](hyp:M), [a directional derivative](hyp:D), and [Neyman orthogonality](hyp:hNO), suppose
the [linearization residual has an integrated L² bound with constant `K`](hyp:K,hSecond), the
[directional derivative is integrable](hyp:hdM_int), the [baseline moment is integrable](hyp:hM0_int),
every [perturbed moment is integrable](hyp:hMη_int), and the [true moment has mean zero](hyp:hMZ).
Then [the population moment obeys a bilinear remainder bound](goal). This integrated hypothesis,
unlike a pointwise envelope, is directly usable for AIPW and other square-integrable scores. -/
theorem bilinear_remainder_of_smoothness
    [IsProbabilityMeasure P_Z]
    (M : GeneralMoment Ω μ Z P_Z H) (D : HasDirDeriv M)
    (hNO : NeymanOrthogonal M D)
    {K : ℝ}
    (hSecond : ∀ η ∈ M.H_ε,
      let rem := fun z => M.m η z M.θ₀ - M.m M.η₀ z M.θ₀ - D.dM η z
      MemLp rem 2 P_Z ∧
        (eLpNorm rem 2 P_Z).toReal ≤
          K * ((M.ρ₁ η M.η₀ : ℝ)) * ((M.ρ₂ η M.η₀ : ℝ)))
    (hdM_int : ∀ η ∈ M.H_ε, Integrable (fun z => D.dM η z) P_Z)
    (hM0_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z)
    (hMη_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => M.m η z M.θ₀) P_Z)
    (hMZ : MeanZero M) :
    ∃ C, BilinearRemainder M C := by
  refine ⟨K, ?_⟩
  intro η hη
  let r₁ : ℝ := M.ρ₁ η M.η₀
  let r₂ : ℝ := M.ρ₂ η M.η₀
  let rem : Z → ℝ := fun z =>
    M.m η z M.θ₀ - M.m M.η₀ z M.θ₀ - D.dM η z
  have hrem_L2 : MemLp rem 2 P_Z := (hSecond η hη).1
  have hrem_integral :
      ∫ z, rem z ∂P_Z = ∫ z, M.m η z M.θ₀ ∂P_Z := by
    have hdiff_int :
        Integrable (fun z => M.m η z M.θ₀ - M.m M.η₀ z M.θ₀) P_Z := by
      exact (hMη_int η hη).sub hM0_int
    dsimp [rem]
    change
      ∫ z,
          ((fun z : Z => M.m η z M.θ₀ - M.m M.η₀ z M.θ₀) z -
              (fun z : Z => D.dM η z) z) ∂P_Z =
        ∫ z, M.m η z M.θ₀ ∂P_Z
    rw [integral_sub hdiff_int (hdM_int η hη)]
    rw [integral_sub (hMη_int η hη) hM0_int]
    rw [hMZ, hNO η hη]
    ring
  calc
    |∫ z, M.m η z M.θ₀ ∂P_Z|
        = |∫ z, rem z ∂P_Z| := by rw [hrem_integral]
    _ ≤ (eLpNorm rem 2 P_Z).toReal :=
      Causalean.Stat.abs_integral_le_eLpNorm_two hrem_L2
    _ ≤ K * r₁ * r₂ := by simpa [rem, r₁, r₂] using (hSecond η hη).2

end OrthogonalMoments
end Estimation
end Causalean
