module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Definitions
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Fold
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Moments

/-!
# Continuity and uniform error of the even Jackson convolution

Define the Jackson approximant and isolate its analytic error estimate from finite
cosine expansion. This module depends only on the closed fold and moment layers;
its proofs need no projection, orthogonality, or convolution-window expansion.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open Causalean.Mathlib.Analysis.JacksonApproximation
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- [The Jackson cosine approximant](goal) of a [target](hyp:f), at
[order](hyp:K) and [position](hyp:x), convolves its even angular extension
with the unit-mass order-four Jackson kernel. -/
def jacksonApproximant (K : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Icc (-Real.pi) Real.pi, evenExtension f (Real.pi * x - t) * jackson K t

/-- A [target continuous on the closed interval](hyp:hf) has
[continuous Jackson approximant](goal) at every order. -/
@[fun_prop]
theorem continuous_jacksonApproximant {K : ℕ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    Continuous (jacksonApproximant K f) := by
  unfold jacksonApproximant
  apply continuous_parametric_integral_of_continuous (s := Set.Icc (-Real.pi) Real.pi)
    (hs := isCompact_Icc)
  have hext := continuous_evenExtension hf
  have hkernel := continuous_jackson K
  fun_prop

/-- For an [exponent between zero and one](hyp:hγ,hγ1), a [nonnegative
Hölder bound](hyp:hH,hholder), a [continuous target](hyp:hf), and a
[positive order](hyp:hK), [the Jackson uniform error is bounded by the
Hölder constant times (2/K)^γ](goal), at every [unit-interval point](hyp:hx).

Subtract the target using unit mass, apply the integral absolute-value bound,
then `evenExtension_holder` and `jackson_holder_moment`. All integrands are
continuous on a compact interval, so integral inequalities have their required
integrability hypotheses.
-/
theorem jacksonApproximant_error {K : ℕ} {f : ℝ → ℝ} {γ H x : ℝ}
    (hK : 0 < K) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H) (hholder : HasHolderBound f γ H)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |f x - jacksonApproximant K f x| ≤ H * (2 / (K : ℝ)) ^ γ := by
  have hext := continuous_evenExtension hf
  have hkernel := continuous_jackson K
  have hconv : Continuous (fun t => evenExtension f (Real.pi * x - t) *
      jackson K t) := by fun_prop
  have hinc : Continuous (fun t => (f x - evenExtension f (Real.pi * x - t)) *
      jackson K t) := by fun_prop
  have hpow : Continuous (fun t : ℝ => (|t| / Real.pi) ^ γ) :=
    (continuous_abs.div_const Real.pi).rpow_const (fun _ => Or.inr hγ.le)
  have hbound : Continuous (fun t => H * ((|t| / Real.pi) ^ γ * jackson K t)) :=
    continuous_const.mul (hpow.mul hkernel)
  have herr : f x - jacksonApproximant K f x =
      ∫ t in Set.Icc (-Real.pi) Real.pi,
        (f x - evenExtension f (Real.pi * x - t)) * jackson K t := by
    simp_rw [sub_mul]
    rw [integral_sub ((integrableOn_jackson K).const_mul (f x))
      (hconv.continuousOn.integrableOn_compact isCompact_Icc),
      integral_const_mul, jackson_integral_eq_one K hK, mul_one]
    rfl
  rw [herr]
  calc
    _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
        |(f x - evenExtension f (Real.pi * x - t)) * jackson K t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
        H * ((|t| / Real.pi) ^ γ * jackson K t) := by
      apply setIntegral_mono_on
        (hinc.abs.continuousOn.integrableOn_compact isCompact_Icc)
        (hbound.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
      intro t ht
      have hh := evenExtension_holder hγ hH hholder (Real.pi * x) (Real.pi * x - t)
      rw [evenExtension_pi_mul f hx, sub_sub_cancel] at hh
      rw [abs_mul, abs_of_nonneg (jackson_nonneg K hK t)]
      exact (mul_le_mul_of_nonneg_right hh (jackson_nonneg K hK t)).trans_eq
        (mul_assoc _ _ _)
    _ = H * ∫ t in Set.Icc (-Real.pi) Real.pi,
        (|t| / Real.pi) ^ γ * jackson K t := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (jackson_holder_moment hK hγ hγ1) hH


end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

