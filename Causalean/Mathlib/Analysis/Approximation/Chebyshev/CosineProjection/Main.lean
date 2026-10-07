module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Approximation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Orthogonality
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Seminorm

/-!
# Constant-five Hölder approximation by the normalized cosine projection

The real finite-bound and extended-seminorm interfaces establish the constant-five
uniform L² approximation rate for finite normalized cosine projections. The infinite-seminorm
case is retained explicitly, so the public result has exactly the interval continuity,
exponent, and rank assumptions required for nonparametric series approximation.
-/

public section

open scoped ENNReal
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- A [continuous real function on the unit interval](hyp:hf), an
[exponent between zero and one](hyp:hγ,hγ1), a [positive rank](hyp:hk), and
a [nonnegative Hölder constant satisfying its increment bound](hyp:hH,hholder)
give [L² cosine projection error at most five times that constant times k⁻γ](goal).

Combine `exists_cosine_approximant`, `cosineProjection_bestApproximation`,
and `l2Norm_le_of_abs_le` for the continuous approximation residual.
-/
theorem cosineProjection_error_le {f : ℝ → ℝ} {γ H : ℝ} {k : ℕ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hk : 1 ≤ k)
    (hH : 0 ≤ H) (hholder : HasHolderBound f γ H) :
    l2Norm (fun x => f x - cosineProjection k f x) ≤ 5 * H * (k : ℝ) ^ (-γ) := by
  obtain ⟨p, hp, hspan, herr⟩ := exists_cosine_approximant hk hf hγ hγ1 hH hholder
  apply (cosineProjection_bestApproximation hf hspan).trans
  exact l2Norm_le_of_abs_le (hf.sub hp) (by positivity) herr

/-- A [continuous real function on the unit interval](hyp:hf), an
[exponent between zero and one](hyp:hγ,hγ1), and a [positive rank](hyp:hk)
give [extended L² projection error at most five times the extended Hölder
seminorm times k⁻γ](goal), including infinite seminorm.

Split whether `holderSeminorm f γ = ⊤`. The infinite branch uses the explicit
trivial corollary. The finite branch uses its toReal increment bound, the real
headline, and the continuous residual's extended norm bridge. This theorem
does not assume finiteness of the seminorm.
-/
theorem cosineProjection_error_le_seminorm {f : ℝ → ℝ} {γ : ℝ} {k : ℕ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hk : 1 ≤ k) :
    extendedL2Norm (fun x => f x - cosineProjection k f x) ≤
      5 * holderSeminorm f γ * ENNReal.ofReal ((k : ℝ) ^ (-γ)) := by
  by_cases htop : holderSeminorm f γ = ⊤
  · exact extended_bound_of_seminorm_top hk htop
  · have hres : ContinuousOn (fun x => f x - cosineProjection k f x)
        (Set.Icc (0 : ℝ) 1) :=
      hf.sub (continuous_cosinePolynomial k (cosineCoefficient f)).continuousOn
    rw [extendedL2Norm_eq_ofReal hres]
    have hreal := cosineProjection_error_le hf hγ hγ1 hk
      (ENNReal.toReal_nonneg : 0 ≤ (holderSeminorm f γ).toReal)
      (hasHolderBound_seminorm hγ htop)
    calc
      _ ≤ ENNReal.ofReal (5 * (holderSeminorm f γ).toReal * (k : ℝ) ^ (-γ)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_toReal htop]
        norm_num

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

