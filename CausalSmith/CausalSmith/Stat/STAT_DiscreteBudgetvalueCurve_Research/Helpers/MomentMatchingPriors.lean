module
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Duality
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Rate

/-! The local absolute-moment prior composition. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

/-- Source match: `cite:cailow2011`, Lemma 1 (p. 10) and the Bernstein-limit
discussion defining \(\delta_K\) (p. 8). T. Tony Cai and Mark G. Low (2011),
arXiv:1105.3039, DOI 10.1214/10-AOS849. [The stated relationship holds](goal).

Lemma 1 gives symmetric probability measures on `[-1,1]` with equal moments
through each positive even `K` and absolute-moment difference `2 * δ_K`.
The positive Bernstein limit on p. 8 gives a universal positive multiple of
`1 / K` on those even degrees; the finitely many remaining positive even
degrees support a smaller common constant. The statement below records exactly
that consequence. Its proof composes Causalean's moment-prior duality and
quantitative approximation bound, choosing `c = 1 / 50`. -/
-- @node: lem:absolute-moment-matching-priors
lemma absolute_moment_matching_priors :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, Even K → 2 ≤ K →
      ∃ nu0 nu1 : Measure ℝ,
        IsProbabilityMeasure nu0 ∧ IsProbabilityMeasure nu1 ∧
        IsSymmetric nu0 ∧ IsSymmetric nu1 ∧
        IsSupportedOnUnitInterval nu0 ∧ IsSupportedOnUnitInterval nu1 ∧
        (∀ m : ℕ, m ≤ K → ∫ t : ℝ, t ^ m ∂nu0 = ∫ t : ℝ, t ^ m ∂nu1) ∧
        c / K ≤ |(∫ t : ℝ, |t| ∂nu1) - (∫ t : ℝ, |t| ∂nu0)| := by
  let c : ℝ := 1 / 50
  refine ⟨c, by norm_num [c], ?_⟩
  intro K _hK_even hK
  let P := Classical.choice
    (exists_symmetric_momentMatched_absGap (K := K))
  refine ⟨P.ν₀, P.ν₁, P.probability₀, P.probability₁,
    P.symmetric₀, P.symmetric₁, P.supported₀, P.supported₁, P.moments_eq, ?_⟩
  have hK_pos : 0 < K := by omega
  have happrox := bestUniformApproxErrorAbs_lower K hK_pos
  have happrox_nonneg : 0 ≤ bestUniformApproxErrorAbs K := by
    exact le_trans (by positivity) happrox
  rw [P.abs_gap, abs_of_nonneg (mul_nonneg (by norm_num) happrox_nonneg)]
  calc
    c / (K : ℝ) = 2 * ((1 / 100 : ℝ) / (K : ℝ)) := by
      dsimp [c]
      ring
    _ ≤ 2 * bestUniformApproxErrorAbs K := by linarith

end CausalSmith.Stat.DiscreteBudgetvalueCurve
