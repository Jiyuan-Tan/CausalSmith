/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.GaussMarkov.LeastNorm
public import Causalean.Stat.LinearModel.GaussMarkov.Variance

/-! # Variance Orderings for Linear Combinations

This file combines the covariance-matrix bridge with algebraic quadratic-form
orderings to compare variances of finite random linear combinations. The
weights satisfy common design-balance identities, but the statements do not
assume a linear mean model and therefore do not by themselves prove estimator
unbiasedness. -/

public section

namespace Causalean.Stat.GaussMarkov

open MeasureTheory ProbabilityTheory Matrix

variable {Ω Obs : Type*} [Fintype Obs]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

set_option linter.unusedFintypeInType false in
/-- A covariance matrix of an `L²` random family is positive semidefinite: it is
symmetric (`cov` is symmetric) and its quadratic form is a genuine variance, hence
nonnegative.  (`Fintype Obs` appears only under the `PosSemidef` definition, which
the `unusedFintypeInType` linter cannot see; it is genuinely required.) -/
lemma covMatrix_posSemidef [IsProbabilityMeasure μ]
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    (covMatrix Y μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    change star (covMatrix Y μ j i) = covMatrix Y μ i j
    rw [star_trivial]
    exact covariance_comm (Y j) (Y i)
  · intro w
    have hsw : star w ⬝ᵥ (covMatrix Y μ) *ᵥ w = quadVar (covMatrix Y μ) w := by
      simp [quadVar, star_trivial]
    rw [hsw, ← variance_linearCombination Y hY]
    exact variance_nonneg _ _

variable {Param : Type*} [Fintype Param]

/-- **Variance ordering under a spherical random family.** For a finite family
of random variables `Y i`, each [square-integrable](hyp:hY), suppose [the family
is spherical: distinct cells are uncorrelated and every cell has the same
variance `σ²`](hyp:hsph). Among all linear combinations `∑ i, w i * Y i`
whose weights satisfy [the same design-balance identity
`w ᵥ* X = c`](hyp:hUStar,hU), if [`wStar` lies in the column span of `X`,
`wStar = X *ᵥ g`](hyp:hStar), then [the linear combination built from `wStar`
has variance no larger than the one built from `w`](goal). -/
theorem linearCombination_variance_spherical_le_of_colSpan [IsProbabilityMeasure μ]
    {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) {σ : ℝ}
    (hsph : SphericalFamily Y μ σ)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hStar : wStar = X *ᵥ g) (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    Var[fun ω => ∑ i, wStar i * Y i ω; μ] ≤ Var[fun ω => ∑ i, w i * Y i ω; μ] := by
  classical
  rw [variance_linearCombination Y hY, variance_linearCombination Y hY]
  have hsph' : SphericalErrors (covMatrix Y μ) σ :=
    sphericalFamily_covMatrix (fun i => (hY i).aestronglyMeasurable.aemeasurable) hsph
  exact quadVar_spherical_le_of_colSpan hsph' hStar hUStar hU

/-- **Variance ordering under a known covariance matrix.** For a finite family
of random variables `Y i`, each [square-integrable](hyp:hY), consider linear
combinations `∑ i, w i * Y i` whose weights satisfy [the same design-balance
identity `w ᵥ* X = c`](hyp:hUStar,hU). If [the family's covariance matrix
applied to `wStar` lies in the column span of `X`](hyp:hGLS), then [the linear
combination built from `wStar` has variance no larger than the one built from
`w`](goal). -/
theorem linearCombination_variance_le_of_covMul_mem_colSpan [IsProbabilityMeasure μ]
    {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hGLS : (covMatrix Y μ) *ᵥ wStar = X *ᵥ g)
    (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    Var[fun ω => ∑ i, wStar i * Y i ω; μ] ≤ Var[fun ω => ∑ i, w i * Y i ω; μ] := by
  rw [variance_linearCombination Y hY, variance_linearCombination Y hY]
  exact quadVar_le_of_mulVec_mem_colSpan (covMatrix_posSemidef Y hY) hGLS hUStar hU

end Causalean.Stat.GaussMarkov
