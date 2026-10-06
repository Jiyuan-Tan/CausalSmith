/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The design-based Wald-interval pipeline, in one theorem

`DependencyCLT` supplies the studentized CLT and `WaldCoverage` turns a studentized CLT plus a
conservative variance into interval coverage.  This file composes them: from primitive
dependency-graph inputs — bounded, mean-zero, bounded-degree unit contributions whose standardized
sum is asymptotically equivalent to the centered, scaled estimator, together with a feasible
random variance estimator — the
two-sided Wald interval has asymptotic coverage at least `1 − α`.  A design-based interference paper
instantiates this single theorem instead of separately building a CLT, a Slutsky/coverage argument,
and their composition.
-/

module
public import Causalean.Experimentation.DesignBased.DependencyCLT
public import Causalean.Experimentation.DesignBased.Slutsky
public import Causalean.Experimentation.DesignBased.WaldCoverage

/-! # Design-based Wald-interval pipeline

`dependency_wald_coverage` chains the design-based dependency CLT (`dependency_studentized_cdf`)
into the feasible Wald-coverage transfer. Given unit contributions `X n` whose standardized sum
`depSum(X n)` is asymptotically equivalent to the scaled centered estimator
`√(m n)·(est n − θ n)`, and a random variance estimator `vhat n` whose probability of materially
undershooting `v n` vanishes, the Wald interval
`|θ n − est n| ≤ z·√(vhat n / m n)` has liminf coverage at least `1 − α`.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open Causalean.Mathlib.Probability.SteinMethod
open scoped Topology BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- **Design-based Wald-interval coverage from dependency-graph primitives.** Consider [a sequence
of finite designs](hyp:D) together with [per-unit contributions `X n i`](hyp:X) governed by [a
dependency graph `Dep n` on those contributions](hyp:Dep) whose [neighbourhoods have cardinality at
most `Dmax`](hyp:hdeg), where [the contributions are uniformly bounded by a nonnegative constant
`M`](hyp:hM,hbound) and [have design mean zero](hyp:hmean). Suppose [the standardizing quantity
`v n` equals the design second moment of the contributions' sum `depSum(X n)`](hyp:hv), [is
bounded below by a positive constant `c` times the number of units eventually](hyp:hc,hvc), and
[the number of units diverges](hyp:hcard). Suppose further that [the standardized sum is
asymptotically equivalent in probability to `√(m n)·(est n − θ n)` for an estimator `est n` of a
target `θ n`](hyp:est,hlinkApprox), [the normalization and oracle variance are positive](hyp:hmpos,hvpos),
and [a random feasible variance estimator has vanishing probability of material
underestimation](hyp:vhat,hVhat), with [`z` the nonnegative](hyp:hz0) quantile
[satisfying `Φ(z) = 1 − α/2`](hyp:hz). Then [the two-sided Wald interval
`|θ n − est n| ≤ z·√(v̂ n / m n)` has asymptotic (liminf) coverage at least `1 − α`](goal).

This is the complete design-based inference pipeline: it obtains the studentized CLT from the
dependency-graph engine, transfers it through the in-probability link by converging together, and
feeds it with the feasible variance into the Wald-coverage transfer. -/
theorem dependency_wald_coverage
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, MeasurableSpace (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (D : ∀ n, FiniteDesign (Ω n))
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (Dep : ∀ n, DepGraph (X n) (D n).toMeasure)
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ n i ω, |X n i ω| ≤ M)
    (hmean : ∀ n i, (D n).E (X n i) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, (D n).E (fun ω => depSum (X n) ω ^ 2) = v n)
    (c : ℝ) (hc : 0 < c)
    (hvc : ∀ᶠ n in atTop, c * (Fintype.card (ι n) : ℝ) ≤ v n)
    (hcard : Tendsto (fun n => Fintype.card (ι n)) atTop atTop)
    (est : ∀ n, Ω n → ℝ) (θ m : ℕ → ℝ)
    (hlinkApprox : ∀ η : ℝ, 0 < η → Tendsto (fun n => (D n).Pr (fun ω =>
      η ≤ |Real.sqrt (m n) * (est n ω - θ n) / Real.sqrt (v n) -
        depSum (X n) ω / Real.sqrt (v n)|)) atTop (𝓝 0))
    (hmpos : ∀ n, 0 < m n) (hvpos : ∀ n, 0 < v n)
    (vhat : ∀ n, Ω n → ℝ)
    (hVhat : ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      (D n).Pr (fun ω => vhat n ω < (1 - η) * v n)) atTop (𝓝 0))
    (α z : ℝ) (hz0 : 0 ≤ z) (hz : stdNormalCdf z = 1 - α / 2) :
    1 - α ≤ liminf (fun n =>
        (D n).Pr (fun ω => |θ n - est n ω| ≤ z * Real.sqrt (vhat n ω / m n))) atTop := by
  classical
  have horacle : ∀ s : ℝ, Tendsto (fun n =>
      (D n).Pr (fun ω =>
        depSum (X n) ω / Real.sqrt (v n) ≤ s))
      atTop (𝓝 (stdNormalCdf s)) := by
    intro s
    exact dependency_studentized_cdf D X Dep Dmax hdeg M hM hbound hmean v hv c hc hvc hcard s
  have hclt : ∀ s : ℝ, Tendsto (fun n =>
      (D n).Pr (fun ω =>
        Real.sqrt (m n) * (est n ω - θ n) / Real.sqrt (v n) ≤ s))
      atTop (𝓝 (stdNormalCdf s)) :=
    finiteDesign_cdf_converging_together D
      (fun n ω => Real.sqrt (m n) * (est n ω - θ n) / Real.sqrt (v n))
      (fun n ω => depSum (X n) ω / Real.sqrt (v n)) stdNormalCdf
      hlinkApprox horacle continuous_stdNormalCdf
  exact conservative_wald_liminf_of_feasible_studentized_cdf D est θ v m vhat
    hmpos hvpos hVhat α z hclt hz0 hz

end DesignBased
end Experimentation
end Causalean
