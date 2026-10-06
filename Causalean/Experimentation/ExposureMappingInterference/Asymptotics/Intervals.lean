/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.WaldCoverage
public import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.SteinCLT
public import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Wald-coverage transfer lemmas

Given the local-dependence CLT interface and rowwise positive variances, this module transfers
asymptotic normality into oracle Wald coverage.  It also gives the corresponding feasible transfer
when variance-estimator undershoot probabilities vanish.  These lemmas assume the main analytic
inputs; they do not by themselves formalize Aronow–Samii (2017), Proposition 6.2 or its
Conditions 3, 5, and 6. An alternative finite-grid sufficient-condition result, based on explicit
bounded-degree, factorization, covariance-vanishing, and scaled-variance hypotheses, is
`wald_coverage_feasible_of_bounded_degree_factorization_covariance` in
`VarEstConsistencyConditions.lean`.

The oracle theorem uses only the *lower* half of the CLT: the event `|τ̂ − τ| ≤ z·√Var` contains
`{−z < W ≤ z}` (with `W` the studentized statistic), whose probability is
`Pr[W ≤ z] − Pr[W ≤ −z] → Φ(z) − Φ(−z) = 1 − α` by the interface plus CDF symmetry
`Φ(−z) = 1 − Φ(z)`. (The matching upper bound — exact convergence to `1 − α` — would need
Gaussian-CDF continuity; the paper only claims "at least", so it is not pursued here.)
-/

public section

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

/-- **Oracle Wald-coverage transfer from a CLT.** For
[a sequence of experiments and treatment contrasts](hyp:Exp,dk,dl), suppose
[the studentized statistic satisfies the local-dependence CLT](hyp:hclt) and
[the effect-estimator variance is everywhere positive](hyp:hVar). Then for
[a nonnegative quantile](hyp:α,zq,hzq0) [satisfying `Φ(zq) = 1 − α/2`](hyp:hzq),
[the oracle Wald interval has liminf coverage at least `1 − α`](goal). -/
theorem wald_coverage (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hclt : LocalDependenceCLT Exp dk dl)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))))
      Filter.atTop := by
  -- The studentized lower-CDF probabilities at `zq` and `-zq`.
  set S : ℕ → ℝ := fun n =>
    (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ zq) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ -zq) with hLodef
  set I : ℕ → ℝ := fun n => (Exp n).D.Pr (fun z =>
    |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
        - tauTrue (Exp n).y (dk n) (dl n)|
      ≤ zq * Real.sqrt ((Exp n).D.Var
          (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))) with hIdef
  -- (1) Limit of `S - Lo`.
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf zq)) := hclt.tendsto_cdf zq
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-zq))) := hclt.tendsto_cdf (-zq)
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (1 - α)) := by
    have h := hS.sub hLo
    rw [stdNormalCdf_neg zq, hzq] at h
    have he : (1 - α / 2) - (1 - (1 - α / 2)) = 1 - α := by ring
    rwa [he] at h
  -- (2) Pointwise lower bound `S - Lo ≤ I`.
  have hbound : ∀ n, S n - Lo n ≤ I n := by
    intro n
    -- Abbreviate the studentized statistic.
    set W : (Exp n).Ω → ℝ := fun z => (Exp n).studentizedEffect (dk n) (dl n) z with hWdef
    -- Split `S` by the event `W ≤ -zq`.
    have hsplit := (Exp n).D.Pr_split (fun z => W z ≤ zq) (fun z => W z ≤ -zq)
    -- The first piece equals `Lo`.
    have hfirst : (Exp n).D.Pr (fun z => W z ≤ zq ∧ W z ≤ -zq) = Lo n := by
      apply (Exp n).D.Pr_congr
      intro z
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith [hzq0]), h2⟩
    -- So `S - Lo` is the probability of the second piece.
    have hSLo : S n - Lo n =
        (Exp n).D.Pr (fun z => W z ≤ zq ∧ ¬ W z ≤ -zq) := by
      have : S n = (Exp n).D.Pr (fun z => W z ≤ zq ∧ W z ≤ -zq)
          + (Exp n).D.Pr (fun z => W z ≤ zq ∧ ¬ W z ≤ -zq) := hsplit
      rw [this, hfirst]; ring
    rw [hSLo]
    -- That second piece is contained in `I`'s event.
    apply (Exp n).D.Pr_mono
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [not_le] at hz2
    -- `|W z| ≤ zq`.
    have habs : |W z| ≤ zq := abs_le.mpr ⟨le_of_lt hz2, hz1⟩
    -- Unfold the studentized statistic.
    set s : ℝ := Real.sqrt ((Exp n).D.Var
        (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))) with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr (hVar n)
    rw [hWdef] at habs
    simp only [Experiment.studentizedEffect] at habs
    rw [← hsdef] at habs
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at habs
    exact habs
  -- (3) Conclude with liminf.
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop I :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      (fun n => (Exp n).D.Pr_le_one _)
  calc 1 - α = Filter.liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf I atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hbdd hcobdd

/-- **Feasible Wald-coverage transfer from a CLT and variance control.** For
[a sequence of experiments and treatment contrasts](hyp:Exp,dk,dl), suppose
[the studentized statistic satisfies the local-dependence CLT](hyp:hclt),
[the effect-estimator variance is everywhere positive](hyp:hVar), and
[variance-estimator undershoot probabilities vanish](hyp:hVhat). Then for
[a nonnegative quantile](hyp:α,zq,hzq0) [satisfying `Φ(zq) = 1 − α/2`](hyp:hzq),
[the feasible Wald interval has liminf coverage at least `1 − α`](goal). -/
theorem wald_coverage_feasible (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (hclt : LocalDependenceCLT Exp dk dl)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hVhat : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (Exp n).D.Pr (fun z =>
        htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
          < (1 - ε) * (Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))))
      atTop (𝓝 0))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt
              (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z)))
      Filter.atTop := by
  simpa only [one_mul, div_one, abs_sub_comm] using
    conservative_wald_liminf_of_feasible_studentized_cdf
      (fun n => (Exp n).D)
      (fun n => htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
      (fun n => tauTrue (Exp n).y (dk n) (dl n))
      (fun n => (Exp n).D.Var
        (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
      (fun _ => 1)
      (fun n => htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n))
      (fun _ => one_pos) hVar hVhat α zq
      (fun t => by
        convert hclt.tendsto_cdf t using 1
        funext n
        apply (Exp n).D.Pr_congr
        intro z
        simp only [Real.sqrt_one, one_mul, Experiment.studentizedEffect])
      hzq0 hzq

end ExposureMappingInterference
end Experimentation
end Causalean
