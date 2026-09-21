/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteDesign.DesignCore
public import Causalean.Experimentation.UnknownInterference.Bernoulli
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Bipartite minimax design (heterogeneous Bernoulli Hájek): shared core

Stage-2 scaffold for `exp_bipartite_minimax_design` (v1).

This file carries the shared environment S-blocks — the reused finite-population
Bernoulli design world S1 (`FiniteDesign` / `bernoulliDesign`) and the local
bipartite-interference potential-outcome world S2 (`BipartiteExperiment`) — together
with the assumption-atom `def`s (`ass:*`), the feasible-design class
(`def:feasible-designs`), and the estimator / linearization / variance-scale
construction `def`s. Each emitted top-level declaration carries its own `@node` tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Experimentation.DesignBased.DesignCore` (`FiniteDesign`/E/Var/Cov) | reuse (S1) | the finite-sum randomization algebra for `E`/`Var`/`Cov` used by `varScale`. |
| `Causalean.Experimentation.UnknownInterference.Bernoulli` (`bernoulliDesign`) | reuse (S1) | the independent heterogeneous Bernoulli product design realizing `ass:independent-heterogeneous-bernoulli`. |
| `Causalean.Experimentation.UnknownInterference` (one-mode interference) | bypass-justified | all interference substrate is one-mode; the bipartite graph layer (`I`,`O`,`N`,`M`,shared sets) has no analogue and is new local scaffolding sitting inside the S1 world. |
-/

@[expose] public section

set_option linter.style.longLine false

open scoped BigOperators
open Finset Filter
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

/-! ## Environment S2 — the bipartite interference / potential-outcome world

`BipartiteExperiment I O` bundles the known bipartite graph `G_n` (as the
intervention neighborhoods `N i = N_i(G_n)`) and the fixed potential-outcome
schedule `Yfun i` (as a function of the treatment vector, later restricted to
`N i` by `ass:bipartite-interference`). The intervention index type `I` realizes
`I_n` (and `m_n = card I`) and the outcome index type `O` realizes `O_n`
(and `n = card O`). -/

-- @env: S2
/-- A bipartite experiment: the known bipartite graph (via outcome-side
neighborhoods) plus the fixed potential-outcome schedule. -/
structure BipartiteExperiment (I O : Type*) [Fintype I] [Fintype O] [DecidableEq I] where
  /-- Intervention neighborhood of each outcome unit. -/
  N : O → Finset I                 -- @realizes N_i(G_n)(N i = intervention neighborhood {k : (k,i) ∈ G_n})
  /-- Fixed potential-outcome schedule as a function of the treatment vector. -/
  Yfun : O → (I → Bool) → ℝ        -- @realizes Y_i(z_{N_i})(carrier; range ℝ); @realizes Z(assignment-vector argument I→Bool = {0,1}^{m_n}); @realizes Z_k(per-unit coordinate z k : Bool = {0,1})

namespace BipartiteExperiment

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] (E : BipartiteExperiment I O)

/-- All-treated potential outcome `Y_i^1 = Y_i(1_{N_i})`. -/
noncomputable def Y1 (i : O) : ℝ := E.Yfun i (fun _ => true)   -- @realizes Y_i^1(Yfun at all-treated)

/-- All-control potential outcome `Y_i^0 = Y_i(0_{N_i})`. -/
noncomputable def Y0 (i : O) : ℝ := E.Yfun i (fun _ => false)  -- @realizes Y_i^0(Yfun at all-control)

/-- Finite-population all-treated mean `μ_1 = n^{-1} ∑_i Y_i^1`. -/
noncomputable def mu1 : ℝ := (Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y1 i   -- @realizes mu_1(mean of Y_i^1)

/-- Finite-population all-control mean `μ_0 = n^{-1} ∑_i Y_i^0`. -/
noncomputable def mu0 : ℝ := (Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y0 i   -- @realizes mu_0(mean of Y_i^0)

/-- Target finite-population effect `τ_n = μ_1 − μ_0`. -/
noncomputable def tau : ℝ := E.mu1 - E.mu0   -- @realizes tau_n(mu_1 - mu_0)

/-- Potential-outcome schedule `Y = ((Y_i^1, Y_i^0) : i ∈ O_n) ∈ ℝ^{2n}`: the
authoritative realization of the paper's fixed schedule symbol `Y`. Its ambient space
`ℝ^{2n}` is carried by the pair-valued function `O → ℝ × ℝ` (each outcome unit `i`
contributing the all-treated / all-control pair `(Y_i^1, Y_i^0)`), so the schedule's
carrier `O → ℝ × ℝ` is (as a real vector space) `ℝ^{card O} × ℝ^{card O} ≅ ℝ^{2n}`. -/
noncomputable def schedule (i : O) : ℝ × ℝ := (E.Y1 i, E.Y0 i)
  -- @realizes Y(AUTHORITATIVE carrier of the fixed potential-outcome schedule symbol Y = ((Y_i^1,Y_i^0) : i∈O_n); carrier O→ℝ×ℝ ≅ ℝ^{2n} — NOT expT, which realizes the exposure indicator T_i(Z); the schedule's bounded ambient box is pinned by BoundedOutcomes)

/-- All-treated exposure indicator `T_i(Z) = ∏_{k∈N_i} Z_k`. -/
noncomputable def expT (z : I → Bool) (i : O) : ℝ :=
  ∏ k ∈ E.N i, (if z k then (1 : ℝ) else 0)   -- @realizes T_i(Z)(product over N_i of Z_k); @realizes Z_k(coordinate assignment z k : Bool realizing {0,1} via if z k then 1 else 0); @realizes Z(assignment vector z : I→Bool = {0,1}^{m_n})

/-- All-control exposure indicator `C_i(Z) = ∏_{k∈N_i} (1−Z_k)`. -/
noncomputable def expC (z : I → Bool) (i : O) : ℝ :=
  ∏ k ∈ E.N i, (if z k then (0 : ℝ) else 1)   -- @realizes C_i(Z)(product over N_i of 1−Z_k)

/-- All-treated exposure probability `π_i^1(p) = ∏_{k∈N_i} p_k`. -/
noncomputable def piT (p : I → ℝ) (i : O) : ℝ :=
  ∏ k ∈ E.N i, p k   -- @realizes pi_i^1(p)(product over N_i of p_k; range (0,1] via p∈[0,1] from ProbVector/PositivityFloor)

/-- All-control exposure probability `π_i^0(p) = ∏_{k∈N_i} (1−p_k)`. -/
noncomputable def piC (p : I → ℝ) (i : O) : ℝ :=
  ∏ k ∈ E.N i, (1 - p k)   -- @realizes pi_i^0(p)(product over N_i of 1−p_k; range (0,1] via p∈[0,1] from ProbVector/PositivityFloor)

/-- Outcome-side degree `d_i = |N_i(G_n)|`. -/
def deg (i : O) : ℕ := (E.N i).card   -- @realizes d_i(card N_i)

/-- Outcome neighborhood of an intervention unit `M_k(G_n) = {i : k ∈ N_i}`. -/
def M (k : I) : Finset O := Finset.univ.filter (fun i => k ∈ E.N i)   -- @realizes M_k(G_n)(outcome neighborhood)

/-- Intervention-side output degree `s_k = |M_k(G_n)|`. -/
def sdeg (k : I) : ℕ := (E.M k).card   -- @realizes s_k(card M_k)

/-- Shared intervention neighborhood `S_{ij}(G_n) = N_i ∩ N_j`. -/
def shared (i j : O) : Finset I := E.N i ∩ E.N j   -- @realizes S_{ij}(G_n)(N_i ∩ N_j)

/-- Overlap-dependency neighbors of `i`: `{j : S_{ij} ≠ ∅}`. -/
def overlapNbrs (i : O) : Finset O :=
  Finset.univ.filter (fun j => 0 < (E.shared i j).card)   -- @realizes Delta_n(overlap neighbor set)

/-- Treated overlap load `r_{ij}^1(G_n,p) = 1{S_{ij}≠∅}(∏_{k∈S_{ij}} p_k^{-1} − 1)`. -/
noncomputable def r1 (p : I → ℝ) (i j : O) : ℝ :=
  if 0 < (E.shared i j).card then (∏ k ∈ E.shared i j, (p k)⁻¹) - 1 else 0
  -- @realizes r_{ij}^1(G_n,p)(reciprocal-product treated load; range [0,∞) via p∈(0,1) from ProbVector/PositivityFloor)

/-- Control overlap load `r_{ij}^0(G_n,p) = 1{S_{ij}≠∅}(∏_{k∈S_{ij}} (1−p_k)^{-1} − 1)`. -/
noncomputable def r0 (p : I → ℝ) (i j : O) : ℝ :=
  if 0 < (E.shared i j).card then (∏ k ∈ E.shared i j, (1 - p k)⁻¹) - 1 else 0
  -- @realizes r_{ij}^0(G_n,p)(reciprocal-product control load; range [0,∞) via p∈(0,1) from ProbVector/PositivityFloor)

/-- Cross-arm overlap load `r_{ij}^{10}(G_n) = 1{S_{ij}≠∅}`. -/
noncomputable def r10 (i j : O) : ℝ :=
  if 0 < (E.shared i j).card then 1 else 0   -- @realizes r_{ij}^{10}(G_n)(shared-neighborhood indicator)

-- @node: def:hajek-denominators
/-- Exposure-weighted Hájek denominators `(D_1, D_0)` with
`D_1 = ∑_i T_i/π_i^1` and `D_0 = ∑_i C_i/π_i^0`. -/
noncomputable def hajekDenominators (p : I → ℝ) (z : I → Bool) : ℝ × ℝ :=
  -- @realizes D_1(p,Z)(first component ∑_i T_i(z)/π_i^1(p); space [0,∞): each `expT z i` is a product of
  -- `{0,1}`-valued factors, hence ≥ 0, and `piT p i > 0` on the feasible box ε ≤ p_k ≤ 1−ε)
  -- @realizes D_0(p,Z)(second component ∑_i C_i(z)/π_i^0(p); space [0,∞): each `expC z i` is a product of
  -- `{0,1}`-valued factors, hence ≥ 0, and `piC p i > 0` on the feasible box ε ≤ p_k ≤ 1−ε)
  (∑ i, E.expT z i / E.piT p i, ∑ i, E.expC z i / E.piC p i)

-- @node: def:hetero-hajek-estimator
/-- The heterogeneous Bernoulli Hájek estimator with the explicit zero-denominator
convention (each arm is `0` when its denominator vanishes). -/
noncomputable def hajekEstimator (p : I → ℝ) (z : I → Bool) : ℝ :=
  (if 0 < (E.hajekDenominators p z).1 then
      (∑ i, E.expT z i * E.Yfun i z / E.piT p i) / (E.hajekDenominators p z).1 else 0)
  - (if 0 < (E.hajekDenominators p z).2 then
      (∑ i, E.expC z i * E.Yfun i z / E.piC p i) / (E.hajekDenominators p z).2 else 0)

-- @node: def:first-order-linearization
/-- First-order heterogeneous Hájek linearization
`η_i = (T_i/π_i^1 − 1)(Y_i^1 − μ_1) − (C_i/π_i^0 − 1)(Y_i^0 − μ_0)`. -/
noncomputable def linScore (p : I → ℝ) (z : I → Bool) (i : O) : ℝ :=
  (E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1)
    - (E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0)

-- @node: def:variance-scale
/-- Asymptotic variance scale `σ²_{G_n,p}(Y) = n · Var_p(n^{-1} ∑_i η_i)` under the
working design `D` (`= bernoulliDesign p` by `ass:independent-heterogeneous-bernoulli`). -/
noncomputable def varScale (D : FiniteDesign (I → Bool)) (p : I → ℝ) : ℝ :=
  -- @realizes sigma_{G_n,p}^2(Y)(defining formula n · Var_p(n^{-1} ∑_i η_i); space [0,∞) since it is the
  -- nonnegative real `card O` times the design variance `FiniteDesign.Var`, itself a mean of squares)
  (Fintype.card O : ℝ) * D.Var (fun z => (Fintype.card O : ℝ)⁻¹ * ∑ i, E.linScore p z i)

end BipartiteExperiment

/-! ## Environment S1 — the reused finite-population Bernoulli design world

The working design `D : FiniteDesign (I → Bool)` is the assignment law over the
finite assignment space `Ω = (I → Bool)`; under `ass:independent-heterogeneous-bernoulli`
it equals `bernoulliDesign p`, so cross-unit independence is structural. -/

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @env: S1
variable (D : FiniteDesign (I → Bool)) (p : I → ℝ)   -- @realizes Z(assignment/sample space Ω = I→Bool = {0,1}^{m_n}, carrier of the working design D); @realizes Z_k(per-unit coordinate Bool = {0,1}); @realizes p(carrier I→ℝ; range p_k ∈ [0,1] via ProbVector, sharpened to (0,1) by PositivityFloor)

/-! ## Assumption atoms -/

/-- Probability-vector well-formedness: every coordinate of the design variable lies
in the unit interval, `p ∈ [0,1]^{m_n}`. This pins the declared space of the design
variable `p` — the bare carrier `I → ℝ` does not force the `[0,1]` range, and every
functional of `p` (`π_i^1`, `π_i^0`, `r_{ij}^1`, `r_{ij}^0`) inherits its range from
this constraint (the positivity floor `ε ≤ p_k ≤ 1 − ε` further sharpens it to the
open interval `(0,1)`). -/
def ProbVector (p : I → ℝ) : Prop :=
  ∀ k, 0 ≤ p k ∧ p k ≤ 1   -- @realizes p(range p_k ∈ [0,1])

-- @node: ass:bipartite-interference
/-- Neighborhood SUTVA: `Y_i` depends on the treatment vector only through its
restriction to `N_i(G_n)`. -/
def BipartiteInterference (E : BipartiteExperiment I O) : Prop :=
  ∀ (i : O) (z z' : I → Bool), (∀ k ∈ E.N i, z k = z' k) → E.Yfun i z = E.Yfun i z'

-- @node: ass:independent-heterogeneous-bernoulli
/-- The working assignment law is the independent heterogeneous Bernoulli design:
`D = bernoulliDesign p` (each `Z_k` independent `Bernoulli(p_k)`). -/
def IndepHeteroBernoulli (D : FiniteDesign (I → Bool)) (p : I → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) : Prop :=
  D = Causalean.Experimentation.DesignBased.bernoulliDesign p hp0 hp1
  -- @realizes Z_k(AUTHORITATIVE {0,1} assignment-coordinate + Bernoulli-law realization: each Z_k independent Bernoulli(p_k), coordinate space Bool = {0,1} via bernoulliDesign per-unit coin flip — this decl, NOT EpsilonAdmissible which only constrains ε, carries the Z_k space); @realizes Z(assignment vector Z = (Z_k)_{k∈I} over I→Bool = {0,1}^{m_n}, law bernoulliDesign p)

/-- Admissible positivity-floor domain: the global side-condition `ε ∈ (0, 1/2)`
required by the paper's positivity floor. This pins the space of the floor symbol
`epsilon`; without it the floor `ε ≤ p_k ≤ 1 − ε` fails to force `p_k ∈ (0,1)` and the
uniform exposure-probability lower bounds `ε^{d̄} > 0` are lost. Threaded into every
statement that relies on strict overlap.

It is therefore a LOAD-BEARING member of the realization clusters of `pi_i^1(p)`,
`pi_i^0(p)`, `V_env(G_n,p)` and `hat_V_cons(G_n,p)`: `PositivityFloor ε p` alone
admits `ε ≤ 0` (e.g. `ε = -1`, `p_k = -1/2`), under which `π_i^1(p) ∉ (0,1]` and the
overlap loads can go negative; the conjunction `EpsilonAdmissible ε ∧ PositivityFloor ε p`
is what forces `p_k ∈ (0,1)` and hence those declared spaces. -/
def EpsilonAdmissible (ε : ℝ) : Prop :=
  0 < ε ∧ ε < 1 / 2   -- @realizes epsilon(domain ε ∈ (0,1/2)); @realizes pi_i^1(p)(range (0,1] co-realizer: 0<ε<1/2 together with the floor ε≤p_k≤1−ε gives p_k∈(0,1), so 0<∏_{k∈N_i}p_k≤1); @realizes pi_i^0(p)(range (0,1] co-realizer: 0<ε<1/2 with the floor gives 1−p_k∈(0,1), so 0<∏_{k∈N_i}(1−p_k)≤1); @realizes V_env(G_n,p)(range [0,∞) co-realizer: 0<ε<1/2 with the floor gives p_k∈(0,1), so every load r_{ij}^1,r_{ij}^0,r_{ij}^{10}≥0 and V_env≥0); @realizes hat_V_cons(G_n,p)(range [0,∞) co-realizer: V̂_cons=V_env≥0 under the admissible ε-domain plus the floor)

-- @node: ass:positivity-floor
/-- Positivity floor: `ε ≤ p_k ≤ 1 − ε` for every intervention unit `k`. Its
range-pinning force for `π_i^1, π_i^0, V_env, V̂_cons` is only released in conjunction
with `EpsilonAdmissible ε` (which supplies `0 < ε < 1/2`). -/
def PositivityFloor (ε : ℝ) (p : I → ℝ) : Prop :=
  ∀ k, ε ≤ p k ∧ p k ≤ 1 - ε   -- @realizes epsilon(floor ε ≤ p_k ≤ 1−ε); @realizes pi_i^1(p)(range (0,1] co-realizer, WITH EpsilonAdmissible ε: the floor ε≤p_k≤1−ε under 0<ε<1/2 makes 0<∏_{k∈N_i}p_k≤1; piT alone is the value, this clause plus EpsilonAdmissible pins its range); @realizes pi_i^0(p)(range (0,1] co-realizer, WITH EpsilonAdmissible ε: ε≤p_k≤1−ε and 0<ε<1/2 make 0<∏_{k∈N_i}(1−p_k)≤1); @realizes V_env(G_n,p)(range [0,∞) co-realizer, WITH EpsilonAdmissible ε: 0<ε≤p_k≤1−ε<1 ⟹ each load r_{ij}^1,r_{ij}^0,r_{ij}^{10}≥0, so V_env≥0); @realizes hat_V_cons(G_n,p)(range [0,∞) co-realizer, WITH EpsilonAdmissible ε: V̂_cons=V_env≥0 under the same admissible floor)

-- @node: ass:budget-balance
/-- Budget balance: the expected number of treated units is fixed at `B_n`,
`∑_k p_k = B_n`. -/
def BudgetBalance (B : ℝ) (p : I → ℝ) : Prop :=
  ∑ k, p k = B   -- @realizes B_n(budget hyperplane ∑ p_k = B_n; admissible interval carried by BudgetAdmissible)

/-- Admissible budget domain: `B_n ∈ [m_n ε, m_n (1 − ε)]`. This carries the declared
space of the budget symbol `B_n` — `BudgetBalance` alone only fixes the hyperplane
`∑_k p_k = B_n` and leaves `B_n` unconstrained, whereas the feasible set is nonempty
(and the constant vector `B_n/m_n` lies in the box `[ε,1−ε]^{m_n}`) exactly when
`B_n` lies in this interval. -/
def BudgetAdmissible (ε B : ℝ) : Prop :=
  (Fintype.card I : ℝ) * ε ≤ B ∧ B ≤ (Fintype.card I : ℝ) * (1 - ε)
  -- @realizes B_n(AUTHORITATIVE budget-space realization: admissible interval B_n ∈ [m_n ε, m_n(1−ε)] = [card I·ε, card I·(1−ε)]; the space of the budget symbol B_n is carried by THIS predicate, not by BudgetBalance (hyperplane only) nor BoundedOutcomes (unrelated))

-- @node: ass:bounded-outcomes
/-- Bounded potential outcomes: `|Y_i^1| ≤ 1` and `|Y_i^0| ≤ 1`. -/
def BoundedOutcomes (E : BipartiteExperiment I O) : Prop :=
  ∀ i, |E.Y1 i| ≤ 1 ∧ |E.Y0 i| ≤ 1
  -- @realizes Y(range predicate pinning the schedule's ambient box: each coordinate pair (Y_i^1,Y_i^0) of the schedule symbol Y ∈ ℝ^{2n} lies in [-1,1]², so the Y-space holds across the CONJUNCTION of the `schedule` carrier ∧ this bound)

-- @node: ass:bounded-outcome-degree
/-- Bounded outcome-side degree: the constant `d̄` is a positive real and
`max_i d_i ≤ d̄`. -/
def BoundedOutcomeDegree (E : BipartiteExperiment I O) (dbar : ℝ) : Prop :=
  0 < dbar                                  -- @realizes dbar(positive regularity constant, space (0,∞))
    ∧ ∀ i, ((E.N i).card : ℝ) ≤ dbar        -- @realizes dbar(uniform outcome-degree bound max d_i ≤ d̄)

-- @node: ass:bounded-overlap-dependency
/-- Bounded overlap-dependency degree: the constant `D̄` is a positive real and
`Δ_n ≤ D̄`. -/
def BoundedOverlapDependency (E : BipartiteExperiment I O) (Dbar : ℝ) : Prop :=
  0 < Dbar                                     -- @realizes Dbar(positive regularity constant, space (0,∞))
    ∧ ∀ i, ((E.overlapNbrs i).card : ℝ) ≤ Dbar -- @realizes Dbar(uniform overlap-dependency bound Δ_n ≤ D̄)

-- @node: ass:variance-nondegenerate
/-- Nondegenerate asymptotic design variance: `liminf_n σ²_n > 0`, encoded as an
eventual uniform positive lower bound on the variance-scale sequence. -/
def VarianceNondegenerate (σ2 : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, c ≤ σ2 n

-- @node: def:feasible-designs
/-- Feasible heterogeneous Bernoulli designs: the probability-vector membership
`p ∈ [0,1]^{m_n}`, the positivity floor, and the budget balance bundled over a
design variable `p : I → ℝ`. The `prob` field pins the declared ambient space of the
class `P_{n,B_n,ε} ⊆ [0,1]^{m_n}` explicitly (the bare carrier `I → ℝ` and
`PositivityFloor`/`BudgetBalance` alone leave the `[0,1]` box unenforced whenever the
floor `ε` is not itself known admissible). -/
structure FeasibleDesign (ε B : ℝ) (p : I → ℝ) : Prop where
  /-- Probability-vector membership `p ∈ [0,1]^{m_n}` (the class' ambient box). -/
  prob : ProbVector p   -- @realizes P_{n,B_n,epsilon}(carrier box: p ∈ [0,1]^{m_n}, the subset-of-[0,1]^{m_n} ambient space of the design class)
  /-- Admissible floor domain `ε ∈ (0,1/2)`: the declared space of the floor symbol.
  Without it the `floor` field admits `ε ≤ 0` and the exposure probabilities
  `π_i^1(p), π_i^0(p)` are no longer pinned to `(0,1]`. -/
  admissible : EpsilonAdmissible ε   -- @realizes pi_i^1(p)(range (0,1] co-realizer inside the design class: 0<ε<1/2 with `floor` gives p_k∈(0,1), hence 0<π_i^1(p)≤1); @realizes pi_i^0(p)(range (0,1] co-realizer inside the design class); @realizes V_env(G_n,p)(range [0,∞) co-realizer: admissible ε + floor ⟹ nonnegative overlap loads); @realizes hat_V_cons(G_n,p)(range [0,∞) co-realizer: V̂_cons=V_env≥0 on the admissible class)
  /-- Positivity floor `ε ≤ p_k ≤ 1 − ε`. -/
  floor : PositivityFloor ε p
  /-- Budget balance `∑_k p_k = B`. -/
  budget : BudgetBalance B p

/-- The feasible-design class `P_{n,B_n,ε}` as a subset of `[0,1]^{m_n}` (realized over
the carrier `I → ℝ`, with the `[0,1]` box pinned by the `prob` field of
`FeasibleDesign`). -/
def feasibleSet (ε B : ℝ) : Set (I → ℝ) := {p | FeasibleDesign ε B p}
  -- @realizes P_{n,B_n,epsilon}(feasible design class ⊆ [0,1]^{m_n}; ambient box carried by FeasibleDesign.prob : ProbVector, floor ε≤p_k≤1−ε, budget ∑ p_k = B)

end CausalSmith.Experimentation.BipartiteMinimaxDesign
