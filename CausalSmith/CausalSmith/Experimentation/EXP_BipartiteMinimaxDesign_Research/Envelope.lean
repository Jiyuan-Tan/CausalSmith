/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: the graph-only envelope design objects

The observable graph-only conservative variance envelope `V_env`, its
normalized per-coordinate gradient `g_k`, the conservative variance-scale
estimator, the envelope-optimal and additive degree-dispersion surrogate design
selectors, and the observable approximation ratio. Each is a design object
depending only on the graph `G_n` and the propensity vector `p`.
-/

module
public import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

namespace BipartiteExperiment

variable (E : BipartiteExperiment I O)

-- @node: def:graph-envelope
/-- Graph-only conservative variance envelope
`V_env = 4 n^{-1} ∑_{i,j} {r_{ij}^1 + r_{ij}^0 + 2 r_{ij}^{10}}`. -/
noncomputable def varEnvelope (p : I → ℝ) : ℝ :=
  -- @realizes V_env(G_n,p)(defining formula 4 n^{-1} ∑_{i,j}{r_{ij}^1 + r_{ij}^0 + 2 r_{ij}^{10}}; space
  -- [0,∞) as a nonnegative multiple of a sum of the nonnegative overlap loads r1, r0, r10)
  4 * (Fintype.card O : ℝ)⁻¹ * ∑ i, ∑ j, (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j)

-- @node: def:kkt-gradient
/-- Gradient of the normalized envelope `V_env/4`:
`g_k = n^{-1} ∑_{i,j : k∈S_{ij}} {−(∏_{ℓ∈S_{ij}} p_ℓ^{-1}) p_k^{-1}
        + (∏_{ℓ∈S_{ij}} (1−p_ℓ)^{-1}) (1−p_k)^{-1}}`. -/
noncomputable def envelopeGrad (p : I → ℝ) (k : I) : ℝ :=
  (Fintype.card O : ℝ)⁻¹ * ∑ i, ∑ j,
    (if k ∈ E.shared i j then
        -(∏ l ∈ E.shared i j, (p l)⁻¹) * (p k)⁻¹
          + (∏ l ∈ E.shared i j, (1 - p l)⁻¹) * (1 - p k)⁻¹
      else 0)

-- @node: def:conservative-variance-estimator
/-- Graph-only conservative variance-scale estimator `V̂_cons = V_env`. -/
noncomputable def varEstCons (p : I → ℝ) : ℝ := E.varEnvelope p
  -- @realizes hat_V_cons(G_n,p)(conservative variance-scale estimator V̂_cons = V_env; space [0,∞) by construction from varEnvelope)

/-- Observable degree-dispersion weight
`h_k(G_n) = n^{-1} ∑_{i,j : k∈S_{ij}} |S_{ij}|^{-1}`. -/
noncomputable def hWeight (k : I) : ℝ :=
  (Fintype.card O : ℝ)⁻¹ * ∑ i, ∑ j, (if k ∈ E.shared i j then ((E.shared i j).card : ℝ)⁻¹ else 0)
  -- @realizes h_k(G_n)(degree-dispersion weight n^{-1} ∑_{i,j:k∈S_{ij}} |S_{ij}|^{-1}; observable graph-only, range [0,∞) as a nonnegative sum of reciprocal shared-set sizes)

/-- Additive degree-dispersion surrogate objective
`A(p) = ∑_k h_k(G_n){p_k^{-1} + (1−p_k)^{-1}}`. -/
noncomputable def surrogateObjective (p : I → ℝ) : ℝ :=
  ∑ k, E.hWeight k * ((p k)⁻¹ + (1 - p k)⁻¹)

end BipartiteExperiment

open Classical in
-- @node: def:optimal-design
/-- Envelope-optimal design selector: any feasible minimizer of `V_env`, with a
junk fallback (the homogeneous budget vector) when the argmin is empty. -/
noncomputable def optimalDesign (E : BipartiteExperiment I O) (ε B : ℝ) : I → ℝ :=
  if h : ∃ p, p ∈ feasibleSet ε B ∧ ∀ q ∈ feasibleSet ε B, E.varEnvelope p ≤ E.varEnvelope q
  then h.choose else (fun _ => B / (Fintype.card I : ℝ))
  -- @realizes p_n^*(G_n)(argmin envelope selector)

/-- The envelope minimum `min_{p∈P} V_env(G_n,p)`, realized as the envelope value at
the optimal design (the minimizer's value equals the minimum whenever it exists). -/
noncomputable def envMin (E : BipartiteExperiment I O) (ε B : ℝ) : ℝ :=
  E.varEnvelope (optimalDesign E ε B)

open Classical in
-- @node: def:surrogate-design
/-- Degree-dispersion surrogate design selector: any feasible minimizer of the
additive surrogate objective `A`, with a junk fallback when the argmin is empty. -/
noncomputable def surrogateDesign (E : BipartiteExperiment I O) (ε B : ℝ) : I → ℝ :=
  if h : ∃ p, p ∈ feasibleSet ε B ∧
      ∀ q ∈ feasibleSet ε B, E.surrogateObjective p ≤ E.surrogateObjective q
  then h.choose else (fun _ => B / (Fintype.card I : ℝ))
  -- @realizes p_n^{deg}(G_n)(argmin additive surrogate selector)

open Classical in
/-- Directional second-order modulus of the normalized envelope `V_env/4` along a
budget-feasible direction `d`, over the feasible set:
`L_d = sup_{q∈P} g_q''(0)` with `g_q(t) = V_env(q + t·d)/4`. This realizes the
observable second-order modulus `L_ab` used in `thm:heterogeneity-separation`
(the paper's directional Hessian modulus `sup_{q∈P} (e_b−e_a)ᵀ Hess(V_env/4)(q) (e_b−e_a)`
along `d = e_b − e_a`). -/
noncomputable def dirModulus (E : BipartiteExperiment I O) (ε B : ℝ) (d : I → ℝ) : ℝ :=
  ⨆ q : feasibleSet (I := I) ε B,
    deriv (deriv fun t : ℝ => E.varEnvelope (fun k => (q : I → ℝ) k + t * d k) / 4) 0
  -- @realizes L_ab(directional second-order modulus sup_{q∈P} g_q''(0) of V_env/4 along d)

open Classical in
-- @node: def:approximation-ratio
/-- Observable approximation ratio `α_cert = V_env(p^{deg}) / min_p V_env` on the
positive-minimum branch, with the no-loss convention `α_cert = 1` when the
envelope minimum is zero. Total and `[1,∞)`-valued. -/
noncomputable def approxRatio (E : BipartiteExperiment I O) (ε B : ℝ) : ℝ :=
  if 0 < envMin E ε B then E.varEnvelope (surrogateDesign E ε B) / envMin E ε B else 1
  -- @realizes alpha_cert(G_n)(observable approximation ratio; total and range [1,∞) — positive-minimum branch V_env(p^deg)/envMin with V_env(p^deg) ≥ min = envMin so ratio ≥ 1, and the no-loss branch = 1)

end CausalSmith.Experimentation.BipartiteMinimaxDesign
