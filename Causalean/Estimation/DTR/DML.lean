/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One-shot DML / sequential DR estimator for the DTR (`n = 2`) effect

`def:est-dml-dtr` and `thm:est-dml-dtr-al` instantiated for the
`DTREstimationSystem` from `Setup.lean`.

The estimator is

    θ̂ⁿ_DML := (1/|B(n)|) Σ_{i ∈ B(n)} m_seqDR( dbar, Zᵢ, η̂(n), 0 )
            + θ_correction,

mirroring `Estimation/ATE/DML.lean` stage-by-stage.  The empirical mean
of `m_seqDR(·, ·, ·, 0)` over fold `B(n)` equals the empirical
sequential-DR pseudo-outcome.

The headline `dml_DTR_isAsymLinear` translates user-friendly stagewise
hypotheses (`μ̂_k_n`, `ê_k_n` for `k ∈ {0, 1}`) into the abstract
`seqDR_dml_isAsymLinear` interface, which in turn delegates to
`oneStepOracleDML_isAsymLinear_of_everywhere`.

The estimator definition accepts the bundled nuisance process
`η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ`.  The asymptotic-linearity theorem
is the public wrapper: it builds that bundle from the four stagewise nuisance
learners, checks the score measurability and integrability obligations, and
transports the abstract Chernozhukov estimator conclusion back to
`dml_DTR_estimator`.
-/

module
public import Causalean.Estimation.DTR.DML.AsymptoticLinearity

/-! # Dynamic-Treatment-Regime DML Estimator

This file defines the one-shot double machine learning estimator for the
two-period dynamic-treatment-regime effect. The main declarations are
`dml_DTR_estimator`, the fold-B empirical mean of the sequential doubly robust
pseudo-outcome, and `dml_DTR_isAsymLinear`, which proves asymptotic linearity
from stagewise nuisance overlap, measurability, L2 integrability, individual
`o_p(1)` rates, and the two same-stage cross-product `o_p(n^{-1/2})` rates. -/
