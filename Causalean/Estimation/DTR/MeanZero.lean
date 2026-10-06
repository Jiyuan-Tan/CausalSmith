/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mean zero of the sequential DR (DTR) influence function

Headline theorem `seqDR_mean_zero`:

    ∫ z, ψ_seqDR z ∂(P_Z) = 0

Decomposition mirrors the ATE AIPW analysis but is staged: the
sequential DR moment expands as

* `μ₀_val(S₀)`                                                 — gives `θ₀`
* `(1{D₀=dbar 0} / e₀_val(S₀)) · (μ₁_val(S₁,D₀,S₀) − μ₀_val(S₀))` — stage-0 correction
* `(1{D₀=dbar 0} · 1{D₁=dbar 1} / (e₀_val(S₀) · e₁_val(S₁,D₀,S₀))) ·
    (Y − μ₁_val(S₁,D₀,S₀))`                                    — stage-1 correction
* `−θ₀`                                                        — constant

The two correction terms vanish via the stagewise weighted-residual integral
lemmas in `ScorePullout.lean`.
-/

module
public import Causalean.Estimation.DTR.MeanZero.Headline

/-!
Roll-up for the stagewise conditioning lemmas and the headline mean-zero
theorem for the sequential doubly robust score.
-/
