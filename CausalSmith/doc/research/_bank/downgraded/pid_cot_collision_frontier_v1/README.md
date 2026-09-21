---
qid: pid_cot_collision_frontier
spec: v1
topic: "Finite-array cross-arm collision frontier for covariate-assisted optimal-transport bounds. In two independent arms, observe binary outcomes on K uniform covariate cells with known amplitudes 0<b<a<1/2 and deterministic sign arrays; target the actual sharp binary-cost COT endpoint L_K=a-b rho_K. When lambda=n_0 n_1/K has a finite limit and triple collisions vanish, prove marked-Poisson equivalence under supported product mixtures and uniform collision-statistic approximation over deterministic arrays. Derive certified finite interval-action LPs for exact minimax absolute risk and uniformly honest expected interval length, and prove two-sided honest-minimax transfer to the full deterministic-array experiment. When lambda diverges sparsely, prove unprojected studentized Gaussian inference centered at L_K with the matching interior local minimax variance. Transfer only to the declared continuous growing-roughness interpolation image. Consumer: causalPIviaCOT partition-resolution diagnostics; coarsening changes the endpoint absent a separate bias bound. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Parameter-free reverse kernels, deterministic collision bounds, interval expansion and coverage repair were derived; exact checks give zero-collision risk b/2 and honest length (1-alpha)b, one-mark honest length 0.09489725068496811, and R(0.025)=0.049950617272262944 for a=.2,b=.1,r=.5. Six LP refinements at lambda=.025,1,10 produced contracting floating-point brackets with explicit off-grid repairs. A former fixed-array witness was rejected because marginal imbalance leaked information; supported mixtures over legal arrays repair the lower experiment without changing the target. UNRESOLVED BOTTLENECK: Complete the LAN-to-deterministic-shell local minimax theorem for bounded truncated quadratic losses, explicitly ordering local-radius and loss-truncation limits, and package rigorous interval-LP enclosures. EARLY KILL TEST: At lambda=1, double interval-action resolution and rigorously enclose primal/dual values and every coverage segment; require a shrinking certified bracket with coverage at least .95, using the exact one-mark value as an independent control. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_cot_collision_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No delivered lambda=1 doubled-resolution rational primal/dual enclosure with segmentwise coverage and exact one-mark comparison; no broad anchor-class achievability or partition-refinement bias theorem."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves two-sided finite-information minimax transfer, honest-length transfer, and a matching ordered local-minimax variance only for the known-amplitude, uniform-cell deterministic-sign experiment."
  - "For general anchor-containing COT classes it proves converse lower bounds only, while continuous achievability is restricted to the specially constructed growing-roughness interpolation image."
  - "The node gives a general LP-certification scheme but does not exhibit the required λ=1 doubled-resolution rational primal/dual enclosure (with its coverage-segment check and comparison to the exact one-mark control), so the promised independently usable finite certificate is not yet delivered."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_finite_information_transfer.tex
  - discovery/solve_thm_honest_interval_transfer.tex
  - discovery/solve_thm_deterministic_shell_local_minimax.tex
  - discovery/solve_thm_anchor_class_collision_converse.tex
  - discovery/solve_prop_exact_controls.tex
seeds_burned:
  - index: 0
    one_liner: "S1: finite-array marked-collision frontier"
    reason: "The finite-array marked-collision angle converged to a sound subfield result but could not clear the field floor without out-of-scope broader-class achievability or coarsening-bias theory."
proof_attempt_summary: |
  Discovery established the sharp finite-array endpoint, marked-Poisson comparison,
  finite-information risk and honest-length transfers, sparse Gaussian inference,
  and the ordered deterministic-shell local-minimax lower bound; the final bounded
  repair pass cleared every math-panel finding. The result remained below the field
  floor because achievability does not extend to the broad anchor COT class and no
  coarsening-bias refinement theory was supplied; the promised explicit λ=1 rational
  primal/dual certificate and segmentwise coverage artifact also remains undelivered.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 39900906
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 39900906
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_cot_collision_frontier / v1 — Downgraded

**Topic.** Finite-array cross-arm collision frontier for covariate-assisted optimal-transport bounds. In two independent arms, observe binary outcomes on K uniform covariate cells with known amplitudes 0<b<a<1/2 and deterministic sign arrays; target the actual sharp binary-cost COT endpoint L_K=a-b rho_K. When lambda=n_0 n_1/K has a finite limit and triple collisions vanish, prove marked-Poisson equivalence under supported product mixtures and uniform collision-statistic approximation over deterministic arrays. Derive certified finite interval-action LPs for exact minimax absolute risk and uniformly honest expected interval length, and prove two-sided honest-minimax transfer to the full deterministic-array experiment. When lambda diverges sparsely, prove unprojected studentized Gaussian inference centered at L_K with the matching interior local minimax variance. Transfer only to the declared continuous growing-roughness interpolation image. Consumer: causalPIviaCOT partition-resolution diagnostics; coarsening changes the endpoint absent a separate bias bound. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Parameter-free reverse kernels, deterministic collision bounds, interval expansion and coverage repair were derived; exact checks give zero-collision risk b/2 and honest length (1-alpha)b, one-mark honest length 0.09489725068496811, and R(0.025)=0.049950617272262944 for a=.2,b=.1,r=.5. Six LP refinements at lambda=.025,1,10 produced contracting floating-point brackets with explicit off-grid repairs. A former fixed-array witness was rejected because marginal imbalance leaked information; supported mixtures over legal arrays repair the lower experiment without changing the target. UNRESOLVED BOTTLENECK: Complete the LAN-to-deterministic-shell local minimax theorem for bounded truncated quadratic losses, explicitly ordering local-radius and loss-truncation limits, and package rigorous interval-LP enclosures. EARLY KILL TEST: At lambda=1, double interval-action resolution and rigorously enclose primal/dual values and every coverage segment; require a shrinking certified bracket with coverage at least .95, using the exact one-mark value as an independent control. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_cot_collision_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the structured collision frontier subfield below the field floor (paper-score ceiling 6.6 < 7.4; salvageable=false); math review passes, but broader-class achievability and the promised lambda=1 rational certificate artifact are not delivered.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
