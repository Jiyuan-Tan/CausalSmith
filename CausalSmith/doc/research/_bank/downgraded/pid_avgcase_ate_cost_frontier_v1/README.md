---
qid: pid_avgcase_ate_cost_frontier
spec: v1
topic: "Sharp full-propensity assignment-information frontier for the ATE. Observe binary Z, finite X and Y in {0,...,K-1}, with overlap and consistency. A compatible full law Q(Y(0),Y(1),Z,X) must match the observed law and satisfy a fixed Gamma bound on the odds distortion of q=P(Z=1|X,Y(0),Y(1)) relative to e(X). Define its Pearson assignment cost R=E[(q-e)^2/{e(1-e)}] and C_P(t) as the minimum R among compatible laws with ATE t. Prove the sharp equivalence t feasible at budget rho iff C_P(t)<=rho, endpoint attainment, the O(|X|K^2)-cell perspective SOCP and explicit conic dual. For binary outcomes, prove a treatment-independent cost-improving garbling to monotone response types, derive the complete six-odds-face scalar catalog plus the unique interior algebraic root, and show the feasible one-stratum null cost equals observed Corr(Z,Y)^2. Prove a one-way cost-nonincreasing embedding of every compatible full law into an explicitly defined box-augmented Neyman specialization of Ishikawa-He-Kanamori equation (14), with the exact and locally uniform separation C(0.3)=9/70>9/91=Ctilde_IHK(0.3). Construct simultaneous multinomial profile confidence envelopes with finite-sample O(n^-1/2) diameter on a named uniformly Slater-regular interior region, and prove that honest confidence sets must retain infinite diameter at a contiguous finite-to-infinite null-cost boundary. Uniform tangent inference through zero cells, optimizer ties, and moving odds faces remains an explicit open problem. Consumer: a prespecified categorical-mercury version of Zhang-Zhao's NHANES fish-consumption ATE sensitivity analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A treatment-independent garbling was derived that removes the minority discordant binary response type while preserving observed margins, ATE, odds bounds, and weakly lowering every convex assignment-information cost. It yields six explicit odds faces and one scalar interior root; for the symmetric Gamma=4 witness, C(t)=(0.6-t)^2/(1-|t|) on [0,0.75] and C(0)=0.36. Separate code matched 140 original SOCP solves within 6.2e-10 and 300 garbling checks within 1.2e-16. Exact arithmetic gives C(0.3)=9/70 versus the explicitly defined box-augmented Neyman specialization of equation (14), valued at 9/91. Boundary checks found infinite null costs, interior active odds faces, and an S5 quintic, so universal radical formulas and globally finite regular vertical bands are excluded. UNRESOLVED BOTTLENECK: Prove uniform stability of the multinomial frontier tangent/profile operator through zero perspective cells and moving odds faces, yielding informative simultaneous confidence sets. EARLY KILL TEST: Independently reconstruct the four-cell garbling, six-face reduction, 9/70 versus 9/91 separation, and asymmetric interior odds-face example; any failure of preservation, monotonicity, or strict separation stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_avgcase_ate_cost_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The sharp frontier and binary reduction are sound, but field-tier framing additionally promised support-changing tangent inference or a completed empirical application, neither delivered within scope."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The inference result does not deliver the tangent/bootstrap procedure introduced in the definitions and remains confined to a uniformly Slater-regular region whose nonemptiness and empirical checkability are not demonstrated for the proposed application."
  - "The Ishikawa–He–Kanamori comparison is correctly only against the note-defined box-augmented specialization, so it does not establish a gap relative to their full published class."
  - "No NHANES or other substantive application is delivered, limiting the demonstrated econometric importance and keeping the projected leading-journal score below the strongest field contributions."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_binary_garbling.tex
  - discovery/solve_thm_strict_jensen_gap.tex
  - discovery/solve_thm_local_uniform_strict_jensen_gap.tex
  - discovery/solve_thm_regular_profile_diameter.tex
seeds_burned: []
proof_attempt_summary: |
  Six D0 solve rounds produced a clean theorem graph for the sharp compatible-full-law frontier,
  binary garbling reduction, scalar catalog, exact box-augmented comparator gap, regular-region
  confidence diameter, and boundary impossibility result; both substantive D0.5 panels passed with
  no findings. The field-tier framing failed because support-changing tangent/bootstrap inference,
  comparison against the unqualified published IHK class, and the proposed empirical application
  remain substantial undelivered extensions, leaving the sound package at subfield tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26022091
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26022091
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_avgcase_ate_cost_frontier / v1 — Downgraded

**Topic.** Sharp full-propensity assignment-information frontier for the ATE. Observe binary Z, finite X and Y in {0,...,K-1}, with overlap and consistency. A compatible full law Q(Y(0),Y(1),Z,X) must match the observed law and satisfy a fixed Gamma bound on the odds distortion of q=P(Z=1|X,Y(0),Y(1)) relative to e(X). Define its Pearson assignment cost R=E[(q-e)^2/{e(1-e)}] and C_P(t) as the minimum R among compatible laws with ATE t. Prove the sharp equivalence t feasible at budget rho iff C_P(t)<=rho, endpoint attainment, the O(|X|K^2)-cell perspective SOCP and explicit conic dual. For binary outcomes, prove a treatment-independent cost-improving garbling to monotone response types, derive the complete six-odds-face scalar catalog plus the unique interior algebraic root, and show the feasible one-stratum null cost equals observed Corr(Z,Y)^2. Prove a one-way cost-nonincreasing embedding of every compatible full law into an explicitly defined box-augmented Neyman specialization of Ishikawa-He-Kanamori equation (14), with the exact and locally uniform separation C(0.3)=9/70>9/91=Ctilde_IHK(0.3). Construct simultaneous multinomial profile confidence envelopes with finite-sample O(n^-1/2) diameter on a named uniformly Slater-regular interior region, and prove that honest confidence sets must retain infinite diameter at a contiguous finite-to-infinite null-cost boundary. Uniform tangent inference through zero cells, optimizer ties, and moving odds faces remains an explicit open problem. Consumer: a prespecified categorical-mercury version of Zhang-Zhao's NHANES fish-consumption ATE sensitivity analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A treatment-independent garbling was derived that removes the minority discordant binary response type while preserving observed margins, ATE, odds bounds, and weakly lowering every convex assignment-information cost. It yields six explicit odds faces and one scalar interior root; for the symmetric Gamma=4 witness, C(t)=(0.6-t)^2/(1-|t|) on [0,0.75] and C(0)=0.36. Separate code matched 140 original SOCP solves within 6.2e-10 and 300 garbling checks within 1.2e-16. Exact arithmetic gives C(0.3)=9/70 versus the explicitly defined box-augmented Neyman specialization of equation (14), valued at 9/91. Boundary checks found infinite null costs, interior active odds faces, and an S5 quintic, so universal radical formulas and globally finite regular vertical bands are excluded. UNRESOLVED BOTTLENECK: Prove uniform stability of the multinomial frontier tangent/profile operator through zero perspective cells and moving odds faces, yielding informative simultaneous confidence sets. EARLY KILL TEST: Independently reconstruct the four-cell garbling, six-face reduction, 9/70 versus 9/91 separation, and asymmetric interior odds-face example; any failure of preservation, monotonicity, or strict separation stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_avgcase_ate_cost_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 panels PASS with no findings, but the general referee assigns subfield at 7.1 below the 7.4 field floor and marks the package not salvageable within scope.

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
