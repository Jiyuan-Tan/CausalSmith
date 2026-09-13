---
qid: exp_awri_mixture_minimax_certificate
spec: v1
topic: "Certified exact-risk weighted-random-isolation design for network total effects. For a fixed directed interference graph, its undirected WRI conflict graph C_G, bounded positive integer priority weights, fixed full-neighborhood potential outcomes, and a prespecified finite rule library, write the RDIM error as a 2n-dimensional random linear form and compute each dense risk matrix Q_l exactly. Prove an output-sensitive L n^2 2^{O(w log(w+1))} poly(n,b) algorithm from a width-w tree decomposition by integrating priority-order and reciprocal-count messages, including correctness and bit complexity. Over the graph ellipsoid defined by diag((I+gamma L_C)^{-1},(I+gamma L_C)^{-1}), return the minimax rule mixture, least-favourable endpoint distribution, and primal-dual optimality certificate. For arbitrary graphs give simultaneous operator-norm Monte Carlo regions and a certified worst-case-risk gap. Consumer: a universal-financial-education versus none follow-up to Cai, de Janvry, and Sadoulet's rural-China insurance diffusion experiment. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Every RDIM risk entry was reduced to one- and two-marked isolated-set count probabilities, including odd counts and bias. Integer-weight risks have polynomial output bit length, and a three-state polynomial recurrence was derived and checked by exact enumeration on three forests and 344 matrix entries. Two bidirected three-leaf stars force isolated-set size two; reciprocal hub/leaf rules produce distinct verified risks. Checks covered local-max versus sequential greedy semantics, directed-star legality, parity denominators, rationality, PSD ellipsoid, generic SDP reduction, treewidth hardness, and recent design papers. UNRESOLVED BOTTLENECK: Compress joined separator priority/count messages to 2^{O(w log(w+1))} poly(n,b) size; the direct construction retains (nb)^{O(w)} coefficients and proves only XP complexity. EARLY KILL TEST: On all width-two/three graphs with n≤9 and weights in {1,2,3}, compare every tagged coefficient with exhaustive priority ordering, then derive the symbolic message-size recurrence; any unavoidable (nb)^w factor or parameter-preserving hardness obstruction kills the promised FPT kernel and forces pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_awri_mixture_minimax_certificate.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The proposal's theorem-level deliverable is the width-w FPT oracle (or a parameterized-hardness boundary), but the current core honestly proves only the forest rung and leaves both branches open."
  - "neither the claimed fixed-parameter exact-risk algorithm nor the alternative parameterized-hardness boundary is proved."
  - "The supplied Renegar record supports quantifier elimination in general but does not source-match the asserted algebraic sample representation or the stated (Lambda_0 s D)^{2^{O(k)}} bit bound."
reusable_artifacts:
  - "discovery/core.json: exact RDIM quadratic-risk reduction, marked-coefficient sufficiency, rational output-size bound, forest oracle, SDP and simulation consequences"
  - "discovery/solve_thm_forest_oracle.json: derivation record for the exact polynomial-time forest oracle"
  - "discovery/writeup.tex: full derivation note and the unresolved separator-compression/XP boundary"
  - "discovery/proto_core.json: accepted proposal, literature map, consumer framing, and presolve evidence"
seeds_burned:
  - index: 0
    one_liner: "seed-fpt-dichotomy"
    reason: "The separator-compression angle ended with only a forest oracle and an XP diagnostic; the proposed hardness retry restated the open branch without a source problem, gadget, coefficient identity, or treewidth map."
proof_attempt_summary: |
  The run derived the exact RDIM quadratic-risk representation, reduced its entries to one- and two-marked isolated-set coefficients, and closed an exact polynomial-time forest oracle together with standard SDP and Monte Carlo consequences. The field-bearing step collapsed because the bounded-treewidth join retained an XP-size multivariate message, while the alternative hardness branch never acquired a source problem, gadget, coefficient identity, or treewidth-preserving reduction. Future work should reuse the forest derivation and exact-risk setup, but must independently solve that separator frontier and must not reuse the underspecified Renegar algebraic-output claim without a precise source or a narrower theorem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 12988674
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 12988674
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_awri_mixture_minimax_certificate / v1 — Downgraded

**Topic.** Certified exact-risk weighted-random-isolation design for network total effects. For a fixed directed interference graph, its undirected WRI conflict graph C_G, bounded positive integer priority weights, fixed full-neighborhood potential outcomes, and a prespecified finite rule library, write the RDIM error as a 2n-dimensional random linear form and compute each dense risk matrix Q_l exactly. Prove an output-sensitive L n^2 2^{O(w log(w+1))} poly(n,b) algorithm from a width-w tree decomposition by integrating priority-order and reciprocal-count messages, including correctness and bit complexity. Over the graph ellipsoid defined by diag((I+gamma L_C)^{-1},(I+gamma L_C)^{-1}), return the minimax rule mixture, least-favourable endpoint distribution, and primal-dual optimality certificate. For arbitrary graphs give simultaneous operator-norm Monte Carlo regions and a certified worst-case-risk gap. Consumer: a universal-financial-education versus none follow-up to Cai, de Janvry, and Sadoulet's rural-China insurance diffusion experiment. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Every RDIM risk entry was reduced to one- and two-marked isolated-set count probabilities, including odd counts and bias. Integer-weight risks have polynomial output bit length, and a three-state polynomial recurrence was derived and checked by exact enumeration on three forests and 344 matrix entries. Two bidirected three-leaf stars force isolated-set size two; reciprocal hub/leaf rules produce distinct verified risks. Checks covered local-max versus sequential greedy semantics, directed-star legality, parity denominators, rationality, PSD ellipsoid, generic SDP reduction, treewidth hardness, and recent design papers. UNRESOLVED BOTTLENECK: Compress joined separator priority/count messages to 2^{O(w log(w+1))} poly(n,b) size; the direct construction retains (nb)^{O(w)} coefficients and proves only XP complexity. EARLY KILL TEST: On all width-two/three graphs with n≤9 and weights in {1,2,3}, compare every tagged coefficient with exhaustive priority ordering, then derive the symbolic message-size recurrence; any unavoidable (nb)^w factor or parameter-preserving hardness obstruction kills the promised FPT kernel and forces pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_awri_mixture_minimax_certificate.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** neither the claimed fixed-parameter exact-risk algorithm nor the alternative parameterized-hardness boundary is proved

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The validity gate classified this as sound incremental work whose ambitious field kernel remains an open program, so `reraise_status: retry` is reserved for a genuinely new separator invariant or parameter-preserving hardness construction. The rural-China consumer was not instantiated with a concrete graph, rule library, or risk comparison in this run.
