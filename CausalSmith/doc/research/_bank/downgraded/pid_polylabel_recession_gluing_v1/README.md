---
qid: pid_polylabel_recession_gluing
spec: v1
topic: "Quantitative weighted recession gluing for honest polyhedral-label inference. For a fully encoded finite-label Gaussian experiment on an unbounded rational-polyhedral fan, prove effective compatibility-density: every globally honest near-minimizer admits a finite core and recession library whose Gaussian-weighted path discrepancies, chart errors, tails, and weight-variation remainders vanish with a computable input-dependent modulus. Build CertGluePFL, a terminating outward-rounded primal-dual algorithm with complete rational geometry, covariance, loss-scale, accuracy, Gaussian-integration, and bit-cost receipts. Prove fixed-stratum, moving-offset, and compact-exhaustion multinomial transfer, and instantiate survivor-complier ordered-wage quantile labels for the Chen--Flores Job Corps setting under M_ASC>=m_*>0. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh presolve derived kernel-independent Gaussian smoothing error s^2 sqrt(d/8), tangential averaging error ||a||_1/T, weighted path and exact coverage-repair inequalities, and an explicit compatible recession representation. Exact rational checks gave contact risk 14/15, preserved four-label r=4 and nine-label r=6 strict gains, and improved the rigorous eta=.05,r=2 enclosure to 0.361100<=M<=0.813799. Destructive checks covered seam-centered means, oscillatory rules, metric rescaling, covariance encoding, escaping dual mass, recursion, moving offsets, and target positivity without finding a model-level counterexample or literature collision. UNRESOLVED BOTTLENECK: Prove simultaneous ECD across the full recession incidence diagram with an input-computable refinement modulus and then derive global certificate convergence and complete termination recurrences. EARLY KILL TEST: On the exact four-label eta=.05,r=2 fan, emit an executable honest primal and finite atomic dual with outward-rounded gap<=.001 after charging every chart, seam, protected-neighborhood integral, tail, covariance error, and repair; the current width is .452699. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_polylabel_recession_gluing.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised input-computable effective compatibility-density construction, unconditional CertGluePFL termination, and <=0.001 four-label certificate were not delivered; only common-ray coherence, compact Carter transfer, global minimax liminf, and diagonal-window convergence survived."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The unconditional results establish atomic dual exhaustion, local smoothing and averaging inequalities, compact Carter transfer, coordinatewise causal endpoint attainment, and windowed minimax convergence, but they do not establish the advertised quantitative recession-gluing construction."
  - "Effective compatible density is left open, so CertGluePFL termination, replayable moving-offset Gaussian rules, and global certified upper bounds remain conditional; only a global liminf and a window-restricted two-sided limit are proved."
  - "The four-label test still has the very wide certified interval [0.361100, 0.813799], so the proposed certification method lacks even its stated bounded-instance validation."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_oeq_effective_compatible_density.tex
  - discovery/solve_thm_attainment_atomic_duality.tex
  - discovery/solve_thm_compact_exhaustion_transfer.tex
  - discovery/writeup.tex
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Discovery attempted to derive a simultaneous, effective recession-incidence gluing theorem and use it to obtain a terminating CertGluePFL primal-dual certificate and global multinomial transfer. Review preserved common-ray coherence, compact Carter comparison, a global minimax lower limit, and two-sided convergence on diagonal expanding windows, but the five effective-compatible-density obligations and the promised four-label milliscale certificate remained open. A correctable sign error also remains in equations (7)-(8) of the atomic-duality derivation, and the Carter/BFFL source attestations were not accepted by the pipeline before termination.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 71060714
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 71060714
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# pid_polylabel_recession_gluing / v1 — Downgraded

**Topic.** Quantitative weighted recession gluing for honest polyhedral-label inference. For a fully encoded finite-label Gaussian experiment on an unbounded rational-polyhedral fan, prove effective compatibility-density: every globally honest near-minimizer admits a finite core and recession library whose Gaussian-weighted path discrepancies, chart errors, tails, and weight-variation remainders vanish with a computable input-dependent modulus. Build CertGluePFL, a terminating outward-rounded primal-dual algorithm with complete rational geometry, covariance, loss-scale, accuracy, Gaussian-integration, and bit-cost receipts. Prove fixed-stratum, moving-offset, and compact-exhaustion multinomial transfer, and instantiate survivor-complier ordered-wage quantile labels for the Chen--Flores Job Corps setting under M_ASC>=m_*>0. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh presolve derived kernel-independent Gaussian smoothing error s^2 sqrt(d/8), tangential averaging error ||a||_1/T, weighted path and exact coverage-repair inequalities, and an explicit compatible recession representation. Exact rational checks gave contact risk 14/15, preserved four-label r=4 and nine-label r=6 strict gains, and improved the rigorous eta=.05,r=2 enclosure to 0.361100<=M<=0.813799. Destructive checks covered seam-centered means, oscillatory rules, metric rescaling, covariance encoding, escaping dual mass, recursion, moving offsets, and target positivity without finding a model-level counterexample or literature collision. UNRESOLVED BOTTLENECK: Prove simultaneous ECD across the full recession incidence diagram with an input-computable refinement modulus and then derive global certificate convergence and complete termination recurrences. EARLY KILL TEST: On the exact four-label eta=.05,r=2 fan, emit an executable honest primal and finite atomic dual with outward-rounded gap<=.001 after charging every chart, seam, protected-neighborhood integral, tail, covariance error, and repair; the current width is .452699. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_polylabel_recession_gluing.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 general referee: meets_floor=false, tier=incremental, paper_score_ceiling 5.4 < field gate 7.4, salvageable=false; effective compatible density and the four-label milliscale certificate remain unresolved.

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
