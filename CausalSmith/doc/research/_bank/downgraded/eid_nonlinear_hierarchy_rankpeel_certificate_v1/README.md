---
qid: eid_nonlinear_hierarchy_rankpeel_certificate
spec: v1
topic: "Quadratic-query reconstruction certificates for nonlinear latent hierarchies. On the unchanged Prashant--Ng--Zhang--Huang ICLR 2025 scalar layered-DAG class with two pure children per latent, equal measured-descendant path lengths, differentiability, conditional sufficiency, and generalized rank faithfulness, construct deterministic RankPeel using only essential-supremum ranks of observed conditional-mean Jacobians. Prove exact parentless detection, <=1 pairwise recovery of every pure block, the representative neutrality iff Pa(c) subset P, recursive full-adjacency recovery up to within-layer permutation, at most p^2+p oracle calls, O(p^3) bookkeeping, and an oracle-relative replayable certificate. Use query-specific private-path lower bounds and restricted pure-surrogate separator upper bounds; do not assume a blanket rank=minimum-separator identity, faithfulness inheritance after latent contraction, an extra saturated-rank condition, or practical CelebA consistency. PRESOLVE EVIDENCE REQUIRING VERIFICATION: disjoint private-path and restricted surrogate-separation arguments derive the exact rank k versus k+1 parent test at every level; 4,408 exact multilevel rational rank checks, a 36-vertex/39-edge reconstruction in 362 calls, and 192 representative-choice cases passed, while isolated blocks, parentless vertices, proportional unfaithful twins, discarded mixed descendants, correlated parents, and misleading blanket separator identities were checked. UNRESOLVED BOTTLENECK: independently validate the anchor's conditional separator-to-Jacobian-rank upper bound under its exact Conditions 1--3. EARLY KILL TEST: enumerate the specified 676 three-level DAGs with two extra mixed measured children and verify every proposed surrogate cut by exact d-separation; any legal counterexample stops the proof. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/eid_nonlinear_hierarchy_rankpeel_certificate.strongest_form.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposal promised quadratic-query RankPeel on the unchanged PNHZ class, but the sound reconstruction theorem requires positive-density/open-support or execution-local jet/fibre assumptions and is therefore only incremental."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proposal promised RankPeel on the unchanged PNHZ class … but the usable headline result adds … positive-density hypotheses and therefore proves a strict-subclass kernel instead."
  - "No faithful bounded same-topic/same-assumptions repair exists: the admitted thin-support witness refutes the all-C1-version law-rank functional under Conditions 1–3."
  - "The cold D0.5.G outcome is tier=incremental, meets_floor=false against floor=field, paper_score_ceiling=5.6<7.2, salvageable=false after the gate, flagship_potential=false."
reusable_artifacts:
  - "discovery/core.json — discharged strict-subclass RankPeel theorem graph and analytic boundary result."
  - "discovery/solve_oeq_analytic_boundary.json — thin-support conditional-version counterexample."
  - "discovery/solve_lem_restricted_separator_upper.json — restricted separator upper-bound proof attempt."
  - "discovery/solve_thm_exact_neutrality.json — canonical execution-local neutrality proof."
  - "discovery/writeup.tex — complete mathematical derivation and scope boundary."
seeds_burned:
  - index: 0
    one_liner: "Certified quadratic-query RankPeel reconstruction"
    reason: "The sole RankPeel angle was exhausted when its unchanged-class oracle was refuted by conditional-version instability; support regularity yields only a substituted strict-subclass kernel."
proof_attempt_summary: |
  The run derived and adjudicated a deterministic RankPeel procedure with quadratic
  oracle-query order, canonical neutrality, replay certificates, and a restricted
  separator proof. A legal thin-support SEM then showed that the all-C¹-version
  conditional-mean Jacobian rank is not an observed-law functional under the promised
  unchanged Conditions 1–3. Positive-density/open-support and execution-local
  jet/fibre assumptions recover a sound strict-subclass theorem, but that substituted
  kernel was graded incremental and could not meet the field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 22683917
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 22683917
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_nonlinear_hierarchy_rankpeel_certificate / v1 — Downgraded

**Topic.** Quadratic-query reconstruction certificates for nonlinear latent hierarchies. On the unchanged Prashant--Ng--Zhang--Huang ICLR 2025 scalar layered-DAG class with two pure children per latent, equal measured-descendant path lengths, differentiability, conditional sufficiency, and generalized rank faithfulness, construct deterministic RankPeel using only essential-supremum ranks of observed conditional-mean Jacobians. Prove exact parentless detection, <=1 pairwise recovery of every pure block, the representative neutrality iff Pa(c) subset P, recursive full-adjacency recovery up to within-layer permutation, at most p^2+p oracle calls, O(p^3) bookkeeping, and an oracle-relative replayable certificate. Use query-specific private-path lower bounds and restricted pure-surrogate separator upper bounds; do not assume a blanket rank=minimum-separator identity, faithfulness inheritance after latent contraction, an extra saturated-rank condition, or practical CelebA consistency. PRESOLVE EVIDENCE REQUIRING VERIFICATION: disjoint private-path and restricted surrogate-separation arguments derive the exact rank k versus k+1 parent test at every level; 4,408 exact multilevel rational rank checks, a 36-vertex/39-edge reconstruction in 362 calls, and 192 representative-choice cases passed, while isolated blocks, parentless vertices, proportional unfaithful twins, discarded mixed descendants, correlated parents, and misleading blanket separator identities were checked. UNRESOLVED BOTTLENECK: independently validate the anchor's conditional separator-to-Jacobian-rank upper bound under its exact Conditions 1--3. EARLY KILL TEST: enumerate the specified 676 three-level DAGs with two extra mixed measured children and verify every proposed surrogate cut by exact d-separation; any legal counterexample stops the proof. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/eid_nonlinear_hierarchy_rankpeel_certificate.strongest_form.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** No faithful bounded same-topic/same-assumptions repair exists: the admitted thin-support witness refutes the all-C1-version law-rank functional under Conditions 1--3; the positive-density strict-subclass result is incremental.

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
