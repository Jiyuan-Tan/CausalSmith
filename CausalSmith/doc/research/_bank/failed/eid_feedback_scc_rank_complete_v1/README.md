---
qid: eid_feedback_scc_rank_complete
spec: v1
topic: "Complete comparator-parent Hall certificates for Gaussian feedback-module identification. Let K and O range over labeled noncomplete orientations of simple graphs on p≥4 vertices. For equal labeled outdegrees but different SCC partitions, define the local dependency digraph D_i(K,O): j→h when j is a K-child of i and h is both a K-parent of j and an O-neighbor of i. With P=ch_K(i)\\ch_O(i), Q=ch_O(i)\\ch_K(i), and Γ_i linking P to Q by D_i reachability, prove the all-size compatibility theorem H★: if every Γ_i(K,O) and Γ_i(O,K) has a perfect matching then SCC(K)=SCC(O). Equivalently, some order and vertex has a positive Hall deficiency, yielding a polynomial-time comparator-parent closed set L with a strict child-count gap. Prove that this certificate gives an explicit precision-Jacobian rank gap by the incoming-star minor, combine it with unequal-outdegree separation, and show a minimum-dimension compatible covariance-model selector generically recovers the true SCC partition. On each fixed compact Gaussian SEM family with stability, edge, eigenvalue, and cross-SCC covariance-separation margins, derive uniform covariance-minimum-distance consistency, honest split-sample SCC supersets, and union equilibrium-effect intervals. Consumer: within-regime Sachs et al. single-cell signaling-network analysis under an explicitly prospective homogeneous iid homoscedastic Gaussian oriented-network approximation; reciprocal arcs and regime pooling are outside scope. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The corrected precision-rank theorem was independently derived and its four-node rank-4-versus-5 witness recomputed exactly. Certificate optimization reduces exactly to |P| minus the maximum matching size in Γ_i, giving a polynomial search algorithm. H★ is proved for graph pairs differing in one outgoing row and for maximum-outdegree-one graphs. Exhaustive p=4 checks, the inherited complete p=5 check, a seeded 100,000-pair p=6–8 test, and 16,455 adversarial states through p=12 found no missing certificate; reciprocal-edge counterexamples confirm that the oriented-simple boundary matters. Searches found no corrected-certificate collision. The accessible arXiv-v1 construction leak is established, but the final journal equations remain unaudited and no broader correction is claimed. UNRESOLVED BOTTLENECK: Prove H★ for arbitrary multiple-tail disagreements by showing that two-sided local perfect matchings force equality of global SCC reachability, or produce another universal precision-variety separator. EARLY KILL TEST: Search dense-block SCC-discordant pairs for perfect matchings in every one of the 2p auxiliary graphs; one such pair refutes comparator-parent completeness and must pivot the run, though it is not by itself a counterexample to SCC identifiability. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_feedback_scc_rank_complete.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The load-bearing all-size H★ compatibility theorem is false, and the suggested certificate-separation replacement only assumes the missing conclusion rather than repairing it."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The explicit seven-vertex pair has equal labeled outdegrees and perfect matchings in all fourteen local Hall graphs but different SCC partitions, so the universal positive implication is false."
  - "REVIEW: assume-the-crux narrowing — a new assume/suppose premise may promote the open obligation into a hypothesis (state the result and leave the construction an open obligation instead)."
reusable_artifacts:
  - "discovery/solve_thm_generic_scc_recovery.tex — explicit verified seven-vertex H★ counterexample, including arc lists and all local perfect matchings"
seeds_burned: []
proof_attempt_summary: |
  The run attempted to prove the all-size two-sided Hall-compatibility theorem H★ and use it as the universal separator supporting generic SCC recovery. The solver instead produced a verified seven-vertex oriented-simple counterexample with equal labeled outdegrees, zero Hall deficiency in both orders, and different SCC partitions; the independent validity gate confirmed that replacing H★ by a familywise separation assumption would only assume the missing conclusion. Unequal-outdegree and positive-deficiency cases remain valid sufficient cases, while a genuinely different universal precision/Jacobian separator is open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 9301819
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 9301819
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_feedback_scc_rank_complete / v1 — Failed

**Topic.** Complete comparator-parent Hall certificates for Gaussian feedback-module identification. Let K and O range over labeled noncomplete orientations of simple graphs on p≥4 vertices. For equal labeled outdegrees but different SCC partitions, define the local dependency digraph D_i(K,O): j→h when j is a K-child of i and h is both a K-parent of j and an O-neighbor of i. With P=ch_K(i)\ch_O(i), Q=ch_O(i)\ch_K(i), and Γ_i linking P to Q by D_i reachability, prove the all-size compatibility theorem H★: if every Γ_i(K,O) and Γ_i(O,K) has a perfect matching then SCC(K)=SCC(O). Equivalently, some order and vertex has a positive Hall deficiency, yielding a polynomial-time comparator-parent closed set L with a strict child-count gap. Prove that this certificate gives an explicit precision-Jacobian rank gap by the incoming-star minor, combine it with unequal-outdegree separation, and show a minimum-dimension compatible covariance-model selector generically recovers the true SCC partition. On each fixed compact Gaussian SEM family with stability, edge, eigenvalue, and cross-SCC covariance-separation margins, derive uniform covariance-minimum-distance consistency, honest split-sample SCC supersets, and union equilibrium-effect intervals. Consumer: within-regime Sachs et al. single-cell signaling-network analysis under an explicitly prospective homogeneous iid homoscedastic Gaussian oriented-network approximation; reciprocal arcs and regime pooling are outside scope. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The corrected precision-rank theorem was independently derived and its four-node rank-4-versus-5 witness recomputed exactly. Certificate optimization reduces exactly to |P| minus the maximum matching size in Γ_i, giving a polynomial search algorithm. H★ is proved for graph pairs differing in one outgoing row and for maximum-outdegree-one graphs. Exhaustive p=4 checks, the inherited complete p=5 check, a seeded 100,000-pair p=6–8 test, and 16,455 adversarial states through p=12 found no missing certificate; reciprocal-edge counterexamples confirm that the oriented-simple boundary matters. Searches found no corrected-certificate collision. The accessible arXiv-v1 construction leak is established, but the final journal equations remain unaudited and no broader correction is claimed. UNRESOLVED BOTTLENECK: Prove H★ for arbitrary multiple-tail disagreements by showing that two-sided local perfect matchings force equality of global SCC reachability, or produce another universal precision-variety separator. EARLY KILL TEST: Search dense-block SCC-discordant pairs for perfect matchings in every one of the 2p auxiliary graphs; one such pair refutes comparator-parent completeness and must pivot the run, though it is not by itself a counterexample to SCC identifiability. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_feedback_scc_rank_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The explicit seven-vertex pair has equal labeled outdegrees and perfect matchings in all fourteen local Hall graphs but different SCC partitions, so the universal positive implication is false.

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
