---
qid: eid_limvam_fragment_hashcons_enumeration
spec: v1
topic: "Output-sensitive exact-once enumeration of distinct coefficient tuples for the component-aligned Gaussian LiMVAM calibration frontier. This is a new attempt at parent eid_limvam_calibration_frontier: replace its failed completed-path quotient and unavailable child oracle by accumulated immutable original-label regression rows. Build and prune the 2^p removed-set compatibility DAG, intern exact edge rows, merge identical fragments at each removed set, prove the live-fragment right congruence and projection-to-output bound, and emit Theta_G(O_G) once per numerical tuple with common union-support ancestry in O(poly(p,m) 2^p max{1,N_out}) ordered-exact-real time and space. Keep the parent's model-valid arbitrary-pairing scope and reuse its covariance-region inference only; do not claim unrestricted LiMVAM, polynomial-delay, off-model nonchordal preprocessing, or continuum-region enumeration. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the immutable row formula b(A,r)=Sigma[r,A]Sigma[A,A]^-1, proved that after source-to-sink pruning equal fragments at fixed A have identical completion sets and unequal fragments are completion-disjoint, and charged each bucket to at most N_out sink tuples. Deterministic exact row interning and integer-fragment tries avoid a real-hash oracle. The nonzero p=3 witness has exactly orders 123,132,213 and one tuple; exact checks passed 28 further cases and 654 permutations, including 24 orders collapsing to one tuple. Checks addressed Schur-slope confusion, dead prefixes, late collisions, empty graphs/outputs, exact equality, singular boundaries, and the off-model nonchordal obstruction. UNRESOLVED BOTTLENECK: Fully verify the composition of arbitrary-graph q-path exactness with coordinate-noise positive-definite completion on maintained-model inputs; no model-specific algebraic lemma otherwise remains open informally. EARLY KILL TEST: Independently implement rational p<=4 exhaustive order comparison, requiring every merged prefix completion set and every bucket bound to match; any mismatch stops the run instead of reverting to order enumeration. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_limvam_fragment_hashcons_enumeration.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "A field-tier version would need a new faithful global cross-subset output-equivalence or canonical-representative method eliminating explicit 2^p preprocessing without assuming the quotient oracle; the zero-system suffix-language witness rules this out for the current deterministic removed-set automaton."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The pairing-informative result applies only to the note-defined component-aligned subclass with cross-coordinate orthogonality and positive-definite coordinate blocks."
  - "The algorithm still constructs an explicit 2^p subset space even when the numerical output is a singleton."
  - "Thus the advertised output sensitivity is only a multiplicative refinement of a subset-exponential algorithm, not conventional output-polynomial enumeration or polynomial delay."
reusable_artifacts:
  - "discovery/core.json — sound two-layer published-class boundary and component-aligned q-path/enumeration theorem graph"
  - "discovery/writeup.tex — complete mathematical derivation and complexity accounting"
  - "reviews/review_general.json — cold-tier assessment and field-floor obstruction"
  - "orchestrator/decision_log.jsonl — maximality audits, zero-system suffix-language witness, and pipeline repair receipts"
seeds_burned: []
proof_attempt_summary: |
  The run proved the published-class all-orders/empty-ancestry boundary and, for the component-aligned refinement, exact q-path fiber characterization plus exact-once tuple and ancestry enumeration with explicit subset-exponential exact-real and rational bit bounds. The field-tier claim collapsed because a zero system has one numerical output but 2^p distinct removed-set suffix languages, so the current deterministic prefix/completion automaton cannot eliminate its explicit subset lattice. A future field-tier attempt needs a genuinely new global output-equivalence or canonical-representative construction rather than an assumed quotient oracle.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 50726165
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# eid_limvam_fragment_hashcons_enumeration / v1 — Downgraded

**Topic.** Output-sensitive exact-once enumeration of distinct coefficient tuples for the component-aligned Gaussian LiMVAM calibration frontier. This is a new attempt at parent eid_limvam_calibration_frontier: replace its failed completed-path quotient and unavailable child oracle by accumulated immutable original-label regression rows. Build and prune the 2^p removed-set compatibility DAG, intern exact edge rows, merge identical fragments at each removed set, prove the live-fragment right congruence and projection-to-output bound, and emit Theta_G(O_G) once per numerical tuple with common union-support ancestry in O(poly(p,m) 2^p max{1,N_out}) ordered-exact-real time and space. Keep the parent's model-valid arbitrary-pairing scope and reuse its covariance-region inference only; do not claim unrestricted LiMVAM, polynomial-delay, off-model nonchordal preprocessing, or continuum-region enumeration. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the immutable row formula b(A,r)=Sigma[r,A]Sigma[A,A]^-1, proved that after source-to-sink pruning equal fragments at fixed A have identical completion sets and unequal fragments are completion-disjoint, and charged each bucket to at most N_out sink tuples. Deterministic exact row interning and integer-fragment tries avoid a real-hash oracle. The nonzero p=3 witness has exactly orders 123,132,213 and one tuple; exact checks passed 28 further cases and 654 permutations, including 24 orders collapsing to one tuple. Checks addressed Schur-slope confusion, dead prefixes, late collisions, empty graphs/outputs, exact equality, singular boundaries, and the off-model nonchordal obstruction. UNRESOLVED BOTTLENECK: Fully verify the composition of arbitrary-graph q-path exactness with coordinate-noise positive-definite completion on maintained-model inputs; no model-specific algebraic lemma otherwise remains open informally. EARLY KILL TEST: Independently implement rational p<=4 exhaustive order comparison, requiring every merged prefix completion set and every bucket bound to match; any mismatch stops the run instead of reverting to order enumeration. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_limvam_fragment_hashcons_enumeration.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** The pairing-informative result applies only to the component-aligned subclass and retains explicit 2^p subset-state dependence, so the sound two-layer theorem is subfield rather than field tier.

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
