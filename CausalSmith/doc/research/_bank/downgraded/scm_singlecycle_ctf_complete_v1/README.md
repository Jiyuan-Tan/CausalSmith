---
qid: scm_singlecycle_ctf_complete
spec: v1
topic: "Source-aware completeness for conditional counterfactual identification in single-cycle simple SCMs. Fix finite alphabets and a semi-Markovian simple SCM class in which every nontrivial directed SCC is an induced chordless cycle, every consolidated district contains at most one such original cycle, and every endogenous-subset intervention has a unique solution. Given any finite menu of complete observational and perfect-interventional laws and an unnested positive-denominator conditional counterfactual query, construct SC-CTFID. It must return a rational arithmetic circuit in the supplied regime probabilities iff the query is uniformly identified; otherwise it must return a finite certificate and two same-alphabet simple SCMs with the declared sparse latent-source incidence that agree on every supplied law but disagree on the query. Preserve original-cycle labels across merged worlds, reduce to acyclic CTFID, and make the terminal test cardinality- and source-aware rather than an unrestricted response-table row-space test. State termination and complexity for explicit legal response-table input. Add multinomial plug-in influence-function and simultaneous confidence-region inference under positive margins, with degenerate exact cells reported separately. Consumer: the cfid R package, which currently supports acyclic ID*/IDC* parallel-world graphs and would gain a formula-or-certified-failure feedback mode. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivations characterize legal chordless-cycle response tables and prove the binary count 4^m-2^m. For a three-cycle with latent path sources, realizability is legal support plus endpoint-table independence; on alphabets (2,2,3), 240 legal profiles produce four source-induced product identities outside unrestricted row span. Across 32 binary menus and 386 conditional pairs per menu, checks found 4,112 identified cases and 8,240 positive rational separators. A two-district construction preserves 81 intervention laws while moving the downstream query from 1/3 to 3/8. A CHSH obstruction shows why unrestricted-table gluing is invalid and must remain excluded. UNRESOLVED BOTTLENECK: Prove sparse-source rational terminal completeness with preserved boundary interfaces: constant target ratios on every legal source-realizable fiber must descend to rational circuits, while nonconstant fibers must yield source-preserving separators that survive recursive gluing. EARLY KILL TEST: Reproduce the 240-profile mixed-alphabet product identities, the complete binary regression suite, legal separators, the CHSH rejection, and the two-district transmitter; any false failure, illegal separator, or nonrational uniformly identified target stops the program. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_singlecycle_ctf_complete.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The arbitrary-menu source-aware completeness theorem and same-alphabet separator compiler were not delivered; universal source-preserving boundary transmission remains open, cycle-legality overclaimed the empty intervention, and the advertised 1/3-to-3/8 transmission witness was unreproduced."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "kernel_substituted@thm:sc-ctfid-completeness — the promised formula-or-same-class-certificate completeness theorem is not delivered; the proved replacement is a rational-output impossibility permitting O while universal source-preserving transmission remains open."
  - "The result is instance-relative, its declared reverse cycle edge is inactive, and the proposed algebraic-output plus universal-transmission upgrade is unproved and load-bearing."
  - "thm:cycle-legality: 'every proper intervention breaks the cycle' is false for the empty intervention; only a nonempty proper intervention breaks it."
  - "lem:boundary-interface-gluing: the stress test invokes do(S=0/1) although S is not an endogenous intervention variable and supplies no structural link from the perturbed upstream event, so the advertised 1/3-to-3/8 transmission witness is unreproduced."
reusable_artifacts:
  - "discovery/core.json — synchronized instance-relative obstruction, legal response-table facts, and remaining universal-transmission open question."
  - "discovery/solve_thm_sc_ctfid_completeness.json — solver derivation and audit trail for the ternary fixed-decoder algebraic-branch counterexample."
  - "discovery/solve_tex/solve_thm_sc_ctfid_completeness.tex — rendered proof attempt for the rational-output obstruction."
seeds_burned: []
proof_attempt_summary: |
  The run attempted a complete arbitrary-menu rational-circuit-or-countermodel calculus for finite-alphabet single-cycle simple SCMs, including source-aware terminal descent and recursive separator transmission. A fixed-decoder ternary instance instead produced the identified algebraic branch x = sqrt(ab/c), proving that rational positive outputs and genuine same-instance negative certificates cannot form a complete two-outcome procedure; this sound obstruction is only incremental and is not intrinsically cyclic. A field-tier continuation would require a new semialgebraic/algebraic output language plus a proof of universal source-preserving boundary transmission, while the cycle-legality and explicit transmission-witness defects also remain to be repaired.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24906439
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24906439
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# scm_singlecycle_ctf_complete / v1 — Downgraded

**Topic.** Source-aware completeness for conditional counterfactual identification in single-cycle simple SCMs. Fix finite alphabets and a semi-Markovian simple SCM class in which every nontrivial directed SCC is an induced chordless cycle, every consolidated district contains at most one such original cycle, and every endogenous-subset intervention has a unique solution. Given any finite menu of complete observational and perfect-interventional laws and an unnested positive-denominator conditional counterfactual query, construct SC-CTFID. It must return a rational arithmetic circuit in the supplied regime probabilities iff the query is uniformly identified; otherwise it must return a finite certificate and two same-alphabet simple SCMs with the declared sparse latent-source incidence that agree on every supplied law but disagree on the query. Preserve original-cycle labels across merged worlds, reduce to acyclic CTFID, and make the terminal test cardinality- and source-aware rather than an unrestricted response-table row-space test. State termination and complexity for explicit legal response-table input. Add multinomial plug-in influence-function and simultaneous confidence-region inference under positive margins, with degenerate exact cells reported separately. Consumer: the cfid R package, which currently supports acyclic ID*/IDC* parallel-world graphs and would gain a formula-or-certified-failure feedback mode. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivations characterize legal chordless-cycle response tables and prove the binary count 4^m-2^m. For a three-cycle with latent path sources, realizability is legal support plus endpoint-table independence; on alphabets (2,2,3), 240 legal profiles produce four source-induced product identities outside unrestricted row span. Across 32 binary menus and 386 conditional pairs per menu, checks found 4,112 identified cases and 8,240 positive rational separators. A two-district construction preserves 81 intervention laws while moving the downstream query from 1/3 to 3/8. A CHSH obstruction shows why unrestricted-table gluing is invalid and must remain excluded. UNRESOLVED BOTTLENECK: Prove sparse-source rational terminal completeness with preserved boundary interfaces: constant target ratios on every legal source-realizable fiber must descend to rational circuits, while nonconstant fibers must yield source-preserving separators that survive recursive gluing. EARLY KILL TEST: Reproduce the 240-profile mixed-alphabet product identities, the complete binary regression suite, legal separators, the CHSH rejection, and the two-district transmitter; any false failure, illegal separator, or nonrational uniformly identified target stops the program. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_singlecycle_ctf_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 decision referee: the promised formula-or-same-class-certificate completeness theorem is not delivered; the sound replacement is an instance-relative rational-output impossibility permitting O, graded incremental with paper_score_ceiling 5.4 below the field floor.

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
