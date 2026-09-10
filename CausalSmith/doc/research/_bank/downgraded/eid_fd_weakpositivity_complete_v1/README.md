---
qid: eid_fd_weakpositivity_complete
spec: v1
topic: "Support-guarded complete causal-effect identification for finite DAGs with fixed alphabets, unknown non-root qualitative functional nodes, and joint treatment positivity. Construct a terminating F-ID+ algorithm that first returns an exact feasibility/infeasibility certificate, then on feasible inputs returns either a piecewise guarded arithmetic circuit for the full intervention distribution—with every division justified by a mechanically entailed support guard—or an exact finite same-observed-law/different-effect countermodel in the original alphabets. Prove soundness, completeness, an elementary complexity/output bound, empirical multinomial branch-respecting inference, and regular fixed-support Wald collapse where justified. Generic real quantifier elimination is allowed only for certificate verification, not as the identification algorithm. Use the binary Z→A→X, A→Y, X→Y model with hidden non-root A=f(Z): single-X has the presolved sharp law-specific rectangle, while joint (Z,X) is graphwide identified by P(Y|Z,X). Treat CRAN dosearch as the software consumer and distinguish Chen–Darwiche Theorem 18, Hwang positivity extraction, invariant-cut and CSI/state algorithms. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Enumerating deterministic functional-map tuples and assigning uniform CPTs elsewhere decides feasibility and returns rational models or finite polynomial contradiction certificates. On the binary witness, exhaustive checks over 8,748 models and 255 observed laws give a sharp product rectangle for single-X effects; a same-law pair reaches (0,0) and (1/2,1/2), while joint intervention on (Z,X) is identified by P(Y|Z,X). The actual dosearch 1.0.12 C++ core returns nonidentifiable on the bow and adjustment after removing it. Checks also exposed infeasible functional/positivity declarations, algebraic latent parameterizations, and the mismatch between the anchor's separate positivity/alphabet enlargement and this fixed-alphabet joint-positivity class; no checked follow-up closes the proposed converse. UNRESOLVED BOTTLENECK: Prove a cardinality-preserving guarded-district dichotomy over compatible functional-map, row-support, and algebraic strata that constructs one guarded target expression or an exact separating pair without generic quantifier elimination or alphabet enlargement. EARLY KILL TEST: On the binary four-node witness and its observed-A closure, require the recursion to recover the sharp single-X rectangle and counterpair, identify joint (Z,X), and reject the unrestricted observed-A joint query; failure without alphabet enlargement forces immediate revision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_fd_weakpositivity_complete.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note does not deliver the targeted graph-general complete F-ID+ algorithm: `thm:fixed-alphabet-four-output-front-end` may terminate with `Psi_U` and explicitly makes no identification verdict."
  - "This restriction leaves the headline general object open and caps the contribution at subfield."
  - "The coefficient-height proof drops a product term: (12) contains Q_theta(ell) P_theta(E0), a product of two network polynomials with up to h monomials each, so after simplex substitution its collected coefficients need not be bounded by 2h as claimed."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/d0_working.json
  - discovery/proof_archive/index.jsonl
  - reviews/review_general.json
  - reviews/review_rubric.json
  - reviews/review_math.json
seeds_burned: []
proof_attempt_summary: |
  The run constructed a graph-general four-output front end and proved exact feasibility,
  support propagation, guarded success cases, and support-hole countermodels, but the
  positive-support residual Psi_U still has no identification verdict. It also derived a
  sound arbitrary-support response-kernel fiber, rational original-alphabet attainment,
  the B_sat^0 cardinality elbow, sharp single-X projection, joint-positive collapse, and
  branch-respecting inference for the four-node hidden-functional family. Reaching field
  tier still requires a cardinality-preserving graph-general converse without generic QE;
  the local h^2/degree-2d output-bound bookkeeping defect should also be repaired on reuse.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 50318859
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# eid_fd_weakpositivity_complete / v1 — Downgraded

**Topic.** Support-guarded complete causal-effect identification for finite DAGs with fixed alphabets, unknown non-root qualitative functional nodes, and joint treatment positivity. Construct a terminating F-ID+ algorithm that first returns an exact feasibility/infeasibility certificate, then on feasible inputs returns either a piecewise guarded arithmetic circuit for the full intervention distribution—with every division justified by a mechanically entailed support guard—or an exact finite same-observed-law/different-effect countermodel in the original alphabets. Prove soundness, completeness, an elementary complexity/output bound, empirical multinomial branch-respecting inference, and regular fixed-support Wald collapse where justified. Generic real quantifier elimination is allowed only for certificate verification, not as the identification algorithm. Use the binary Z→A→X, A→Y, X→Y model with hidden non-root A=f(Z): single-X has the presolved sharp law-specific rectangle, while joint (Z,X) is graphwide identified by P(Y|Z,X). Treat CRAN dosearch as the software consumer and distinguish Chen–Darwiche Theorem 18, Hwang positivity extraction, invariant-cut and CSI/state algorithms. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Enumerating deterministic functional-map tuples and assigning uniform CPTs elsewhere decides feasibility and returns rational models or finite polynomial contradiction certificates. On the binary witness, exhaustive checks over 8,748 models and 255 observed laws give a sharp product rectangle for single-X effects; a same-law pair reaches (0,0) and (1/2,1/2), while joint intervention on (Z,X) is identified by P(Y|Z,X). The actual dosearch 1.0.12 C++ core returns nonidentifiable on the bow and adjustment after removing it. Checks also exposed infeasible functional/positivity declarations, algebraic latent parameterizations, and the mismatch between the anchor's separate positivity/alphabet enlargement and this fixed-alphabet joint-positivity class; no checked follow-up closes the proposed converse. UNRESOLVED BOTTLENECK: Prove a cardinality-preserving guarded-district dichotomy over compatible functional-map, row-support, and algebraic strata that constructs one guarded target expression or an exact separating pair without generic quantifier elimination or alphabet enlargement. EARLY KILL TEST: On the binary four-node witness and its observed-A closure, require the recursion to recover the sharp single-X rectangle and counterpair, identify joint (Z,X), and reject the unrestricted observed-A joint query; failure without alphabet enlargement forces immediate revision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_fd_weakpositivity_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Field-floor terminal: the graph-general F-ID+ front-end retains an explicit positive-support residual with no identification verdict; the sound categorical four-node theorem achieves subfield tier. review_math also records a local output-bound h^2/degree-2d bookkeeping defect that does not affect the tier verdict.

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
