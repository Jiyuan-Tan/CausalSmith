---
qid: eid_blocked_colour_rational_separation_complete
spec: v1
topic: "Binary-star separation certificates and complete equivalence for singleton-permitting blocked Gaussian DAGs. Revival of parent eid_blocked_colour_reversal_complete: replace its citation-dependent necessity bridge by the precise theorem that every static-signature mismatch is separated by a unit-noise covariance with at most two coefficient-one blocks at one target, integer entries bounded by p, and an exact CI-minor or cleared-regression certificate in {+/-1,+/-2}, yielding B(p)=ceil(log2 p). Prove this constructive certificate theorem together with covariance-model equality iff static-signature equality iff explicitly defined legal singleton covered-reversal connectivity; then give exact component enumeration and the qualified generic fixed-p BIC/simultaneous-effect inference rung. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact star formulas and exhaustive rational p<=4 checks separated 1,310,886 differing-signature pairs; a five-node extra-parent/two-reversal witness has cleared difference -1. UNRESOLVED BOTTLENECK: independently prove the all-p four-case router, especially mutual containment in the unequal-family reversed-edge case. EARLY KILL TEST: independently verify the router through p=4, then reproduce p=5 and stress all reversed-family pairs. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_blocked_colour_rational_separation_complete.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "Field-PASS discovery and the constructive equivalence/certificate core were formalized substantially, but the statistical recovery rung and one certificate vanishing bridge remain unverified because the required noncompact covariance-image geometry and elimination arguments are paper-specific research-scale cores."
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Needs noncompact blocked-covariance BIC consistency and elimination of comparison parameters; concept/type/goal CLI searches, lean_local_search, Mathlib leansearch/loogle, and the relevant API sections found only compact-model finiteCovarianceModel_populationGap/HasCompactDiscrepancySublevel and joint-parameter rationalMatrixMap_imageIntersection_locus, which do not compose because blocked covariance images are noncompact and the joint locus does not produce a nonzero polynomial solely on C's parameter space."
  - "Irreducible residual: proving unconditional Gaussian discrepancy compact sublevels plus relative closedness for every noncompact blocked covariance image, and eliminating the comparison parameter from the real joint algebraic locus to an exact nonzero zero-locus polynomial on the reference parameter space."
  - "Global positive-definite nonconstancy does not directly provide formal nonconstancy of the effect map restricted through rawCovParam."
reusable_artifacts:
  - "discovery/core.json and discovery/writeup.tex — field-PASS constructive separator, exact equivalence component, and sharp finite binary-star dictionary."
  - "formalization/plan.json and graph.json — reviewed 30-node proof decomposition and dependency graph."
  - "Lean output EID_BlockedColourRationalSeparationComplete_Research — discharged bounded separator, sharp dictionary, complete equivalence, Chickering gate, and paper-local Gaussian/rational adapters; three explicit sorries remain."
  - "Causalean.Stat.MEstimation.FiniteModelSelection and Causalean.Mathlib.MeasureTheory.PolynomialZeroLocus — first axiom-clean reusable study."
  - "Causalean.Stat.GaussianCovariance and Causalean.Mathlib.AlgebraicGeometry.{RationalMap,RationalDerivative} — second axiom-clean reusable study."
seeds_burned: []
proof_attempt_summary: |
  Discovery passed at field tier and formalization proved the constructive bounded binary-star separator, the sharp finite dictionary, the complete blocked-equivalence theorem, and the exact Chickering covered-reversal gate. Two independently verified Causalean studies and two paper-local adapter builds supplied finite-model selection, polynomial zero-locus, Gaussian discrepancy, rational intersection, and derivative-locus infrastructure. Fourteen subsequent F3 rounds still could not close three paper-specific obligations: noncompact blocked-covariance BIC recovery, its downstream simultaneous inference theorem, and certificate vanishing via comparison-parameter elimination/restricted rational nonconstancy; retry only with new architecture for those cores.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 257573432
  pipeline_claude_tokens: 5210669
  pipeline_tokens_consumed: 262784101
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# eid_blocked_colour_rational_separation_complete / v1 — Failed

**Topic.** Binary-star separation certificates and complete equivalence for singleton-permitting blocked Gaussian DAGs. Revival of parent eid_blocked_colour_reversal_complete: replace its citation-dependent necessity bridge by the precise theorem that every static-signature mismatch is separated by a unit-noise covariance with at most two coefficient-one blocks at one target, integer entries bounded by p, and an exact CI-minor or cleared-regression certificate in {+/-1,+/-2}, yielding B(p)=ceil(log2 p). Prove this constructive certificate theorem together with covariance-model equality iff static-signature equality iff explicitly defined legal singleton covered-reversal connectivity; then give exact component enumeration and the qualified generic fixed-p BIC/simultaneous-effect inference rung. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact star formulas and exhaustive rational p<=4 checks separated 1,310,886 differing-signature pairs; a five-node extra-parent/two-reversal witness has cleared difference -1. UNRESOLVED BOTTLENECK: independently prove the all-p four-case router, especially mutual containment in the unequal-family reversed-edge case. EARLY KILL TEST: independently verify the router through p=4, then reproduce p=5 and stress all reversed-family pairs. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_blocked_colour_rational_separation_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** substrate-unbuildable: two verified Causalean studies, two local adapters, and fourteen further F3 rounds still leave three load-bearing paper-specific proofs for noncompact blocked-covariance BIC consistency, comparison-parameter elimination, and restricted rational-effect nonconstancy.

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
