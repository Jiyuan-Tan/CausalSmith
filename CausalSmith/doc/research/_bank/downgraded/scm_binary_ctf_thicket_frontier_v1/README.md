---
qid: scm_binary_ctf_thicket_frontier
spec: v1
topic: "Closed-form sharp multi-regime effect bounds for a two-source binary collider SCM. Let X,Z,Y be binary in the recursive graph X→Y←Z with two mutually independent latent roots shared along X↔Y and Z↔Y and independent private outcome noise. Given normalized strictly positive tables A(x,y)=P(X=x,Y=y | do(Z=0)) and B(z,y)=P(Z=z,Y=y | do(X=0)), set p=A(0,0)+A(0,1), r=B(0,0)+B(0,1), a=A(0,1), and b=B(0,1). Prove compatibility iff -(1-p)r≤a-b≤p(1-r), and prove that q=P(Y=1 | do(X=0,Z=0)) has the sharp interval [max{a,b,a+b-pr}, min{a+1-p,b+1-r,a+b+(1-p)(1-r)}]. Construct source-preserving finite SCMs attaining every real interval point and rational endpoint certificates for rational inputs. Give the constant-time compatibility/endpoint procedure and an optional simultaneous-multinomial outer confidence interval, while excluding any general thicket compiler or field-tier claim. Credit Duarte et al., JASA 2024, Autobounds as the same-input generic polynomial-program comparator and Zaffalon et al., IJAR 2023, as adjacent multi-source approximate bounding work; Autobounds is the software consumer whose generic optimization would be replaced by this analytic certificate. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivation parameterized the fiber by c and d, obtaining q=a+b-c+d, and built one finite private-threshold law matching all eight table cells. Exact checks matched 1,225 positive denominator-eight table pairs to LP values, including 42 pinned-c cases, and reconstructed 3,339 finite SCMs; the positive witness yields [1/8,1/2], and a correlated-source control escapes the valid independent-source bound. Current primary-source searches found generic methods but no exact formula collision. UNRESOLVED BOTTLENECK: Independently verify the universal source-preserving threshold extension in Section 4: one finite private-noise law and one deterministic outcome function must reproduce every prescribed response and both complete experimental tables. EARLY KILL TEST: Reconstruct both endpoint SCMs for A=((1/8,3/8),(3/8,1/8)) and B=((3/8,1/8),(3/8,1/8)); require exact agreement with all eight cells, mutually independent roots, and target values 3/8 and 5/8. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_binary_ctf_thicket_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The promised exact closed-form theorem was delivered soundly, but one fixed three-variable binary graph and scalar query remained incremental rather than field-level; related_work_omission@thm:sharp-risk-interval remains."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered contribution is nevertheless a closed-form specialization for one three-variable binary graph, one intervention menu, and one scalar risk already covered computationally by a published generic polynomial-program framework."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 5.5 < 7.4, so the graded tier 'subfield' is capped at 'incremental'."
  - "Panel findings left unrepaired (the tier, not these, is the reason for the halt): related_work_omission@thm:sharp-risk-interval."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_source_preserving_lift.tex
  - discovery/solve_thm_compatibility_frontier.tex
  - discovery/solve_prop_constant_time_certificate.tex
  - discovery/solve_prop_outer_confidence_interval.tex
seeds_burned: []
proof_attempt_summary: |
  The D stage proved the closed-simplex compatibility frontier, the exact sharp interval,
  source-preserving finite-SCM attainment, rational endpoint certificates, a constant-operation
  procedure, and a conservative outer confidence interval; the D0.5 math panel passed. The result
  collapsed only on novelty: the fixed graph, intervention menu, and scalar query were rated
  incremental. Reaching the field floor would require a new, re-anchored dependence-budget
  sensitivity proposal rather than an in-scope repair.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 10819543
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 10819543
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# scm_binary_ctf_thicket_frontier / v1 — Downgraded

**Topic.** Closed-form sharp multi-regime effect bounds for a two-source binary collider SCM. Let X,Z,Y be binary in the recursive graph X→Y←Z with two mutually independent latent roots shared along X↔Y and Z↔Y and independent private outcome noise. Given normalized strictly positive tables A(x,y)=P(X=x,Y=y | do(Z=0)) and B(z,y)=P(Z=z,Y=y | do(X=0)), set p=A(0,0)+A(0,1), r=B(0,0)+B(0,1), a=A(0,1), and b=B(0,1). Prove compatibility iff -(1-p)r≤a-b≤p(1-r), and prove that q=P(Y=1 | do(X=0,Z=0)) has the sharp interval [max{a,b,a+b-pr}, min{a+1-p,b+1-r,a+b+(1-p)(1-r)}]. Construct source-preserving finite SCMs attaining every real interval point and rational endpoint certificates for rational inputs. Give the constant-time compatibility/endpoint procedure and an optional simultaneous-multinomial outer confidence interval, while excluding any general thicket compiler or field-tier claim. Credit Duarte et al., JASA 2024, Autobounds as the same-input generic polynomial-program comparator and Zaffalon et al., IJAR 2023, as adjacent multi-source approximate bounding work; Autobounds is the software consumer whose generic optimization would be replaced by this analytic certificate. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivation parameterized the fiber by c and d, obtaining q=a+b-c+d, and built one finite private-threshold law matching all eight table cells. Exact checks matched 1,225 positive denominator-eight table pairs to LP values, including 42 pinned-c cases, and reconstructed 3,339 finite SCMs; the positive witness yields [1/8,1/2], and a correlated-source control escapes the valid independent-source bound. Current primary-source searches found generic methods but no exact formula collision. UNRESOLVED BOTTLENECK: Independently verify the universal source-preserving threshold extension in Section 4: one finite private-noise law and one deterministic outcome function must reproduce every prescribed response and both complete experimental tables. EARLY KILL TEST: Reconstruct both endpoint SCMs for A=((1/8,3/8),(3/8,1/8)) and B=((3/8,1/8),(3/8,1/8)); require exact agreement with all eight cells, mutually independent roots, and target values 3/8 and 5/8. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_binary_ctf_thicket_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental; projected paper_score_ceiling 5.5 < 7.4, with no bounded fix in scope; math review passed.

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
