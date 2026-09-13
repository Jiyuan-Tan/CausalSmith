---
qid: panel_waoss_conditional_completion_frontier
spec: v1
topic: "Correct the marginal-to-conditional quasi-stayer gap in de Chaisemartin, D'Haultfœuille and Vazquez-Bare's continuous-treatment DiD Theorem 1. For iid two-period data with static potential outcomes, conditional parallel trends, known compact treatment support, a baseline trend m bounded by M and L-Lipschitz, and conditional mean causal movement bounded by K|delta|, define g(d,delta)=E[Delta Y|D1=d,Delta D=delta], nu_P(B)=E[sgn(Delta D)1{D1 in B}], and C_P={u: |u|<=M, Lip(u)<=L, |g(d,delta)-u(d)|<=K|delta| on the observed support}. Prove that the full-observed-law sharp WAOSS set is exactly Theta(P)={(E[sgn(Delta D)Delta Y]-integral u dnu_P)/E|Delta D|:u in C_P}; every u must be attained by a legal full potential-outcome law matching P. Prove compact attained interval geometry, the exact point-identification criterion R(P)=max_C integral u dnu_P-min_C integral u dnu_P=0, recovery of the published formula under conditional zero-support, observable obstacle-envelope compatibility, constant-one clipping stability, certified finite LP approximations, and a uniformly honest outer confidence interval on the fixed beta-Hölder, bounded-density, bounded-outcome finite-rectangle support subclass. Do not claim novelty for common-zero-baseline scalar bounded-slope intervals, already in arXiv:2405.04465v4, or invalidate the source's separate parametric estimate. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Derived the exact affine lift b=(g(D1,Delta D)-u(D1))/Delta D, Y1^u(t)=Y1, Y2^u(t)=Y2+b(t-D2), which preserves the entire observed law, realizes trend u, and has |b|<=K. Derived obstacle clipping with exact constant-one Hausdorff error and checked finite Theta=[-3/5,1] and continuous-density Theta=[-4/7,4/7] witnesses; signed cancellation, equality constraints, empty classes, support versions, denominator boundaries, and the common-baseline prior-art collision were checked. The lift also explains why marginal quasi-stayers alone cannot identify a baseline-specific trend: observed increments constrain u only through support-local cones, while the signed baseline measure transmits unresolved components directly into WAOSS endpoints. UNRESOLVED BOTTLENECK: Complete the uniform band-to-finite-program lemma on every allowed rectangle union, including boundary-aware regression coverage, signed-DKW control, measurable endpoint construction, and the stated ratio error. EARLY KILL TEST: Prove that lemma first on a fixed rectangle union with touching boundaries and one component separated from zero changes; if it needs extra density smoothness, strict feasibility, or stronger support assumptions than K4, pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_waoss_conditional_completion_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No unrestricted source-class identified-set characterization, no minimax converse for the inference rate, and no substantive implementation study; the positive sharp interval applies to a strengthened sensitivity class."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The source paper's universal singleton claim is decisively refuted by a regular witness, but the note does not characterize the unrestricted source-class identified set beyond that witness."
  - "Its positive sharp interval concerns a substantively strengthened sensitivity model imposing finite movement, bounded Lipschitz trends, continuity, and a separate realized-baseline identity, so it is not a repaired identification theorem under the source assumptions themselves."
  - "The inference result supplies a conservative uniform outer interval and an upper excess-endpoint rate, but no converse establishes minimaxity or the necessity of either rate component."
  - "The narrow fixed-support subclass and absence of a substantive application or implementation study constrain the publication case despite the exact identification, computation, and coverage results."
reusable_artifacts:
  - "discovery/core.json — validated theorem graph for the bounded sensitivity-class sharp interval, source-class recession witness, and inference upper bound."
  - "discovery/writeup.tex — synchronized 29-page derivation note; two-pass TeX compilation passed at banking."
  - "discovery/gaps.json — verified literature map and source locators for the marginal-versus-conditional quasi-stayer gap."
  - "discovery/solve_thm_full_law_sharpness.json — full-law affine completion proof artifact."
  - "discovery/solve_thm_finite_program.json — continuum-to-finite obstacle-program certificate."
  - "discovery/solve_thm_uniform_band_to_program.json — honest outer-inference upper-bound argument."
seeds_burned:
  - index: 0
    one_liner: "seed:full-law-completion"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 1
    one_liner: "seed:obstacle-criterion"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 2
    one_liner: "seed:signed-dual"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 3
    one_liner: "seed:certified-continuum-lp"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 4
    one_liner: "seed:honest-outer-inference"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 5
    one_liner: "seed:point-to-set-transition"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 6
    one_liner: "seed:boundary-band"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
  - index: 7
    one_liner: "seed:common-baseline-reduction"
    reason: "All eight proposal seeds were exhausted, merged, or ruled out without an in-scope lift to the field floor."
proof_attempt_summary: |
  The run proved a regular counterexample to the published singleton formula, an unbounded
  source-class recession witness, and an exact attained WAOSS interval with certified finite
  approximation and honest outer inference on a strengthened bounded sensitivity class. After
  five solve rounds, three revision rounds, and eight directed repairs, the result remained below
  field tier because it did not characterize the unrestricted source-class set or prove a matching
  minimax inference converse; those are new-anchor research problems, not bounded repairs.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 59683556
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 59683556
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# panel_waoss_conditional_completion_frontier / v1 — Downgraded

**Topic.** Correct the marginal-to-conditional quasi-stayer gap in de Chaisemartin, D'Haultfœuille and Vazquez-Bare's continuous-treatment DiD Theorem 1. For iid two-period data with static potential outcomes, conditional parallel trends, known compact treatment support, a baseline trend m bounded by M and L-Lipschitz, and conditional mean causal movement bounded by K|delta|, define g(d,delta)=E[Delta Y|D1=d,Delta D=delta], nu_P(B)=E[sgn(Delta D)1{D1 in B}], and C_P={u: |u|<=M, Lip(u)<=L, |g(d,delta)-u(d)|<=K|delta| on the observed support}. Prove that the full-observed-law sharp WAOSS set is exactly Theta(P)={(E[sgn(Delta D)Delta Y]-integral u dnu_P)/E|Delta D|:u in C_P}; every u must be attained by a legal full potential-outcome law matching P. Prove compact attained interval geometry, the exact point-identification criterion R(P)=max_C integral u dnu_P-min_C integral u dnu_P=0, recovery of the published formula under conditional zero-support, observable obstacle-envelope compatibility, constant-one clipping stability, certified finite LP approximations, and a uniformly honest outer confidence interval on the fixed beta-Hölder, bounded-density, bounded-outcome finite-rectangle support subclass. Do not claim novelty for common-zero-baseline scalar bounded-slope intervals, already in arXiv:2405.04465v4, or invalidate the source's separate parametric estimate. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Derived the exact affine lift b=(g(D1,Delta D)-u(D1))/Delta D, Y1^u(t)=Y1, Y2^u(t)=Y2+b(t-D2), which preserves the entire observed law, realizes trend u, and has |b|<=K. Derived obstacle clipping with exact constant-one Hausdorff error and checked finite Theta=[-3/5,1] and continuous-density Theta=[-4/7,4/7] witnesses; signed cancellation, equality constraints, empty classes, support versions, denominator boundaries, and the common-baseline prior-art collision were checked. The lift also explains why marginal quasi-stayers alone cannot identify a baseline-specific trend: observed increments constrain u only through support-local cones, while the signed baseline measure transmits unresolved components directly into WAOSS endpoints. UNRESOLVED BOTTLENECK: Complete the uniform band-to-finite-program lemma on every allowed rectangle union, including boundary-aware regression coverage, signed-DKW control, measurable endpoint construction, and the stated ratio error. EARLY KILL TEST: Prove that lemma first on a fixed rectangle union with touching boundaries and one component separated from zero changes; if it needs extra density smoothness, strict feasibility, or stronger support assumptions than K4, pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_waoss_conditional_completion_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 graded the delivered package subfield with paper_score_ceiling 7.1 below the 7.2 field gate and declared it not salvageable within scope.

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
