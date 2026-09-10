---
qid: scm_finiteplate_bernstein_ate_bounds
spec: v1
topic: "Sharp finite-plate hierarchical ATE bounds: observe n independent clusters, each with exactly fixed m conditionally iid binary exposure-outcome pairs generated from a latent four-cell law q with positivity epsilon, latent ignorability given q, and unknown mixing law mu; only each cluster's multinomial count is observed. For every b in the relative interior of the feasible degree-m Bernstein moment body, characterize the sharp cluster-equally-weighted ATE interval as an attained generalized-moment primal and Bernstein-polynomial dual with no gap; prove endpoint compatible hierarchical SCMs need at most N_m=binom(m+3,3) atoms; prove universal point identification iff the nonlinear ATE functional lies in the affine Bernstein span and hence fails for every finite m; give a terminating CAD recovery-or-endpoint-witness procedure for rational inputs and uniform whole-identified-set coverage by simultaneous multinomial-region inversion. Consumer: the JRSS C 2023 São Paulo directly-observed-therapy versus binary-cure analysis, whose ATE posteriors change with city random-effect specification. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The attainable (b,t) pairs reduce to the convex hull of (g(q),f(q)); at relative-interior b, a supporting hyperplane has nonzero objective coefficient, giving an attained Bernstein-polynomial dual without a gap, while a contact-set Caratheodory argument gives at most N_m atoms. Since the Bernstein coordinates sum to one, universal point identification is equivalent to f lying in their affine span. For m=1 and epsilon=1/4, the checked witness has one law with ATE 1/4 and a two-atom law with ATE 23/60 but the same observed counts; the exact fiber interval is [-1/6,1/2]. Boundary checks found degenerate point-identified laws for m>=2, confirming that the relative-interior restriction is essential; literature and collision checks found no finite-m sharp HCM bound. UNRESOLVED BOTTLENECK: Prove that every relative-interior b has a full-support representing measure and use dual contact conditions to derive strict fiber width whenever f is outside the Bernstein span. IMPLEMENTATION SCOPE: The theorem-level CAD statements concern exact termination and witness recovery in principle for fixed rational inputs via complete real-closed-field quantifier elimination. No concrete m=2 certificate or practical-runtime claim is part of the promised result."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: scm_finiteplate_bernstein_ate_bounds_v1_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 141197404
  pipeline_claude_tokens: 14472268
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# scm_finiteplate_bernstein_ate_bounds / v1 — Downgraded

**Topic.** Sharp finite-plate hierarchical ATE bounds: observe n independent clusters, each with exactly fixed m conditionally iid binary exposure-outcome pairs generated from a latent four-cell law q with positivity epsilon, latent ignorability given q, and unknown mixing law mu; only each cluster's multinomial count is observed. For every b in the relative interior of the feasible degree-m Bernstein moment body, characterize the sharp cluster-equally-weighted ATE interval as an attained generalized-moment primal and Bernstein-polynomial dual with no gap; prove endpoint compatible hierarchical SCMs need at most N_m=binom(m+3,3) atoms; prove universal point identification iff the nonlinear ATE functional lies in the affine Bernstein span and hence fails for every finite m; give a terminating CAD recovery-or-endpoint-witness procedure for rational inputs and uniform whole-identified-set coverage by simultaneous multinomial-region inversion. Consumer: the JRSS C 2023 São Paulo directly-observed-therapy versus binary-cure analysis, whose ATE posteriors change with city random-effect specification. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The attainable (b,t) pairs reduce to the convex hull of (g(q),f(q)); at relative-interior b, a supporting hyperplane has nonzero objective coefficient, giving an attained Bernstein-polynomial dual without a gap, while a contact-set Caratheodory argument gives at most N_m atoms. Since the Bernstein coordinates sum to one, universal point identification is equivalent to f lying in their affine span. For m=1 and epsilon=1/4, the checked witness has one law with ATE 1/4 and a two-atom law with ATE 23/60 but the same observed counts; the exact fiber interval is [-1/6,1/2]. Boundary checks found degenerate point-identified laws for m>=2, confirming that the relative-interior restriction is essential; literature and collision checks found no finite-m sharp HCM bound. UNRESOLVED BOTTLENECK: Prove that every relative-interior b has a full-support representing measure and use dual contact conditions to derive strict fiber width whenever f is outside the Bernstein span. IMPLEMENTATION SCOPE: The theorem-level CAD statements concern exact termination and witness recovery in principle for fixed rational inputs via complete real-closed-field quantifier elimination. No concrete m=2 certificate or practical-runtime claim is part of the promised result.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Operator decision 2026-09-04: paper_score_ceiling 7.3 is below the raised D0.5 field bar of 7.5. All three D0.5 referees passed (general field/meets_floor, math pass, rubric pass). Banked downgraded without further formalization spend.

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
