---
qid: panel_bhar_proxy_modulus_frontier
spec: proxy_modulus_v1
topic: "Sharp generated-donor-proxy minimax frontier for realized-path causal buy-and-hold level wealth. Fix H, proxy dimension p and finitely many cohorts; observe N donor scores and n_s replicated untreated wealth blocks across T pre-event windows, with conditional cross-unit independence, geometric temporal beta-mixing, bounded wealth, stable Holder(lambda) proxy-coordinate regressions, interior event-path overlap, limited anticipation and no spillovers. Use the full uniformly elliptic conditional covariance of the stacked donor-error path. At each realized event path impose a two-sided covariance-standardized local modulus with kappa=min(lambda,1). Determine sharp conditional MSE and uniformly honest expected-length rates across arbitrary N,T,n_s growth, the exact oracle/generated-proxy phase diagram, an attaining replicated-donor cross-fitted local-polynomial or tensor-sieve estimator with calendar-block inference, and matching Le Cam/Assouad bounds. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the scalar H=0, one-cohort Gaussian-donor subexperiment, event locations O(N^-1/2) apart have bounded KL; affine or asymmetric-cusp regressions satisfying the corrected modulus separate targets by O(N^-kappa/2), yielding MSE N^-kappa and honest-length N^-kappa/2 lower bounds, matched by known-regression plug-in. Checks excluded constant-regression, noiseless temporal-contrast, cohort-cancellation, and identified prior-art collisions; the combined four-term rate remains heuristic and unproved. UNRESOLVED BOTTLENECK: Prove one feasible estimator and conditionally honest interval attain the maximum of treated-mean noise, replicated-response smoothing, random-design spacing, and proxy-modulus terms under unknown heteroscedastic donor laws and overlapping beta-mixing windows, with matching lower bounds in every relative-growth regime and no extra deconvolution or logarithmic phase. EARLY KILL TEST: In scalar iid H=0 with lambda=kappa<=1, bounded responses, T latent design points, n response replicates, and N donor replicates, prove MSE max{n^-1,(Tn)^(-2lambda/(2lambda+1)),T^(-2lambda),N^-lambda} and the square-root honest-length rate; pivot if noisy training covariates force any larger term."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "lower-witness-not-uniform-over-class@lem:joint-law-embedding"
  - "lower-witness-not-uniform-over-class@lem:geometric-mixing-spacing-obstruction"
  - "lower-witness-not-uniform-over-class@lem:iid-joint-law-embedding"
  - "related_work_incomplete@thm:sharp-joint-frontier"
  - "The proofs repeatedly assert that carrier-plus-bump perturbations can be scaled to preserve the Holder, bounded-response, and two-sided-modulus envelopes, although nonemptiness and B>D^2 provide no interior slack in those envelopes; for example, c_mod=C_mod is allowed."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/d0_escalation_log.jsonl
  - reviews/review_general.json
  - reviews/review_math.json
  - reviews/review_rubric.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Discovery constructed event-transport identification, estimator upper bounds, exact conditional
  coverage, an iid-versus-beta-mixing dependence elbow, and a universal shared-design obstruction.
  The matching lower-frontier claims collapsed because their bump witnesses were not shown to remain
  inside boundary-tight Holder, response, and two-sided-modulus envelopes; the banked artifact therefore
  preserves an open uniformity defect and must not be treated as a sound proof of those converses.
  A future attempt must either build boundary-compatible witnesses or state and justify primitive uniform
  interior slack before reasserting the beta/iid matching frontiers.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 119924233
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 119924233
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# panel_bhar_proxy_modulus_frontier / proxy_modulus_v1 — Downgraded

**Topic.** Sharp generated-donor-proxy minimax frontier for realized-path causal buy-and-hold level wealth. Fix H, proxy dimension p and finitely many cohorts; observe N donor scores and n_s replicated untreated wealth blocks across T pre-event windows, with conditional cross-unit independence, geometric temporal beta-mixing, bounded wealth, stable Holder(lambda) proxy-coordinate regressions, interior event-path overlap, limited anticipation and no spillovers. Use the full uniformly elliptic conditional covariance of the stacked donor-error path. At each realized event path impose a two-sided covariance-standardized local modulus with kappa=min(lambda,1). Determine sharp conditional MSE and uniformly honest expected-length rates across arbitrary N,T,n_s growth, the exact oracle/generated-proxy phase diagram, an attaining replicated-donor cross-fitted local-polynomial or tensor-sieve estimator with calendar-block inference, and matching Le Cam/Assouad bounds. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the scalar H=0, one-cohort Gaussian-donor subexperiment, event locations O(N^-1/2) apart have bounded KL; affine or asymmetric-cusp regressions satisfying the corrected modulus separate targets by O(N^-kappa/2), yielding MSE N^-kappa and honest-length N^-kappa/2 lower bounds, matched by known-regression plug-in. Checks excluded constant-regression, noiseless temporal-contrast, cohort-cancellation, and identified prior-art collisions; the combined four-term rate remains heuristic and unproved. UNRESOLVED BOTTLENECK: Prove one feasible estimator and conditionally honest interval attain the maximum of treated-mean noise, replicated-response smoothing, random-design spacing, and proxy-modulus terms under unknown heteroscedastic donor laws and overlapping beta-mixing windows, with matching lower bounds in every relative-growth regime and no extra deconvolution or logarithmic phase. EARLY KILL TEST: In scalar iid H=0 with lambda=kappa<=1, bounded responses, T latent design points, n response replicates, and N donor replicates, prove MSE max{n^-1,(Tn)^(-2lambda/(2lambda+1)),T^(-2lambda),N^-lambda} and the square-root honest-length rate; pivot if noisy training covariates force any larger term.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the delivered package incremental with paper-score ceiling 5.6 below the field floor 7.4 and found it not salvageable in scope because lower witnesses are not uniform over boundary-tight envelopes.

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
