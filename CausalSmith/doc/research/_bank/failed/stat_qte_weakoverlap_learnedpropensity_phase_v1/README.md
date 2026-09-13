---
qid: stat_qte_weakoverlap_learnedpropensity_phase
spec: v1
topic: "Flexible-propensity weak-overlap limit theory for convex weighted quantile treatment effects. In the iid binary-treatment unconfounded model with positivity almost surely and quantitative Hall propensity tails, construct a cross-fitted boundary-adapted growing Bernoulli/logistic series learner and prove the weighted signed-functional likelihood expansion needed by the positive-weight clipped-IPW quantile argmin. Derive the corrected oracle-preservation condition E_n M_n^(gamma-1)=o_p(1), the compensated extreme-weight mark and signed-drift phase diagram, the learned-propensity Gaussian branch, joint equal/unequal-tail QTE laws, and refitted arm-vector m-out-of-n inference uniformly away from gamma=2. Do not assume oracle propensity, fixed parametric logit, desired score convergence, deterministic PRM behavior under shared folds, or raw scalar QTE subsampling. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the extreme treated-observation intensity, exact Knight decomposition, clipping-bias constant, positive drift sign, corrected score-transfer inequality, and a nonempty sieve window 1/[s(alpha+1)]<xi<1/(alpha+1). On the legal alpha=3/2 witness, J=n^0.3 gives candidate E=O_p(n^-1/8 polylog n) and D=O_p(n^-1/40 polylog n). Counterexamples require compensation/escape conditions and arm-vector recombination but leave the model, target, estimator type, and tier unchanged. UNRESOLVED BOTTLENECK: Prove the constrained-sieve weighted signed-functional expansion, then uniform centering and refitted inference. EARLY KILL TEST: Refute or prove the rate J^(-s)+n^(-1/2)J^((alpha-1)/2)+J^alpha/n; failure kills this construction. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/stat_qte_weakoverlap_learnedpropensity_phase.strongest_form.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "claim text changes only through proposed_statement_changes"
  - "restrict it to d>=q_N or the actual transfer region"
  - "In the Gaussian weighted variance, add the clipped-tail term N^{-b0(1-alpha)} for 0<alpha<1"
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_gaussian_branch.json
  - discovery/solve_thm_vector_subsampling.json
  - discovery/vcs/prs/ac841ac579db1beb528e7eedf27317183bc2701a25d19dfe5a018a210a49a829.inputs.json
  - reviews/review_math.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  Discovery reached a field-tier accepted proposal and derived a viable canonical joint-logit repair,
  including nonempty schedules and the main oracle/joint-law structure. The final D0 PR could not be
  merged soundly because three corrected theorem statements were emitted through a rejected carrier;
  the remaining mathematical work is the bounded clipping-region restriction and clipped-tail variance
  term after the graph-store carrier is redesigned.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 69462814
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 69462814
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_qte_weakoverlap_learnedpropensity_phase / v1 — Failed

**Topic.** Flexible-propensity weak-overlap limit theory for convex weighted quantile treatment effects. In the iid binary-treatment unconfounded model with positivity almost surely and quantitative Hall propensity tails, construct a cross-fitted boundary-adapted growing Bernoulli/logistic series learner and prove the weighted signed-functional likelihood expansion needed by the positive-weight clipped-IPW quantile argmin. Derive the corrected oracle-preservation condition E_n M_n^(gamma-1)=o_p(1), the compensated extreme-weight mark and signed-drift phase diagram, the learned-propensity Gaussian branch, joint equal/unequal-tail QTE laws, and refitted arm-vector m-out-of-n inference uniformly away from gamma=2. Do not assume oracle propensity, fixed parametric logit, desired score convergence, deterministic PRM behavior under shared folds, or raw scalar QTE subsampling. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived the extreme treated-observation intensity, exact Knight decomposition, clipping-bias constant, positive drift sign, corrected score-transfer inequality, and a nonempty sieve window 1/[s(alpha+1)]<xi<1/(alpha+1). On the legal alpha=3/2 witness, J=n^0.3 gives candidate E=O_p(n^-1/8 polylog n) and D=O_p(n^-1/40 polylog n). Counterexamples require compensation/escape conditions and arm-vector recombination but leave the model, target, estimator type, and tier unchanged. UNRESOLVED BOTTLENECK: Prove the constrained-sieve weighted signed-functional expansion, then uniform centering and refitted inference. EARLY KILL TEST: Refute or prove the rate J^(-s)+n^(-1/2)J^((alpha-1)/2)+J^alpha/n; failure kills this construction. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/stat_qte_weakoverlap_learnedpropensity_phase.strongest_form.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Terminal carrier failure: PR ac841ac579db could not soundly land corrected statements for prop:smooth-inclusion, thm:oracle-preservation, and thm:joint-qte; the supervisor deferred the required graph-store redesign and directed banking if this blocked bounded corrections.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

PR `ac841ac579db` and its raw input bundle were deliberately preserved. The failure classification is
operational, not a refutation of the mathematical kernel: the supervisor deferred the third-in-a-week
graph-store redesign and directed banking when the carrier defect blocked the bounded correction round.
