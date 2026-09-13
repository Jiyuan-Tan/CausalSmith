---
qid: stat_proxy_effectlaw_eigencollision_frontier
spec: v1
topic: "K1 prove root-n W1 estimation of the quotient latent-effect law in the fixed-k Virk-Mazaheri-Wu proxy model through eigenvalue collisions. K2 construct honest cluster-adaptive W1 confidence sets. K3 prove labeled-weight error min{1,(sqrt(n)delta)^-1}. K4 match both regimes by local lower bounds. Include the explicit full-rank k=2 collision witness and PROTECT stage-III NSCLC consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the witness, proxy matrices remain nonsingular while effects .25-epsilon and .25+epsilon merge. Observable operators and auxiliary moments fluctuate at root-n scale. For a delta-wide cluster, projector-mass error of order 1/(sqrt(n)delta) is transported only across distance delta, suggesting root-n W1 cancellation even though labels fail. Bauer-Fike localization and aggregate cluster projectors provide a plausible proof spine. Exact collision, unequal weights, and delta near n^-1/2 showed no immediate contradiction; complex empirical eigenvalues remain unresolved. Separated submodels also provide a standard Gaussian local lower bound. UNRESOLVED BOTTLENECK: Prove a uniform operator-to-positive-measure perturbation lemma through simultaneous cluster merges and splits, including nonreal empirical spectra, then calibrate honest clustering and a matching local experiment. EARLY KILL TEST: Exhaust the two-by-two witness under all root-n moment perturbations. Stop if quotient W1 error contains any inverse-epsilon factor or construct two statistically root-n-close admissible operators whose quotient laws are separated by more than root-n."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - formalization/crosswalk_full.json
seeds_burned: []
proof_attempt_summary: |
  The run proved uniform root-n quotient-law estimation through eigenvalue collisions,
  honest cluster-adaptive confidence sets, the separated labeled-weight rate, matching
  local lower bounds, and a finite-net estimator. Repeated review-driven repairs made
  the positive-measure projection metric, explicit Bernoulli path, model-conditional
  effect-gap range, cluster nonemptiness, and published VMW premises fully explicit;
  the final graph has no gated, undelivered, sorry-backed, or added-axiom obligations.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 1452603715
  pipeline_claude_tokens: 240948321
  total_tokens_consumed: null
banked_on: "2026-09-07"
paper_score: 6.4
paper_score_rationale: "The paper delivers a technically significant and unusually well-scoped collision-uniform inference result, but stale verification metadata, an oracle-contaminated algorithm definition, foundational representation ambiguities, and severe organizational redundancy prevent publication in its current form."
---

# stat_proxy_effectlaw_eigencollision_frontier / v1 — Accepted

**Topic.** K1 prove root-n W1 estimation of the quotient latent-effect law in the fixed-k Virk-Mazaheri-Wu proxy model through eigenvalue collisions. K2 construct honest cluster-adaptive W1 confidence sets. K3 prove labeled-weight error min{1,(sqrt(n)delta)^-1}. K4 match both regimes by local lower bounds. Include the explicit full-rank k=2 collision witness and PROTECT stage-III NSCLC consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: In the witness, proxy matrices remain nonsingular while effects .25-epsilon and .25+epsilon merge. Observable operators and auxiliary moments fluctuate at root-n scale. For a delta-wide cluster, projector-mass error of order 1/(sqrt(n)delta) is transported only across distance delta, suggesting root-n W1 cancellation even though labels fail. Bauer-Fike localization and aggregate cluster projectors provide a plausible proof spine. Exact collision, unequal weights, and delta near n^-1/2 showed no immediate contradiction; complex empirical eigenvalues remain unresolved. Separated submodels also provide a standard Gaussian local lower bound. UNRESOLVED BOTTLENECK: Prove a uniform operator-to-positive-measure perturbation lemma through simultaneous cluster merges and splits, including nonreal empirical spectra, then calibrate honest clustering and a matching local experiment. EARLY KILL TEST: Exhaust the two-by-two witness under all root-n moment perturbations. Stop if quotient W1 error contains any inverse-epsilon factor or construct two statistically root-n-close admissible operators whose quotient laws are separated by more than root-n.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Supervisor independently approved CKPT 2 at field tier after full source re-elaboration, placeholder scan, and headline axiom audit.

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
