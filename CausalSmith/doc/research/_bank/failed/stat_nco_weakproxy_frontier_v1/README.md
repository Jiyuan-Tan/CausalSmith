---
qid: stat_nco_weakproxy_frontier
spec: v1
topic: "Minimax weak-proxy testing for constrained one-NCO bridge images. Observe growing finite ordered X,W and binary Y. Use probability-weighted known DCT Hilbert scales, fixed beta,R and box slack, and let the conditional-expectation operator obey a two-sided polynomial link condition with unknown a in a fixed interval. Define the observable defect as distance from b(x)=P(Y=1|X=x) to the estimated image A H_beta(R). Characterize the sharp total-error minimax separation radius jointly in n,K,a,beta, including every phase transition and the maximal polynomial K growth. Construct one sample-split convex-projection test, uniformly level alpha over the common composite null and adaptive to a, with a valid calibration that includes training/operator uncertainty and active source/box constraints; prove matching legal positive-multinomial lower bounds and invert the test to a lower confidence bound for the defect. Rejection only falsifies the restricted Wu et al. one-NCO causal null; nonrejection identifies nothing. The consumer is Wu et al.'s proxy-testing workflow, restricted here to binary-event and declared discrete-covariate implementations. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A finite-sample projection inequality gives radius sqrt(K/n)[1+R sqrt(sum j^(-2 beta)/eta)]; fixed K has a matched n^(-1/2) frontier. A positive DCT Rademacher block gives K^(1/4)/sqrt(n) when K^(-(a+beta)) is negligible, with mixture chi-square at most exp(8n^2 delta^4/m)-1. Checks exposed 16.58% rejection for a naive nominal-5% residual bootstrap and found no exact literature collision. UNRESOLVED BOTTLENECK: Prove a sharp lower-deviation bound for the profiled quadratic statistic over the full moving source/box image under estimated-operator fluctuations and arbitrary legal output rotations, then match its nuisance-fitting cost by joint-law perturbations. EARLY KILL TEST: Derive the two-split statistic and bootstrap law at K=2 and K=32 on interior, source-boundary, and box-boundary nulls; stop if training variance is omitted or any claimed rate beats the dense-block lower bound. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_nco_weakproxy_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Advertised matching growing-K separation frontier, phase transitions, maximal polynomial K growth, and unknown-a adaptive calibration were not delivered; only a conservative upper bound, fixed-K rates, and a restricted dense lower bound were proved."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "They do not prove the advertised growing-K separation frontier: the available projection upper bound is generally of order sqrt(K/n) plus training terms, leaving a polynomial gap from the dense lower bound."
  - "Operator-nuisance matching, active-face calibration, adaptation to unknown a, phase transitions, and the maximal K-growth range are all left as open-ended questions, so the central frontier contribution is not delivered."
  - "Stage 0.5 (typed) finding outside D0.R core-edit scope — kernel_substituted@oeq:sharp-frontier."
reusable_artifacts:
  - discovery/solve_thm_finite_sample_projection.tex
  - discovery/solve_thm_fixed_k_root_n_resolution.tex
  - discovery/solve_thm_legal_dense_lower_bound.tex
  - discovery/core.json
seeds_burned: []
proof_attempt_summary: |
  Discovery proved a conservative finite-sample projection test, explicit fixed-K
  root-n upper and lower results, and a legal restricted dense-block lower bound.
  The advertised sharp growing-K frontier collapsed because the matching centered
  cross-fit upper theorem, operator-training control, active-face calibration,
  unknown-a adaptation, phase transitions, and maximal K-growth range remained open.
  D0.5 therefore found kernel substitution and rated the delivered package incremental.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 20286803
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 20286803
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# stat_nco_weakproxy_frontier / v1 — Failed

**Topic.** Minimax weak-proxy testing for constrained one-NCO bridge images. Observe growing finite ordered X,W and binary Y. Use probability-weighted known DCT Hilbert scales, fixed beta,R and box slack, and let the conditional-expectation operator obey a two-sided polynomial link condition with unknown a in a fixed interval. Define the observable defect as distance from b(x)=P(Y=1|X=x) to the estimated image A H_beta(R). Characterize the sharp total-error minimax separation radius jointly in n,K,a,beta, including every phase transition and the maximal polynomial K growth. Construct one sample-split convex-projection test, uniformly level alpha over the common composite null and adaptive to a, with a valid calibration that includes training/operator uncertainty and active source/box constraints; prove matching legal positive-multinomial lower bounds and invert the test to a lower confidence bound for the defect. Rejection only falsifies the restricted Wu et al. one-NCO causal null; nonrejection identifies nothing. The consumer is Wu et al.'s proxy-testing workflow, restricted here to binary-event and declared discrete-covariate implementations. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A finite-sample projection inequality gives radius sqrt(K/n)[1+R sqrt(sum j^(-2 beta)/eta)]; fixed K has a matched n^(-1/2) frontier. A positive DCT Rademacher block gives K^(1/4)/sqrt(n) when K^(-(a+beta)) is negligible, with mixture chi-square at most exp(8n^2 delta^4/m)-1. Checks exposed 16.58% rejection for a naive nominal-5% residual bootstrap and found no exact literature collision. UNRESOLVED BOTTLENECK: Prove a sharp lower-deviation bound for the profiled quadratic statistic over the full moving source/box image under estimated-operator fluctuations and arbitrary legal output rotations, then match its nuisance-fitting cost by joint-law perturbations. EARLY KILL TEST: Derive the two-split statistic and bootstrap law at K=2 and K=32 on interior, source-boundary, and box-boundary nulls; stop if training variance is omitted or any claimed rate beats the dense-block lower bound. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_nco_weakproxy_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@oeq:sharp-frontier: the paper's named sharp growing-K frontier remains explicitly open; the delivered package is incremental and below the field floor.

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
