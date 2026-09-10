---
qid: stat_nestedmarkov_multiconstraint_efficiency
spec: v1
topic: "K1 Fix a positive dominated ADMG nested-Markov model with a finite complete list of ordinary and post-fixing Verma constraints and an identified smooth causal functional. K2 characterize exactly when the closure of the sum of residualized weighted-moment spaces equals the full tangent-space orthocomplement, including a compatibility characterization when equality fails. K3 derive the canonical gradient and efficiency bound and construct an alternating-projection or sieve one-step estimator whose rate tracks subspace angle and nuisance error. K4 prove the semiparametric convolution lower bound and quantify efficiency lost by incomplete constraints. Use the anchor's smallest continuous two-Verma graph and Ananke as the witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Writing the combined constraint map as F=(F_1,...,F_J), a complemented constant-rank derivative would give T=ker DF=intersection ker DF_j and T-perp=closure of the summed residual spaces. Evans covers finite-state algebraic completeness, while Phung-Shpitser 2607.23439 covers ordinary conditional independences, not fixing-derived Verma constraints. UNRESOLVED BOTTLENECK: Prove a right inverse or exact compatibility condition for the combined fixing derivative in dominated L2 and obtain projection rates when the subspace angle can vanish. EARLY KILL TEST: On the smallest positive continuous two-Verma graph, compute both derivative operators and search for a common-kernel score not integrable to a regular submodel; pivot if one exists."
novelty_target: flagship
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The G2 efficiency claim is already supplied by NabiGuoLiu2026 Appendix S4.2, yet v5 still characterizes it as partial and claims a new complete two-Verma efficiency result."
  - "Phi_nu lacks a defined generic overlap domain."
  - "H^s(O) and finite-alphabet Evans embedding lack a mixed finite/Euclidean Sobolev convention."
reusable_artifacts:
  - "discovery/proto_core.json — final synchronized LFF/fixing-map proposal, useful only as a negative design record."
  - "reviews/angle0_v1.json through reviews/angle0_v5.json — successive audits of the joint-fixing, causal-target, learned-projector, and comparator defects."
  - "discovery/gaps.json — literature and theorem-gap record, including the Nabi–Guo–Liu Appendix S4.2 collision."
seeds_burned:
  - index: 0
    one_liner: "Joint fixing compatibility defect and exact orthocomplement frontier"
    reason: "Five synchronized revisions retained the contradicted G2 novelty claim and left foundational overlap/Sobolev definitions incomplete; independent validity gate found no non-identical continuation with established flagship headroom."
proof_attempt_summary: |
  Five proposal revisions attempted to turn the multi-constraint tangent-space idea into a flagship theorem by adding a joint fixing map, a finite-recursion right inverse, causal stochastic-intervention identification, and learned-projector inference. The attempt collapsed because its concrete G2 efficiency novelty was already covered by Nabi–Guo–Liu (2026), while the generic overlap domain and mixed finite/Euclidean Sobolev model remained undefined. A future topic would need a genuinely distinct family of simultaneous Verma constraints and a fresh novelty check; continuing this angle would repeat the exhausted root.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 37546407
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-02"
---

# stat_nestedmarkov_multiconstraint_efficiency / v1 — Failed

**Topic.** K1 Fix a positive dominated ADMG nested-Markov model with a finite complete list of ordinary and post-fixing Verma constraints and an identified smooth causal functional. K2 characterize exactly when the closure of the sum of residualized weighted-moment spaces equals the full tangent-space orthocomplement, including a compatibility characterization when equality fails. K3 derive the canonical gradient and efficiency bound and construct an alternating-projection or sieve one-step estimator whose rate tracks subspace angle and nuisance error. K4 prove the semiparametric convolution lower bound and quantify efficiency lost by incomplete constraints. Use the anchor's smallest continuous two-Verma graph and Ananke as the witness and consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Writing the combined constraint map as F=(F_1,...,F_J), a complemented constant-rank derivative would give T=ker DF=intersection ker DF_j and T-perp=closure of the summed residual spaces. Evans covers finite-state algebraic completeness, while Phung-Shpitser 2607.23439 covers ordinary conditional independences, not fixing-derived Verma constraints. UNRESOLVED BOTTLENECK: Prove a right inverse or exact compatibility condition for the combined fixing derivative in dominated L2 and obtain projection rates when the subspace angle can vanish. EARLY KILL TEST: On the smallest positive continuous two-Verma graph, compute both derivative operators and search for a common-kernel score not integrable to a regular submodel; pivot if one exists.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 revision cap exhausted after five REVISE verdicts; the load-bearing G2 efficiency novelty claim is already supplied by Nabi–Guo–Liu (2026) Appendix S4.2.

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
