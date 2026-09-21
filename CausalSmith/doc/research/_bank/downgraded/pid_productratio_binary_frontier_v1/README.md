---
qid: pid_productratio_binary_frontier
spec: v1
topic: "Closed-form sharp binary frontier under longitudinal product sensitivity ratios. Observe positive binary O=(A0,A1,L1,Y) with degenerate baseline, target mu11=E[Y(1,1)], fixed interior margin eta, and Tan product ratios lambda1, lambda0L, lambda0Y bounded by finite G,B,C. Impose exactly Tan Lemma 7's cellwise normalization constraints and use Lemma 8's compatible-law objective. Prove both sharp endpoints are attained and equal explicit evaluations of at most 64 rational branches each after reducing the ratios to binary success probabilities and one L1 reweighting. Prove complete necessary-and-sufficient observable conditions for equality versus strictness of both Proposition-3 conservative endpoints, including sensitivity-free faces and active ties. Construct multinomial plug-in confidence sets with uniform asymptotic coverage for the entire sharp interval over the eta-interior class using an all-branch Gaussian-multiplier envelope. Credit Tan (Biometrika 2025) for the product model, exact compatibility, generic sharp optimization, conservative bounds, and sensitivity-free exact faces; credit Bonvini et al. for longitudinal MSM sensitivity. Dickerman et al.'s repeated-strategy metformin target-trial analysis is the consumer for the absolute sustained-metformin cancer risk; no contrast or sign-breakdown claim is made. PRESOLVE EVIDENCE REQUIRING VERIFICATION: All ten ratio cells reduce to r_l=e_l p_l+(1-e_l)U_G(p_l), t_l=U_B(r_l), and one endpoint L1 reweighting, yielding at most 64 rational branches and attaining full-data laws. The supplied witness reproduces [0.3625,0.6375]. For active covariate sensitivity Tan v1 is strictly loose; for G,B>1 v2 is exact iff (p_l-1/(G+1))(r_l-1/(B+1))>=0 in both strata, with ties included. A strict interior witness gives sharp 61/80, v1 25/32, and v2 49/64; 1,000 random exact comparisons found no criterion failure. UNRESOLVED BOTTLENECK: Prove uniform Gaussian-multiplier quantile approximation over all branch gradients, including redundant or zero-variance coordinates, and the uniform quadratic remainder bound across branch changes; independently verify both equality-chain proofs against the final published Proposition 3. EARLY KILL TEST: Reproduce the published binary check-loss programs and certify the rational strictness witness 61/80 versus 25/32 and 49/64; a different shared-threshold specification requires re-deriving the strictness theorem before proceeding. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_productratio_binary_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The proposed field-level complete binary frontier was delivered soundly, but its restricted two-decision binary scope and lack of a delivered empirical consumer analysis capped the package below field."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The contribution is nevertheless confined to two decisions, binary intermediate covariate and outcome, a degenerate baseline, and an absolute sustained-strategy mean, so it does not supply a broadly reusable longitudinal characterization."
  - "The Dickerman application remains only a proposed consumer rather than reproduced evidence showing how much the sharp frontier changes an empirical conclusion, while the sole quantitative demonstration is the constructed strictness witness."
  - "[D0.5.G projected paper-score gate: paper_score_ceiling 7.1 < 7.4, so the graded tier 'field' is capped at 'subfield'. The score assesses the delivered research package without credit for unfinished work.]"
reusable_artifacts:
  - "discovery/core.json — source-verified theorem graph, binary ratio reduction, attained endpoint program, equality frontier, strict rational witness, and uniform inference statement."
  - "discovery/writeup.tex — complete informal derivation, including the repaired Tan compatibility bridge and both image inclusions."
  - "discovery/solve_thm_sharp_binary_frontier.tex — sharp endpoint and attainment proof artifact."
  - "discovery/solve_thm_conservative_equality_frontier.tex — complete equality/strictness classification and rational witness proof artifact."
  - "discovery/solve_thm_uniform_interval_coverage.tex — all-branch Gaussian-multiplier coverage proof artifact."
seeds_burned:
  - index: 0
    one_liner: "seed:finite-frontier"
    reason: "The sole developed angle was mathematically sound after source-fidelity repair but capped at subfield and not salvageable to field within scope."
proof_attempt_summary: |
  The run derived and source-checked the attained sharp binary interval, the full equality-versus-strictness frontier for Tan's two conservative relaxations, the 61/80 versus 25/32 and 49/64 strict witness, and uniform all-branch endpoint inference. A validity audit found that the first citation bridge overstated the attested source; the run repaired it by narrowing Tan's cited result, separately deriving necessity and the binary ICE/IPW specialization, and then passed both math and citation review. The work was downgraded only because its binary two-decision scope and prospective-only empirical consumer capped its paper score at 7.1, below the 7.4 field threshold.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 22018586
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 22018586
  total_tokens_consumed: null
banked_on: "2026-09-16"
---

# pid_productratio_binary_frontier / v1 — Downgraded

**Topic.** Closed-form sharp binary frontier under longitudinal product sensitivity ratios. Observe positive binary O=(A0,A1,L1,Y) with degenerate baseline, target mu11=E[Y(1,1)], fixed interior margin eta, and Tan product ratios lambda1, lambda0L, lambda0Y bounded by finite G,B,C. Impose exactly Tan Lemma 7's cellwise normalization constraints and use Lemma 8's compatible-law objective. Prove both sharp endpoints are attained and equal explicit evaluations of at most 64 rational branches each after reducing the ratios to binary success probabilities and one L1 reweighting. Prove complete necessary-and-sufficient observable conditions for equality versus strictness of both Proposition-3 conservative endpoints, including sensitivity-free faces and active ties. Construct multinomial plug-in confidence sets with uniform asymptotic coverage for the entire sharp interval over the eta-interior class using an all-branch Gaussian-multiplier envelope. Credit Tan (Biometrika 2025) for the product model, exact compatibility, generic sharp optimization, conservative bounds, and sensitivity-free exact faces; credit Bonvini et al. for longitudinal MSM sensitivity. Dickerman et al.'s repeated-strategy metformin target-trial analysis is the consumer for the absolute sustained-metformin cancer risk; no contrast or sign-breakdown claim is made. PRESOLVE EVIDENCE REQUIRING VERIFICATION: All ten ratio cells reduce to r_l=e_l p_l+(1-e_l)U_G(p_l), t_l=U_B(r_l), and one endpoint L1 reweighting, yielding at most 64 rational branches and attaining full-data laws. The supplied witness reproduces [0.3625,0.6375]. For active covariate sensitivity Tan v1 is strictly loose; for G,B>1 v2 is exact iff (p_l-1/(G+1))(r_l-1/(B+1))>=0 in both strata, with ties included. A strict interior witness gives sharp 61/80, v1 25/32, and v2 49/64; 1,000 random exact comparisons found no criterion failure. UNRESOLVED BOTTLENECK: Prove uniform Gaussian-multiplier quantile approximation over all branch gradients, including redundant or zero-variance coordinates, and the uniform quadratic remainder bound across branch changes; independently verify both equality-chain proofs against the final published Proposition 3. EARLY KILL TEST: Reproduce the published binary check-loss programs and certify the rational strictness witness 61/80 versus 25/32 and 49/64; a different shared-threshold specification requires re-deriving the strictness theorem before proceeding. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_productratio_binary_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G achieved subfield below the fixed field floor: the contribution is confined to two decisions, binary intermediate covariate and outcome, a degenerate baseline, and an absolute sustained-strategy mean.

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
