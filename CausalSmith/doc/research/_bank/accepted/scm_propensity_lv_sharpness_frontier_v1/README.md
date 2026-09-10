---
qid: scm_propensity_lv_sharpness_frontier
spec: v1
topic: "Propensity-hinge completeness frontier for divergence-based causal bounds. In the binary-treatment bow ADMG with consistency, positivity and mutual absolute continuity, prove that the compatible marginal laws of Y(a) are exactly Q=eP+(1-e)R with R absolutely continuous with P. For every finite continuous convex f with f(1)=0, characterize equality between this set and the Jung-Kang ball D_f(P||Q)<=e f(1/e)+(1-e)f(0): modulo affine terms, f must vanish on [0,1/e] and be strictly positive above 1/e. Prove an open strict-containment region for every failing generator, exact piecewise CDF endpoints with attaining SCMs, and simultaneous endpoint inference. PRESOLVE EVIDENCE REQUIRING VERIFICATION: On a binary alphabet, cap-boundary equality and an outward-continuity argument force the ball radius to zero; the resulting functional equation forces f to be affine below 1/e, while convexity and strict positivity above the cap give the converse. Conditioning directly gives Q=eP+(1-e)R, and a latent U=(A,Y(0),Y(1)) construction realizes every admissible R and both CDF endpoints. The e=1/2 binary law supplies an interior illegal point for KL, Hellinger, chi-square, TV, and JS balls. Manski, linear-vacuous/Huber contamination, density-band testing, and generic SCM polynomial bounds were checked without locating the universal generator iff or the software-legality correction. UNRESOLVED BOTTLENECK: Prove the fully quantified open-set dichotomy for every finite continuous nondifferentiable convex generator, including piecewise-linear generators with zero intervals beyond the likelihood-ratio cap. EARLY KILL TEST: First complete the binary boundary-equality/open-gap proof and display an open illegal neighborhood for every failing piecewise-linear generator; any generator outside the claimed class with no open illegal ball region should stop or pivot the run."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  - "The promised itbound/IHDP legality application has been replaced by a conditional generic cap correction: the core itself leaves the program's support convention unaudited, so it supplies no source-audited software deliverable."
reusable_artifacts:
  - "CausalSmith/SCM/SCM_PropensityLvSharpnessFrontier_Research/TBowMixtureCompleteness.lean — bow-SCM mixture realization and completeness machinery."
  - "CausalSmith/SCM/SCM_PropensityLvSharpnessFrontier_Research/TOpenIllegalDichotomy.lean — open illegal-region construction for failing convex generators."
  - "CausalSmith/SCM/SCM_PropensityLvSharpnessFrontier_Research/TFiniteSampleSimultaneousBand.lean — finite-sample endpoint-band propagation from explicit Hoeffding and DKW hypotheses."
  - "discovery/proof_archive/ — accepted and superseded proof objects documenting the eventual-tail repair and open-set witnesses."
seeds_burned: []
proof_attempt_summary: |
  The run proved fixed-stratum bow-mixture completeness, the affine-invariant generator exactness frontier, open illegal regions for every failing generator, sharp CDF endpoints, heterogeneous-propensity impossibility, and simultaneous finite-sample endpoint bands. Discovery repaired a false all-n tie-contact formulation to an eventual-tail statement, while formalization repaired generator-domain and support-regime scaffold mismatches; all 70 delivered targets ultimately matched under both F4 reviewers with no source placeholders or project axioms. The proposed source-specific itbound/IHDP software correction was removed because the implementation convention was not audited; the accepted result retains the generic lawful cap correction instead.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 425921188
  pipeline_claude_tokens: 85696382
  total_tokens_consumed: null
banked_on: "2026-09-06"
paper_score: 6.1
paper_score_rationale: "The paper contains a credible and potentially useful exact divergence-frontier result, but its estimand framing, novelty positioning, contribution hierarchy, and presentation require substantial revision before the submission is ready for a leading econometrics journal."
---

# scm_propensity_lv_sharpness_frontier / v1 — Accepted

**Topic.** Propensity-hinge completeness frontier for divergence-based causal bounds. In the binary-treatment bow ADMG with consistency, positivity and mutual absolute continuity, prove that the compatible marginal laws of Y(a) are exactly Q=eP+(1-e)R with R absolutely continuous with P. For every finite continuous convex f with f(1)=0, characterize equality between this set and the Jung-Kang ball D_f(P||Q)<=e f(1/e)+(1-e)f(0): modulo affine terms, f must vanish on [0,1/e] and be strictly positive above 1/e. Prove an open strict-containment region for every failing generator, exact piecewise CDF endpoints with attaining SCMs, and simultaneous endpoint inference. PRESOLVE EVIDENCE REQUIRING VERIFICATION: On a binary alphabet, cap-boundary equality and an outward-continuity argument force the ball radius to zero; the resulting functional equation forces f to be affine below 1/e, while convexity and strict positivity above the cap give the converse. Conditioning directly gives Q=eP+(1-e)R, and a latent U=(A,Y(0),Y(1)) construction realizes every admissible R and both CDF endpoints. The e=1/2 binary law supplies an interior illegal point for KL, Hellinger, chi-square, TV, and JS balls. Manski, linear-vacuous/Huber contamination, density-band testing, and generic SCM polynomial bounds were checked without locating the universal generator iff or the software-legality correction. UNRESOLVED BOTTLENECK: Prove the fully quantified open-set dichotomy for every finite continuous nondifferentiable convex generator, including piecewise-linear generators with zero intervals beyond the likelihood-ratio cap. EARLY KILL TEST: First complete the binary boundary-equality/open-gap proof and display an open illegal neighborhood for every failing piecewise-linear generator; any generator outside the claimed class with no open illegal ball region should stop or pivot the run.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** CKPT 2 supervisor independently approved field acceptance after full source elaboration, zero-placeholder scan, and axioms audit.

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
