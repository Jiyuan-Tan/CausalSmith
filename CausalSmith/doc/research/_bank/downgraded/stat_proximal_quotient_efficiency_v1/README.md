---
qid: stat_proximal_quotient_efficiency
spec: v1
topic: "Quotient-tangent efficiency for nonunique proximal ATE bridges. Work in the dominated observed-data proximal model for O=(Y,A,Z,W,X) whose only bridge restrictions are existence of square-integrable outcome and treatment bridges; neither bridge is unique. Restrict to locally constant closed-range/rank strata and require pathwise differentiability, but do not add bijectivity, surjectivity, or a preferred minimum-norm bridge as a model assumption. Characterize the tangent space and prove an iff criterion for ATE pathwise differentiability. Define the proximal bridge-quotient canonical gradient as the minimum-norm element of the closed affine hull of all valid bridge doubly-robust scores, enlarged if tangent completeness requires it. Prove its efficiency bound and construct a cross-fitted penalized-minimax/Galerkin affine-ensemble one-step estimator with asymptotic linearity, ratio-consistent variance estimation, and Wald coverage under explicit approximation and product-remainder conditions. The hard kernel is the general score-lifting/tangent-normal completeness theorem; a finite constrained-GMM calculation is only a witness. Anchor at Bennett et al. 2023/JRSS-B 2026 Theorems 3 and 6 plus their efficiency boundary, Zhang et al. 2023 Theorem 2.5, Imbens et al. 2025 Theorem 7, and Ai–Shan 2025; distinguish all uniqueness-restricted efficiency results. Cui et al.'s SUPPORT right-heart-catheterization analysis is the consumer: the theorem determines whether bridge-dependent standard errors are globally efficient under redundant proxies and supplies the variance-minimizing replacement. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived outcome-solvability, treatment-solvability, and null-space-interaction normal generators and showed their closed span equals differences of bridge DR scores. An exact positive 36-cell example with both bridges nonunique has canonical variance 773723312/334026875, and an exact coefficient obstruction shows no single bridge pair attains it. A singular 3-by-3 branch example and four-corner affine-score identities were also checked. Destructive checks covered rank-changing neighborhoods, compact-operator closed-range collapse, Galerkin overclaims, product integrability, and current proximal-efficiency papers; no exact collision was found, but Bennett's final publisher text remains to be checked. UNRESOLVED BOTTLENECK: Prove that scores of actual dominated paths span exactly the annihilator of the three normal classes across the accepted closed-range model, including moving kernels and the arms' shared marginal. EARLY KILL TEST: Reproduce both finite witnesses, then compare actual tangent-score spans with the proposed normal annihilator in positive 4-by-4 rank-two models with different arm row spaces; an extra unresolved normal direction requires revision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_proximal_quotient_efficiency.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The proposed general quotient-tangent iff/kernel is still an OEQ; the delivered finite germs and conditional inference are a strictly weaker object, so retitle/reposition the contribution to that conditional-and-finite result or close the lifting theorem."
  - "The proof extends the pure-shift/four-corner identity from its stipulated square-integrable product domain to arbitrary pairs in Phi_P, but Phi_P requires only the total scores to be L2; the separate F, G, and R products can fail to be L2 while their displayed sum is L2, so C_P need not equal the closed span of all score differences."
  - "The conditional sub-exponential bounds are imposed directly on training-determined squared learned dictionary and score products, but no primitive learner/tail conditions derive or demonstrate their achievability; the L4 and residual-rate assumptions do not imply them, so this estimator-side concentration premise must be discharged or the inference claim explicitly re-scoped to a verified bounded/sub-exponential learner regime."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_selected_pair_strict_gap.tex
  - discovery/solve_thm_quotient_efficiency.tex
  - discovery/solve_lem_conditional_calibration_concentration.tex
seeds_burned: []
proof_attempt_summary: |
  The run developed transported fixed-defect operator charts, exact finite positive witnesses,
  affine bridge-score algebra, and a nested construction/calibration/evaluation estimator plan.
  The field-level result collapsed because the reverse tangent-score lifting theorem remained open;
  completing it would require a new coupled path-realization theorem, while the unrestricted affine
  identity and learned-product concentration also need narrower integrability and tail conditions.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 45574885
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 45574885
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# stat_proximal_quotient_efficiency / v1 — Downgraded

**Topic.** Quotient-tangent efficiency for nonunique proximal ATE bridges. Work in the dominated observed-data proximal model for O=(Y,A,Z,W,X) whose only bridge restrictions are existence of square-integrable outcome and treatment bridges; neither bridge is unique. Restrict to locally constant closed-range/rank strata and require pathwise differentiability, but do not add bijectivity, surjectivity, or a preferred minimum-norm bridge as a model assumption. Characterize the tangent space and prove an iff criterion for ATE pathwise differentiability. Define the proximal bridge-quotient canonical gradient as the minimum-norm element of the closed affine hull of all valid bridge doubly-robust scores, enlarged if tangent completeness requires it. Prove its efficiency bound and construct a cross-fitted penalized-minimax/Galerkin affine-ensemble one-step estimator with asymptotic linearity, ratio-consistent variance estimation, and Wald coverage under explicit approximation and product-remainder conditions. The hard kernel is the general score-lifting/tangent-normal completeness theorem; a finite constrained-GMM calculation is only a witness. Anchor at Bennett et al. 2023/JRSS-B 2026 Theorems 3 and 6 plus their efficiency boundary, Zhang et al. 2023 Theorem 2.5, Imbens et al. 2025 Theorem 7, and Ai–Shan 2025; distinguish all uniqueness-restricted efficiency results. Cui et al.'s SUPPORT right-heart-catheterization analysis is the consumer: the theorem determines whether bridge-dependent standard errors are globally efficient under redundant proxies and supplies the variance-minimizing replacement. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived outcome-solvability, treatment-solvability, and null-space-interaction normal generators and showed their closed span equals differences of bridge DR scores. An exact positive 36-cell example with both bridges nonunique has canonical variance 773723312/334026875, and an exact coefficient obstruction shows no single bridge pair attains it. A singular 3-by-3 branch example and four-corner affine-score identities were also checked. Destructive checks covered rank-changing neighborhoods, compact-operator closed-range collapse, Galerkin overclaims, product integrability, and current proximal-efficiency papers; no exact collision was found, but Bennett's final publisher text remains to be checked. UNRESOLVED BOTTLENECK: Prove that scores of actual dominated paths span exactly the annihilator of the three normal classes across the accepted closed-range model, including moving kernels and the arms' shared marginal. EARLY KILL TEST: Reproduce both finite witnesses, then compare actual tangent-score spans with the proposed normal annihilator in positive 4-by-4 rank-two models with different arm row spaces; an extra unresolved normal direction requires revision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_proximal_quotient_efficiency.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Field floor not met: score-lifting completeness remains unresolved, while the unrestricted affine identity has an L2 integrability gap and the estimator concentration premise is not derived.

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
