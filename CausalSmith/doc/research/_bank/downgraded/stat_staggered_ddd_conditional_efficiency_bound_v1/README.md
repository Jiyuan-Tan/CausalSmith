---
qid: stat_staggered_ddd_conditional_efficiency_bound
spec: v1
topic: "Conditional efficiency bound for staggered triple differences. In an iid fixed-T panel with adoption cohort G, eligibility S, covariates X, overlap, no anticipation, and the target-indexed covariate-conditional DDD parallel-gap restrictions of Ortiz-Villavicencio--Sant'Anna, fix finitely many group-time ATTs and a prespecified aggregate omega. Use every admissible clean comparison cohort. Derive the full observed-law tangent space and canonical gradient. Prove, rather than assume, that the efficient gradient is the joint OVS score vector Psi weighted by b*(x)=Gamma(x)^(-1)A{A'Gamma(x)^(-1)A}^(-1)omega, with the correct operator form for singular fixed-rank cases. Construct an attaining cross-fitted estimator under explicit overlap, conditional-eigenvalue, L4, nuisance and learned-weight product-rate conditions, with pointwise Wald inference. Characterize exactly when OVS's published loading and the parent's best constant joint loading satisfy the pointwise projection equations. Give a bounded open binary-covariate family where conditional weighting strictly beats every constant loading, and pointwise inference for the efficiency gap away from equality. Integrate the method as an optional backend for CRAN triplediff; do not call score-class projection semiparametric efficiency before tangent exhaustion is proved. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived Var{b(X)'Psi}=Var{omega'h(X)}+E[b(X)'Gamma(X)b(X)] and its pointwise constrained optimizer, including the singular operator condition. A legal binary-X mixture of the parent's bounded witness with rho_x=xr makes every constant loading choose q=0 while q*(x)=xr omega_2/2; the exact gain is 3r^2 omega_2^2/32, equal to 3/512 at r=omega_2=1/2, with separated conditional eigenvalues. Current searches distinguish overidentified staggered DDD from just-identified DDD EIFs and efficient DiD. UNRESOLVED BOTTLENECK: Prove local full-data-to-observed equivalence and tangent exhaustion: every regular aggregate gradient must differ from a fixed pairwise gradient exactly by the closure of measurable conditional clean-comparison contrasts. Without this theorem, b*(X)'Psi is only optimal in a chosen score family. Then control shared-cell covariance and learned-weight remainders. EARLY KILL TEST: Symbolically differentiate the finite-support binary-X three-score submodel under both conditional clean-cohort equalities, compute its complete tangent matrix, and verify that the projected gradient is b*(X)'Psi with gain 3/512. Any extra variance-reducing direction, missing gradient, or omitted compatibility restriction kills the canonical-gradient claim. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_staggered_ddd_conditional_efficiency_bound.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "Promised: b^star(X)prime Psi_P is the efficient/canonical gradient for the published OVS class. Delivered: b^star(X)prime Psi_P is only aggregate score-family optimal."
  - "The original flagship promise was not derived."
  - "statistical attainment and efficiency-gap inference are only pointwise for fixed finite covariate support; continuous-covariate and rank-changing inference remain open"
  - "general.paper_score_ceiling=6.7 < 7.2; general.salvageable=false; no bounded field-tier fix in scope"
reusable_artifacts:
  - "discovery/core.json — audited theorem graph, complete OVS normal-space projection, and finite-support tangent construction"
  - "discovery/solve_thm_binary_strict_gain.json — bounded binary-X strict efficiency-gap witness"
  - "discovery/solve_thm_crossfit_attainment.json — orthogonal complete-normal cross-fit construction"
  - "discovery/solve_lem_csx_staggered_did_eif_scope.json — source-scoped staggered-DiD comparison lemma"
seeds_burned: []
proof_attempt_summary: |
  The run attempted to prove that the covariate-varying aggregate loading b-star applied to the OVS
  score vector is itself the published-class canonical gradient. Tangent exhaustion instead exposed
  additional period-specific normal directions: the sound finite-support result projects a reference
  score onto the complete OVS normal space, while b-star remains only aggregate-family optimal. The
  repaired note retains pointwise finite-support attainment and gap inference, but the promised kernel,
  continuous-covariate extension, rank-changing inference, and package implementation remain unresolved.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 58887138
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 58887138
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# stat_staggered_ddd_conditional_efficiency_bound / v1 — Downgraded

**Topic.** Conditional efficiency bound for staggered triple differences. In an iid fixed-T panel with adoption cohort G, eligibility S, covariates X, overlap, no anticipation, and the target-indexed covariate-conditional DDD parallel-gap restrictions of Ortiz-Villavicencio--Sant'Anna, fix finitely many group-time ATTs and a prespecified aggregate omega. Use every admissible clean comparison cohort. Derive the full observed-law tangent space and canonical gradient. Prove, rather than assume, that the efficient gradient is the joint OVS score vector Psi weighted by b*(x)=Gamma(x)^(-1)A{A'Gamma(x)^(-1)A}^(-1)omega, with the correct operator form for singular fixed-rank cases. Construct an attaining cross-fitted estimator under explicit overlap, conditional-eigenvalue, L4, nuisance and learned-weight product-rate conditions, with pointwise Wald inference. Characterize exactly when OVS's published loading and the parent's best constant joint loading satisfy the pointwise projection equations. Give a bounded open binary-covariate family where conditional weighting strictly beats every constant loading, and pointwise inference for the efficiency gap away from equality. Integrate the method as an optional backend for CRAN triplediff; do not call score-class projection semiparametric efficiency before tangent exhaustion is proved. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived Var{b(X)'Psi}=Var{omega'h(X)}+E[b(X)'Gamma(X)b(X)] and its pointwise constrained optimizer, including the singular operator condition. A legal binary-X mixture of the parent's bounded witness with rho_x=xr makes every constant loading choose q=0 while q*(x)=xr omega_2/2; the exact gain is 3r^2 omega_2^2/32, equal to 3/512 at r=omega_2=1/2, with separated conditional eigenvalues. Current searches distinguish overidentified staggered DDD from just-identified DDD EIFs and efficient DiD. UNRESOLVED BOTTLENECK: Prove local full-data-to-observed equivalence and tangent exhaustion: every regular aggregate gradient must differ from a fixed pairwise gradient exactly by the closure of measurable conditional clean-comparison contrasts. Without this theorem, b*(X)'Psi is only optimal in a chosen score family. Then control shared-cell covariance and learned-weight remainders. EARLY KILL TEST: Symbolically differentiate the finite-support binary-X three-score submodel under both conditional clean-cohort equalities, compute its complete tangent matrix, and verify that the projected gradient is b*(X)'Psi with gain 3/512. Any extra variance-reducing direction, missing gradient, or omitted compatibility restriction kills the canonical-gradient claim. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_staggered_ddd_conditional_efficiency_bound.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G assessed subfield below the field floor: the proposed b-star aggregate-score canonicality was not derived; the sound delivered theorem uses an additional complete OVS normal-space projection.

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
