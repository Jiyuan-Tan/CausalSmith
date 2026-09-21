---
qid: stat_kl_frontier_postselection_band
spec: v1
topic: "Post-selection-valid welfare–divergence frontier bands for benchmark-centered assignment rules. In an iid bounded-outcome causal model with overlap, finitely many actions, and a fixed finite-dimensional benchmark-centered softmax class, index the best rule by a KL preference c in a positive compact interval. Assume a unique uniformly interior optimizer with a uniformly negative Hessian and cross-fitted doubly robust nuisance conditions. Prove a joint uniform influence expansion and Gaussian limit for the optimizer, welfare, and benchmark-divergence paths, consistently estimate the covariance kernel, and validate a conditional multiplier bootstrap. Construct a simultaneous confidence tube for the two-coordinate welfare–divergence frontier that remains valid after any measurable choice of c from the plotted curve; use set-valued inversion at tangencies or self-intersections. Jointly calibrate the n-scaled penalized-regret process through its Hessian quadratic form. Credit Fang–Ridder–Xie arXiv:2512.19230v3 for fixed-preference efficiency and their three-arm commitment-savings frontier. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the joint influence maps for the optimizer, welfare, and divergence, the penalized cancellation identity, and the uniform quadratic-regret reduction. It solved the binary-covariate three-action witness exactly, established a uniform curvature lower bound 0.0026816936, and numerically checked influence centering and frontier derivatives. Vanishing penalties, weak overlap, redundant logits, localization, selected-index limits, constrained inversion, estimated scale, and oracle-versus-implemented welfare were checked; generic indexed-inference results cap novelty but no exact collision was found. UNRESOLVED BOTTLENECK: Prove conditional multiplier replacement and tightness for fold-specific estimated stacked influences evaluated along the same-sample optimizer path, using shrinking empirical-L2 error and uniform entropy bounds. EARLY KILL TEST: On the twelve-atom witness at c=.5,1,2, verify influence centering, penalized cancellation, H theta-prime=-grad K, and the quadratic regret expansion, then check held-out nuisance linearization and multiplier covariance errors; a persistent root-n remainder or failed identity stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_kl_frontier_postselection_band.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Promised a field-level post-selection welfare-divergence frontier band; delivered a specialized penalty-indexed uniform tube, population slope geometry, and conservative set inversion without the smooth divergence-indexed inverse/Bahadur theorem or application."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves a uniform influence law, multiplier tube, quadratic-regret process, and softmax monotonicity result, but these are smooth fixed-dimensional indexed-inference extensions of published fixed-penalty results rather than a distinct field-level framework."
  - "The foldwise nuisance-rate events are assumed rather than derived from primitive learner/model conditions; discharge conditional rates for the actual fold learners or explicitly rescope the theorem conditionally."
  - "The proof asserts |hat e-e|<=1 after a lower-only epsilon/2 clip, but no upper range restriction on hat e is declared; add an upper clip/range condition or remove this false bound."
  - "Its Taylor reduction invokes uniform interiority to set gradient M_c(theta_c)=0, but ass:uniform-interior is absent from depends_on; add it (or a declared FOC lemma) to the DAG route."
  - "Theorem-level related-work comparisons for the post-selection tube remain incomplete."
reusable_artifacts:
  - "discovery/core.json — discharged theorem graph for the penalty-indexed uniform influence law, multiplier tube, regret process, slope geometry, and set-valued inversion."
  - "discovery/writeup.tex — rendered derivation note and exact assumptions."
  - "discovery/vcs/ — complete graph history, including the two attempted divergence-indexed inverse upgrades."
  - "reviews/review_math.json — citation attestations and bounded soundness repairs for a future re-raise."
seeds_burned: []
proof_attempt_summary: |
  D0 proved the central foldwise multiplier-replacement theorem after repairing its dependency closure, then established the penalty-indexed uniform influence law, shared multiplier tube, quadratic-regret process, population divergence-slope dichotomy, and conservative set-valued inversion. Two targeted maximality rounds attempted to add a smooth sample inverse, uniform Bahadur expansion, cancellation-based fixed-divergence welfare law, and simultaneous band; both workers declined that theorem as unproved and retained only the honest fallback. D0.5 therefore capped novelty at incremental, with the foldwise-rate setup, propensity-clipping bound, uniform-interiority dependency, and related-work comparison still requiring repair before reuse.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 25032686
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 25032686
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# stat_kl_frontier_postselection_band / v1 — Downgraded

**Topic.** Post-selection-valid welfare–divergence frontier bands for benchmark-centered assignment rules. In an iid bounded-outcome causal model with overlap, finitely many actions, and a fixed finite-dimensional benchmark-centered softmax class, index the best rule by a KL preference c in a positive compact interval. Assume a unique uniformly interior optimizer with a uniformly negative Hessian and cross-fitted doubly robust nuisance conditions. Prove a joint uniform influence expansion and Gaussian limit for the optimizer, welfare, and benchmark-divergence paths, consistently estimate the covariance kernel, and validate a conditional multiplier bootstrap. Construct a simultaneous confidence tube for the two-coordinate welfare–divergence frontier that remains valid after any measurable choice of c from the plotted curve; use set-valued inversion at tangencies or self-intersections. Jointly calibrate the n-scaled penalized-regret process through its Hessian quadratic form. Credit Fang–Ridder–Xie arXiv:2512.19230v3 for fixed-preference efficiency and their three-arm commitment-savings frontier. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the joint influence maps for the optimizer, welfare, and divergence, the penalized cancellation identity, and the uniform quadratic-regret reduction. It solved the binary-covariate three-action witness exactly, established a uniform curvature lower bound 0.0026816936, and numerically checked influence centering and frontier derivatives. Vanishing penalties, weak overlap, redundant logits, localization, selected-index limits, constrained inversion, estimated scale, and oracle-versus-implemented welfare were checked; generic indexed-inference results cap novelty but no exact collision was found. UNRESOLVED BOTTLENECK: Prove conditional multiplier replacement and tightness for fold-specific estimated stacked influences evaluated along the same-sample optimizer path, using shrinking empirical-L2 error and uniform entropy bounds. EARLY KILL TEST: On the twelve-atom witness at c=.5,1,2, verify influence centering, penalized cancellation, H theta-prime=-grad K, and the quadratic regret expansion, then check held-out nuisance linearization and multiplier covariance errors; a persistent root-n remainder or failed identity stops the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_kl_frontier_postselection_band.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 graded the honest penalty-indexed softmax result incremental with paper_score_ceiling 6 below the field floor 7.4; the divergence-indexed inverse upgrade was exhausted twice, and four bounded panel findings remain unrepaired.

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
