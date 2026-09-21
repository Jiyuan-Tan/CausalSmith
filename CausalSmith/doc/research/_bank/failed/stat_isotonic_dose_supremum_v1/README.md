---
qid: stat_isotonic_dose_supremum
spec: v1
topic: "Extreme-value calibration for simultaneous causal-isotonic likelihood-ratio bands. Observe iid (W,A,Y) with compact W, continuous A, bounded Y, no unmeasured confounding, strict overlap, and fixed C^s radii with s>3(dim(W)+1) for the W density, treatment density, outcome mean and conditional second moment. On a fixed interior interval assume the causal dose-response is C^2 with derivative bounded above and away from zero and effective score variance nondegenerate. From the cross-fitted AIPW Grenander primitive, define the continuum supremum of local constrained-versus-unconstrained isotonic LR statistics. Prove the canonical Brownian-GCM high-excursion tail, additive ratio, cluster intensity, spatial-volume clock and Poisson/Gumbel limit; then prove primitive-to-LR transfer, feasible volume/variance estimation, calibrated joint profile bands and threshold-crossing confidence sets. Do not claim optimal width, tuning freedom or dominance over the Doss--VandenBerg 2026 multiscale Gaussian bands. Consumer: the AHA/CMS nurse-hours--readmission analysis, where joint profile inference replaces pointwise LR reporting. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fixed-radius primitive smoothness yields a common Lipschitz modulus for the effective LR variance and boundary-corrected local-polynomial nuisance rates with exponent above 5/12. Foldwise product bias, bounded-variable Gaussian coupling conditions, optimized-LR stability and finite dose-cell reduction were derived. Exact Brownian scaling gives effective spatial length n^(1/3) times the integral of [f theta'^2/(4 kappa)]^(1/3); a finite-energy plateau witness attains LR 1 at energy 9/8, while the true excursion rate remains bracketed and unproved. UNRESOLVED BOTTLENECK: Prove the canonical Brownian-GCM LR excursion theorem with sharp declustered high-threshold probabilities, additive tail ratio, constructive centering and a Poisson/Gumbel limit on a growing spatial interval. EARLY KILL TEST: On oracle PAVA windows of radii 4,8,16 and meshes 1/64,1/128,1/256, reproduce the plateau witness and importance-sampled excursion/cluster probabilities at thresholds 4,6,8; a stable failure of localization or additive-ratio scaling triggers an analytic counterexample attempt and stops the spine if verified. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_isotonic_dose_supremum.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Kernel substitution: the canonical LR-energy excursion rate/prefactor, additive tail ratio, anticlustering, Poisson/Gumbel limit, grid approximation, calibrated estimator, and nominal coverage remain unproved."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised Stat contribution—an evaluable simultaneous LR calibration with an extreme-value/Poisson/Gumbel limit—is replaced by an unconsumed open program; the retained scaling and action facts establish none of the Stat frontier objects (rate, limit law, coverage, or calibrated estimator)."
  - "The note does not deliver the advertised extreme-value calibration: it proves only finite-dimensional stationarity, scaling identities, a loose deterministic action bracket, an algebraic spatial clock, and deterministic profile inversion."
  - "The score assesses the delivered research package without credit for unfinished work."
reusable_artifacts:
  - "discovery/solve_lem_causal_identification.tex — explicit random-diagonal nonidentification witness"
  - "discovery/solve_thm_canonical_excursion.tex — exact Brownian scaling and plateau/action calculations"
  - "discovery/solve_oeq_cluster_mechanism.tex — documented open Palm/LDP/anticlustering program"
  - "discovery/core.json — maximized honest theorem graph and literature provenance"
seeds_burned: []
proof_attempt_summary: |
  The run attempted to derive the canonical Brownian–GCM LR-energy excursion tail, additive ratio, cluster intensity, and Poisson/Gumbel limit needed for simultaneous causal-isotonic calibration. Primary-source comparison and high-reasoning review showed that fixed-location LR and argmax/slope-error extreme-value results do not transfer to this nonlocal LR-energy field; the missing Palm/LDP, anticlustering, grid, and statistical-coupling theory is genuine new research. The final honest graph retains an exact random-diagonal nonidentification witness, finite-dimensional stationarity, scaling identities, a 1/2-to-9/8 action bracket, spatial-clock algebra, and deterministic inversion, but not the promised calibrated band.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 27708516
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 27708516
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# stat_isotonic_dose_supremum / v1 — Failed

**Topic.** Extreme-value calibration for simultaneous causal-isotonic likelihood-ratio bands. Observe iid (W,A,Y) with compact W, continuous A, bounded Y, no unmeasured confounding, strict overlap, and fixed C^s radii with s>3(dim(W)+1) for the W density, treatment density, outcome mean and conditional second moment. On a fixed interior interval assume the causal dose-response is C^2 with derivative bounded above and away from zero and effective score variance nondegenerate. From the cross-fitted AIPW Grenander primitive, define the continuum supremum of local constrained-versus-unconstrained isotonic LR statistics. Prove the canonical Brownian-GCM high-excursion tail, additive ratio, cluster intensity, spatial-volume clock and Poisson/Gumbel limit; then prove primitive-to-LR transfer, feasible volume/variance estimation, calibrated joint profile bands and threshold-crossing confidence sets. Do not claim optimal width, tuning freedom or dominance over the Doss--VandenBerg 2026 multiscale Gaussian bands. Consumer: the AHA/CMS nurse-hours--readmission analysis, where joint profile inference replaces pointwise LR reporting. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fixed-radius primitive smoothness yields a common Lipschitz modulus for the effective LR variance and boundary-corrected local-polynomial nuisance rates with exponent above 5/12. Foldwise product bias, bounded-variable Gaussian coupling conditions, optimized-LR stability and finite dose-cell reduction were derived. Exact Brownian scaling gives effective spatial length n^(1/3) times the integral of [f theta'^2/(4 kappa)]^(1/3); a finite-energy plateau witness attains LR 1 at energy 9/8, while the true excursion rate remains bracketed and unproved. UNRESOLVED BOTTLENECK: Prove the canonical Brownian-GCM LR excursion theorem with sharp declustered high-threshold probabilities, additive tail ratio, constructive centering and a Poisson/Gumbel limit on a growing spatial interval. EARLY KILL TEST: On oracle PAVA windows of radii 4,8,16 and meshes 1/64,1/128,1/256, reproduce the plateau witness and importance-sampled excursion/cluster probabilities at thresholds 4,6,8; a stable failure of localization or additive-ratio scaling triggers an analytic counterexample attempt and stops the spine if verified. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_isotonic_dose_supremum.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The promised simultaneous LR calibration with an extreme-value/Poisson/Gumbel limit is replaced by an unconsumed open program; the retained scaling and action facts establish none of the advertised rate, limit-law, coverage, or calibrated-estimator objects.

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
