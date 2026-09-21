---
qid: panel_ife_heterospike_phase
spec: v1
topic: "Local treatment-factor detectability and ATT absorption in full-sample interactive fixed effects. For triangular rectangular panels with N/T in a compact subset of (0,infinity), iid Gaussian noise sigma in [sigma_min,sigma_max], a fixed-rank strong baseline Lambda F^T, block treatment D=dq^T, and treatment-supported heterogeneity delta_NT(d elementwise a)(q elementwise b)^T at delta_NT=theta/sqrt(min(N,T)), impose exact finite-array orthogonality to the baseline factor spaces, bounded nonzero supported means and variances, and positive full plus untreated/pre-period restricted Gram limits. Define the full-sample coefficient as the smallest beta in the compact-domain rank-(r+1) profiled least-squares argmin. Derive its uniform ATT absorption law as the explicit noise-normalized 2-by-2 spiked-SVD profile, including critical selections, prove undercoverage of the explicitly residualized conventional IFE Wald interval on a nonempty transition region, and construct rank-r masked-cell imputation with studentized coverage uniform over theta in a fixed compact interval. Consumer: Gobillon--Magnac's enterprise-zone full-sample Bai-IFE workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: After strong-factor removal, the coefficient profile reduces to B(x)=sqrt(max(c,1)pq){h[[mu_a mu_b,mu_a sqrt(v_b)],[sqrt(v_a)mu_b,sqrt(v_a v_b)]]-x e11} and Phi(x)=||B(x)||_F^2-psi_c(s1(B(x))). A unique no-absorption minimizer is proved on a nonzero subcritical region; the replicated witness has checked edge theta/sigma=2/3 and local large-signal absorption expansion. Checks covered zero heterogeneity, spectral crossing, coefficient escape, rectangular normalization, and current weak-factor literature, which excludes this rank-one treatment regressor. For the replicated geometry, the limiting potential is strictly separated below the edge. A 20,000-geometry search found no multiple local minima on the ATT-to-rank-one interval, while small Gaussian panels exposed finite-size variability but no normalization contradiction; exact orthogonality also confirms that masked validity alone is not the novelty. UNRESOLVED BOTTLENECK: Prove uniform global argmin localization and selection for the random profiled criterion, including uniqueness/separation or the correct law at every genuine tie. EARLY KILL TEST: Certify the explicit scalar profile's stationary/global-minimizer structure; if admissible opposite m^(-1/4) perturbations around a separated global tie yield different selections with identical limiting nuisance coordinates, pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ife_heterospike_phase.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Field-level phase-transition and inference claims were not established: global localization, masked-factor rates, dependencies, the fixed-rank below-threshold citation scope, a negative target/witness, and related-work coverage remain unresolved; a novelty-lifting approximate-orthogonality result would require a new model class."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "Even after repairing those gaps, the delivered contribution is an exact-oracle sensitivity result built on four hand-crafted finite-array orthogonalities, with no robustness to approximate or estimable residualization and no applied evidence, which keeps it below field level and constrains the projected journal score."
  - "HALTED AT TRIAGE: the math panel returned `revise` and its findings were never repaired, so this note is NOT established as mathematically sound — do not bank it as downgraded on this verdict alone."
  - "the supplied record limits Theorem 2.10's below-threshold edge-vector claim to r=1 with a derivative condition; it does not verify this node's all-subcritical fixed-rank clause."
  - "Stronger results require a new model class or critical-edge stochastic theory."
reusable_artifacts:
  - discovery/solve_thm_global_profile_singleton.tex
  - discovery/solve_oeq_global_selection.tex
  - discovery/solve_prop_oracle_class_nonempty.tex
  - discovery/solve_thm_absorption_law.tex
  - discovery/solve_thm_masked_coverage.tex
  - discovery/core.json
seeds_burned: []
proof_attempt_summary: |
  The run reduced the absorption problem to an explicit 2-by-2 spiked-SVD profile, derived a singleton global-profile characterization and an exact phase threshold, and verified the primary rectangular-Gaussian outlier citation. It stopped at D0.5 because the field-level promise remained an exact-oracle sensitivity result, while global stochastic localization, masked-factor rates, the all-subcritical fixed-rank citation, and the advertised negative inference witness were still unresolved. The only credible novelty lift requires a new approximate or estimable orthogonality model class, so it is outside this run's scope.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34937172
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34937172
  total_tokens_consumed: null
banked_on: "2026-09-16"
---

# panel_ife_heterospike_phase / v1 — Downgraded

**Topic.** Local treatment-factor detectability and ATT absorption in full-sample interactive fixed effects. For triangular rectangular panels with N/T in a compact subset of (0,infinity), iid Gaussian noise sigma in [sigma_min,sigma_max], a fixed-rank strong baseline Lambda F^T, block treatment D=dq^T, and treatment-supported heterogeneity delta_NT(d elementwise a)(q elementwise b)^T at delta_NT=theta/sqrt(min(N,T)), impose exact finite-array orthogonality to the baseline factor spaces, bounded nonzero supported means and variances, and positive full plus untreated/pre-period restricted Gram limits. Define the full-sample coefficient as the smallest beta in the compact-domain rank-(r+1) profiled least-squares argmin. Derive its uniform ATT absorption law as the explicit noise-normalized 2-by-2 spiked-SVD profile, including critical selections, prove undercoverage of the explicitly residualized conventional IFE Wald interval on a nonempty transition region, and construct rank-r masked-cell imputation with studentized coverage uniform over theta in a fixed compact interval. Consumer: Gobillon--Magnac's enterprise-zone full-sample Bai-IFE workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: After strong-factor removal, the coefficient profile reduces to B(x)=sqrt(max(c,1)pq){h[[mu_a mu_b,mu_a sqrt(v_b)],[sqrt(v_a)mu_b,sqrt(v_a v_b)]]-x e11} and Phi(x)=||B(x)||_F^2-psi_c(s1(B(x))). A unique no-absorption minimizer is proved on a nonzero subcritical region; the replicated witness has checked edge theta/sigma=2/3 and local large-signal absorption expansion. Checks covered zero heterogeneity, spectral crossing, coefficient escape, rectangular normalization, and current weak-factor literature, which excludes this rank-one treatment regressor. For the replicated geometry, the limiting potential is strictly separated below the edge. A 20,000-geometry search found no multiple local minima on the ATT-to-rank-one interval, while small Gaussian panels exposed finite-size variability but no normalization contradiction; exact orthogonality also confirms that masked validity alone is not the novelty. UNRESOLVED BOTTLENECK: Prove uniform global argmin localization and selection for the random profiled criterion, including uniqueness/separation or the correct law at every genuine tie. EARLY KILL TEST: Certify the explicit scalar profile's stationary/global-minimizer structure; if admissible opposite m^(-1/4) perturbations around a separated global tie yield different selections with identical limiting nuisance coordinates, pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ife_heterospike_phase.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Even after repairing the proof and citation gaps, the exact-oracle sensitivity result remains below field level because it has four hand-crafted finite-array orthogonalities, no robustness to approximate or estimable residualization, and no applied evidence.

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
