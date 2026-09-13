---
qid: panel_ipcw_spectral_ssc_inference
spec: v1
topic: "Censoring-robust spectral synthetic survival control under covariate-dependent right censoring. Fix N0 donor units, T0 pre-treatment times, J post-treatment grid points and rank r while K independent individuals per cell tends to infinity; assume conditional independent censoring given covariates with positivity, exact donor-span transport, a rank-r singular gap, cross-fitted censor and event-survival nuisances with product rate o(K^-1/2), and nondegenerate covariance. Construct augmented-IPCW cell survival estimates, differentiate the full stacked rank-r pseudoinverse map, and prove joint root-K asymptotic linearity, a Gaussian-multiplier simultaneous band for the J-point untreated counterfactual curve, a studentized grid-RMST effect interval, and an open-subclass theorem that unadjusted KM/PCR has fixed bias. Consumer: Han and Shah's 925-patient, 10-country TCL analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For donor-pre matrix M, target row y, donor-post matrix B, and P=M_r^+, the presolver derived the full differential D(yPB)=h_yPB+y[-PHP+PP' H'(I-MP)+(I-PM)H'P'P]B+yPh_B. The rational rank-two witness has det(M)=-3/25, weights (1/2,1/2), counterfactual curve (3/5,3/10), and an informative-censoring construction whose naive KM/PCR limit differs by (1/46560,-2209/124650432). Checks covered censor-positivity failure, singular-gap closure, covariance degeneracy, transport failure, growing grids, full rank, continuous-versus-grid RMST, generic delta-method collapse, and the visible literature without finding a collision. UNRESOLVED BOTTLENECK: For one fully specified right-censoring AIPCW score and tie convention, prove the joint cellwise cross-fitted expansion with o_p(K^-1/2) remainder and L2-consistent estimated influence vectors from positivity, the common moment bound, nuisance consistency, and a_K b_K=o(K^-1/2), adding any event-survival tail condition actually needed. EARLY KILL TEST: Derive that score's cross-fitted second-order remainder and verify it is O_p(a_K b_K)+o_p(K^-1/2) jointly over all fixed cells and times; if any uncancelled first-order nuisance term survives, pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ipcw_spectral_ssc_inference.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The limit law and bands are proved only for fixed dimensions, exact rank, exact post-transport, and independent equal-K samples in every cell"
  - "The load-bearing AIPCW expansion assumes the proof-tailored condition that the total variation of Q/Qhat-1 is O_P(a_K)"
  - "No bounded in-scope D0 root repair can restore a field-tier PASS."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_lem_joint_cell_expansion.json
  - discovery/solve_thm_joint_spectral_limit.json
  - discovery/solve_thm_band_and_rmst.json
  - discovery/solve_prop_km_pcr_cancellation.json
  - discovery/solve_prop_han_shah_fixed_grid_embedding.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the fixed-cell AIPCW expansion under an explicit finite-stratum learner
  certificate, propagated all three input blocks through the truncated-pseudoinverse map,
  obtained singular-covariance simultaneous and grid-RMST inference, and repaired the
  KM/PCR inconsistency witness as a full-data causal law. The mathematics passed review,
  but the result reached only subfield novelty because it retains fixed dimensions,
  exact transport/rank, independent equal-size cells, and a strong path-variation rate;
  reaching field requires a new dependent unequal-cell sampling theory or a concrete
  continuous-time, continuous-covariate learner theory.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 77055751
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# panel_ipcw_spectral_ssc_inference / v1 — Downgraded

**Topic.** Censoring-robust spectral synthetic survival control under covariate-dependent right censoring. Fix N0 donor units, T0 pre-treatment times, J post-treatment grid points and rank r while K independent individuals per cell tends to infinity; assume conditional independent censoring given covariates with positivity, exact donor-span transport, a rank-r singular gap, cross-fitted censor and event-survival nuisances with product rate o(K^-1/2), and nondegenerate covariance. Construct augmented-IPCW cell survival estimates, differentiate the full stacked rank-r pseudoinverse map, and prove joint root-K asymptotic linearity, a Gaussian-multiplier simultaneous band for the J-point untreated counterfactual curve, a studentized grid-RMST effect interval, and an open-subclass theorem that unadjusted KM/PCR has fixed bias. Consumer: Han and Shah's 925-patient, 10-country TCL analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For donor-pre matrix M, target row y, donor-post matrix B, and P=M_r^+, the presolver derived the full differential D(yPB)=h_yPB+y[-PHP+PP' H'(I-MP)+(I-PM)H'P'P]B+yPh_B. The rational rank-two witness has det(M)=-3/25, weights (1/2,1/2), counterfactual curve (3/5,3/10), and an informative-censoring construction whose naive KM/PCR limit differs by (1/46560,-2209/124650432). Checks covered censor-positivity failure, singular-gap closure, covariance degeneracy, transport failure, growing grids, full rank, continuous-versus-grid RMST, generic delta-method collapse, and the visible literature without finding a collision. UNRESOLVED BOTTLENECK: For one fully specified right-censoring AIPCW score and tie convention, prove the joint cellwise cross-fitted expansion with o_p(K^-1/2) remainder and L2-consistent estimated influence vectors from positivity, the common moment bound, nuisance consistency, and a_K b_K=o(K^-1/2), adding any event-survival tail condition actually needed. EARLY KILL TEST: Derive that score's cross-fitted second-order remainder and verify it is O_p(a_K b_K)+o_p(K^-1/2) jointly over all fixed cells and times; if any uncancelled first-order nuisance term survives, pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ipcw_spectral_ssc_inference.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The limit law and bands are proved only for fixed dimensions, exact rank, exact post-transport, and independent equal-K samples in every cell.

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
