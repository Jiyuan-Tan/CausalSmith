---
qid: pid_dropout_cate_flowsharp_set
spec: v1
topic: "Flow-sharp simultaneous CATE-curve sets under informative randomized-trial dropout. With finite baseline genomic profiles Z, a continuous predeclared prognostic score R, bounded survival, randomized treatment, censoring overlap, and profile-specific bounded nondecreasing Lipschitz residual-contribution functions, prove the law-sharp compact set of CATE curves tau_z(r)=b_1,z(r)-b_0,z(r)+s_1,z(r)-s_0,z(r). Derive a certified obstacle/min-cost-flow support representation, uniform grid Hausdorff error, and a uniformly shrinking whole-set confidence superset with simultaneous post-selection intervals for every eligible finite-VC genomic leaf. Reanalyse the ADJUVANT subgroup signs reported by Wang et al. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For any feasible s, setting q=s/u on positive-u cells and completing each censored event time at tmax with probability q yields the required contribution while preserving the observed censoring law; independent armwise completion gives sharpness and remains legal on zero-u contact sets. Each support direction separates into observed terms and arm/profile obstacle problems; grid versions are path min-cost transshipments, while Lipschitz-Hölder interpolation gives a candidate O(Lh+Mh^(beta wedge 1)) support/Hausdorff error. The obstacle set is sup-norm stable under perturbing u, and the duplicated two-profile witness is non-box. Existing pointwise dropout bounds, IV survival bounds, and generic support-function inference were checked without an estimand-level collision. UNRESOLVED BOTTLENECK: Prove one uniform theorem combining nuisance bands, robust obstacle optimization, and estimated covariate laws to attain the stated excess-Hausdorff and simultaneous selected-leaf rates through changing contact sets. EARLY KILL TEST: On ADJUVANT, predeclare R and the coarsest Z encoding the reported leaves, then propagate honest pilot bands through the obstacle program; if no leaf meets the mass conditions or every defensible-L sign interval contains zero, pivot to coarser profiles or a residual-mean sensitivity model."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Original promise to reanalyse ADJUVANT subgroup signs was replaced by a generic construction that expressly asserts no empirical subgroup sign; the independent validity gate found no lawful same-topic completion from current inputs."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised ADJUVANT subgroup-sign reanalysis is not delivered: this theorem supplies only a generic construction and expressly leaves all trial-specific inputs and sign conclusions absent, so the applied deliverable was substituted by a conditional caveat."
  - "The note proves an exact law-sharp curve identified set, exact pointwise projections, a strict-contraction characterization, and certified grid/flow representations, which is sufficient for the field tier. Its inference result is substantially narrower: uniform validity is conditional on an externally supplied band certificate, with no theorem establishing that the certified subclass is nonempty or constructing the band from the stated primitive Hölder model."
  - "The proposed ADJUVANT subgroup-sign reanalysis is not delivered, leaving the package without the empirical evidence invoked to motivate its practical significance and limiting its leading-journal score."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_law_sharp_curve_set.json
  - discovery/solve_thm_grid_hausdorff.json
  - discovery/solve_thm_wang_compatible_box_sharpness.json
  - discovery/solve_oeq_uniform_changing_contact_inference.json
seeds_burned: []
proof_attempt_summary: |
  Discovery derived a law-sharp monotone–Lipschitz CATE-curve set, exact obstacle-envelope
  projections and strictness, changing-contact stability, certified grid/flow representations,
  and a Wang-compatible endpoint-box comparison. The field package collapsed because its promised
  ADJUVANT sign reanalysis could not be run faithfully without a predeclared score, honest nuisance
  bands, a fixed eligible-leaf protocol, and externally calibrated L; the robust inference result
  also remained conditional on an external band certificate. The population identification and
  obstacle machinery remain reusable, but a future empirical run must freeze those inputs before
  outcome analysis rather than retroactively weakening the promise.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 33572123
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 33572123
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# pid_dropout_cate_flowsharp_set / v1 — Failed

**Topic.** Flow-sharp simultaneous CATE-curve sets under informative randomized-trial dropout. With finite baseline genomic profiles Z, a continuous predeclared prognostic score R, bounded survival, randomized treatment, censoring overlap, and profile-specific bounded nondecreasing Lipschitz residual-contribution functions, prove the law-sharp compact set of CATE curves tau_z(r)=b_1,z(r)-b_0,z(r)+s_1,z(r)-s_0,z(r). Derive a certified obstacle/min-cost-flow support representation, uniform grid Hausdorff error, and a uniformly shrinking whole-set confidence superset with simultaneous post-selection intervals for every eligible finite-VC genomic leaf. Reanalyse the ADJUVANT subgroup signs reported by Wang et al. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For any feasible s, setting q=s/u on positive-u cells and completing each censored event time at tmax with probability q yields the required contribution while preserving the observed censoring law; independent armwise completion gives sharpness and remains legal on zero-u contact sets. Each support direction separates into observed terms and arm/profile obstacle problems; grid versions are path min-cost transshipments, while Lipschitz-Hölder interpolation gives a candidate O(Lh+Mh^(beta wedge 1)) support/Hausdorff error. The obstacle set is sup-norm stable under perturbing u, and the duplicated two-profile witness is non-box. Existing pointwise dropout bounds, IV survival bounds, and generic support-function inference were checked without an estimand-level collision. UNRESOLVED BOTTLENECK: Prove one uniform theorem combining nuisance bands, robust obstacle optimization, and estimated covariate laws to attain the stated excess-Hausdorff and simultaneous selected-leaf rates through changing contact sets. EARLY KILL TEST: On ADJUVANT, predeclare R and the coarsest Z encoding the reported leaves, then propagate honest pilot bands through the obstacle program; if no leaf meets the mass conditions or every defensible-L sign interval contains zero, pivot to coarser profiles or a residual-mean sensitivity model.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The promised ADJUVANT subgroup-sign reanalysis is not delivered; the available data do not supply the predeclared score, honest nuisance bands, fixed eligible-leaf protocol, or externally calibrated sensitivity value required for a faithful analysis.

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
