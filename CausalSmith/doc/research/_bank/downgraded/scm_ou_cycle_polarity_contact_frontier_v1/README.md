---
qid: scm_ou_cycle_polarity_contact_frontier
spec: v1
topic: "Study exactly bivariate stationary Gaussian OU systems dX_t=-A X_t dt+D^{1/2}dW_t with known bidirected support, trace(D)=1, D diagonal and strictly positive, kappa I <= Sigma <= kappa^{-1} I, |A_12| and |A_21| at least eta, ||A||_F <= M, and iid stationary snapshots. Prove an exact characterization of the compatible sign set of A_12 A_21 using the affine Lyapunov fiber and four finite sector certificates, including explicit witnesses and every open-versus-closed attainment branch. Derive the equal-variance thresholds, exhibit an open region where neither edge sign is identified but their product sign is, and analyze the explicit asymmetric zero-diffusion contact. Invert a covariance confidence region with a measurable nearest-model fallback to obtain honest finite-sample set coverage, uniform singleton recovery beyond root-n clearance, and a matching local Gaussian lower bound on compact contact subcharts. Exclude larger-graph projection, marginalization, global boundary-distance equivalence, and empirical-performance claims. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The affine Lyapunov parametrization yields explicit scalar sector-feasibility rules: u A_12+s A_21=t[s+(u-s)d]/(2 Delta), exact same-sign strict-feasibility branches, always strictly feasible opposite-sign polygons, and a closed-form equal-variance norm after x=d-1/2 and y=q+rx/2. These reductions give positive and negative thresholds, including unattained norm equality. At the asymmetric contact, g >= (s-u)td is necessary and d=g/[2(s-u)t], q=(eta Delta-dt/2)/s constructs positive witnesses for g>0. Symbolic algebra and 400 randomized active-set comparisons supported these unverified derivations. Checks covered empty K, kappa=1, t=0, s=u, margin equality, norm equality, zero-diffusion contact, fixed-alpha empty covariance regions, and local-versus-global boundary distance; no verified current-literature collision was found. UNRESOLVED BOTTLENECK: Independently prove completeness of the finite equality-active-set certificate and its scalar J and strict-attainment branches on every rank-deficient, lower-dimensional, and norm-equality sector. EARLY KILL TEST: Exactly certify the asymmetric g=0 J-false contact, an attained equal-variance positive threshold, and the r=1/2, eta=3/5, M^2=67/45 unattained negative infimum; any failure stops this theorem spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_ou_cycle_polarity_contact_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves global product-sign nonidentification in the unrestricted bivariate class and an exact finite certificate under imposed edge-margin and norm restrictions, but the unrestricted result is an elementary two-dimensional fiber consequence and the positive identification result remains tied to a narrowly bounded refinement."
  - "The inference converse is established only around one constructed asymmetric zero-diffusion contact, so the advertised frontier is not a general characterization of the certificate boundaries, although the prose eventually discloses this local scope."
  - "No theorem-level claim is left conjectural or proved only one-sidedly, but the practical meaning and calibration of the analyst-chosen eta and M restrictions are unsupported by an application or sensitivity analysis."
  - "The positioning omits relevance/comparison sentences for cited VarandoHansen2020, AmendolaBoegeHolleringMisra2025, and BoegeBoegeHolleringMisra2025; add their precise relation to the unrestricted two-cycle polarity theorem and distinguish their scope from this product-sign result."
reusable_artifacts:
  - "discovery/core.json — complete theorem graph and proofs for the unrestricted polarity result and bounded-margin certificate."
  - "discovery/writeup.tex — maximized derivation note with the affine-fiber reduction, sector certificate, contact analysis, and inference results."
  - "discovery/solve_tex/solve_thm_sector_characterization.tex — reusable at-most-eleven-candidate active-set proof, including degenerate and strict-attainment branches."
  - "discovery/solve_tex/solve_thm_asymmetric_contact.tex — explicit zero-diffusion contact construction."
  - "discovery/solve_tex/solve_thm_rootn_obstruction.tex — local Gaussian root-n obstruction argument."
seeds_burned:
  - index: 0
    one_liner: "four_sector_certificate"
    reason: "The single bivariate OU polarity angle was mathematically sound but structurally below the field floor; the proposed all-boundary extension is a separate research program."
proof_attempt_summary: |
  The derivation proved the unrestricted published-class result P_pub(Sigma)={-1,+1}, a complete bounded-margin four-sector certificate with at most eleven active-set candidates, a t-faithful joint-only open region, the asymmetric contact, honest covariance inversion, and matched local root-n recovery and impossibility results. The mathematical review passed without findings, but the general referee graded the package incremental because the unrestricted result is elementary, the positive results remain bivariate and depend on uncalibrated eta/M restrictions, and the inference boundary theory covers only one constructed contact. A field-tier continuation would require a separate all-regular-boundary semialgebraic and LAN program; the bank also preserves the unresolved related-work positioning omission rather than claiming every D0.5 finding was discharged.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 16400629
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 16400629
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# scm_ou_cycle_polarity_contact_frontier / v1 — Downgraded

**Topic.** Study exactly bivariate stationary Gaussian OU systems dX_t=-A X_t dt+D^{1/2}dW_t with known bidirected support, trace(D)=1, D diagonal and strictly positive, kappa I <= Sigma <= kappa^{-1} I, |A_12| and |A_21| at least eta, ||A||_F <= M, and iid stationary snapshots. Prove an exact characterization of the compatible sign set of A_12 A_21 using the affine Lyapunov fiber and four finite sector certificates, including explicit witnesses and every open-versus-closed attainment branch. Derive the equal-variance thresholds, exhibit an open region where neither edge sign is identified but their product sign is, and analyze the explicit asymmetric zero-diffusion contact. Invert a covariance confidence region with a measurable nearest-model fallback to obtain honest finite-sample set coverage, uniform singleton recovery beyond root-n clearance, and a matching local Gaussian lower bound on compact contact subcharts. Exclude larger-graph projection, marginalization, global boundary-distance equivalence, and empirical-performance claims. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The affine Lyapunov parametrization yields explicit scalar sector-feasibility rules: u A_12+s A_21=t[s+(u-s)d]/(2 Delta), exact same-sign strict-feasibility branches, always strictly feasible opposite-sign polygons, and a closed-form equal-variance norm after x=d-1/2 and y=q+rx/2. These reductions give positive and negative thresholds, including unattained norm equality. At the asymmetric contact, g >= (s-u)td is necessary and d=g/[2(s-u)t], q=(eta Delta-dt/2)/s constructs positive witnesses for g>0. Symbolic algebra and 400 randomized active-set comparisons supported these unverified derivations. Checks covered empty K, kappa=1, t=0, s=u, margin equality, norm equality, zero-diffusion contact, fixed-alpha empty covariance regions, and local-versus-global boundary distance; no verified current-literature collision was found. UNRESOLVED BOTTLENECK: Independently prove completeness of the finite equality-active-set certificate and its scalar J and strict-attainment branches on every rank-deficient, lower-dimensional, and norm-equality sector. EARLY KILL TEST: Exactly certify the asymmetric g=0 J-false contact, an attained equal-variance positive threshold, and the r=1/2, eta=3/5, M^2=67/45 unattained negative infimum; any failure stops this theorem spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_ou_cycle_polarity_contact_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental < floor=field; paper_score_ceiling 6.1 < ceiling_for_field 7.4; not salvageable within scope.

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
