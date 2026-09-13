---
qid: exp_mrd_spectral_honest_length_frontier
spec: v1
topic: "Sharp honest interval-length frontier for four-exposure multiple-randomization experiments. For every even n>=4 independently select n/2 buyers and n/2 sellers uniformly from n each. A fixed schedule consists of four matrices Y^gamma in [-2,2]^(n x n), gamma=(tr,ib,is,cc), satisfying exposure consistency under the published local-interference model. Observe assignments and exactly one Y^gamma_ij per pair. Fix direct-effect contrast c=(1,-1,-1,1). Target tau=n^-2 sum_ij sum_gamma c_gamma Y^gamma_ij. Let tauhat be the contrast of four observed block means. Let r=(2W_B-1)*sqrt((n-1)/n), s analogous, so Cov(r)=Cov(s)=P_n=I-11^T/n. Expand uniquely tauhat-tau=a^T r+b^T s+r^T C s with centered a,b and P_n C P_n=C. Define Vplus=(sum_gamma |c_gamma| sqrt(Var_design(Ybarhat_gamma)))^2, precisely source equation 41. Its four component variances are population design quantities, not assumed known to the procedure. For rho in [0,1], F_n(rho) consists of all such schedules with Vplus>=1/(100 n^2), ||C||op/sqrt(Vplus)<=rho, and max_i,j{|a_i|,|b_j|,||C_i.||2,||C_.j||2}/sqrt(Vplus)<=n^(-1/8). Empty finitely many F_n do not define asymptotic claims; show eventual nonemptiness. No assumed CLT, observed spectral profile, variance consistency at chaos boundary, or counterfactual covariance is supplied. For fixed alpha in (0,1/4) define H_alpha(rho) as all sequences of data-measurable (optionally independently randomized) closed intervals I_n with liminf_even n inf_{Y in F_n(rho)} Pr_Y(tau(Y) in I_n)>=1-alpha. Determine the exact asymptotic decision value R_alpha(rho)=inf_{(I_n) in H_alpha(rho)} limsup_even n sup_{Y in F_n(rho)} E_Y length(I_n)/sqrt(Vplus(Y)) for every rho in [0,1], and construct a finite data-computable sequence attaining it, or epsilon-attaining for every epsilon>0, with a matching lower bound against all intervals on the same four-schedule observation experiment. Establish the alignment-aware low-influence Gaussian-chaos approximation needed for the interval and characterize the Gaussian limit boundary. The curve, its possible flatness, and whether Gaussian versus finite-rank interactions change the optimal constant are answers to derive, not assumed conclusions. An exact characterization by a limiting variational problem counts only if accompanied by a convergent finite evaluation algorithm with certified error; restating the original infimum, Chebyshev intervals without sharpness, or declaring Gaussian replacement the main result does not complete the kernel. Explicit interval from the observed four-block table; finite calibration algorithm with a proved convergence/error certificate for any limiting optimization. Full potential outcomes, true Vplus, and unobserved cross-world covariances cannot be inputs. Numerical integration or finite optimization is allowed; exact algorithm and complexity are outputs. Novelty is the sharp observed-data frontier, not Gaussian approximation, a generic finite LP, or conservative intervals alone. Consumers are published MRD marketplace inference and Liu–Shaikh–Toulis's Comola–Prina savings-network reanalysis; the square-half design is an idealized benchmark. Primary sources and exact assumptions are recorded in <repo-root>/internal/topic_selection_20260909_novel2/candidate_final.json.\n\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact four-exposure linear-plus-bilinear decomposition and variance identity, a quantitative balanced-slice-to-Gaussian replacement preserving shared coordinates, and a certified rank truncation. An interval computed from observed block row and column standard deviations has finite-sample honesty and expected length bounded by a loose constant times the population Neyman envelope. A canceled single-row schedule proves that this envelope cannot be uniformly estimated in relative error even at rho=0; therefore plug-in spectral calibration is not justified. Finite assignment enumeration checked decomposition, moment identities, and the non-Gaussian witness. A hypergeometric lower-benchmark transfer is only sketched. Current MRD, multiway-clustering, and one-population minimax sources did not supply the exact requested frontier. None of this proves the sharp curve.\nUNRESOLVED BOTTLENECK: Construct explicit finite completion games retaining unobserved potential-outcome ambiguity and irregular component nuisance, and prove both uniform observable-policy attainment and same-experiment all-interval lower transfer with a computable vanishing error.\nEARLY KILL TEST: At n=8,12 and rho=0,.5,.8,1 compare certified interval LPs on admissible hypergeometric, aligned-interaction, and canceled-nuisance families with quantized-data upper policies. Equal statistic profiles with different decision values reject a profile-only reduction; preserve the full experiment or pivot that route. Drop only for an affirmative collision, generic reduction, or obstruction to every route.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_mrd_spectral_honest_length_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "No exact sufficient-experiment or complete-class theorem couples arbitrary interval policies across raw and quantized observation spaces."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "No rank-K truncated schedule, experiment, likelihood, or calibrated-risk functional is defined."
  - "generic linear contrasts are handled by the displayed formula after Theorem 4.4 and Lemma A.18"
  - "The all-policy raw-to-grid discrepancy can equal 1 because policies act independently on the disjoint observation spaces, contradicting the required chi <= n^-3."
reusable_artifacts:
  - "discovery/proto_core.json — final finite-game specification and bibliography; reuse only the exact decomposition, witnesses, and source map, not the failed transfer theorem."
  - "discovery/proto_core.json.attempt-a5f5fca9-c3f8-43fc-a327-719947a6f753 — validated v5 attempt preserving the robust completion-cell formulation."
  - "reviews/angle0_v6.json — terminal reviewer audit of the rank-truncation and Masoero locator defects."
seeds_burned:
  - index: 0
    one_liner: "seed:sharp-observed-data-frontier"
    reason: "Angle 0 exhausted six revisions; validity gate found the central all-interval transfer false as defined and not locally repairable."
proof_attempt_summary: |
  Six proposal revisions developed the exact linear-plus-bilinear MRD decomposition,
  low-influence Gaussian-chaos approximation, completion-cell finite games, observable
  interval ideas, and persistent-rank witnesses. The central lower/upper decision transfer
  collapsed because arbitrary interval policies can act independently on raw and quantized
  observations, forcing the proposed discrepancy to one; repairing this requires a new exact
  sufficient-experiment or complete-class theorem, not another local revision.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 61073816
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 61073816
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_mrd_spectral_honest_length_frontier / v1 — Failed

**Topic.** Sharp honest interval-length frontier for four-exposure multiple-randomization experiments. For every even n>=4 independently select n/2 buyers and n/2 sellers uniformly from n each. A fixed schedule consists of four matrices Y^gamma in [-2,2]^(n x n), gamma=(tr,ib,is,cc), satisfying exposure consistency under the published local-interference model. Observe assignments and exactly one Y^gamma_ij per pair. Fix direct-effect contrast c=(1,-1,-1,1). Target tau=n^-2 sum_ij sum_gamma c_gamma Y^gamma_ij. Let tauhat be the contrast of four observed block means. Let r=(2W_B-1)*sqrt((n-1)/n), s analogous, so Cov(r)=Cov(s)=P_n=I-11^T/n. Expand uniquely tauhat-tau=a^T r+b^T s+r^T C s with centered a,b and P_n C P_n=C. Define Vplus=(sum_gamma |c_gamma| sqrt(Var_design(Ybarhat_gamma)))^2, precisely source equation 41. Its four component variances are population design quantities, not assumed known to the procedure. For rho in [0,1], F_n(rho) consists of all such schedules with Vplus>=1/(100 n^2), ||C||op/sqrt(Vplus)<=rho, and max_i,j{|a_i|,|b_j|,||C_i.||2,||C_.j||2}/sqrt(Vplus)<=n^(-1/8). Empty finitely many F_n do not define asymptotic claims; show eventual nonemptiness. No assumed CLT, observed spectral profile, variance consistency at chaos boundary, or counterfactual covariance is supplied. For fixed alpha in (0,1/4) define H_alpha(rho) as all sequences of data-measurable (optionally independently randomized) closed intervals I_n with liminf_even n inf_{Y in F_n(rho)} Pr_Y(tau(Y) in I_n)>=1-alpha. Determine the exact asymptotic decision value R_alpha(rho)=inf_{(I_n) in H_alpha(rho)} limsup_even n sup_{Y in F_n(rho)} E_Y length(I_n)/sqrt(Vplus(Y)) for every rho in [0,1], and construct a finite data-computable sequence attaining it, or epsilon-attaining for every epsilon>0, with a matching lower bound against all intervals on the same four-schedule observation experiment. Establish the alignment-aware low-influence Gaussian-chaos approximation needed for the interval and characterize the Gaussian limit boundary. The curve, its possible flatness, and whether Gaussian versus finite-rank interactions change the optimal constant are answers to derive, not assumed conclusions. An exact characterization by a limiting variational problem counts only if accompanied by a convergent finite evaluation algorithm with certified error; restating the original infimum, Chebyshev intervals without sharpness, or declaring Gaussian replacement the main result does not complete the kernel. Explicit interval from the observed four-block table; finite calibration algorithm with a proved convergence/error certificate for any limiting optimization. Full potential outcomes, true Vplus, and unobserved cross-world covariances cannot be inputs. Numerical integration or finite optimization is allowed; exact algorithm and complexity are outputs. Novelty is the sharp observed-data frontier, not Gaussian approximation, a generic finite LP, or conservative intervals alone. Consumers are published MRD marketplace inference and Liu–Shaikh–Toulis's Comola–Prina savings-network reanalysis; the square-half design is an idealized benchmark. Primary sources and exact assumptions are recorded in <repo-root>/internal/topic_selection_20260909_novel2/candidate_final.json.

PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact four-exposure linear-plus-bilinear decomposition and variance identity, a quantitative balanced-slice-to-Gaussian replacement preserving shared coordinates, and a certified rank truncation. An interval computed from observed block row and column standard deviations has finite-sample honesty and expected length bounded by a loose constant times the population Neyman envelope. A canceled single-row schedule proves that this envelope cannot be uniformly estimated in relative error even at rho=0; therefore plug-in spectral calibration is not justified. Finite assignment enumeration checked decomposition, moment identities, and the non-Gaussian witness. A hypergeometric lower-benchmark transfer is only sketched. Current MRD, multiway-clustering, and one-population minimax sources did not supply the exact requested frontier. None of this proves the sharp curve.
UNRESOLVED BOTTLENECK: Construct explicit finite completion games retaining unobserved potential-outcome ambiguity and irregular component nuisance, and prove both uniform observable-policy attainment and same-experiment all-interval lower transfer with a computable vanishing error.
EARLY KILL TEST: At n=8,12 and rho=0,.5,.8,1 compare certified interval LPs on admissible hypergeometric, aligned-interaction, and canceled-nuisance families with quantized-data upper policies. Equal statistic profiles with different decision values reject a profile-only reduction; preserve the full experiment or pivot that route. Drop only for an affirmative collision, generic reduction, or obstruction to every route.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_mrd_spectral_honest_length_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** All-policy raw-to-grid transfer permits independent actions on disjoint observations, so chi can equal 1 rather than the required n^-3; the load-bearing defect recurred across v2, v3, v4, and v6.

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
