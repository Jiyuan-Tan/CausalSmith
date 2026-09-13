---
qid: stat_cate_homogeneity_testing_nuisance_frontier
spec: v1
topic: "Sharp minimax detection of conditional average treatment-effect heterogeneity under rough unknown confounding. Observe n iid (X,A,Y), with known X uniform on [0,1]^d, d>=1 fixed, and binary A,Y. Impose consistency and conditional exchangeability; write e(x)=P(A=1|X=x), m0(x)=E[Y|A=0,X=x], m1=m0+tau. For known fixed alpha,beta,gamma in (0,1] and L>=2 require e in H^alpha(L), m0 in H^beta(L), tau in H^gamma(L), and 1/4<=e,m0,m1<=3/4 everywhere. H^s(L) means sup|f|<=L and |f(x)-f(z)|<=L||x-z||_2^s. No true nuisance or nuisance convergence rate is supplied. Test H0: tau is an unknown constant, against D(P)=[integral(tau(x)-integral tau(u)du)^2 dx]^(1/2)>=rho. Define rho_n^* as the infimum rho>0 admitting a measurable randomized test with worst-case null rejection <=.05 and worst-case type-II error <=.2 over the separated alternatives, with empty alternative supremum zero. Determine an explicitly evaluable matching critical-radius rate for every fixed (alpha,beta,gamma,d,L), including any transition logarithms, with constants depending only on these fixed class parameters for all sufficiently large n. Supply a total finite-data attaining test, uniform calibration, tuning and computation cost, and a matching original-fixed-n all-test converse whose null priors EACH have exactly constant tau and whose alternatives satisfy the same original class. On this identical class derive the known-propensity experiment, where the test receives e_P, and characterize exactly when the unknown- and known-propensity radii have the same order. All formulas and the existence of any nuisance penalty are answer-open; smoothness adaptation is not claimed. The full rough-nuisance detection map is the kernel, not pointwise estimation, fixed-alternative power, a regular first-order product-rate theorem or an oracle-only bound. Sanity witness: e=.5+(x1-.5)/16, m0=3/8, tau=1/8+eta*sin(2*pi*x1), |eta|<=1/32, so D=|eta|/sqrt(2), ATE=1/8 and all Bernoulli probabilities satisfy the class; eta=0 is a nonzero homogeneous null. A disclosed known-c channel B|A,Y~Bernoulli(1/4+Y/2-c*A/2) converts tau=c to binary conditional independence; profiling c or importing this reduction alone is not new. Compare precisely against Neykov-Balakrishnan-Wasserman CI testing, PCM 2211.02039, Dukes et al 2410.00985v4, KBRW 2203.00837 and McGrath-Mukherjee 2212.14857 latest version. Consumer: grf::test_calibration and Shiba-Inoue AJE2024 epidemiologic heterogeneity workflows gain a detectability benchmark and a test beyond a fitted forest-score projection; do not claim to certify any existing forest or interpret non-rejection as homogeneity.\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: A derived binned covariance identity separates the homogeneous-null bias Cov_bin(e,m0), of order h^(alpha+beta), from the centered effect signal. An explicit fourth-order within-bin statistic estimates the squared covariance and profiles the unknown constant by minimizing a quadratic, without a grid. Its derived variance is bounded by C[Q/n+J/n^2+J^2/n^3+J^3/n^4]. This gives a conservative upper bound throughout the class and a matched oracle-rate region alpha+beta>=gamma, d<=4gamma, including the asymmetric example d=gamma=1, alpha=.1, beta=.9. A known-propensity projection test and fixed-n bump lower argument are supplied. Exact rational checks cover the binned identity, fourth-order expectation and first projection. Every component of a sign-prior null has constant effect and matches a heterogeneous alternative for one observation, but repeated observations expose nuisance moments. Sparse bins, zero curvature, boundary constants, exact-uniform design, and current CI/PCM/nuisance-tuning comparisons were checked; the complete frontier is unproved.\nUNRESOLVED BOTTLENECK: Establish sharp multiresolution null calibration and matching fixed-n null-supported mixtures through all sparse regimes, preserving smooth transitions under exact uniform design.\nEARLY KILL TEST: At d=gamma=1 and alpha=beta=.1, compute every correction projection and first nonmatching mixture moment; stop a leaking construction or a novelty claim closed by generic transfer.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_cate_homogeneity_testing_nuisance_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "PANEL DECISION: REVISE — kernel_substituted@oeq:complete-frontier: the original all-parameter matching critical-radius frontier, attaining omnibus test, fixed-n converse, and transition logarithms remain open; the core instead delivers an honest bracket and selected regions."
  - "COLD TIER: subfield; target/floor field; paper_score_ceiling 6.5 < 7.2; meets_floor=false; salvageable=false; improvement_directive=null."
  - "UNREPAIRED FINDINGS: complete rough-nuisance frontier, matching sparse upper bound, dense-regime nuisance converse, transition logarithms, and necessary-and-sufficient known-versus-unknown propensity comparison remain open."
reusable_artifacts:
  - "discovery/core.json — proved exact-uniform sparse-nuisance lower bound, strict unknown-propensity penalty region, and scoped obstruction diagnostics"
  - "discovery/writeup.tex — bounded four-atom prior, conditional Hellinger argument, and failed pair-factor/full-cell upper routes"
  - "discovery/vcs/ — replayable solver rounds and adjudication history"
seeds_burned: []
proof_attempt_summary: |
  The run proved an original fixed-n exact-uniform sparse-nuisance converse, including the n^(-2/7) stress-tuple lower bound, and derived a sufficient polynomial separation between unknown- and known-propensity experiments. Two distinct attaining-test architectures—pair-factor and projected full-cell kernels—failed explicit population-signal kill tests after bounded repairs. A matching sparse upper bound, dense-regime nuisance converse, transition logarithms, and the necessary-and-sufficient propensity frontier remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 79044602
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 79044602
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_cate_homogeneity_testing_nuisance_frontier / v1 — Downgraded

**Topic.** Sharp minimax detection of conditional average treatment-effect heterogeneity under rough unknown confounding. Observe n iid (X,A,Y), with known X uniform on [0,1]^d, d>=1 fixed, and binary A,Y. Impose consistency and conditional exchangeability; write e(x)=P(A=1|X=x), m0(x)=E[Y|A=0,X=x], m1=m0+tau. For known fixed alpha,beta,gamma in (0,1] and L>=2 require e in H^alpha(L), m0 in H^beta(L), tau in H^gamma(L), and 1/4<=e,m0,m1<=3/4 everywhere. H^s(L) means sup|f|<=L and |f(x)-f(z)|<=L||x-z||_2^s. No true nuisance or nuisance convergence rate is supplied. Test H0: tau is an unknown constant, against D(P)=[integral(tau(x)-integral tau(u)du)^2 dx]^(1/2)>=rho. Define rho_n^* as the infimum rho>0 admitting a measurable randomized test with worst-case null rejection <=.05 and worst-case type-II error <=.2 over the separated alternatives, with empty alternative supremum zero. Determine an explicitly evaluable matching critical-radius rate for every fixed (alpha,beta,gamma,d,L), including any transition logarithms, with constants depending only on these fixed class parameters for all sufficiently large n. Supply a total finite-data attaining test, uniform calibration, tuning and computation cost, and a matching original-fixed-n all-test converse whose null priors EACH have exactly constant tau and whose alternatives satisfy the same original class. On this identical class derive the known-propensity experiment, where the test receives e_P, and characterize exactly when the unknown- and known-propensity radii have the same order. All formulas and the existence of any nuisance penalty are answer-open; smoothness adaptation is not claimed. The full rough-nuisance detection map is the kernel, not pointwise estimation, fixed-alternative power, a regular first-order product-rate theorem or an oracle-only bound. Sanity witness: e=.5+(x1-.5)/16, m0=3/8, tau=1/8+eta*sin(2*pi*x1), |eta|<=1/32, so D=|eta|/sqrt(2), ATE=1/8 and all Bernoulli probabilities satisfy the class; eta=0 is a nonzero homogeneous null. A disclosed known-c channel B|A,Y~Bernoulli(1/4+Y/2-c*A/2) converts tau=c to binary conditional independence; profiling c or importing this reduction alone is not new. Compare precisely against Neykov-Balakrishnan-Wasserman CI testing, PCM 2211.02039, Dukes et al 2410.00985v4, KBRW 2203.00837 and McGrath-Mukherjee 2212.14857 latest version. Consumer: grf::test_calibration and Shiba-Inoue AJE2024 epidemiologic heterogeneity workflows gain a detectability benchmark and a test beyond a fitted forest-score projection; do not claim to certify any existing forest or interpret non-rejection as homogeneity.
PRESOLVE EVIDENCE REQUIRING VERIFICATION: A derived binned covariance identity separates the homogeneous-null bias Cov_bin(e,m0), of order h^(alpha+beta), from the centered effect signal. An explicit fourth-order within-bin statistic estimates the squared covariance and profiles the unknown constant by minimizing a quadratic, without a grid. Its derived variance is bounded by C[Q/n+J/n^2+J^2/n^3+J^3/n^4]. This gives a conservative upper bound throughout the class and a matched oracle-rate region alpha+beta>=gamma, d<=4gamma, including the asymmetric example d=gamma=1, alpha=.1, beta=.9. A known-propensity projection test and fixed-n bump lower argument are supplied. Exact rational checks cover the binned identity, fourth-order expectation and first projection. Every component of a sign-prior null has constant effect and matches a heterogeneous alternative for one observation, but repeated observations expose nuisance moments. Sparse bins, zero curvature, boundary constants, exact-uniform design, and current CI/PCM/nuisance-tuning comparisons were checked; the complete frontier is unproved.
UNRESOLVED BOTTLENECK: Establish sharp multiresolution null calibration and matching fixed-n null-supported mixtures through all sparse regimes, preserving smooth transitions under exact uniform design.
EARLY KILL TEST: At d=gamma=1 and alpha=beta=.1, compute every correction projection and first nonmatching mixture moment; stop a leaking construction or a novelty claim closed by generic transfer.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_cate_homogeneity_testing_nuisance_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** PANEL DECISION: the original all-parameter matching critical-radius frontier, attaining omnibus test, fixed-n converse, and transition logarithms remain open; the core instead delivers an honest bracket and selected regions.

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
