---
qid: exp_conflictgraph_uniform_clt_degree_frontier
spec: v1
topic: "When normal confidence intervals work under Conflict Graph Design: a sharp degree frontier. For each n>=1 observe one design realization on n fixed labeled units with known simple undirected graph G and arbitrary-neighborhood-interference potential outcomes. Endpoint arrays a_i=Y_i(e_i), b_i=Y_i(0) define direct effect tau=n^-1 sum_i(a_i-b_i). H has adjacency I+A_G, lambda=lambda_max(H)>=1, D=max_i(1+deg_G(i)). Order each connected component by descending positive unit-norm Perron coordinate, ties by label; concatenate components by smallest label. B_i is the set of earlier neighbors. Independently sample U_i=1,0,* with probabilities 1/(4lambda),1/(4lambda),1-1/(2lambda). Fix r=2 and use published CGD Algorithm1 to realize E_ik={U_i=k, all earlier neighbors null}. Record U and observed outcomes. q_i=Pr(E_ik)=(4lambda)^-1(1-1/(2lambda))^|B_i|. T=n^-1 sum_i Yobs_i(1[E_i1]-1[E_i0])/q_i. For fixed B>=1 and 0<c<=1 impose n^-1 sum_i |a_i|^4<=B, n^-1 sum_i |b_i|^4<=B, and sigma²=Var_U(T)>=c lambda/n. Other potential outcomes unrestricted. No maximum-outcome bound or assumed CLT. All randomness is U. Define K_n(d;B,c)=sup over the specified fixed-design class with D<=d of sup_z |Pr_U((T-tau)/sigma<=z)-Phi(z)|, for integers 1<=d<=n. For each fixed B>=1,0<c<=1 determine an explicit necessary and sufficient growth condition on every integer sequence d_n for K_n(d_n;B,c)->0, including any essential slowly varying boundary factors. Derive a quantitative uniform normal-approximation upper bound and legal failure sequences proving necessity outside that regime. The formula/exponent is answer-open, not assumed. Strictly close the unresolved gap beyond the published sufficient d=o(n^(1/9)) condition, or show that condition sharp with a new legal obstruction. Defining the frontier by the original supremum or giving only a better unmatched sufficient exponent does not deliver the kernel. For W_ik=s_k 1[E_ik]/q_i (s_1=1,s_0=-1), let V=Cov_U(W), a known 2n×2n PSD matrix. VB=lambda_max(V)n^-2 sum_i(a_i²+b_i²); VBhat=lambda_max(V)n^-2 sum_i,k (Yobs_i)²1[E_ik]/q_i. Prove uniform VBhat/VB->1 in the normal regime and conservative coverage of T±z_(1-alpha/2)sqrt(VBhat) for each fixed alpha∈(0,1), with R fallback if VBhat=0. This estimates the conservative spectral variance bound, not the generally unidentifiable exact variance. Estimator algebra and class fixed; proof mechanism delegated. CONSUMER: DeclareDesign's published Research Design in the Social Sciences, section18.10/Declaration18.13, https://book.declaredesign.org/library/experimental-causal.html, implements the inquiry direct_ATE=mean(Y_1_0-Y_0_0) using the interference package for a lawn-sign/vote-margin design modeled after Green et al. (2016), The Effects of Lawn Signs on Vote Outcomes: Results from Four Randomized Field Experiments, Electoral Studies41:143–150. Its units are 238 Fairfax voting precincts; treatment is placement of candidate lawn signs, outcome is precinct vote margin, and the known undirected graph is geographic queen adjacency from poly2nb. The declared hop=1 model makes Y_i(e_i)=Y_1_0 and Y_i(0)=Y_0_0: signs in i with no neighboring signs versus no local signs. This is exactly this kernel's direct-effect inquiry, and the broader arbitrary-neighborhood class includes that exposure model. Changed practice: for future CGD replications of this SAME inquiry, replace the assignment/estimator by fixed CGD and use the derived degree rule to choose when its shorter Wald interval is justified rather than conservative Chebyshev calibration. The published declaration uses Bernoulli assignment and Aronow–Samii HT/Hajek, not CGD; no historical interval is retroactively validated, and the theorem gives an asymptotic benchmark rather than a finite-n certificate for the 238-precinct example.\nPRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh presolve derived an exact forward Doob decomposition of the fixed r=2 estimator. Oriented-adjacency interpolation controls the sum of fourth increments by C B n lambda D²; a prefix-product coordinate-flip bound and Bernoulli variance tensorization control quadratic-variation variance by C B n lambda² D. A classical martingale normal-approximation theorem then suggests the sharp condition d_n=o(n^(2/3)). Repeated Perron-ordered stars give a Gaussian-plus-centered-Poisson boundary limit while preserving the original endpoint fourth moments and variance floor. A separate second-moment argument supports the stipulated spectral variance-bound estimator and conservative Wald coverage. Seven finite graph-family enumerations passed; these checks are not a universal proof. Direct substitutions in recent generic dependency-graph bounds did not supply the same frontier.\nUNRESOLVED BOTTLENECK: Independently audit the general coordinate-flip envelope and its operator-norm chain in draft equations (4.1)–(4.4), alongside the imported martingale theorem; the proposed exponent remains unverified.\nEARLY KILL TEST: Prove or refute equation (4.2) for overlapping parent prefixes and arbitrary signed endpoints, especially shared-parent bipartite graphs. Stop this exponent claim if repair requires stronger graph or moment assumptions; retain the original answer-open problem for reassessment.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_conflictgraph_uniform_clt_degree_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "repeated_star_boundary still requires an exact estimator/variance decomposition, eventual ModelClass witness, joint leaf-Gaussian/hub-Poisson convergence across varying finite spaces, growing-mixture interchange, and mixture moment/CDF identification"
  - "prefix_flip_moments remains sorry-backed and feeds uniform_normal_bound"
  - "This residual is the paper-owned headline boundary claim; gating it would launder the result"
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - formalization/formalization.md
  - formalization/plan.json
  - orchestrator/perron_frobenius_requirement.md
  - orchestrator/finite_design_heyde_brown_bridge_requirement.md
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run proved the premise-free repeated-star diagnostic and developed reusable Perron-order,
  finite-design Heyde--Brown, spectral-moment, and repeated-star combinatorial infrastructure.
  It stopped because the paper-owned boundary obstruction still needs a triangular-array
  Gaussian--Poisson mixture development, while prefix_flip_moments independently remains unproved;
  consequently every sorryAx-dependent field-level inference headline is excluded from this bank.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 277050379
  pipeline_claude_tokens: 9911273
  pipeline_tokens_consumed: 286961652
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_conflictgraph_uniform_clt_degree_frontier / v1 — Downgraded

**Topic.** When normal confidence intervals work under Conflict Graph Design: a sharp degree frontier. For each n>=1 observe one design realization on n fixed labeled units with known simple undirected graph G and arbitrary-neighborhood-interference potential outcomes. Endpoint arrays a_i=Y_i(e_i), b_i=Y_i(0) define direct effect tau=n^-1 sum_i(a_i-b_i). H has adjacency I+A_G, lambda=lambda_max(H)>=1, D=max_i(1+deg_G(i)). Order each connected component by descending positive unit-norm Perron coordinate, ties by label; concatenate components by smallest label. B_i is the set of earlier neighbors. Independently sample U_i=1,0,* with probabilities 1/(4lambda),1/(4lambda),1-1/(2lambda). Fix r=2 and use published CGD Algorithm1 to realize E_ik={U_i=k, all earlier neighbors null}. Record U and observed outcomes. q_i=Pr(E_ik)=(4lambda)^-1(1-1/(2lambda))^|B_i|. T=n^-1 sum_i Yobs_i(1[E_i1]-1[E_i0])/q_i. For fixed B>=1 and 0<c<=1 impose n^-1 sum_i |a_i|^4<=B, n^-1 sum_i |b_i|^4<=B, and sigma²=Var_U(T)>=c lambda/n. Other potential outcomes unrestricted. No maximum-outcome bound or assumed CLT. All randomness is U. Define K_n(d;B,c)=sup over the specified fixed-design class with D<=d of sup_z |Pr_U((T-tau)/sigma<=z)-Phi(z)|, for integers 1<=d<=n. For each fixed B>=1,0<c<=1 determine an explicit necessary and sufficient growth condition on every integer sequence d_n for K_n(d_n;B,c)->0, including any essential slowly varying boundary factors. Derive a quantitative uniform normal-approximation upper bound and legal failure sequences proving necessity outside that regime. The formula/exponent is answer-open, not assumed. Strictly close the unresolved gap beyond the published sufficient d=o(n^(1/9)) condition, or show that condition sharp with a new legal obstruction. Defining the frontier by the original supremum or giving only a better unmatched sufficient exponent does not deliver the kernel. For W_ik=s_k 1[E_ik]/q_i (s_1=1,s_0=-1), let V=Cov_U(W), a known 2n×2n PSD matrix. VB=lambda_max(V)n^-2 sum_i(a_i²+b_i²); VBhat=lambda_max(V)n^-2 sum_i,k (Yobs_i)²1[E_ik]/q_i. Prove uniform VBhat/VB->1 in the normal regime and conservative coverage of T±z_(1-alpha/2)sqrt(VBhat) for each fixed alpha∈(0,1), with R fallback if VBhat=0. This estimates the conservative spectral variance bound, not the generally unidentifiable exact variance. Estimator algebra and class fixed; proof mechanism delegated. CONSUMER: DeclareDesign's published Research Design in the Social Sciences, section18.10/Declaration18.13, https://book.declaredesign.org/library/experimental-causal.html, implements the inquiry direct_ATE=mean(Y_1_0-Y_0_0) using the interference package for a lawn-sign/vote-margin design modeled after Green et al. (2016), The Effects of Lawn Signs on Vote Outcomes: Results from Four Randomized Field Experiments, Electoral Studies41:143–150. Its units are 238 Fairfax voting precincts; treatment is placement of candidate lawn signs, outcome is precinct vote margin, and the known undirected graph is geographic queen adjacency from poly2nb. The declared hop=1 model makes Y_i(e_i)=Y_1_0 and Y_i(0)=Y_0_0: signs in i with no neighboring signs versus no local signs. This is exactly this kernel's direct-effect inquiry, and the broader arbitrary-neighborhood class includes that exposure model. Changed practice: for future CGD replications of this SAME inquiry, replace the assignment/estimator by fixed CGD and use the derived degree rule to choose when its shorter Wald interval is justified rather than conservative Chebyshev calibration. The published declaration uses Bernoulli assignment and Aronow–Samii HT/Hajek, not CGD; no historical interval is retroactively validated, and the theorem gives an asymptotic benchmark rather than a finite-n certificate for the 238-precinct example.
PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh presolve derived an exact forward Doob decomposition of the fixed r=2 estimator. Oriented-adjacency interpolation controls the sum of fourth increments by C B n lambda D²; a prefix-product coordinate-flip bound and Bernoulli variance tensorization control quadratic-variation variance by C B n lambda² D. A classical martingale normal-approximation theorem then suggests the sharp condition d_n=o(n^(2/3)). Repeated Perron-ordered stars give a Gaussian-plus-centered-Poisson boundary limit while preserving the original endpoint fourth moments and variance floor. A separate second-moment argument supports the stipulated spectral variance-bound estimator and conservative Wald coverage. Seven finite graph-family enumerations passed; these checks are not a universal proof. Direct substitutions in recent generic dependency-graph bounds did not supply the same frontier.
UNRESOLVED BOTTLENECK: Independently audit the general coordinate-flip envelope and its operator-norm chain in draft equations (4.1)–(4.4), alongside the imported martingale theorem; the proposed exponent remains unverified.
EARLY KILL TEST: Prove or refute equation (4.2) for overlapping parent prefixes and arbitrary signed endpoints, especially shared-parent bipartite graphs. Stop this exponent claim if repair requires stronger graph or moment assumptions; retain the original answer-open problem for reassessment.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_conflictgraph_uniform_clt_degree_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** substrate-unbuildable: premise-free diagnostic proved, but paper-owned repeated-star boundary and prefix-flip moment chains remain unverified; no frozen claim was refuted

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
