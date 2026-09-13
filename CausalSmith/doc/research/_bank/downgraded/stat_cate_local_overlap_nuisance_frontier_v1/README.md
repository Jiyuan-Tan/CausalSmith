---
qid: stat_cate_local_overlap_nuisance_frontier
spec: v1
topic: "Exact-uniform pointwise CATE under local overlap: a sharp supplied-propensity benchmark for every kappa, total unknown-propensity brackets, and a total second-order bounded-overlap estimator attaining the oracle rate at and above the nuisance elbow.  MODEL AND TARGET: For each fixed integer d>=1, kappa>=0, alpha>0, beta>0, and gamma>beta, observe n>=2 iid O=(X,A,Y), with X exactly uniform on [0,1]^d with known law and A,Y binary. Put r(x)=||x||_infinity and use r^0=1 including at zero. The propensity is e(x)=r(x)^kappa g(x)/4, where the unknown g belongs to Holder H^alpha(L) and 1<=g<=2. The control mean mu0 belongs to H^beta(L), the continuous contrast tau belongs to H^gamma(L), and mu0 and mu1=mu0+tau both take values in [1/8,7/8]. The fixed known L>=4. H^s(L) uses derivatives through m=ceil(s)-1, bounded by L, with derivatives of order m uniformly (s-m)-Holder on the cube; when m=0 this includes the function bound. No smoothness of E[Y|X] is assumed. Conditional outcomes obey Y|X,A=a ~ Bernoulli(mu_a(X)). For causal interpretation impose consistency and conditional exchangeability; independent potential Bernoulli outcomes given X give a valid completion. The target tau(0) is the value of the unique continuous extension from x!=0. For kappa>0 the propensity vanishes only at the measure-zero corner and is positive almost everywhere, so this remains an estimation problem. Estimators know d,kappa,alpha,beta,gamma,L and the uniform design law, but not g,e,mu0,tau.  KERNEL: Define R_n(d,kappa,alpha,beta,gamma,L)=inf_T sup_P E_P|T(O_1,...,O_n)-tau_P(0)| over all Borel data-only estimators and the exact class above. Separately define the oracle risk R_n^e when the full propensity function e is supplied. Prove the sharp oracle benchmark R_n^e asymp n^{-gamma/(2gamma+d+kappa)} for every kappa. Construct a total first-order estimator proving the all-kappa bracket c n^{-gamma/(2gamma+d+kappa)} <= R_n <= C n^{-t/(2t+d+kappa)}, t=min{gamma,alpha+beta}. For kappa=0, construct a total one-sided second-order projection estimator and prove R_n <= C max{n^{-gamma/(2gamma+d)}, n^{-1/D_star}}, where D_star=1+d/(2gamma)+d/(2(alpha+beta)); combine it with the oracle lower bound to prove R_n asymp n^{-gamma/(2gamma+d)} when alpha+beta>=d gamma/(2gamma+d), including equality with no logarithmic loss. Below that elbow, claim only the proved bracket and leave the exact-uniform nuisance converse open. For kappa>0, claim only the proved first-order bracket and leave the higher-order rate, critical logarithms, matching converse, and necessary-and-sufficient oracle-penalty partition open. Every estimator must be total, computable from sample moments and finite matrix operations, and uniform over the same exact class.  COMPUTATION: Use localized weighted polynomial moments for the first-order estimator. At kappa=0 use finite-dimensional projection U-statistic corrections to both matrix and vector moments, the known exact Lebesgue Gram matrix, deterministic bandwidth and projection-rank tuning, explicit singular-value flooring, and clipping. State the finite algorithm and tuning directly in the estimator presentation rather than only inside a proof.  CONSUMER AND POSITIONING: The official grf causal_forest/R-learner workflow estimates heterogeneous effects using learned outcome and propensity regressions and treatment-balanced leaf restrictions, and diagnoses weak overlap as a barrier. These theorems provide a precision benchmark; they do not claim that the existing forest attains it. KBRW2024 supplies the closest bounded-overlap higher-order rate architecture on a density-qualified design class. Do not claim that rate itself is new. The specialized contribution is a direct one-sided exact-uniform construction with known Lebesgue Gram, total stabilization on every dataset, and an honest class-specific account of which converse does not transfer. Position Athey-Wager policy learning as a downstream welfare problem with a different loss, or remove it if unused.  OPEN FOLLOW-ONS: The matching exact-uniform fixed-n Bernoulli product-mixture lower bound below the kappa=0 nuisance elbow is open; KBRW's perforated-support hard laws are not members of the singleton uniform-design class. The complete kappa>0 higher-order frontier is also open. Do not infer either result from one-observation mixture cancellation, support deletion, disjoint microbumps that violate gamma-Holder smoothness, or an oracle submodel."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised full same-class unknown-propensity frontier remains open for kappa>0, and the matching exact-uniform nuisance lower bound below the bounded-overlap elbow is not proved."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The note proves a sharp supplied-propensity rate for every κ and an unknown-propensity oracle-rate result only in the relatively smooth region α+β≥γ; elsewhere for κ>0 it delivers only a first-order bracket, leaving the principal higher-order frontier, logarithmic boundaries, and oracle-penalty classification open."
  - "Its κ=0 higher-order rate and elbow are expressly already covered by Kennedy–Balakrishnan–Robins–Wasserman, so totalization and exact-uniform implementation are incremental rather than a new rate result."
  - "The delivered contribution remains too specialized and incomplete for the field tier or a projected leading-journal score of 7.8."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_lem_bounded_overlap_second_order_risk.json
  - discovery/solve_thm_bounded_overlap_second_order.json
  - discovery/solve_thm_bounded_overlap_reduction.json
  - discovery/d0_escalation_log.jsonl
seeds_burned:
  - index: 0
    one_liner: "full-local-zero-minimax-frontier"
    reason: "The sole accepted angle exhausted five solve rounds and three D0.5 revisions; the only tier-lifting path is the unresolved central fixed-n product-mixture converse."
proof_attempt_summary: |
  D0 proved the all-κ supplied-propensity minimax rate, a total first-order
  unknown-propensity bracket, and a total exact-uniform second-order estimator at
  κ=0 that attains the oracle rate at and above the nuisance elbow. The attempted
  field-tier completion failed at the matching fixed-n Bernoulli product-mixture
  converse below that elbow: disjoint bumps violate γ-Hölder smoothness, overlapping
  frames lose partition locality, and filling support holes leaves a divergent
  n h^d δ² term. A future retry must prove that converse or derive and match a
  corrected rate, then complete the κ>0 higher-order frontier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 46350432
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 46350432
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# stat_cate_local_overlap_nuisance_frontier / v1 — Downgraded

**Topic.** Exact-uniform pointwise CATE under local overlap: a sharp supplied-propensity benchmark for every kappa, total unknown-propensity brackets, and a total second-order bounded-overlap estimator attaining the oracle rate at and above the nuisance elbow.  MODEL AND TARGET: For each fixed integer d>=1, kappa>=0, alpha>0, beta>0, and gamma>beta, observe n>=2 iid O=(X,A,Y), with X exactly uniform on [0,1]^d with known law and A,Y binary. Put r(x)=||x||_infinity and use r^0=1 including at zero. The propensity is e(x)=r(x)^kappa g(x)/4, where the unknown g belongs to Holder H^alpha(L) and 1<=g<=2. The control mean mu0 belongs to H^beta(L), the continuous contrast tau belongs to H^gamma(L), and mu0 and mu1=mu0+tau both take values in [1/8,7/8]. The fixed known L>=4. H^s(L) uses derivatives through m=ceil(s)-1, bounded by L, with derivatives of order m uniformly (s-m)-Holder on the cube; when m=0 this includes the function bound. No smoothness of E[Y|X] is assumed. Conditional outcomes obey Y|X,A=a ~ Bernoulli(mu_a(X)). For causal interpretation impose consistency and conditional exchangeability; independent potential Bernoulli outcomes given X give a valid completion. The target tau(0) is the value of the unique continuous extension from x!=0. For kappa>0 the propensity vanishes only at the measure-zero corner and is positive almost everywhere, so this remains an estimation problem. Estimators know d,kappa,alpha,beta,gamma,L and the uniform design law, but not g,e,mu0,tau.  KERNEL: Define R_n(d,kappa,alpha,beta,gamma,L)=inf_T sup_P E_P|T(O_1,...,O_n)-tau_P(0)| over all Borel data-only estimators and the exact class above. Separately define the oracle risk R_n^e when the full propensity function e is supplied. Prove the sharp oracle benchmark R_n^e asymp n^{-gamma/(2gamma+d+kappa)} for every kappa. Construct a total first-order estimator proving the all-kappa bracket c n^{-gamma/(2gamma+d+kappa)} <= R_n <= C n^{-t/(2t+d+kappa)}, t=min{gamma,alpha+beta}. For kappa=0, construct a total one-sided second-order projection estimator and prove R_n <= C max{n^{-gamma/(2gamma+d)}, n^{-1/D_star}}, where D_star=1+d/(2gamma)+d/(2(alpha+beta)); combine it with the oracle lower bound to prove R_n asymp n^{-gamma/(2gamma+d)} when alpha+beta>=d gamma/(2gamma+d), including equality with no logarithmic loss. Below that elbow, claim only the proved bracket and leave the exact-uniform nuisance converse open. For kappa>0, claim only the proved first-order bracket and leave the higher-order rate, critical logarithms, matching converse, and necessary-and-sufficient oracle-penalty partition open. Every estimator must be total, computable from sample moments and finite matrix operations, and uniform over the same exact class.  COMPUTATION: Use localized weighted polynomial moments for the first-order estimator. At kappa=0 use finite-dimensional projection U-statistic corrections to both matrix and vector moments, the known exact Lebesgue Gram matrix, deterministic bandwidth and projection-rank tuning, explicit singular-value flooring, and clipping. State the finite algorithm and tuning directly in the estimator presentation rather than only inside a proof.  CONSUMER AND POSITIONING: The official grf causal_forest/R-learner workflow estimates heterogeneous effects using learned outcome and propensity regressions and treatment-balanced leaf restrictions, and diagnoses weak overlap as a barrier. These theorems provide a precision benchmark; they do not claim that the existing forest attains it. KBRW2024 supplies the closest bounded-overlap higher-order rate architecture on a density-qualified design class. Do not claim that rate itself is new. The specialized contribution is a direct one-sided exact-uniform construction with known Lebesgue Gram, total stabilization on every dataset, and an honest class-specific account of which converse does not transfer. Position Athey-Wager policy learning as a downstream welfare problem with a different loss, or remove it if unused.  OPEN FOLLOW-ONS: The matching exact-uniform fixed-n Bernoulli product-mixture lower bound below the kappa=0 nuisance elbow is open; KBRW's perforated-support hard laws are not members of the singleton uniform-design class. The complete kappa>0 higher-order frontier is also open. Do not infer either result from one-observation mixture cancellation, support deletion, disjoint microbumps that violate gamma-Holder smoothness, or an oracle submodel.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered contribution remains too specialized and incomplete for field tier; the exact-uniform nuisance-dominated converse needed for a new bounded-overlap minimax characterization is absent.

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
