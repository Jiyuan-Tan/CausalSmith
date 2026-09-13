---
qid: exp_finitepopulation_variance_rounding_frontier
spec: v1
topic: "The sharp finite-population price of fractional causal variance bounds. For each integer N>=2 take three multisets x_a=(x_a1,...,x_aN) in [0,1]^N, repeats permitted. Fixed contrast c=(1/4,1/4,-1/2). Put F_a=N^-1 sum_i delta_x_ai. V_rel(x)=inf over all probability couplings pi with marginals(F1,F2,F3) of E_pi[(sum_a c_a Y_a)^2]. V_int(x)=min over permutations sigma2,sigma3 of N^-1 sum_i(c1 x_1i+c2 x_2,sigma2(i)+c3 x_3,sigma3(i))^2. Define Delta_N=sup_x[V_int(x)-V_rel(x)]. Population marginal means are fixed, so the identical gap holds for contrast variances. For N>=3, under complete random assignment with fixed positive arm sizes n1+n2+n3=N, the sharp estimator-variance upper bound based on the known marginals differs between fractional and realizable completions by (V_int-V_rel)/(N-1). No claim that all full marginals are observed in one experiment. Determine the sharp asymptotic order of Delta_N, with any necessary arithmetic subsequences explicitly resolved: derive an explicit rate sequence r_N and universal constants 0<a<=b<infinity such that a r_N<=Delta_N<=b r_N for all sufficiently large N (or exact zero exceptional N classified). Prove the upper bound by a deterministic algorithm, polynomial in N and rational-input bit length, that takes empirical marginals and an optimal rational fractional coupling and outputs N-row permutations with cost at most V_rel+b r_N. Prove the matching lower bound over the SAME three-arm scalar [0,1] class by explicit families. The exponent/log factors and proof mechanics are answer-open; no unverified rate is assumed. Translate the guarantee into computable two-sided certificates for the marginal-information sharp randomization variance, and provide a consistent plug-in estimator of its endpoints under complete randomization, deriving sampling error from the empirical marginal distributions. A generic finite LP or an arbitrary vanishing rate is insufficient. Grounding: Gao-Ge-Qian (AISTATS2025), Brennan et al. (ICML2025), Haus (2015), and Puccetti-Wang (2015); the new object is same-empirical-marginal fractional-versus-N-row squared-cost loss, not quantile-discretization error, a generic integer program, or ordinary bottleneck mixability. Consumer: three-arm contrast comparisons within published multi-arm trials such as ACTG175 (Hammer et al.1996). PRESOLVE EVIDENCE REQUIRING VERIFICATION: The informal draft derives ordered support-slope intervals from fractional LP duality, builds nested dyadic partitions, freezes integer masses from successive basic feasible tables, and repairs each marginal hierarchically. Its quadratic slack accounting gives a candidate universal upper bound 3456/N. An exactly certified four-row obstruction, padded with isolated dummy rows, gives 1/(46080N) for every N at least four. Thus the supported answer is a sharp 1/N rate within the original answer-open coordinates. Thirty-six rational implementation checks passed, using numerical bases only as proposals followed by exact rational verification. Repeated atoms, dyadic boundary contacts, replication parity, and the two-row case were checked; arbitrarily tiny rational gaps are covered by the bit-length argument rather than a floating-point LP experiment. The variance certificates concern the sharp upper endpoint, with sampling uncertainty separately retained.\nUNRESOLVED BOTTLENECK: Independently verify the slope-interval bound, residual-to-repair accounting, and polynomial rational vertex extraction; no remaining structural mathematical gap was identified, but standard LP, tree-matching, quantile/gluing and sampling steps remain compressed.\nEARLY KILL TEST: Reconstruct the three load-bearing inequalities on exact optimal supports with ties and boundary contacts; stop this route on a counterexample, or on a verified same-marginal sharp-rounding prior-art collision.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/round1040_presolve_strongest.md. PRACTICAL LIMITATION: The useful numerical certificate is the actual primal-dual width. The loose universal 3456/N bound may be uninformative at ordinary trial sizes, and the sampling uncertainty is larger than the deterministic rounding term asymptotically."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Exact normalized frontier/extremal constant remains open; 402/N is loose, the O(N^-2) causal variance correction is dominated by sampling error, computational validation is compressed, and boundary-count/target-functional findings remain unrepaired."
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "The note proves the advertised sharp order, not the exact frontier: it establishes a same-class 1/N bracket, while the limit of N Delta_N and the extremal constant remain open."
  - "The universal upper constant is extremely loose—402/N is weaker than the trivial bound until N=1609—and the resulting O(N^-2) variance correction is dominated by the proved sampling error."
  - "The exact-rational polynomial-time claim is supported only by a compressed freezing/tree-matching specification and a high-level bit-growth argument, without executable pseudocode, implementation, or the cited rational verification checks needed for reproducibility."
  - "HALTED AT TRIAGE: the math panel returned revise and its findings were never repaired, so this note is NOT established as mathematically sound."
  - "Open findings: boundary-count-clarify@lem:general-hierarchical-repair, target_functional_mismatch@thm:variance-certificate."
reusable_artifacts:
  - "discovery/core.json — maximized arbitrary-K scalar rank-one contrast formulation, including the support-size dichotomy and 402/N specialization"
  - "discovery/writeup.tex — rendered derivation note and explicit lower-witness construction"
  - "discovery/solve_thm_constructive_rounding_upper.json — constructive rounding proof attempt"
  - "discovery/solve_prop_two_arm_reduction.json — integral two-arm zero-gap boundary proof"
  - "reviews/review_general.json — terminal novelty and paper-score assessment"
  - "reviews/review_math.json — unrepaired boundary-count finding"
  - "reviews/review_rubric.json — unrepaired target-functional finding"
seeds_burned:
  - index: 0
    one_liner: "Sharp \\(N^{-1}\\) same-marginal three-arm realization frontier with a bit-polynomial rounding algorithm"
    reason: "The selected same-marginal rounding angle exhausted its bounded in-scope maximality improvements but remained below the field floor."
proof_attempt_summary: |
  Discovery derived a same-class Θ(1/N) realizability-gap bracket, strengthened the upper
  constant from 3456 to 402, and generalized the argument to an arbitrary-K scalar rank-one
  contrast support-size dichotomy with explicit padded lower witnesses. The field claim failed
  because the exact normalized frontier remains open, the finite-N certificate is loose and
  practically dominated by sampling error, and the implementation/comparator evidence stayed
  compressed. Triage also stopped before two local math-panel findings were repaired, so this
  bank entry records useful derivations but not an established sound theorem package.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 32235941
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 32235941
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# exp_finitepopulation_variance_rounding_frontier / v1 — Downgraded

**Topic.** The sharp finite-population price of fractional causal variance bounds. For each integer N>=2 take three multisets x_a=(x_a1,...,x_aN) in [0,1]^N, repeats permitted. Fixed contrast c=(1/4,1/4,-1/2). Put F_a=N^-1 sum_i delta_x_ai. V_rel(x)=inf over all probability couplings pi with marginals(F1,F2,F3) of E_pi[(sum_a c_a Y_a)^2]. V_int(x)=min over permutations sigma2,sigma3 of N^-1 sum_i(c1 x_1i+c2 x_2,sigma2(i)+c3 x_3,sigma3(i))^2. Define Delta_N=sup_x[V_int(x)-V_rel(x)]. Population marginal means are fixed, so the identical gap holds for contrast variances. For N>=3, under complete random assignment with fixed positive arm sizes n1+n2+n3=N, the sharp estimator-variance upper bound based on the known marginals differs between fractional and realizable completions by (V_int-V_rel)/(N-1). No claim that all full marginals are observed in one experiment. Determine the sharp asymptotic order of Delta_N, with any necessary arithmetic subsequences explicitly resolved: derive an explicit rate sequence r_N and universal constants 0<a<=b<infinity such that a r_N<=Delta_N<=b r_N for all sufficiently large N (or exact zero exceptional N classified). Prove the upper bound by a deterministic algorithm, polynomial in N and rational-input bit length, that takes empirical marginals and an optimal rational fractional coupling and outputs N-row permutations with cost at most V_rel+b r_N. Prove the matching lower bound over the SAME three-arm scalar [0,1] class by explicit families. The exponent/log factors and proof mechanics are answer-open; no unverified rate is assumed. Translate the guarantee into computable two-sided certificates for the marginal-information sharp randomization variance, and provide a consistent plug-in estimator of its endpoints under complete randomization, deriving sampling error from the empirical marginal distributions. A generic finite LP or an arbitrary vanishing rate is insufficient. Grounding: Gao-Ge-Qian (AISTATS2025), Brennan et al. (ICML2025), Haus (2015), and Puccetti-Wang (2015); the new object is same-empirical-marginal fractional-versus-N-row squared-cost loss, not quantile-discretization error, a generic integer program, or ordinary bottleneck mixability. Consumer: three-arm contrast comparisons within published multi-arm trials such as ACTG175 (Hammer et al.1996). PRESOLVE EVIDENCE REQUIRING VERIFICATION: The informal draft derives ordered support-slope intervals from fractional LP duality, builds nested dyadic partitions, freezes integer masses from successive basic feasible tables, and repairs each marginal hierarchically. Its quadratic slack accounting gives a candidate universal upper bound 3456/N. An exactly certified four-row obstruction, padded with isolated dummy rows, gives 1/(46080N) for every N at least four. Thus the supported answer is a sharp 1/N rate within the original answer-open coordinates. Thirty-six rational implementation checks passed, using numerical bases only as proposals followed by exact rational verification. Repeated atoms, dyadic boundary contacts, replication parity, and the two-row case were checked; arbitrarily tiny rational gaps are covered by the bit-length argument rather than a floating-point LP experiment. The variance certificates concern the sharp upper endpoint, with sampling uncertainty separately retained.
UNRESOLVED BOTTLENECK: Independently verify the slope-interval bound, residual-to-repair accounting, and polynomial rational vertex extraction; no remaining structural mathematical gap was identified, but standard LP, tree-matching, quantile/gluing and sampling steps remain compressed.
EARLY KILL TEST: Reconstruct the three load-bearing inequalities on exact optimal supports with ties and boundary contacts; stop this route on a counterexample, or on a verified same-marginal sharp-rounding prior-art collision.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/mill/scratch/mill-w10/round1040_presolve_strongest.md. PRACTICAL LIMITATION: The useful numerical certificate is the actual primal-dual width. The loose universal 3456/N bound may be uninformative at ordinary trial sizes, and the sampling uncertainty is larger than the deterministic rounding term asymptotically.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: delivered tier=subfield below novelty_target=field; the note proves the advertised sharp order, not the exact frontier, and two local panel findings remain unrepaired, so mathematical soundness is not established.

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
