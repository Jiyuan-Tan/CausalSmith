---
qid: eid_gene_population_landscape
spec: v1
topic: "Population success certificates, a sharp failure frontier, and adaptive uncertainty for GENE-style order optimization. Fix support-closed compact causally minimal restricted additive-noise models with smooth mechanisms, independent innovation densities positive on support interiors, and the stated Condition 19 configurations. Define the exact alpha=1 population-oracle analogue of GENE Equation (6) from conditional correlation ratios and exact characteristic-kernel residual-dependence labels. On the subclass M_pair(d), whose weak components are isolated vertices or single directed edges and whose primitive forward and reverse signal ratios satisfy rho_forward_uv > (d-1) rho_reverse_uv / d, prove that every non-topological order has a reversal-correcting insertion with a uniform positive gain, every insertion-local maximizer is topological, and best-improvement search followed by residual-independence pruning recovers the labelled DAG from every start with finite oracle-query bounds. Prove by an explicit smooth six-node nonlinear witness that this local certificate is strictly weaker than the global reversal-monotone premise of Li et al. Theorem 4.3, while making no recovery claim for their full nonlinear class or their released finite-sample neural-network and p-value implementation. Give the quadratic two-node positive-gain witness. For every eta in (0,1/2), construct an explicitly parameterized nonempty relatively open bivariate identifiable family, including a nonempty relatively open non-affine subfamily, on which the wrong order is the unique global and insertion-local maximizer by more than eta, and prove that 1/2 is the universal sharp supremum of this advantage. Give cross-fitted simultaneous conditional-risk and residual-HSIC bands with set-valued independence decisions: exact-path separation yields graph-set coverage, whereas singleton recovery requires all-compatible-query separation and resolved score and HSIC margins. Retain the generic ambient-dimensional rates and prove a pairing-agnostic matching-adaptive branch with intrinsic one-dimensional regression rate 3/7, risk exponent 6/7, sufficient singleton order log(M_d/alpha) times max of (d/delta_pair)^2 and lambda^(-7/3), and no ambient-dimensional elbow. Treat the released Sachs workflow only as an audit case. This topic delivers a sufficient structural success region and a sharp existential failure frontier; it does not claim a non-tautological necessary-and-sufficient maximal classification of general GENE landscapes, minimax-optimal rates, or a refutation of Li et al. conditional theorem."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "Delivered tier incremental < floor field; not salvageable within scope."
  - "The reproduced compact-support argument does not establish the cited finite-graph reduction: positivity on connected relative interiors of individual fibers does not supply the global/product-support intersection and conditional-factorization hypotheses used by the restricted-ANM proof; the claimed extension needs a proved bridge or a restriction to the cited theorem's domain."
  - "The singleton claim conditions on Q_all(B), where B is the realized random band collection, without a quantifier making this a property of P or an event controlled on E_n; state separation uniformly for every band realization compatible with E_n (or give an equivalent deterministic query set) before asserting the probability guarantee."
  - "At y=h(x) with a uniform root, L_xy/L_xx=-1/h'(x), so its x-derivative is h''(x)/h'(x)^2=2/(1+2x)^2, not 2h''(x)/h'(x)^2=4/(1+2x)^2; the nonzero-obstruction conclusion survives after correction."
  - "The flagship sharp open trapped-order theorem gives its construction-specific gap but does not name and distinguish the closest published score-landscape/counterexample result class; add that theorem-level comparison (or a targeted no-comparator statement) after this theorem."
  - "Hoyer et al. (2009) appears in the bibliography but has no relevance sentence in the related-work positioning; explain its role relative to the compact restricted-ANM bridge or remove the unused citation."
reusable_artifacts:
  - "discovery/core.json — maximized matching-ANM certificate, sharp trap frontier, and adaptive-band theorem graph; reuse only after resolving the recorded soundness gaps."
  - "discovery/solve_thm_li_strict_separation.json — explicit six-node separation argument against Li et al.'s global premise."
  - "discovery/solve_thm_smooth_open_trap.json — parameterized smooth open wrong-order family and sharp 1/2 score-gap endpoint."
  - "discovery/solve_thm_simultaneous_bands.json — generic and matching-adaptive band derivation, subject to the random-separation correction."
  - "discovery/gaps.json — verified literature opportunity map and source anchors."
seeds_burned:
  - index: 0
    one_liner: "seed:block-iff-boundary"
    reason: "The only field-scoped angle exhausted bounded repair; any renewed field attempt requires a genuine D-1.2 re-anchor."
proof_attempt_summary: |
  D-1 rejected the requested general necessary-and-sufficient boundary as circular and converged on a narrower matching-component success certificate, strict Li-separation witness, sharp open failure family, and matching-adaptive uncertainty branch. D0 discharged and maximized that graph, but D0.5 rated the package incremental with ceiling 6.4 below the 7.2 field bar and no bounded same-scope salvage. mathematical-soundness-unresolved / REVISE: the compact identification bridge and random singleton-separation premise remain load-bearing gaps; the calculus factor and two positioning findings also remain unrepaired, so this artifact is not publication-ready.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 23549545
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 23549545
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_gene_population_landscape / v1 — Downgraded

**Topic.** Population success certificates, a sharp failure frontier, and adaptive uncertainty for GENE-style order optimization. Fix support-closed compact causally minimal restricted additive-noise models with smooth mechanisms, independent innovation densities positive on support interiors, and the stated Condition 19 configurations. Define the exact alpha=1 population-oracle analogue of GENE Equation (6) from conditional correlation ratios and exact characteristic-kernel residual-dependence labels. On the subclass M_pair(d), whose weak components are isolated vertices or single directed edges and whose primitive forward and reverse signal ratios satisfy rho_forward_uv > (d-1) rho_reverse_uv / d, prove that every non-topological order has a reversal-correcting insertion with a uniform positive gain, every insertion-local maximizer is topological, and best-improvement search followed by residual-independence pruning recovers the labelled DAG from every start with finite oracle-query bounds. Prove by an explicit smooth six-node nonlinear witness that this local certificate is strictly weaker than the global reversal-monotone premise of Li et al. Theorem 4.3, while making no recovery claim for their full nonlinear class or their released finite-sample neural-network and p-value implementation. Give the quadratic two-node positive-gain witness. For every eta in (0,1/2), construct an explicitly parameterized nonempty relatively open bivariate identifiable family, including a nonempty relatively open non-affine subfamily, on which the wrong order is the unique global and insertion-local maximizer by more than eta, and prove that 1/2 is the universal sharp supremum of this advantage. Give cross-fitted simultaneous conditional-risk and residual-HSIC bands with set-valued independence decisions: exact-path separation yields graph-set coverage, whereas singleton recovery requires all-compatible-query separation and resolved score and HSIC margins. Retain the generic ambient-dimensional rates and prove a pairing-agnostic matching-adaptive branch with intrinsic one-dimensional regression rate 3/7, risk exponent 6/7, sufficient singleton order log(M_d/alpha) times max of (d/delta_pair)^2 and lambda^(-7/3), and no ambient-dimensional elbow. Treat the released Sachs workflow only as an audit case. This topic delivers a sufficient structural success region and a sharp existential failure frontier; it does not claim a non-tautological necessary-and-sufficient maximal classification of general GENE landscapes, minimax-optimal rates, or a refutation of Li et al. conditional theorem.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Delivered tier incremental < floor field; not salvageable within scope; mathematical-soundness-unresolved / REVISE.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

This bank entry preserves useful constructions but is explicitly not established as mathematically sound. Any future field attempt requires a genuine D-1.2 re-anchor rather than another reformulation of the exhausted maximal-boundary target or a lowered novelty floor.
