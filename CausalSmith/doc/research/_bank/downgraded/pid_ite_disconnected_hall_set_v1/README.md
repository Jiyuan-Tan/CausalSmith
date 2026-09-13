---
qid: pid_ite_disconnected_hall_set
spec: v1
topic: "Sharp disconnected Hall prediction sets for ordinal individual treatment effects. Fix L>=3 and two randomized arms with Y(d) in {0,...,L-1}; the marginals mu0,mu1 are identified and their coupling is unrestricted. For every effect set S define worst-coupling coverage h_mu(S), and define the deterministic shortest valid set by cardinality, span, then binary code. Prove the exact Hall/rectangle representation, characterize all shortest sets, give necessary-and-sufficient disconnectedness inequalities and the complete L=3 frontier, derive sharp general-L bounds comparing shortest arbitrary sets with shortest intervals, and compute them by an explicit min-cut plus finite outer optimization. Use simultaneous multinomial confidence-polytopes to certify every reported set uniformly, with selection consistency on the stated fixed-margin class. Consumer: the seven-category endpoint in Goldman et al.'s remdesivir 5-versus-10-day trial. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivation gives h(S)=max(0,max_{A-B subset S}[mu1(A)+mu0(B)-1]), so every cardinality minimizer is a threshold-feasible difference set A-B. The presolve derived a complete L=3 frontier and sharp bounds I*/k* <= (2L-1)/3 and I*-k* <= 2L-4, attained by strictly positive endpoint-heavy marginals for every 0<alpha<1/2. The accepted witness has exact coverage 39/50; 43,560 rational L=3 cases and 120 independent transport comparisons passed. An invalid robust min/max interchange was found and removed; Hall duality is supporting prior art, not the headline. UNRESOLVED BOTTLENECK: Independently verify the all-minimizer rectangle normal form at boundary marginal laws and the exhaustive L=3 support-pattern classification; numerical checks do not prove the universal statements. EARLY KILL TEST: Compare transport LPs with rectangle selection for every effect set on bounded L=3 and L=4 rational grids, including zero cells and threshold equalities, and verify the endpoint-heavy extremizers; any mismatch stops or pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_ite_disconnected_hall_set.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The advertised remdesivir relevance remains prospective: the package reports no trial marginals, selected effect set, confidence-certified set, or coverage-level sensitivity analysis."
  - "The min-cut handles evaluation of a fixed candidate, while the global optimization remains exponential enumeration, so scalability beyond small ordinal supports is not established."
  - "Selection consistency is confined to a fixed-margin class that excludes positive-width neighborhoods of feasibility surfaces, and the inference result certifies validity without addressing efficiency."
reusable_artifacts:
  - "discovery/core.json — checked Hall/rectangle normal form, ternary frontier, phase-transition bounds, equality regimes, and finite-sample certification graph"
  - "discovery/writeup.tex — complete derivations and sharp constructions"
  - "discovery/solve_tex/ — solver proof artifacts for the Hall, frontier, and equality-regime nodes"
  - "discovery/proto_core.json and reviews/ — proposal evidence, comparator map, and terminal tier receipts for future re-raising"
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the optimizer-wide Hall/rectangle normal form, complete ternary frontier,
  both sharp interval-price regimes and equality cases, exact finite computation, and the
  certification/selection results; the cited finite Strassen deficiency was verified from
  Koperberg's Proposition 6. The field claim collapsed on materiality rather than correctness:
  no delivered remdesivir analysis, exponential outer enumeration, and a separated-class
  selector theorem kept the package at subfield tier. A re-raise should add a real-data or
  scalable computational contribution rather than rerun the same mathematics.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 22762540
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 22762540
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# pid_ite_disconnected_hall_set / v1 — Downgraded

**Topic.** Sharp disconnected Hall prediction sets for ordinal individual treatment effects. Fix L>=3 and two randomized arms with Y(d) in {0,...,L-1}; the marginals mu0,mu1 are identified and their coupling is unrestricted. For every effect set S define worst-coupling coverage h_mu(S), and define the deterministic shortest valid set by cardinality, span, then binary code. Prove the exact Hall/rectangle representation, characterize all shortest sets, give necessary-and-sufficient disconnectedness inequalities and the complete L=3 frontier, derive sharp general-L bounds comparing shortest arbitrary sets with shortest intervals, and compute them by an explicit min-cut plus finite outer optimization. Use simultaneous multinomial confidence-polytopes to certify every reported set uniformly, with selection consistency on the stated fixed-margin class. Consumer: the seven-category endpoint in Goldman et al.'s remdesivir 5-versus-10-day trial. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivation gives h(S)=max(0,max_{A-B subset S}[mu1(A)+mu0(B)-1]), so every cardinality minimizer is a threshold-feasible difference set A-B. The presolve derived a complete L=3 frontier and sharp bounds I*/k* <= (2L-1)/3 and I*-k* <= 2L-4, attained by strictly positive endpoint-heavy marginals for every 0<alpha<1/2. The accepted witness has exact coverage 39/50; 43,560 rational L=3 cases and 120 independent transport comparisons passed. An invalid robust min/max interchange was found and removed; Hall duality is supporting prior art, not the headline. UNRESOLVED BOTTLENECK: Independently verify the all-minimizer rectangle normal form at boundary marginal laws and the exhaustive L=3 support-pattern classification; numerical checks do not prove the universal statements. EARLY KILL TEST: Compare transport LPs with rectangle selection for every effect set on bounded L=3 and L=4 rational grids, including zero cells and threshold equalities, and verify the endpoint-heavy extremizers; any mismatch stops or pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_ite_disconnected_hall_set.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The contribution is graded subfield rather than field: paper_score_ceiling 6.9 < 7.4, with no bounded salvage in the current scope.

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
