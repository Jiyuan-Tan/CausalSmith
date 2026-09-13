---
qid: exp_weaknull_alphabet_symmetry_frontier
spec: v1
topic: "Outcome-alphabet frontier for exact weak-null randomization symmetry. Fix every even n=2m and balanced complete randomization of m treated units, with fixed no-interference potential outcomes in A_K={0,...,K-1}. A legal response table N has total n and zero sum of individual effects. For observed treated/control histograms C=(H1,H0), define C equivalent to C' iff their exact multivariate-hypergeometric probabilities agree for every legal N. Prove for all even n that the equivalence classes are exactly transpose pairs when K=2, and singletons except the opposing endpoint-saturation pair when K>=3. Give a constructive legal separator with at most three heterogeneous units for every inequivalent pair and prove three are necessary in general; identify the maximal common bijection group and show only its conventional nonrandomized orbit-rank p-values lie in {1/2,1}, without claiming impossibility of other exact tests. Consumer: DeclareDesign's balanced 250-of-500 binary reply audit experiment and its HC2/t weak-ATE workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The exact coefficient formula was derived; diagonal schedules plus symmetric two-unit switches recover the arm-imbalance outer product and restrict every class to a transpose pair, while explicit asymmetric two- and three-unit schedules eliminate all nonendpoint transposes. Binary transposition and endpoint saturation are universal; 91,120 exact obstruction checks and stress tests through n=200 support the three-unit necessity argument. UNRESOLVED BOTTLENECK: Independently audit the cubic endpoint identity and the claim that every legal schedule with at most two heterogeneous units leaves the designated profiles equivalent. EARLY KILL TEST: Reconstruct the symmetric-switch identity and the K=3,n=6 cubic witness directly from the raw hypergeometric kernel, confirm assignment counts 1 versus 0, then exhaust legal tables with at most two heterogeneous units; any discrepancy stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_weaknull_alphabet_symmetry_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "A field-tier upgrade requires a newly anchored nuisance-maximized binary histogram procedure with uniform finite-sample validity, power analysis, and a 250-of-500 audit comparison to HC2/robust-t."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The contribution nevertheless concerns a deliberately restricted schedule-universal, histogram-measurable stabilizer rather than exact weak-null tests generally, and its inferential output consists only of coarse orbit ranks plus a corner-event p-value with an exceptionally degenerate rejection event."
  - "The DeclareDesign and HC2 discussion therefore remains diagnostic: no usable exact procedure, power calculation, or audit computation demonstrates practical inferential value for the 250-of-500 experiment."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 5.9 < 7.4, so the graded tier 'subfield' is capped at 'incremental'."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_tex/solve_thm_alphabet_frontier.tex
  - discovery/solve_tex/solve_thm_unbalanced_frontier.tex
  - discovery/solve_tex/solve_prop_diagonal_reduction.tex
  - discovery/gaps.json
seeds_burned: []
proof_attempt_summary: |
  D0 proved the balanced binary-versus-multilevel equivalence classification, maximal common groups,
  the exact 0/2/3-unit sparse-separator phase diagram, and the unequal-allocation identity-group elbow;
  the mathematical referee reported no correctness findings. The field claim collapsed at novelty and
  practical inference: orbit ranks and the corner-event construction did not yield a useful exact audit
  procedure. A re-raise must newly anchor and prove a nuisance-maximized finite-sample test, power
  behavior, and the promised 250-of-500 HC2 comparison rather than re-derive the combinatorics.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 15304105
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 15304105
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_weaknull_alphabet_symmetry_frontier / v1 — Downgraded

**Topic.** Outcome-alphabet frontier for exact weak-null randomization symmetry. Fix every even n=2m and balanced complete randomization of m treated units, with fixed no-interference potential outcomes in A_K={0,...,K-1}. A legal response table N has total n and zero sum of individual effects. For observed treated/control histograms C=(H1,H0), define C equivalent to C' iff their exact multivariate-hypergeometric probabilities agree for every legal N. Prove for all even n that the equivalence classes are exactly transpose pairs when K=2, and singletons except the opposing endpoint-saturation pair when K>=3. Give a constructive legal separator with at most three heterogeneous units for every inequivalent pair and prove three are necessary in general; identify the maximal common bijection group and show only its conventional nonrandomized orbit-rank p-values lie in {1/2,1}, without claiming impossibility of other exact tests. Consumer: DeclareDesign's balanced 250-of-500 binary reply audit experiment and its HC2/t weak-ATE workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The exact coefficient formula was derived; diagonal schedules plus symmetric two-unit switches recover the arm-imbalance outer product and restrict every class to a transpose pair, while explicit asymmetric two- and three-unit schedules eliminate all nonendpoint transposes. Binary transposition and endpoint saturation are universal; 91,120 exact obstruction checks and stress tests through n=200 support the three-unit necessity argument. UNRESOLVED BOTTLENECK: Independently audit the cubic endpoint identity and the claim that every legal schedule with at most two heterogeneous units leaves the designated profiles equivalent. EARLY KILL TEST: Reconstruct the symmetric-switch identity and the K=3,n=6 cubic witness directly from the raw hypergeometric kernel, confirm assignment counts 1 versus 0, then exhaust legal tables with at most two heterogeneous units; any discrepancy stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_weaknull_alphabet_symmetry_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental < floor=field and not salvageable in scope; the proved combinatorial classification has a projected paper-score ceiling of 5.9 below the 7.4 field gate.

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
