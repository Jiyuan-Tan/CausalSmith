---
qid: pid_categorical_itr_joint_saddle_v1
spec: v1
topic: "Joint-polytope randomized minimax-regret treatment rules under categorical-IV partial identification. For finite positive-probability covariate strata, finite randomized Z, categorical A, and binary Y under exclusion and response-type exogeneity, construct each full response-function action-mean polytope; derive observable dual inequalities iff a pure rule is minimax, enumerate the entire optimal-mixture correspondence, and specialize to Stoye's spike-state result when all spikes are feasible. Build a Bonferroni Clopper-Pearson simultaneous multinomial fiber, cover the population optimizer correspondence, and certify deployed worst-case regret with unique-face root-n theory and uniform set-valued validity across face intersections. Include the exact three-action witness with mu0<=mu2, joint rule q=(0,1/4,3/4), value 3/16, and rectangle rule q=(0,0,1), value 1/4, and target Hruza et al.'s released multicategory implementation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact response-type enumeration for the supplied three-action categorical-IV law attained all ten projected vertices and confirmed the nonrectangular constraint mu0<=mu2. The induced joint-polytope minimax rule q=(0,1/4,3/4) has regret 3/16, while actionwise rectangularization gives q=(0,0,1) and regret 1/4. Writing the response fiber as W(p)={w>=0:Bw=p} reduces the general problem to a finite primal-dual basis enumeration. On the simultaneous Clopper-Pearson event, unioning optimizer correspondences over the confidence fiber contains the true population correspondence, and robust optimization over that fiber upper-bounds deployed regret. Checks covered zero-probability observed cells, every claimed vertex, face ties, rare-cell vacuity, and the Stoye/Hruza/general robust-decision collisions; only the LP machinery was generic. UNRESOLVED BOTTLENECK: Prove Hadamard differentiability of the parametric LP optimizer and value maps on an explicit nondegenerate unique-face margin class, yielding the claimed root-n normal policy and regret law while retaining set-valued uniform validity at face intersections. EARLY KILL TEST: Exhaustively enumerate active bases for the twenty-type witness and its codimension-one face-boundary perturbations, compare every pure-rule certificate and optimizer union with independent exact LP solutions, and stop if any optimizer is omitted or any certificate is false."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No proved workflow, estimation, tie-breaking, surrogate, or optimization map connects the released deterministic Hruza learner to the randomized population rectangle oracle; removing the named target would substitute the accepted kernel."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised Hruza-implementation comparison has been replaced by a generic randomized rectangle-oracle separation: the theorem does not establish that Hruza et al.'s deterministic learned rule has this oracle, so either prove the workflow mapping under its stated scope or position the witness solely as a generic rectangle benchmark."
  - "Removing the explicit Hruza target would substitute the promised kernel rather than repair it."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_three_action_witness.json
  - discovery/solve_thm_unique_face_rootn.json
  - discovery/solve_thm_face_intersection_impossibility.json
  - discovery/solve_thm_cp_correspondence_coverage.json
seeds_burned: []
proof_attempt_summary: |
  Discovery built the finite response-type LP, exact three-action nonrectangular witness,
  separated-unique-face root-n theory, exact confidence-fiber coverage, and the
  face-intersection impossibility result, surviving multiple mathematical repairs.
  The run collapsed at D0.5 because those results compare randomized population
  joint and rectangle oracles, while the committed consumer promise targets Hruza
  et al.'s released deterministic learned rule. A future re-raise must add and verify
  the missing workflow, estimation, tie-breaking, surrogate, and optimization map;
  relabeling the result as a generic rectangle benchmark is not a faithful repair.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 68551148
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# pid_categorical_itr_joint_saddle_v1 / v1 — Failed

**Topic.** Joint-polytope randomized minimax-regret treatment rules under categorical-IV partial identification. For finite positive-probability covariate strata, finite randomized Z, categorical A, and binary Y under exclusion and response-type exogeneity, construct each full response-function action-mean polytope; derive observable dual inequalities iff a pure rule is minimax, enumerate the entire optimal-mixture correspondence, and specialize to Stoye's spike-state result when all spikes are feasible. Build a Bonferroni Clopper-Pearson simultaneous multinomial fiber, cover the population optimizer correspondence, and certify deployed worst-case regret with unique-face root-n theory and uniform set-valued validity across face intersections. Include the exact three-action witness with mu0<=mu2, joint rule q=(0,1/4,3/4), value 3/16, and rectangle rule q=(0,0,1), value 1/4, and target Hruza et al.'s released multicategory implementation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact response-type enumeration for the supplied three-action categorical-IV law attained all ten projected vertices and confirmed the nonrectangular constraint mu0<=mu2. The induced joint-polytope minimax rule q=(0,1/4,3/4) has regret 3/16, while actionwise rectangularization gives q=(0,0,1) and regret 1/4. Writing the response fiber as W(p)={w>=0:Bw=p} reduces the general problem to a finite primal-dual basis enumeration. On the simultaneous Clopper-Pearson event, unioning optimizer correspondences over the confidence fiber contains the true population correspondence, and robust optimization over that fiber upper-bounds deployed regret. Checks covered zero-probability observed cells, every claimed vertex, face ties, rare-cell vacuity, and the Stoye/Hruza/general robust-decision collisions; only the LP machinery was generic. UNRESOLVED BOTTLENECK: Prove Hadamard differentiability of the parametric LP optimizer and value maps on an explicit nondegenerate unique-face margin class, yielding the claimed root-n normal policy and regret law while retaining set-valued uniform validity at face intersections. EARLY KILL TEST: Exhaustively enumerate active bases for the twenty-type witness and its codimension-one face-boundary perturbations, compare every pure-rule certificate and optimizer union with independent exact LP solutions, and stop if any optimizer is omitted or any certificate is false.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The promised Hruza-implementation comparison has been replaced by a generic randomized rectangle-oracle separation: the theorem does not establish that Hruza et al.'s deterministic learned rule has this oracle.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The mathematical core remains potentially reusable for a differently scoped paper,
but it cannot be presented as validating or tightening the named released workflow
without the missing implementation-level mapping.
