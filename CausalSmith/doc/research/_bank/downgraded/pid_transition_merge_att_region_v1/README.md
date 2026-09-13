---
qid: pid_transition_merge_att_region
spec: v1
topic: "Sharp aggregate-ATT regions under latent-transition type mergers. In the compact binary four-period at-most-two-type Ahn–Kasahara model, with the pre-treatment transition shared across treatment arms within type and all primitive probabilities in [η,1−η] for fixed rational 0<η<0.15, define the global transition-alignment fiber of the full observed path PMF. Prove a branch-complete 16-chart full-path factorization covering terminal collisions, rank failures, all probability-box faces, and every cross-arm alignment; derive explicit observable vanishing/sign conditions necessary and sufficient for aggregate ATT at dates 3 and 4 to be point identified; otherwise compute the attained sharp region, allowing disconnected finite unions of intervals, by a terminating branch-aware exact algorithm. Give uniformly honest confidence regions for the entire identified set and endpoint/Hausdorff consistency under explicit branch-continuity conditions. Consumer: the public ak package and its Dodd–Frank, Norwegian patenting, and ADA analyses, whose reported ATT sign and bootstrap uncertainty change at merger fibers. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Full path tensors, not pair moments, are necessary. Sixteen terminal-collision charts yield explicit splitting formulas, eight rank-one constraints, and four cross-arm alignment equations. A positive law has exactly two attainable ATT values. For the supplied merger law, every unequal-ATT representation has common prehistory and falls into four control cases; convexity fixes extremizing arm weights, reducing full endpoints to four eight-inequality polygon problems. At η=1/10, exact rational arithmetic gives I3=[−8867/29480,7517/29480] and I4=[−8611/29480,7773/29480], both crossing zero; endpoint PMFs and an η=7/50 branch switch were checked. Pair-moment insufficiency, terminal collisions, coincident components, disconnected regions, and fixed-coverage Hausdorff failure were tested; no exact literature collision was found. UNRESOLVED BOTTLENECK: Derive model-specific observable vanishing/sign tests that are necessary and sufficient for all sixteen feasible chart images to coincide at one ATT value, including rank deficiencies, alignments, and box contacts, without substituting unrestricted multivariate quantifier elimination. EARLY KILL TEST: Independently verify the sixteen-chart reconstruction, then completely classify the case with distinct treated terminal rows and exactly one collided control terminal row. An omitted legal branch or classification requiring only unrestricted generic QE triggers a pivot before expanding the atlas. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_transition_merge_att_region.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: re-raise
gap_reasons:
  - "The delivered result covers only the exclusive stratum with one specified collided control terminal row; its sixteen charts are orientation/alignment branches within that stratum, not the requested branch-complete atlas of terminal-collision patterns."
  - "Point identification is characterized only by acceptance or rejection of a generic full Collins quantifier-elimination computation, rather than by the advertised explicit observable vanishing and sign conditions."
  - "The checker confirms arithmetic on the proposed four leaves; it does not prove computationally that no fifth equality leaf exists."
  - "The second response did not implement the explicitly requested execution certificate. It documented a future validity contract while leaving the fixture/checker byte-identical."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - discovery/p_diamond_onecollisionatt.json
  - discovery/replay_p_diamond_onecollisionatt.mjs
  - discovery/solve_prop_open_chamber_benchmark.json
  - discovery/solve_thm_exact_one_collision_region.json
seeds_burned: []
proof_attempt_summary: |
  The run repaired the local CAD projection and domain defects, proved the compact one-collided-control-row classification, and produced an exact rational P-diamond regression fixture with 32 cells, eight accepted labels, 24 analytic exclusions, and two attained ATT values. The field-tier continuation required an executable Collins projection and signed Sturm-Habicht lifting certificate, but the D0 solve worker's authorized outputs could not contain an implementation; two retries therefore left the checker and fixture byte-identical. The mathematics remains sound at the referee-assessed incremental tier, while a future run needs a tool-capable implementation stage before re-review.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 60817371
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 60817371
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# pid_transition_merge_att_region / v1 — Downgraded

**Topic.** Sharp aggregate-ATT regions under latent-transition type mergers. In the compact binary four-period at-most-two-type Ahn–Kasahara model, with the pre-treatment transition shared across treatment arms within type and all primitive probabilities in [η,1−η] for fixed rational 0<η<0.15, define the global transition-alignment fiber of the full observed path PMF. Prove a branch-complete 16-chart full-path factorization covering terminal collisions, rank failures, all probability-box faces, and every cross-arm alignment; derive explicit observable vanishing/sign conditions necessary and sufficient for aggregate ATT at dates 3 and 4 to be point identified; otherwise compute the attained sharp region, allowing disconnected finite unions of intervals, by a terminating branch-aware exact algorithm. Give uniformly honest confidence regions for the entire identified set and endpoint/Hausdorff consistency under explicit branch-continuity conditions. Consumer: the public ak package and its Dodd–Frank, Norwegian patenting, and ADA analyses, whose reported ATT sign and bootstrap uncertainty change at merger fibers. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Full path tensors, not pair moments, are necessary. Sixteen terminal-collision charts yield explicit splitting formulas, eight rank-one constraints, and four cross-arm alignment equations. A positive law has exactly two attainable ATT values. For the supplied merger law, every unequal-ATT representation has common prehistory and falls into four control cases; convexity fixes extremizing arm weights, reducing full endpoints to four eight-inequality polygon problems. At η=1/10, exact rational arithmetic gives I3=[−8867/29480,7517/29480] and I4=[−8611/29480,7773/29480], both crossing zero; endpoint PMFs and an η=7/50 branch switch were checked. Pair-moment insufficiency, terminal collisions, coincident components, disconnected regions, and fixed-coverage Hausdorff failure were tested; no exact literature collision was found. UNRESOLVED BOTTLENECK: Derive model-specific observable vanishing/sign tests that are necessary and sufficient for all sixteen feasible chart images to coincide at one ATT value, including rank deficiencies, alignments, and box contacts, without substituting unrestricted multivariate quantifier elimination. EARLY KILL TEST: Independently verify the sixteen-chart reconstruction, then completely classify the case with distinct treated terminal rows and exactly one collided control terminal row. An omitted legal branch or classification requiring only unrestricted generic QE triggers a pivot before expanding the atlas. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_transition_merge_att_region.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Sound one-collision benchmark and repaired D0.5 mathematics, but field-tier completion stopped at a deterministic artifact/output-channel mismatch: the D0 solve worker had no channel to deliver the required executable Collins/Sturm-Habicht certificate; referee-assessed tier incremental (score ceiling 5.4 below 7.4 field floor).

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
