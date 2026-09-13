---
qid: eid_pbscm_sourceforest_complete_fiber
spec: v1
topic: "Source-forest complete observational fibers for strict Poisson branching SCMs. For every finite labeled causally sufficient DAG with independent positive Poisson innovations and edge-specific independent Bernoulli thinning probabilities strictly between zero and one, characterize the unrestricted observational fiber D(P). Prove that singleton/pair and degree-four log-PGF coefficient signatures fix the skeleton and every arrow entering a multi-parent vertex; after deleting those arrows the residual graph is a forest whose anchored components have forced roots and whose free components may be independently rerooted, and prove these are all and only the compatible DAGs. Give the explicit positive source-edge reversal preserving the complete PGF, the exact fiber cardinality, compelled-edge certificates, and the reverse-topological rational decoder yielding the unique parameter point on each compatible DAG. Prove degree-four coefficients determine the entire strict-model law and fiber and are sharp because strict triangle laws can agree through degree three while differing at the squared-sink monomial. From bounded count-cell indicators construct a simultaneous low-degree coefficient confidence region, outward-invert it to a graph set covering the full unrestricted fiber, and report only arrows unanimous over the nonempty outer set; do not claim automatic faithfulness or unrestricted uniform singleton recovery. Consumer: the football-event and shopping-mall PB-SCM analyses of Xiang et al. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh presolver derived the fixed-DAG inverse, complete-PGF source-reversal identity, residual-forest converse, and degree-four triangle lower bound. Exact rational checks recovered the correct fibers for every 2-, 3-, and 4-node DAG, tested all eligible source reversals through four nodes, and reproduced 29,281 five-node DAGs in 13,521 source-forest classes; diamonds, linked multi-parent vertices, overlapping descendants, and a complete five-node graph produced no counterexample. It also derived degree-four log-PGF coefficients as finite rational functions of bounded count-cell probabilities and a Hoeffding-union confidence region. Boundary thinning probabilities, zero innovation rates, automatic faithfulness, generic CAD as the headline, unrestricted singleton consistency, and a compact-box target substitution were tested and excluded. Focused current/citing searches found local PGF/cumulant rules and a latent-confounded three-variable extension, but no global source-forest converse. UNRESOLVED BOTTLENECK: Formalize the arbitrary-DAG genealogy-to-coefficient lemma when multiple downstream paths repeat vertex labels, then connect it rigorously to every local signature used by the forest converse. EARLY KILL TEST: On a six-node rational graph with a reversible source edge, overlapping descendants, a downstream collider, and an anchored tail, enumerate every skeleton orientation and compare its exact full-PGF decoder with the predicted forest family; any missing representation, false positive, nonunique parameter point, or failed reversal stops the claim. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_pbscm_sourceforest_complete_fiber.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - >-
    The computational contribution stops at defining the outward inverse as an existential union: no procedure is proved to construct or enumerate it, and the certified handle explicitly asserts neither existence nor an algorithm, so the claim that football and shopping analysts can report fiber-unanimous arrows is not operationally delivered.
  - >-
    No data reanalysis or finite-sample computation demonstrates that the confidence set is informative, despite the acknowledged possibility that it is unbounded when the data do not control the zero-cell probability.
  - >-
    D0.5.G projected paper-score gate: paper_score_ceiling 7.1 < 7.2, so the graded tier 'field' is capped at 'subfield'.
reusable_artifacts:
  - discovery/core.json — synchronized theorem graph and exact source-forest fiber specification.
  - discovery/solve_thm_degree_four_completeness.json — degree-four completeness proof artifact.
  - discovery/solve_thm_degree_three_sharpness.json — strict triangle degree-three collision witness.
  - discovery/solve_thm_coefficient_confidence.json — bounded-cell confidence-region argument.
  - discovery/writeup.tex — repaired source with w_gamma in (0,1] and the outward-inversion interface/OEQ split.
seeds_burned: []
proof_attempt_summary: |
  The run proved the strict-model population fiber, constructive source reversals, unique fixed-DAG decoding, degree-four completeness and sharpness, and set-theoretic outer-fiber coverage. Formalization exposed and repaired two source defects: genealogy weights can equal one, and the outward-inversion certificate had to be specified as an interface without asserting existence. The remaining field-tier gap is operational: an actual evaluator/enumerator or informative finite-sample application was not proved, and promoting the exact-feasibility discussion would assume an oracle and launder the open inversion problem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 49349469
  pipeline_claude_tokens: 3470096
  pipeline_tokens_consumed: 52819565
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_pbscm_sourceforest_complete_fiber / v1 — Downgraded

**Topic.** Source-forest complete observational fibers for strict Poisson branching SCMs. For every finite labeled causally sufficient DAG with independent positive Poisson innovations and edge-specific independent Bernoulli thinning probabilities strictly between zero and one, characterize the unrestricted observational fiber D(P). Prove that singleton/pair and degree-four log-PGF coefficient signatures fix the skeleton and every arrow entering a multi-parent vertex; after deleting those arrows the residual graph is a forest whose anchored components have forced roots and whose free components may be independently rerooted, and prove these are all and only the compatible DAGs. Give the explicit positive source-edge reversal preserving the complete PGF, the exact fiber cardinality, compelled-edge certificates, and the reverse-topological rational decoder yielding the unique parameter point on each compatible DAG. Prove degree-four coefficients determine the entire strict-model law and fiber and are sharp because strict triangle laws can agree through degree three while differing at the squared-sink monomial. From bounded count-cell indicators construct a simultaneous low-degree coefficient confidence region, outward-invert it to a graph set covering the full unrestricted fiber, and report only arrows unanimous over the nonempty outer set; do not claim automatic faithfulness or unrestricted uniform singleton recovery. Consumer: the football-event and shopping-mall PB-SCM analyses of Xiang et al. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh presolver derived the fixed-DAG inverse, complete-PGF source-reversal identity, residual-forest converse, and degree-four triangle lower bound. Exact rational checks recovered the correct fibers for every 2-, 3-, and 4-node DAG, tested all eligible source reversals through four nodes, and reproduced 29,281 five-node DAGs in 13,521 source-forest classes; diamonds, linked multi-parent vertices, overlapping descendants, and a complete five-node graph produced no counterexample. It also derived degree-four log-PGF coefficients as finite rational functions of bounded count-cell probabilities and a Hoeffding-union confidence region. Boundary thinning probabilities, zero innovation rates, automatic faithfulness, generic CAD as the headline, unrestricted singleton consistency, and a compact-box target substitution were tested and excluded. Focused current/citing searches found local PGF/cumulant rules and a latent-confounded three-variable extension, but no global source-forest converse. UNRESOLVED BOTTLENECK: Formalize the arbitrary-DAG genealogy-to-coefficient lemma when multiple downstream paths repeat vertex labels, then connect it rigorously to every local signature used by the forest converse. EARLY KILL TEST: On a six-node rational graph with a reversible source edge, overlapping descendants, a downstream collider, and an anchored tail, enumerate every skeleton orientation and compare its exact full-PGF decoder with the predicted forest family; any missing representation, false positive, nonunique parameter point, or failed reversal stops the claim. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_pbscm_sourceforest_complete_fiber.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 graded the sound delivered package subfield at 7.1 below the fixed field threshold 7.2; no bounded honest repair supplies the missing outer-fiber evaluator or application.

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
