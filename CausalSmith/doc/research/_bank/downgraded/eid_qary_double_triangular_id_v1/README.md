---
qid: eid_qary_double_triangular_id
spec: v1
topic: "q-state double-triangular latent causal measurement identification via the explicit local-minor certificate Delta_DT: prove the determinant factorization, K_min(P_X)=K, and a terminating sound-and-complete same-K BLCM reconstruction algorithm A_q modulo coordinate/state relabeling and latent MEC; include the q=3 dense no-pure-child witness and CDM/cdmTools identifiability-check consumer"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No calibrated finite-sample certificate, implementation, complexity analysis, or reproducible cdmTools demonstration; three review findings remain on empirical-question typing, omitted positioning, and unconsumed Chen-comparison ballast."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The cdmTools consumer remains only a population specification: the algorithm relies on exact equality, rank, and conditional-independence queries, while multiplicity-calibrated finite-sample inference is left open."
  - "sampling-law-contradiction@oeq:empirical-check"
  - "related_work_omitted@thm:fixed-k-identification"
  - "ballast@thm:chen-class-relation"
reusable_artifacts:
  - "discovery/core.json — maximized theorem graph, cited-source attestations, heterogeneous rectangular sufficiency, and exact equal-q frontier"
  - "discovery/writeup.tex — complete population-level derivations and the positive heterogeneous-converse counterexample"
  - "discovery/solve_tex/solve_thm_certificate_frontier.tex — local-minor factorization/frontier proof"
  - "discovery/solve_tex/solve_thm_coordinate_alignment.tex — equality-lattice coordinate and MEC alignment proof"
  - "discovery/solve_tex/solve_thm_chen_class_relation.tex — full-class incomparability construction"
seeds_burned:
  - index: 0
    one_liner: "Exact local-minor frontier for \\(q\\)-state triangular views"
    reason: "The local-minor frontier was maximized through D0, but reaching field would require a calibrated finite-sample procedure, implementation, complexity analysis, or reproducible computational demonstration rather than another in-scope revision."
proof_attempt_summary: |
  The run derived a sound exact-population package: rectangular Gram-certificate sufficiency,
  an equal-q iff frontier, generic nonvanishing, q^K latent-state and K_min bounds, exact
  three-view coordinate/MEC recovery, and a terminating exhaustive exact-real reconstruction.
  The proposed heterogeneous necessity direction was refuted by a strictly positive counterexample
  and honestly narrowed. The surviving package remained subfield because it supplied no calibrated
  finite-sample certificate, practical implementation, complexity analysis, or reproducible consumer
  demonstration; the three listed review findings remain unrepaired, so this is an unrepaired draft.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24063596
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24063596
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# eid_qary_double_triangular_id / v1 — Downgraded

**Topic.** q-state double-triangular latent causal measurement identification via the explicit local-minor certificate Delta_DT: prove the determinant factorization, K_min(P_X)=K, and a terminating sound-and-complete same-K BLCM reconstruction algorithm A_q modulo coordinate/state relabeling and latent MEC; include the q=3 dense no-pure-child witness and CDM/cdmTools identifiability-check consumer

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 typed BELOW NOVELTY FLOOR: the maximized exact-population identification note is subfield tier with ceiling 6.8 below the fixed field floor and is not salvageable in scope.

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
