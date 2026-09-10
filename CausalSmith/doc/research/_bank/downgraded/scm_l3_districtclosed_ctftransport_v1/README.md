---
qid: scm_l3_districtclosed_ctftransport
spec: v1
topic: "District-closed Layer-3 counterfactual transport from heterogeneous typed menus. For finite acyclic SCMs, require each selection domain to alter whole bidirected districts, define a source-labelled graphical recursion for observational, interventional, and declared partial-copy counterfactual inputs, and prove soundness plus fixed-declared-cardinality completeness: every failure produces two SCMs on the original state spaces with identical supplied laws but unequal target conditional counterfactuals. Return either an allowed rational identifying functional or an explicit paired-model certificate, with zero-denominator rejection. Apply it to Park-Lee transport and counterfactual-bandit arm pruning. PRESOLVE EVIDENCE REQUIRING VERIFICATION: On a fixed district response set, every supplied typed-menu cell is a zero-one incidence row applied to the district response-law vector. Stacking extractable rows gives a matrix A: a target row outside the affine row span admits an exact nullspace perturbation producing two same-cardinality laws with equal menus and unequal targets, while a row inside the span gives an affine identifying functional. District closure lifts the paired law across domains without partial-district leakage. The three-node transport witness checks target joint 1/4, target conditional 6/11, and source joint 3/8; the binary bow pair has identical observational laws but target values 1 and 1/2. Searches found existing CTFTR only for Layer-1/2 inputs and CTFIDU+ only for one-domain Layer-3 inputs. UNRESOLVED BOTTLENECK: Prove that the source-labelled graphical recursion preserves all cross-menu information and fails exactly when the target district incidence row leaves the stacked affine span for every finite multi-district compatibility fiber. EARLY KILL TEST: Enumerate the smallest binary two-hedge thicket, form the exact rational incidence matrix of every supplied menu cell, and compare graphical failure with affine-span membership; any failed recursion whose target row lies in the span refutes the fixed-cardinality converse and should stop or pivot the run."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The delivered local recursion is proved sound but not complete: FACE_NOT_IDENTIFIED certifies variation only in an outer row relaxation and need not imply broad-model nonidentification."
  - "The nonidentification branch returns QE range and endpoint formulas but expressly does not construct paired SCMs, missing the proposal's promised explicit fixed-alphabet paired-model certificate."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_prop_binary_acquisition_check.json
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run derived a sound source-labelled district recursion, exact saturated-fiber local results,
  and an exact global sparse-canonical QE fallback with range, evidence, and acquisition results.
  The proposed broad local converse is false because the row face can strictly outer-relax the true
  sparse/cross-district compatibility projection. Returning explicit paired SCM objects would require
  new semialgebraic sampling, representation, decoding, and correctness machinery beyond the attested
  quantifier-elimination result, so the maximized sound paper remains subfield-tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 134129141
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-03"
---

# scm_l3_districtclosed_ctftransport / v1 — Downgraded

**Topic.** District-closed Layer-3 counterfactual transport from heterogeneous typed menus. For finite acyclic SCMs, require each selection domain to alter whole bidirected districts, define a source-labelled graphical recursion for observational, interventional, and declared partial-copy counterfactual inputs, and prove soundness plus fixed-declared-cardinality completeness: every failure produces two SCMs on the original state spaces with identical supplied laws but unequal target conditional counterfactuals. Return either an allowed rational identifying functional or an explicit paired-model certificate, with zero-denominator rejection. Apply it to Park-Lee transport and counterfactual-bandit arm pruning. PRESOLVE EVIDENCE REQUIRING VERIFICATION: On a fixed district response set, every supplied typed-menu cell is a zero-one incidence row applied to the district response-law vector. Stacking extractable rows gives a matrix A: a target row outside the affine row span admits an exact nullspace perturbation producing two same-cardinality laws with equal menus and unequal targets, while a row inside the span gives an affine identifying functional. District closure lifts the paired law across domains without partial-district leakage. The three-node transport witness checks target joint 1/4, target conditional 6/11, and source joint 3/8; the binary bow pair has identical observational laws but target values 1 and 1/2. Searches found existing CTFTR only for Layer-1/2 inputs and CTFIDU+ only for one-domain Layer-3 inputs. UNRESOLVED BOTTLENECK: Prove that the source-labelled graphical recursion preserves all cross-menu information and fails exactly when the target district incidence row leaves the stacked affine span for every finite multi-district compatibility fiber. EARLY KILL TEST: Enumerate the smallest binary two-hedge thicket, form the exact rational incidence matrix of every supplied menu cell, and compare graphical failure with affine-span membership; any failed recursion whose target row lies in the span refutes the fixed-cardinality converse and should stop or pivot the run.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Broad local failure completeness is false on sparse compatibility fibers, and explicit paired-SCM extraction requires a new sample-point, representation, decoding, and correctness architecture; the sound achieved contribution is subfield tier (6.8), below the field floor.

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
