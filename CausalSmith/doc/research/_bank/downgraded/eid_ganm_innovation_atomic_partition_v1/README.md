---
qid: eid_ganm_innovation_atomic_partition
spec: v1
topic: "Population identification of innovation-atomic causal units in grouped additive-noise models. For observed scalar coordinates with a smooth positive density, define admissible partitions by C3 additive block mechanisms, mutually independent smooth positive block noises, causal minimality, Göbler edgewise Condition-1 restrictions, and innovation atomicity: no nontrivial coordinate split of a block noise admits an additive-noise representation in either direction. Prove that every admissible law has one refinement-minimal coordinate partition equal to the generating causal units and one labelled block DAG, excluding all incomparable crossings; give assumption-removal converses and a finite-dimensional certification corollary. Distinguish Niu and Rajpal joint-learning algorithms and audit the Bosch 19-process grouping. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For two empty-DAG representations, smooth log-density decompositions over both partitions force decomposition over common-refinement cells, so every crossed block innovation splits independently and violates atomicity. For the three-coordinate crossing {1,2}<-{3} versus {1,3}<-{2}, equating conditional densities yields an exact translation-family equation; on every nonsingular chart it forces alternative conditional innovation laws to be translates, while the identically singular case conflicts with nondegenerate independent noise. The disclosed quadratic/Gaussian four-variable threat is inadmissible because both middle-block innovations are explicit scalar ANMs. Searches found joint grouping algorithms and interventional/temporal partition results, but no population uniqueness theorem. UNRESOLVED BOTTLENECK: Globalize the local translation-family conclusion, or prove an equivalent nondescendant-conditioning lemma, for arbitrary crossing blocks when conditioning selects coordinates from a correlated alternative innovation. EARLY KILL TEST: Complete the smooth-positive three-coordinate crossing lemma first; one solution with both bivariate innovations atomic and every edgewise Condition-1 clause satisfied should immediately stop the kernel."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Population identification of the generating causal-unit partition is not proved: the domain of the recovery map may contain multiple incomparable or refinement-related partitions."
  - "The new cross-partition results exclude only unequal empty-DAG factorizations, one three-coordinate crossed single-edge pattern, and coarse-root refinements whose fine blocks have no external parents; arbitrary crossings and externally parented refinements remain open."
  - "The delivered result is a narrow ambiguity frontier rather than the requested identification theorem."
reusable_artifacts:
  - discovery/core.json
  - discovery/d0_working.json
  - discovery/writeup.tex
  - discovery/proof_archive.jsonl
  - reviews/review_math.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the empty-DAG partition theorem, a smooth-positive three-coordinate
  crossed-single-edge exclusion, and a root/fine-parent-closed strict-refinement
  exclusion, while preserving fixed-partition DAG uniqueness from the cited GANM result.
  It could not globalize the crossing argument through conditioning on correlated
  competing innovations or cancel external fine-parent terms under the stated class.
  The surviving identified-set/ambiguity-frontier result is sound and citation-verified,
  but those unresolved cases keep it below the field novelty floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 126795287
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# eid_ganm_innovation_atomic_partition / v1 — Downgraded

**Topic.** Population identification of innovation-atomic causal units in grouped additive-noise models. For observed scalar coordinates with a smooth positive density, define admissible partitions by C3 additive block mechanisms, mutually independent smooth positive block noises, causal minimality, Göbler edgewise Condition-1 restrictions, and innovation atomicity: no nontrivial coordinate split of a block noise admits an additive-noise representation in either direction. Prove that every admissible law has one refinement-minimal coordinate partition equal to the generating causal units and one labelled block DAG, excluding all incomparable crossings; give assumption-removal converses and a finite-dimensional certification corollary. Distinguish Niu and Rajpal joint-learning algorithms and audit the Bosch 19-process grouping. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For two empty-DAG representations, smooth log-density decompositions over both partitions force decomposition over common-refinement cells, so every crossed block innovation splits independently and violates atomicity. For the three-coordinate crossing {1,2}<-{3} versus {1,3}<-{2}, equating conditional densities yields an exact translation-family equation; on every nonsingular chart it forces alternative conditional innovation laws to be translates, while the identically singular case conflicts with nondegenerate independent noise. The disclosed quadratic/Gaussian four-variable threat is inadmissible because both middle-block innovations are explicit scalar ANMs. Searches found joint grouping algorithms and interventional/temporal partition results, but no population uniqueness theorem. UNRESOLVED BOTTLENECK: Globalize the local translation-family conclusion, or prove an equivalent nondescendant-conditioning lemma, for arbitrary crossing blocks when conditioning selects coordinates from a correlated alternative innovation. EARLY KILL TEST: Complete the smooth-positive three-coordinate crossing lemma first; one solution with both bivariate innovations atomic and every edgewise Condition-1 clause satisfied should immediately stop the kernel.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The partial-function identified set excludes only empty-DAG ambiguity, one three-coordinate crossed single-edge pattern, and parent-closed root refinements; arbitrary crossings and externally parented refinements remain open, so the sound ambiguity frontier is subfield rather than field.

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
