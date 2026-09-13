---
qid: eid_esep_dmg_greatest_complete
spec: v1
topic: "Greatest E-separation representatives for finite directed mixed graphs: prove unrestricted single-edge transfer, deduce binary-union closure and simultaneous admissible-edge saturation, and recover the canonical greatest representative and compelled edges from finitely many singleton E-separation queries. Preserve arbitrary directed cycles, self-loops, and bidirected confounding; cover SCC-changing directed additions and bidirected additions outside existing SCC rectangles. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Singleton composition and fixed-profile mixed saturation were derived; exhaustive checks through three vertices and sampled five/six-node tests found no union failure. UNRESOLVED BOTTLENECK: unrestricted single-edge transfer. EARLY KILL TEST: exhaust all five-vertex bases with at most five edges and independently confirm any failure. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_esep_dmg_greatest_complete.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised unrestricted all-DMG single-edge transfer and greatest representative remain open; the delivered theorem proves fixed-profile saturation and conditional/order-theoretic recovery only."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "fixed-profile result is genuine but narrow; raw union/intersection recovery mostly finite enumeration; central all-DMG conjecture unresolved."
  - "promised unrestricted all-DMG greatest representative/single-edge transfer is left open; node delivers fixed-profile saturation plus order-theoretic equivalence."
  - "Complete the contextual-replacement theorem for every edge appearing in an E-equivalent graph, explicitly handling collider activation and SCC-tail changes."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_greatest_representative.json
  - discovery/writeup.tex
  - logs/early_kill_35.cpp
  - logs/early_kill_40.cpp
seeds_burned: []
proof_attempt_summary: |
  The run formalized the fixed mixed-SCC-profile saturation theorem and tried to
  extend it through a shortest-witness, marked contextual-replacement argument. Two
  explicit counterexamples invalidated that proof architecture without refuting the
  conjecture itself. Unrestricted single-edge transfer across SCC/profile changes and
  bidirected loops remains open, so the honest result is incremental rather than field.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 18618159
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 18618159
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_esep_dmg_greatest_complete / v1 — Downgraded

**Topic.** Greatest E-separation representatives for finite directed mixed graphs: prove unrestricted single-edge transfer, deduce binary-union closure and simultaneous admissible-edge saturation, and recover the canonical greatest representative and compelled edges from finitely many singleton E-separation queries. Preserve arbitrary directed cycles, self-loops, and bidirected confounding; cover SCC-changing directed additions and bidirected additions outside existing SCC rectangles. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Singleton composition and fixed-profile mixed saturation were derived; exhaustive checks through three vertices and sampled five/six-node tests found no union failure. UNRESOLVED BOTTLENECK: unrestricted single-edge transfer. EARLY KILL TEST: exhaust all five-vertex bases with at most five edges and independently confirm any failure. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_esep_dmg_greatest_complete.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** General referee: fixed-profile result is genuine but narrow; central unrestricted all-DMG conjecture remains unresolved; normalized tier incremental with paper_score_ceiling 4.8 below the field floor.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The fixed-profile saturation construction and the bounded early-kill programs are
the reusable starting points. A follow-on should not repeat the marked-probe route;
it needs a genuinely new copy-aware replacement architecture for profile-changing
edges.
