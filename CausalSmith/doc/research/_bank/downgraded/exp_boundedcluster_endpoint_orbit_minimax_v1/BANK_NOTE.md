# Banked `downgraded` / subfield — anchored D0.5.G re-score under the projected-P5 rule

Banked by the supervisor on 2026-09-09 at the operator's direction. **The run did not fail**; it was
re-scored against a scoring rule that changed after it started.

On 2026-09-08 the operator rewrote D0.5.G's `paper_score_ceiling` from a best-case CEILING ("the
highest score this note could earn IF formalization and writing went perfectly", explicitly "do NOT
dock for exposition, positioning, or a missing empirical bridge") to a **projected P5 score** for the
delivered package — judging claim fidelity, exposition, positioning and reproducible supporting
evidence together, crediting only delivered results.

Every live F-stage run was re-scored cold against the new prompt WITH the runtime calibration anchors
(`loadPaperScoreAnchors`: six banked papers shown with the score P5 actually gave them, 8.0 down to
4.0). Anchoring matters — the same runs scored 0.2–0.7 higher without it.

| | score | tier |
|---|---|---|
| original in-pipeline D0.5.G (old rule) | 8.2 | field |
| anchored re-score (new rule) | **7.4** | **subfield** |

Below the operator's 7.5 stop-and-bank line. `salvageable: true`.

- full referee output: `reviews/d05g_rescore_anchored_20260909.log`
- state at stop: `stage_completed` around F1.5; run was ~6h into the F stages
- Lean work is preserved in place; nothing was deleted

**Re-raise path.** `salvageable: true`, so this is a live re-raise candidate per `_bank/README.md`:
move the directory back to `doc/research/active/` and resume. Caveat: the re-score is a cold read of
`discovery/writeup.tex` only — it did not see the F-stage Lean state, and the two windows scored in
the live pipeline the same evening came in at 7.8 and 7.9, so the anchored cold read may run harsher
than a full in-pipeline call.
