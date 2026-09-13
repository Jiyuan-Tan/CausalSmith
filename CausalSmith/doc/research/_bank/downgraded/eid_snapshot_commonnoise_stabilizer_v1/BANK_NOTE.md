# Banked `downgraded` / subfield — anchored D0.5.G re-score

Banked by the supervisor on 2026-09-09 at the operator's direction. **The run did not fail**; it was
re-scored against the projected-P5 D0.5.G rule the operator installed on 2026-09-08 (20:08 PDT).

| | score | tier |
|---|---|---|
| in-pipeline D0.5.G at 20:33 (after the rule change) | 7.9 | field |
| anchored cold re-score, same rule + `loadPaperScoreAnchors` | **7.4** | **subfield** |

Below the operator's 7.5 stop-and-bank line. `salvageable: true`.

- full referee output: `reviews/d05g_rescore_anchored_20260909.log`
- Lean/F-stage work preserved in place; nothing deleted

**Known caveat, recorded honestly.** The two numbers above came from the same rule and the same anchor
block, so the 0.5 gap is context, not rule: the in-pipeline call also supplies `discoveryBrief` and
resolves the note via `loadPaperView` (which stitches in current proof text), while the re-score read
`discovery/writeup.tex` alone. The cold read therefore runs harsher than the stage. Whether the run's
in-pipeline D0.5.G actually used the new prompt was under investigation when this was banked.

**Re-raise path.** `salvageable: true` — move the directory back to `doc/research/active/` and resume
per `_bank/README.md`.
