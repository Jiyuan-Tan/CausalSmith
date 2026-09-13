# Re-tiered `accepted` → `downgraded` (subfield) — STRICT anchored D0.5.G re-score

Moved by the supervisor on 2026-09-09 at the operator's direction. **The run did not fail and its
mathematics was not refuted**; it was re-judged under a scoring rule installed after it was banked.

On 2026-09-08 the operator rewrote D0.5.G's `paper_score_ceiling` from a best-case CEILING to a
**projected P5 score** for the delivered package (claim fidelity, exposition, positioning and
reproducible supporting evidence judged together, crediting only delivered results), and added a STRICT
referee persona. Every accepted entry that had never been presented was re-scored cold against that
prompt with the runtime calibration anchors (`loadPaperScoreAnchors`).

| | score | tier |
|---|---|---|
| original D0.5.G (old best-case-ceiling rule) | field-clearing | field |
| STRICT anchored re-score, 2026-09-09 | **6.7** | **subfield** |

It was the only one of four unpresented accepted entries to fall below the 7.8 field bar, and it fell a
full point clear of the ±0.25 reviewer dispersion we measured — not a borderline call. Its writeup is
37 KB against 122–157 KB for the three that held (8.0, 7.9, 7.8), consistent with less delivered
substance rather than a harsher reading.

Referee's reasoning: for `beta < gamma` the note proves only a bracket whose lower endpoint depends on
gamma and upper endpoint on beta — it does not determine the advertised causal-private frontier, the
`alpha+beta` privacy regime, or even the full-class privacy-free minimax rate. The one matched case
`beta = gamma` comes from armwise private regression plus an embedded regression lower subproblem, so
it is regression inheritance rather than a new causal-nuisance frontier. The two-point barrier excludes
only lower bounds certified through one particular TV-contraction route, supplying neither the missing
converse nor achievability. The consumer claim that the frontier supplies an optimal privacy-budget and
localization rule overstates what was delivered.

- full referee output: `reviews/d05g_rescore_anchored_strict_20260909.log`
- no presentation bundle was ever produced, and none should be; the P stages are not worth spending here
- Lean output and all artifacts preserved unchanged

**Re-raise path.** `salvageable: true`. The bounded move that would lift it, in the referee's words:
close the `beta < gamma` privacy gap by proving a private higher-order causal estimator and a matching
fuzzy or multi-hypothesis lower bound for the `alpha+beta` privacy branch over the stated full law
class. Move the directory back to `doc/research/active/` per `_bank/README.md` to re-raise.
