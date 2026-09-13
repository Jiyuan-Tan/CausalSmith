# Re-tiered `accepted` → `downgraded` — D0.5.G recalibration, 2026-09-09

Moved by the supervisor at the operator's direction. **The run did not fail and its mathematics was
not refuted.** It was re-judged after the D0.5.G scoring scale was recalibrated.

What changed: the D0.5.G prompt contained a tier-cap table naming 7.8 as the field boundary, and the
referee was anchoring on it — 26% of all scores landed on exactly 7.8, including papers whose real P5
scores ranged from 5.7 to 7.0. Removing the cap table (the prompt now says only "Score the paper on its
own merits"; the threshold lives solely in code) moved every score down and, more importantly, restored
ranking: mean absolute error against known P5 scores fell from 1.4 to 0.58. The code threshold was then
lowered 7.8 → 7.2 to match the new scale.

| | score | tier |
|---|---|---|
| original D0.5.G (cap-table prompt) | field-clearing | field |
| re-score, no-cap prompt, 2026-09-09 | **6.9** | below the 7.2 field bar |
| actual P5, where one exists | 5.7 | |

- full referee output: `reviews/d05g_rescore_nocap_20260909.log`
- all artifacts, Lean output and any presentation bundle preserved unchanged

**This is a scale change, not a verdict on the work.** Every one of the mill's six acceptances scored
below the old 7.8 bar under the new prompt (7.2/7.2/7.2/6.9/6.9/6.4), which is why the threshold moved
with it. Re-raise per `_bank/README.md` if the score is later judged unrepresentative.
