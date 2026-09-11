# scripts/dev — formalization debugging tools

Reusable, parameterized dev utilities for inspecting / testing the CausalSmith research
formalization gates without running the whole pipeline. Run from `tools/` on node 20
(`source scripts/node_env.sh`).

## `hidden_defs.ts` — inspect the F2.5 hidden-def surface (no LLM)

Runs the deterministic `findHiddenStatementDefs` BFS and prints every build-inline
`def`/`structure`/ℝ-quantity reached from a theorem STATEMENT that becomes an `AUX-`
crosswalk row (what F2.5 check K and F4 audit). Pure TypeScript — no codex, instant.

```
npx tsx scripts/dev/hidden_defs.ts <qid> <spec>        # resolve leanDir from state
npx tsx scripts/dev/hidden_defs.ts --lean-dir <path>   # any Lean dir (abs or repo-relative)
```

Each row prints its `flavor` (`const-exist` | `structure` | `predicate` | `quantity`),
file:line, and the T-blocks that reach it.

## Other relocated dev / one-off scripts

- `regen_snippets.ts` — one-off: re-extract `statement` fields in a bundle's
  `lean_snippets.json` with the current `lean_extract` (fixes snippets captured by an
  older extractor). `npx tsx scripts/dev/regen_snippets.ts <bundleDir>`.
- `migrate_bank_stage_prose.mjs` (+ `.d.mts`) — one-off bank migration (old bare-number
  stage ids → `D-`/`F-` labels in bank README prose). Tested by
  `test/migrate_bank_stage_prose.test.ts`. `node scripts/dev/migrate_bank_stage_prose.mjs`.
- `repin_frozen_hashes.mjs` — one-off: regenerate a bundle's `frozen_hashes.json` from a
  hand-amended `formal_layer.tex` (mirrors P1's hashing).
  `npx tsx scripts/dev/repin_frozen_hashes.mjs <bundleDirAbs>`.
- `salvage_resolved_oeqs.ts` — one-off audited migration for legacy D0 cores that proved
  open equivalences in place; reads the core + plan, re-runs the plan gate, rebuilds the graph.
- `watch.py` — ad-hoc poller that tails active research runs (hardcoded run list / path;
  edit before use). Pure scratch monitoring helper.
