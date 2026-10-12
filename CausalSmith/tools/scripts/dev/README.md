# scripts/dev — formalization debugging tools

Reusable, parameterized dev utilities for inspecting / testing the CausalSmith research
formalization gates without running the whole pipeline. Run from `tools/` after
`source scripts/node_env.sh`.

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
