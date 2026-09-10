# The D0 graph store — invariants and how to fix a bug here

Read this before changing anything under `src/discovery/vcs/`. The store exists
because the previous D0 stage kept one fact in several places and asked an LLM to
echo it back; every incident was two copies disagreeing. A fix that adds a copy, an
echo, or a check the orchestrator must feed by hand is the bug this module removes.

## The model in five sentences

`main` is a commit; a commit is a tree of content-addressed node blobs; `core.json`
is the rendering of `main` and the orchestrator's working copy. A solver round is a
pull request on the base the solver saw; a PR that only adds merges itself, a PR that
changes an existing claim, definition, assumption, symbol, source or the estimand
waits for a per-node verdict. A proof carries the content keys of its closure and is
proved iff every one still matches; status is never stored. Nothing is deleted: a
reset is a commit, a closed PR keeps its head, every round's raw solver outputs are
kept beside its record. The only writer is `commitGraph`, and a refused commit writes
nothing.

## Invariants (a change that breaks one is wrong, whatever it fixes)

1. **One identity per purpose.** `blobId` is storage identity; `contentKey` is
   mathematical identity. Nothing else identifies a version. No revision stamps,
   digests, attestations, or echoed bytes anywhere in the solver contract or the CLI.
2. **The parent commit is the basis.** A PR, a legacy carry, a hand edit: each is a
   tree against a known parent. Never ask the solver, the operator, or a marker to
   restate what the parent already says.
3. **Nothing lands without a check; nothing is lost without the orchestrator deciding.** Every tree
   passes `checkGraph` before it becomes a commit. When a solver item cannot land
   (fold conflict, check-driven revert, converter rejection, main-versus-PR
   conflict), it is listed on the PR, the PR stays open, and the D-orch (an agent, never a person) merges
   it by hand or closes it. Auto-merge is only for a PR that needs no verdict and
   lost nothing. A migration reports exactly what it could not carry and never
   calls an empty merge a success.
4. **Attribute a violation to a change, never to the round.** A check names things
   by DISPLAY NAME (a symbol as the gate normalizes it, a definition's `name`, a bib
   key, an id), and reports them on whichever node it noticed them on — often an
   untouched consumer. `reconcileToBase` therefore builds one table of every display
   name of every touched node and blames the change that owns a quoted name before
   the node the violation was reported on. If a new check prints names another way,
   extend that table, never add a prefix rule for one message. Only when no change
   can be blamed does it revert everything, and then it says so in `dropped`.
5. **Migration is idempotent and never blocks a run.** A store that exists is
   done; a marker that exists is done, whatever its schema. `ensureStore` runs on
   every D0 and F entry, so it must not throw for anything a run can be in: a core
   that fails a check becomes the initial commit with the violations recorded on
   it (`status` shows them); a corrupt legacy cursor is converted around; a carry
   that fails writes its marker with the failure note and keeps the raw bundle at
   `prs/legacy.inputs.json`. Legacy files are read once and never validated again.
6. **Derived, never stored.** Status, `used_by`, ordering, `core.json`, the paper.
   If a field can be computed from the tree, compute it.
7. **Small surface.** The orchestrator's interface is `d0_vc.ts`: `commit`,
   `reset`, `pr show|merge|reapply|close`, `log|show|diff|status|fsck|migrate`. A new
   situation gets a message that names one of these, not a new flag.
8. **Layout is never a reason to lose content, and blame is verified.** Positions
   are derived: `normalizeGraph` places every symbol after the symbols it references
   and `foldUnitHeads` renumbers each unit's additions after the base, so an order
   rule can only fire on a genuine cycle. `reconcileToBase` blames a touched node
   only after checking that reverting it alone removes the violation (deletions
   first — reverting one restores main's bytes and loses nothing the solver wrote);
   a violation no single revert removes collapses the round, and says so. Every
   PR keeps its raw inputs so `pr reapply` can replay the round against a repaired
   main: the recovery from ANY mis-drop is "fix the cause on main, reapply", never
   retyping solver output.

## What enforces what

| Invariant | Enforced by | Pinned by |
|---|---|---|
| 1 identity | `node.ts` only computes ids; the solver schema ignores `current`/`based_on_revision` | `store.test`, `validity.test` |
| 2 parent is basis | `openPr` takes `base`; `mergePr` three-way against it | `pr.test` |
| 3 nothing lost silently | `prLosses` gates auto-merge in `round.ts`; `mergePr` refuses undecided conflicts, records cascades in `pr.dropped`; `openPr` stores `inputs.json`; a rejected claim keeps its proof bytes | `pr.test`, `flow.test` (the w3 bundle) |
| 4 attribution | `reconcileToBase` display-name table | `pr.test`, `flow.test` |
| 5 migration never blocks | `ensureStore` → `carryLegacyLeftovers` try/catch + marker; `recordViolations` on initial commits | `flow.test` |
| 6 derived | `renderCore` computes status/`used_by`; `render.ts` never reads status for a known tree | `validity.test` (status flip) |
| 7 small surface | `bin/d0_vc.ts` | — |
| 8 layout/blame | `normalizeGraph` symbol order, `foldUnitHeads` renumbering, `reconcileToBase` verified blame, `reapplyPr` | `pr.test` (layout, verified attribution, reapply), `corpus_pr_replay.test` (every recorded real round replays no worse) |

## How to fix a bug here

- Reproduce it as a synthetic graph in `test/discovery/vcs/` (fixture.ts + a few
  nodes). Real-run reproduction is for diagnosis, not for the test.
- Find which invariant the bug violates. The fix restores that invariant in the one
  module that owns it: identity → `node.ts`; validity → `validity.ts`; what the
  solver may change → `pr.ts` `applyUnitOutput`; what needs a verdict →
  `approvalItems`; what is lost and how it is reported → `reconcileToBase`,
  `foldUnitHeads`, `mergePr`; migration → `convert.ts`; dispatch → `round.ts`.
- If the fix needs the operator to supply a hash, or the code to re-read a legacy
  file on every entry, or a second copy of a fact, stop: that is the wrong fix.
- Run `npx vitest run test/discovery/vcs` (the corpus roundtrip covers every real
  core in the repository; the corpus PR replay re-folds every real round whose raw
  inputs are on disk) and `d0_vc migrate` on one real run. A real incident's PR is
  the regression: replay it (`pr reapply` on a scratch copy, or the replay test) and
  check that the only drops left are reverted deletions the orchestrator must decide.

## Where things are

| Concern | Module |
|---|---|
| node blobs, `blobId`, `contentKey` | `node.ts` |
| objects, commits, `refs/main` (CAS), reflog, lock | `store.ts` |
| materialized tree, diff | `graph.ts` |
| closure, basis, `proofVerdict`, `deriveStatus` | `validity.ts` |
| render graph → core, core → graph, normalization | `render.ts` |
| the checks a tree must pass | `checks.ts` |
| the single write path, `publishCore`, rendered-main sidecar | `commit.ts` |
| solver output → unit head, fold, approval, merge, PR records | `pr.ts` |
| a solve round: units, dispatch, reuse receipts, outcome | `round.ts` |
| bringing an old run onto the store, legacy carry, re-proposal | `convert.ts` |
| orphan lemmas, dangling citations | `hygiene.ts` |
