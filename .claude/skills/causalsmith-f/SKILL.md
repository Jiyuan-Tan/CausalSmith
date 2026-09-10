---
name: causalsmith-f
description: CausalSmith research F-stage (formalization) sub-orchestrator — drives F1/F1.5/F2/F2.5/F3/F3.5/F4/F5. Dispatched by causalsmith; not invoked directly by the user.
---

# causalsmith-f — formalization sub-orchestrator

You own F1…F5 under the **resume-lease**: F2.5 faithfulness, the proof loop, and substrate intervention.
You never bank, stop/SIGINT, or cross D/F. Return the lease (§ "Returning the lease") only for
`f5-clean`, `rewind:fix-source`, `substrate-build:study`, `citation-instantiation-overflow`, `cap-block`,
`substrate-unbuildable`, `codex-blocked`, `reviewer-dispute`, `dispatch-request`, a terminal,
`pipeline-bug`, or `request-reseed`.

Shared reference: [`causalsmith-shared/reference.md`](../causalsmith-shared/reference.md). CLIs run from
`<AUTOID>/CausalSmith` after `source tools/scripts/node_env.sh`; `bin/x.ts` = `npx --prefix tools tsx
tools/bin/x.ts`. `{resume-from}` means you resume that stage yourself.

## Re-ground and monitoring

- Each dispatch: `bin/decision_log.ts read <qid> <spec> --phase F` + `state.json`. Attach a watcher to
  the live PID main started; never launch/resume before it exits at its first halt.
- Every resume is detached:
  `setsid bash -c 'source tools/scripts/node_env.sh && npx --prefix tools tsx tools/bin/causalsmith.ts research --resume --from-stage <F-stage> [--auto] <qid> <spec> > logs/<file> 2>&1' < /dev/null & disown`
  then foreground-poll line counts of `pipeline.jsonl` and `reviews/reviews.jsonl` plus a real argv
  token (never `tail -F | grep`; never pipe the node command). State ratchets: after death or lock
  contention, re-resume detached. Never set `CAUSALSMITH_ALLOW_PARALLEL=1`.
- **Codex runtime:** one 30-minute logical window per blocking call, probes ≥120 s apart; complete the
  call only on an actionable halt, exact-PID exit, or deadline; two fully stale windows before
  `pipeline-bug`.
- At every halt: apply the lever, log a `judgment`, resume, re-arm. Paths are writable at a halt; always
  diff EMITTED vs PERSISTED.
- Resume freely within F, including the work-owed `--clear-gate substrate_build_required`. **Never
  clear an iteration/round/budget cap** (F2.5 scaffold-redirect, F1.5 rewinds, theorem splits,
  proof-loop bounds, per-node strikes, filler budgets, any `*_cap_hit`): escalate `cap-block` with the
  node, the recurring verdict across rounds, and what you changed each round; main resets.

## Statements are yours; proofs go to codex

You hand-edit statements, `def`s, scaffolding, imports, and namespaces at halts (including
de-laundering a narrowed definition or weakened T-block). You never hand-write a proof, tactic,
substrate lemma, or compile repair. Loop: diagnose → author statement → codex proves → verify.

- **Workers:** under Codex, managed subagents (`spawn_agent` / warm follow-up), `gpt-5.6-sol` medium.
  Under Claude Code, the canonical `codex exec` invocation from CLAUDE.md (stdin prompt, lean-lsp
  injected, `run_in_background: true`), `gpt-5.6-sol` medium. Never duplicate a pipeline worker by hand.
- Prompts decompose leaves-first, name the statement/helpers, and require `lake build <module>` green
  with zero sorry and no new axioms. Never overlap worker edit scopes; parallelize only disjoint import
  closures.
- Disposable probes, `#check` files, tests, and scripts go in `<paper lean directory>/tmp/` (excluded
  from the inventory/build barrel), never the package root.
- After every round: rebuild, grep the SOURCE for `sorry|axiom` (a green `lake build` exits 0 with
  sorries), run `#print axioms`, diff signatures. A re-scaffold can silently reintroduce a `sorry`.
- A denied/cancelled codex call → `codex-blocked`; never hand-prove or weaken the gate around it.

## Citation rule

Formalize every cited node a delivered `headline` or `headline-support` result needs. A cited node may
remain an explicit conditional premise (`def … : Prop`, recorded in `CITED_DEPENDENCIES.md`) only when
it is secondary with no delivered main-contribution consumer. If formalizing a main-contribution citation becomes substantial → `citation-instantiation-overflow`;
never weaken the consumer or silently leave it conditional.

## Per-stage event → action

**F1 plan** (`stage_1`) halts only for no usable plan or `needs-new-infrastructure`/
`substrate_build_required`. No plan → inspect the artifact. Gates → build per § "Substrate building",
clear the work-owed flag on resume, discharge later via F2.5 (not a re-plan).

**F1.5 / CKPT 1** (`stage_1.5_to_1`) — audit reuse, role, depth, size, fidelity before F2:
- Search Mathlib/Causalean (absolute paths — reference § "Substrate search") for every assumed/gated
  hypothesis and ad-hoc `def`; import and derive existing primitives, never reinvent them.
- Classify each promised theorem as `headline`, `headline-support`, or `secondary` from contribution +
  consumers (`crux:true` is not headline); classify dependencies by provenance: source-owned,
  source-matched facts are `cited`; uncited reusable external debt is `gated`. An uncited paper-specific
  step is never relabeled cited.
- Require every §11 primitive, the full L-block decomposition, and construction hypotheses. Size and
  unbundle each gate: bounded build → minimal `gated` debt; a whole absent named theory → thread only
  its irreducible core as `lean_kind:"assumption"` on every consumer. Prove note-derived reductions; if
  unsure, thread.
- For cited input make one focused application attempt, splitting the generic paper-agnostic bridge from
  paper-specific construction/witness/completeness work. If it becomes citation implementation, new
  general theory, helper clusters, or an unshrinking extra round → `citation-instantiation-overflow`;
  never `--study` it.
- Restate statement/spec mismatch; on `missing_architecture`, build gates and proceed conditional.
  Scaffold post-proof modules topic-split under `Helpers/<Topic>.lean` + barrel.

**F2–F4 proof-review loop** (`PROOF-REVIEW LOOP ESCALATION [<route>]` in `reviews.jsonl`). The loop
self-heals; act per route:
- `hint` → `bin/f3_directive.ts <qid> <spec> --directive "…"` (a PROOF hint only; persists on
  `state.flags.f3_filler_directive`; `--clear` once it lands).
- `build-substrate` → § "Substrate building".
- `fix-source` at phase 4 with reason `F4 dead-helper sweep` → an agent-authored decl nothing consumes
  (`@[…]`-attributed, `instance`, graph-node, and `-- keep:`-marked decls are exempt). Verify with your
  own grep, then DELETE it (default; rebuild after) or add `-- keep: <reason>` directly above it when it
  is deliberate reusable substrate. Never keep silently; never manufacture a use.
- `fix-source` otherwise → reproduce the Lean↔`.tex` conflict yourself (reference § "Rewind
  verification"). False → restore and fix the reviewer or scaffolder in place. Scaffold-side drift the
  F2.5 loop cannot converge → `bin/f2_directive.ts <qid> <spec> --directive "…"` (persistent until
  `--clear`), then rewind to F1.5. A true note error needing a claim change → `rewind:fix-source`.
  Escalate only a mathematical defect; fix mechanical errors in place.
  - F2.5 is incremental: a `scaffold-mismatch` reroute patches only the drifted decl; do not rewind to
    F1.5 for a per-node fix. Reserve a full F1.5 rewind for a genuine plan change.
  - Accept-as-is must be persisted: `npx tsx bin/graph.ts accept-review --dir <formalization-dir>
    --qid <qid> --spec <spec> --id <node-id> --lean-dir <lean-dir> --note "<why>"` (records
    `review.status: matched` at the current statement hash).
- `unclear` (`unadjudicable` / `ambiguous-spec`) → investigate first: read the reviewer/filler
  reasoning, reproduce the conflict or its absence, then route to `fix-source`, an in-place patch, or
  escalate to main with your finding. Never default to "the note is wrong".
- `bank-partial` / `abandon` → escalate (terminal).
- **Strengthen-if-dischargeable:** if an assumed hypothesis is provable from the construction / §6
  primitives, discharge it as a lemma, drop it, edit the `.tex` upward, re-gate F3.5→F5. Weakening the
  `.tex` to match a degraded proof is forbidden.

**The loop (F2.5 → F3 → F3.5 → F3.7 → F4) is never skipped.** F3.5 and the dual-model F4 review fire
only at the loop's done-gate (zero real `sorry` and a settled frozen graph). An escalation means F4 did
not run: never `--resume --from-stage 5` (or any later stage) after a loop escalation — the symptom is
`stage 2.5 … LOOP ESCALATION` followed by `stage 3/3.5/3.7/4 skipped` and no this-round verdict in
`reviews/reviews.jsonl`. Resolve the non-convergent node at the root, re-enter at F2.5, let it run to
completion. If you believe a review is wrong, encode your reasoning as an `f2_directive` and let the
loop converge; if it still will not, return `reviewer-dispute` — never overrule a reviewer or advance the
stage pointer past it. Your own audit never substitutes for F4.

**F5** (`stage_5`, CKPT 2). Return `f5-clean` with the F4 both-reviewer verdicts + recommended tier; no
F4 verdicts ⇒ no `f5-clean`. Bank and promotion require one CKPT 2 acceptance; that single acceptance
authorizes the continuous bank/commit/F7/verification/final-commit sequence, with no repeated approval.
F5 also owns docstring coverage: every
declaration in the run's modules (umbrella root included) gets a docstring whose first paragraph is the
NL translation with `[phrase](hyp:name)`/`[phrase](goal)` crosslinks covering every theorem hypothesis
and conclusion and every definition's explicit parameters and defined object, via one managed
proof-worker pass with build-validated rollback, run before the bank-soundness token scan and the
crosswalk emit. A residual undocumented or crosslink-defective decl blocks F5.

## Faithfulness

Audit every filler statement/`def` edit and `state.added_assumptions` against the `.tex` for
crux-as-bookkeeping, narrowed defs, weakened T-blocks, vacuous witnesses. Reject/reroute drift, inject
`f2_directive`, or hand-de-launder then re-gate F3.5→F5. Disclose every added assumption with
`bin/add_assumption.ts <qid> <spec> --label "…" --statement "…" --classification
faithful-refinement|regularity-bookkeeping [--decision "<key>=<note>"]`, then resume `--stop-after F4`
and confirm `laundering_count` is zero. Never hand-edit the array; `add_assumption.ts` refuses a
substrate gate — use `bin/gate.ts`.

Escalate only a `.tex` claim that is actually wrong (`terminal:tex-claim-wrong`) or a fix that changes
the claim and needs D0/F1 (`rewind:fix-source`). Sync every Lean statement change to the note/JSON NL:
regularity side conditions and lemma statements may refine NL directly; a load-bearing hypothesis,
narrowed class, or weaker bound requires `rewind:fix-source`. Re-render a Lean-hostile definition to a
faithful equivalent only when the NL specifies the concept; it may loosen a downstream constant, never
strengthen, then re-gate through F2.5.

## Substrate building (`gated` only)

Gate only missing external substrate — a general reusable Mathlib/Causalean-missing primitive — never
the note's conclusion. If proving the gate alone yields the headline/converse/identification claim, it
is contribution laundering: attack the core and halt honestly if it fails. `undelivered` is fail-closed
(main skill § "UNDELIVERED safeguard").

**Route:** assume small until proved otherwise. Default: `gpt-5.6-sol` medium proof workers with
lean-lsp and disjoint leaves-first scopes build an in-place research/`Helpers`/`CausalSmith/Mathlib`
lemma. Verify zero sorry, axiom cleanliness, and statement/NL match yourself. Escalate
`substrate-build:study` only for a substantial reusable standard primitive (requirement + slug, proposed
imports, research-folder prerequisites); study substrate never imports `CausalSmith/*_Research` (main
extracts prerequisites first). Study promotion never blocks the current run past its gate. Attempt every
`gated` item; only after a real attempt may an irreducible research-scale core remain debt.

**Register with `bin/gate.ts`, never Lean alone** (unregistered hypotheses vanish on re-scaffold):
`npx tsx tools/bin/gate.ts <qid> <spec> <node_id> --consumers <id1,id2> [--class gated|cited] [--source ..] [--reason ..]`
writes `plan.json`, `graph.json`, `state.added_assumptions`/`SUBSTRATE_DEBT.md` atomically; `--show`
inspects. For prose-only debt mint a node with `--statement "<Lean premise>"` and optional
`--supersedes "<old prose label>"`. A gate is an input, never the consumer's conclusion. Then resume
F2.5 so the `_of_gate` conditional is reviewed.

**Discharge with the CLI:** `npx tsx tools/bin/gate.ts <qid> <spec> <node_id> --discharge [--lean-name
<Name>]` (`--ungate`/`--unset`) clears plan/graph/debt and reopens consumers; then resume F2.5. Resume
after a build with `--resume --from-stage F1.5 --clear-gate substrate_build_required`; later wire the
lemma, replace `_of_gate`, and re-enter F2.5 (not F1). Every discharge re-passes F4.

Before banking run `npx tsx tools/bin/gate.ts <qid> <spec> --audit` (0 clean). `accepted` is refused for
an unregistered substrate disclosure or `cited-mismatch`/`cited-underspecified`. Split a compound gate
into the proved crux and the honest external input. Keep modules ≤600 lines (split before ~900 with
`bin/split_lean_file.ts`), annotate decls `-- @node: <id>`, maintain `proof-uses`, unfreeze affected
nodes.

## Returning the lease to main

Hand back `{escalation: <type>, receipts: [...]}` plus an `escalation` decision-log entry and stop
resuming. `request-reseed` only for a concrete context-capacity problem.

| Escalation | Receipts |
|---|---|
| `terminal:tex-claim-wrong` / `terminal:laundering` | the `.tex` line + the reviewer phrase naming the collapsed conjecture |
| `rewind:fix-source` | the Lean↔note conflict, independently reproduced (`.tex` line + Lean line + why) |
| `cap-block` / `substrate-unbuildable` | the halt + what a real build attempt showed |
| `citation-instantiation-overflow` | consumer node + role; cited interface/source; the focused attempt; residual split generic vs paper-specific; downstream consumer graph; evidence further work implements the citation or builds substantial theory |
| `codex-blocked` | verbatim denial + exact worker request + purpose |
| `reviewer-dispute` | the reviewer's verbatim demand + the conjunct/decl it would break + your reasoning |
| `substrate-build:study` | the `requirement.md` content + slug |
| `f5-clean` | the F4 both-reviewer convergence verdicts + recommended tier |
| `pipeline-bug` | agent-I/O diff (EMITTED vs PERSISTED) + recurrence count |

## Recording

`bin/decision_log.ts append <qid> <spec> --json '<entry>'`. Per intervention a `judgment`
(`{type:"judgment",phase:"F",stage,tried,why}`); on escalation an `escalation` entry with receipts.
