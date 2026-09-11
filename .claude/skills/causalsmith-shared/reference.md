# CausalSmith research orchestrator — shared reference

Lookup tables and recipes shared by `causalsmith`, `causalsmith-d`, and `causalsmith-f`. Read the
section a skill pointer names. Stage-internal logic (prompts, the loop's filler/reviewer internals,
rewinds) lives in the TS pipeline at [`CausalSmith/tools/`](../../../CausalSmith/tools/).

## Process rules

- **Protected paths:** while a run's heartbeat is fresh the guardrail hook (§ "Guardrail hook") denies
  every edit anywhere under `CausalSmith/doc/research/active/<qid>/`, `state.json` included (the
  `state.json` / `PIPELINE_NOTES.md` exemptions apply only on the legacy no-heartbeat fallback). The
  run's Lean tree `CausalSmith/<Substrate>/<QName>/` is not hook-protected — treat it as read-only by
  convention while the run is live. Edit at a halt, where the
  process has already exited.
- **Stopping a run is main's authority.** SIGINT the pipeline node, verify the tree is down (no
  orphaned `codex exec`), then relaunch. A lease-holding sub never SIGINTs. On Windows `TaskStop` kills
  only the wrapper: kill the `Local\OpenAI\Codex\bin` codex tree and any `*sandbox-setup*` process (an
  orphaned one breaks the next run), sparing the desktop `Codex.exe`, `.vscode` Codex, and your harness.
- **Triage a halt** from the last line of `pipeline.jsonl`. If the intervention judge itself failed to
  parse, its raw dump is the newest `intervention_raw_<timestamp>.txt` at the run-dir root.
- **Watcher ownership.** The current lease holder arms the watcher for its whole phase, including the
  cold-start→first-halt window. Exactly one watcher per qid; different qids are independent.
- **Subs stay in their turn.** A dispatched sub that starts a `run_in_background` task and ends its
  turn is not re-woken (the notification routes to the parent). Launch the node `--resume` detached
  (`setsid … < /dev/null & disown`, stdout/stderr to `<qid>/logs/`), then foreground-poll, re-issuing
  the poll at the Bash time cap. A foreground `--resume` dies at the ~10-min cap; a plain
  `run_in_background` node dies at ~60 min. Never pipe the node command through `grep`.
- **Only main dispatches Claude subagents** (Claude runtime); a sub returns
  `{escalation:"dispatch-request", spec:…}`. Under Codex every orchestrator-initiated child goes through
  `spawn_agent`, never a shell `codex exec`. The long TS node itself is still a detached OS process.
- **A denied or cancelled codex call is `codex-blocked`.** Return the lease with the verbatim denial,
  the exact command, and its purpose. Never hand-prove, weaken, `sorry`/gate the node, or retry with
  different flags. Once the user grants permission, re-issue the same command.

## Watcher recipes (Claude runtime; Codex uses the fixed-window contract in each skill)

Watch **both** `pipeline.jsonl` (stage completions) and `reviews/reviews.jsonl` (per-round verdicts;
the `reviews/` dir does not exist until the first review lands). Poll line counts — `tail -F | grep`
misses sparse verdicts and files created after arming:

    DIR=doc/research/active/<qid>; pl=0; rv=0
    [ -f "$DIR/pipeline.jsonl" ] && pl=$(wc -l <"$DIR/pipeline.jsonl")
    [ -f "$DIR/reviews/reviews.jsonl" ] && rv=$(wc -l <"$DIR/reviews/reviews.jsonl")
    while true; do sleep 15
      for e in "pl:$DIR/pipeline.jsonl" "rv:$DIR/reviews/reviews.jsonl"; do
        v=${e%%:*}; f=${e#*:}; [ -f "$f" ] || continue
        n=$(wc -l <"$f"); old=$(eval echo \$$v)
        [ "$n" -gt "$old" ] && { sed -n "$((old+1)),\$p" "$f"; eval $v=$n; }
      done
    done

Emit every new line (no filter). Detect exit with `pgrep -f "causalsmith.ts research.*<qid>"` (the
`causalsmith.ts research` token avoids self-match). For main only, a lightweight terminal-event
watcher (`run_in_background`; exits on bank / checkpoint / process exit):

    DIR=doc/research/active/<qid>; STATE=$DIR/state.json; PLOG=$DIR/pipeline.jsonl
    until ! pgrep -f "causalsmith.ts research.*<qid>" >/dev/null \
       || python3 -c "
    import json,sys
    d=json.load(open('$STATE'))
    try: last=json.loads(open('$PLOG').read().strip().splitlines()[-1])
    except Exception: last={}
    sys.exit(0 if (d.get('banked') or d.get('next_action')=='pending_checkpoint' or last.get('status')=='checkpoint') else 1)"; do
      sleep 15
    done

Arm the watcher in the same turn as the launch/resume, paired with a second `Monitor` on process
liveness + newest-file mtime to catch a silent hang (alive, no writes, no live `codex exec`).

## Liveness and stale processes

Flat file mtimes during F3 are normal (workers run long elaboration cycles before writing). Stuck =
no live `lean`/`lake`/`codex` at non-trivial CPU AND nothing appended to `reviews.jsonl`,
`state.json`, or `.lean` files for well beyond one elaboration cycle. A widening gap between writes on
an oversized file is a split signal (`bin/split_lean_file.ts` at a clean boundary), not a hang.

A finished run can linger, held open by orphaned `lean`/`lake` children: terminal `pipeline.jsonl`
line, no `state.json` write for a long time, no live `codex exec` under this qid, idle `lean` children,
yet `pgrep` still matches. Treat "stage advanced AND no state write AND no live codex" as a terminal
trigger: verify the tree is idle, then reap only THIS qid's tree (`TaskStop` the task; kill surviving
`lean`/`lake` children under it — never another qid's processes, your lean-lsp server, or a separate
codex). Never force-kill mid-`codex`. Reaping keeps the cluster under its process/file caps.

## Substrate search and build technique

- **Search at the right path.** Causalean is a sibling of the CausalSmith package: `import
  Causalean.X.Y` is `<AUTOID>/Causalean/X/Y.lean`. Grep with the absolute path or from `<AUTOID>/`;
  confirm absence with `find <AUTOID>/Causalean -name '<File>.lean'` or `lean_local_search`, never a
  relative grep from inside `CausalSmith/`.
- **Verify a "missing" gap before building.** F1 surveys by name and over-defers; read the candidate
  module (`npm run search`, `lean_local_search`) before trusting a defer estimate.
- **Build as a dependency graph.** Decompose; dispatch the smallest independently verifiable leaves
  first, verify each, assemble the coupled proof last. On an honest codex stop, classify the gap
  (missing leaf → build it; wrong instance/typeclass route → search it; your own over-constraint →
  relax it) rather than re-dispatching the same prompt.
- **Check the specific structure before accepting a general Mathlib gap** — the construction's own
  definitions often sidestep the general theorem.
- **Side-conditions are discovered by building.** Sanity-check a gate is true as stated before assuming
  it; attempt the build to surface its hypotheses. Gates are tracked debt (`SUBSTRATE_DEBT.md`).
- `--study` PASS ends in `coordinate`: a codex coordinator merges the substrate into its topical
  Causalean home, dedups, documents it docstring-canonically, under the verify-or-rollback gate.

## Proof-review loop — when to intervene

Default: let it run; act per the checkpoint route (`hint` / `build-substrate` / `fix-source` / `unclear` /
`bank-partial` / `abandon`). Intervene when the faithful fix is one the loop's lanes structurally
cannot make: a decl loops with no goal movement because its fix needs a frozen-theorem-meaning change or
a core-`def` strengthen, or the reviewer keeps flagging drift the filler cannot resolve without changing
the spec. A `fix-source`/`user` checkpoint whose diagnosis points at an internal helper needing only a
T-block-preserving fix (a sign correction, a bookkeeping premise threadable from an existing ledger) is
yours to audit and fix in place.

How: (1) act at the halt; (2) patch faithfully — confirm the `.tex`/`.md` defines or uses the thing,
derive the correct statement from the definitions, correct the helper, cascade through dependent signed
helpers up to the first sign-insensitive consumer, document the derivation, and `lake -d CausalSmith
build <module>` the chain green (sorries OK); (3) leave it compiling with `BLOCKER` hints for the filler,
then resume. Read the F4 convergence verdict before banking whenever a localized edit touched a
load-bearing statement.

**Helper hygiene.** Judge by quality, not count: flag a new helper only when redundant (duplicates a
Causalean/module lemma), trivial (inline it), or orphaned (nothing references it); prune at a clean
boundary, never mid-decomposition. F3 scans only `state.lean_subdir`, so abandoned `by sorry` stubs in
`CausalSmith/CausalSmith/Mathlib/` are yours to clean after all F3 jobs finish: delete a `by sorry` stub
only if nothing in the whole CausalSmith package references it; never delete a proved lemma.

## state.json — fields

Schema: [`tools/src/state.ts`](../../../CausalSmith/tools/src/state.ts).

| Field | Meaning |
|-------|---------|
| `stage_completed` | Bare number on disk, order `"-1.1","-1.2","-0.5","0","0.5","1","1.5","2","2.5","3","3.5","4","5"` (a legacy on-disk `"3.7"` is remapped to `"3.5"` on load); cold-start sentinel `"-1.2"`. F5 ≡ `"5"`, D0 ≡ `"0"`, D0.5 ≡ `"0.5"`, D-1 ≡ `"-1.2"`. |
| `next_action` | `"pending_checkpoint"` after a clean F5, `"user_chose:<command>"` once acted on, else `null`. No `ckpt_pending` field exists. |
| `flags.missing_architecture` (+`_items`) | Scaffolder reported `blocked-missing-architecture`; resume blocks until each item exists. |
| `flags.stage_neg1_fallback` | D-1 budget spent without an acceptable proposal. Bank, or `--resume --clear-gate stage_neg1_fallback` after an out-of-band revision. |
| `flags.general_review_halt` | General-reviewer halt with reason; clear via `--clear-gate` after addressing it. |
| `flags.theorem_splits_cap_hit`, `stage1_rewinds_cap_hit`, `scaffold_redirect_cap_hit`, `stage0_budget_exhausted`, `d0_loop_cap_hit`, `proof_loop_cap_hit` | Cap/budget exceeded (reason in value). Clear only via `--resume --clear-gate <flag>` (registry in `tools/src/cap_gates.ts`); clearing resets the paired counters. |
| `flags.f2_scaffold_directive` | Persistent F2 scaffold-faithfulness directive (`bin/f2_directive.ts --directive "…" \| --directive - \| --clear \| --show`), injected on every scaffold pass until cleared. Statement-shape steer only. F3 analogue: `flags.f3_filler_directive` (`bin/f3_directive.ts`), a proof hint. |
| `banked` (+`banked_tier`, `banked_on`, `banked_reason`) | Run retired into `_bank/<tier>/`; inert. |
| `proposed_from` | `--propose` runs: `topic`, `final_verdict`, `iterations[]`, `seed_list`. |
| `design_decisions`, `added_assumptions`, `pending_sorries` | Relayed at checkpoints. Add an assumption only via `bin/add_assumption.ts` (re-using a `label` replaces; `--show` lists; refuses `substrate-gate` — use `bin/gate.ts`). |
| `cited_checks` | F4 cited source-match verdicts; `cited-mismatch`/`cited-underspecified` make `bank_entry.ts` refuse `accepted`. |

**Never hand-edit `state.json`.** Every mutation has a CLI: cap clears → `--resume --clear-gate`;
stage re-entry → `--resume --from-stage`; gates → `bin/gate.ts` (`--discharge` to clear); F2/F3
directives → `bin/f2_directive.ts` / `bin/f3_directive.ts`; D0 directive → `bin/d0_directive.ts`;
D-1.2 directive → `bin/dneg1_directive.ts`; assumptions → `bin/add_assumption.ts`; D0 solver pull
requests → `bin/d0_vc.ts <qid> <spec> pr show|merge|reapply|close`; bank → `bin/bank_entry.ts`; decision log →
`bin/decision_log.ts`. The one store the orchestrator DOES hand-edit is the D0 working copy
(`discovery/core.json`), always followed by `bin/d0_vc.ts <qid> <spec> commit --note "…"`, which checks
it and commits it to the graph's `main`; `discovery/vcs/` is never hand-edited.

## Checkpoint recognition

The authoritative signal is the **last line of `pipeline.jsonl`**: `"status":"checkpoint"` with a
`message` and, on a halt, `next_step_guidance` (post-F5 also `next_action:"pending_checkpoint"`). Never
classify from stdout (the CLI always prints `finished at stage <N>`). In auto mode, "ask/offer/wait"
actions collapse to "decide per the rule, then `--resume`" except the main skill's hard stops.

| Observed | Meaning | Action |
|----------|---------|--------|
| `stage_completed:"5"` + checkpoint line / `next_action:"pending_checkpoint"` | CKPT 2 | Print Lean file list, API.md diff path, `added_assumptions`, and planned F7 closure; ask once to accept the continuous bank → scoped commit → F7 → verification → final scoped commit sequence. |
| `stage_completed:"5"`, no pending signal | CKPT 2 already acted on | Nothing to resume. |
| `stage_completed:"1.5"` + `CONSOLIDATED CKPT 1` | CKPT 1 | Depth/reuse/fidelity audit (F skill § "F1.5"); wait for user unless auto. |
| `stage_completed:"1"` + no-usable-plan | F1 self-halt (its only one — F1 no longer halts for substrate) | Inspect `plan.json`; substrate gates are classified at F1.5. |
| `flags.missing_architecture:true` | Resume blocked | Build each listed item, clear, resume gated. |
| `flags.stage_neg1_fallback` | D-1 budget spent | Bank `downgraded|failed`, or clear deliberately to retry. |
| `flags.general_review_halt` / a cap flag | Halt / cap | Address the cause, then `--clear-gate`. |
| `stage_completed:"-1.2"` + `proposed_from.final_verdict=="NO-PASS"` | D-0.5 NO-PASS, revises exhausted | Bank `failed`. |
| `stage_completed:"0.5"` + terminal REJECT in `reviews.jsonl` | D0.5 terminal reject | Bank `failed` (correctness) or `downgraded` (sound, over-framed). A mid-stage `revise` is iteration. |
| `banked:true` | Already banked | Do not re-enter. |
| stderr error, `state.json` unchanged | Crash | Print stderr tail; do not auto-retry. |

## Rewind verification

Read the rewind verdict (the `PROOF-REVIEW LOOP ESCALATION [fix-source]` line in `pipeline.jsonl`
and the reviewer reasoning in `logs/_reviewer_calls.log`), locate the flagged declaration, and independently reproduce the conflict against the
`.md`/`.tex` (the verdict must cite the spec line, the Lean line, and why they conflict). Drift
signatures: a hypothesis over-quantified to unsatisfiability (`∀ n` where the spec says *eventually*),
a dropped/extra term, a wrong sign, a `def` gerrymandered to the proof's objects. Legitimate → let the
re-scaffold run, then re-read the patched declaration and confirm 0-sorry. False → restore the
pre-rewind state (`state.json` `.bak` + `git restore` of only the rewound files) and carry on.

## Bank

Bank only on the verdict the run terminated on; `revise` is iteration.

| Final state | Tier |
|-------------|------|
| F5 complete, CKPT 2 approved | `accepted` (bank first, then run F7 and its scoped commit without another approval stop) |
| D-0.5 ACCEPT but D0.5 terminal REJECT / exhausted NO-PASS on novelty, math sound | `downgraded` (record `seeds_burned[]`) |
| D-0.5 NO-PASS, or D0.5 REJECT on correctness/structure | `failed` |

```bash
cd <AUTOID>/CausalSmith && source tools/scripts/node_env.sh
npx --prefix tools tsx tools/bin/bank_entry.ts \
  --qid <qid> --spec <spec> --tier <tier> \
  --reason "<one-sentence verdict; verbatim where possible>" \
  [--achieved-tier <incremental|subfield|field|flagship>] \
  [--seeds-burned "0,3" --seed-burn-reason "<why>"] \
  [--reusable <solver_blocked|not_reusable|unknown>] \
  [--reraise-status <re-raise|retry|true-negative|unknown>] \
  [--proposal-promise-gap <gap>] [--dry-run]
npx --prefix tools tsx tools/bin/bank_drift.ts [--json]     # tier-drift audit
```

`bank_entry.ts` patches the `banked*` fields, moves the run dir to `_bank/<tier>/<qid>_<spec>/`, and
generates a README with TODOs for `gap_reasons[]`, `reusable_artifacts[]`, `proof_attempt_summary` —
fill them. `--reraise-status`: `true-negative` = hopeless topic; `re-raise` = sound math, novelty
over-framed; `retry` = sound math, one construction fell short. Schema:
[`_bank/README.md`](../../../CausalSmith/doc/research/_bank/README.md).

## Guardrail hook

[`.claude/hooks/causalsmith-guardrail.sh`](../../hooks/causalsmith-guardrail.sh) (`PreToolUse`) denies
`Edit/Write/MultiEdit` on paths owned by an active run. Active = a fresh heartbeat
(`research/active/<qid>/logs/.run.active` or `study/runs/<run_id>/.active`; mtime < 5 min and PID
alive), or, as fallback, any `*_state.json` in the dir with `stage_completed != "5"`. It never fires on
Read; a denial means you tried to mutate a protected path.

## What lives where

| Concern | Path |
|---------|------|
| Stage dispatcher + helpers | [`pipeline_stages.ts`](../../../CausalSmith/tools/src/pipeline_stages.ts), [`pipeline_support.ts`](../../../CausalSmith/tools/src/pipeline_support.ts) |
| Prompts | [`src/discovery/prompts/`](../../../CausalSmith/tools/src/discovery/prompts/) (D-1, D0, D0.5); [`src/formalization/prompts/`](../../../CausalSmith/tools/src/formalization/prompts/) (F1/F1.5/F2, `proof_filler.txt`, `proof_reviewer.txt`, F5) + [`proof_review_loop.ts`](../../../CausalSmith/tools/src/formalization/proof_review_loop.ts) |
| State schema / stage order | [`state.ts`](../../../CausalSmith/tools/src/state.ts), [`constants.ts`](../../../CausalSmith/tools/src/constants.ts) |
| Bank tools / archive | [`tools/bin/bank_*.ts`](../../../CausalSmith/tools/bin/), [`doc/research/_bank/`](../../../CausalSmith/doc/research/_bank/) |
| Per-run logs (heartbeat, reviewer-call log, any manual redirect/pid file) | `<qid>/logs/` — never the qid root |
| Pipeline-failure notes | `CausalSmith/doc/research/PIPELINE_NOTES.md` (created on first use) |
