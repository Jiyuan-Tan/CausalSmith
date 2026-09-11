---
name: causalsmith
description: Run the CausalSmith pipeline. Invoke on `/causalsmith research` to discover, formalize, verify, and bank a causal theorem — with a qid and specialization, or with no topic at all, in which case it selects the topic and names the run itself; `/causalsmith present` with a qid and specialization to turn an accepted entry into a verified paper bundle; or `/causalsmith study` with a slug to build reusable Causalean substrate. Also invoke on conversational requests to launch, resume, present, or study a CausalSmith result. Research owns the D-/F-stage workflow and dispatches `causalsmith-d` and `causalsmith-f`; presentation details live in `causalsmith-present/SKILL.md`.
---

# /causalsmith research — main orchestrator

You are the **main orchestrator**: you own this qid's node process, its watcher, and every terminal or
cross-boundary decision. Phase sub-orchestrators read verdicts and return receipts. Your job: route,
resume, record.

- **Sub-skills:** `causalsmith-topics` (no-qid proposal selection) · `causalsmith-d` (D-1/D0/D0.5) ·
  `causalsmith-f` (F1…F5) · `causalsmith-present` (P0–P6).
- **Shared reference:** [`causalsmith-shared/reference.md`](../causalsmith-shared/reference.md) —
  `state.json` fields, checkpoint recognition, bank tool, watcher/process rules, rewind verification,
  substrate-build technique. Read the section a pointer names.
- **F7 payload:** [`f7-substrate-promotion.md`](f7-substrate-promotion.md).

**Mode routing:** `causalsmith present` → follow [`causalsmith-present/SKILL.md`](../causalsmith-present/SKILL.md).
`causalsmith study` → § "study". Otherwise the research procedure below.

State is externalized: on compaction/respawn, re-ground from `state.json` and
`orchestrator/decision_log.jsonl`; never rely on an agent handle.

**Citation/contribution invariant.** A published, exactly source-matched result that is not this paper's
contribution may stay `gate_class:"cited"` even when a headline invokes it. Anything paper-owned — the
advertised theorem step, an adaptation to a new model, an embedding, normalization or transfer, a regime
splice, any novel bridge — must be proved in Lean. At CKPT 1, classify ownership from the source and the
full dependency graph (`crux:true` alone is insufficient) and reject relabeling of new work as cited.

## The loop

**One holder per qid.** Main owns the node process + watcher but grants a phase-scoped `resume-lease` to
the D or F sub. The holder alone arms the watcher and calls `--resume`, self-driving its own phase. A
lease never carries terminal authority (bank, stop, SIGINT, cross-boundary rewind); it returns to main at
a phase boundary, escalation, or terminal.

**Different qids run concurrently.** `<run-dir>/logs/.run.active` rejects only a duplicate of the SAME
qid; scope every liveness/reap check to that qid. Never kill or postpone another qid; shared build/graph
locks serialize contention. `CAUSALSMITH_ALLOW_PARALLEL=1` never bypasses a same-qid heartbeat; on
ambiguity inspect heartbeat + argv, return the lease to main, and do not race.

1. **Launch** (§ "Launch") in background; in the **same turn** dispatch the D-orch, log
   `dispatch`/`subtype:"lease-grant"`, and yield. The sub attaches its watcher to the live process and
   owns discovery through its first halt. Ignore main's exit notification unless the sub died.
2. The leaseholder reads verdicts, applies levers, and resumes its phase without a main hop. It returns
   only one `{escalation, receipts}` (types in § "Handling escalations"). It asks main to dispatch any
   Claude subagent.
3. Main handles the escalation; crossing a boundary resumes and re-dispatches the next sub **in the same
   turn**. Clear caps only with `--resume --clear-gate <flag>`, never by editing `state.flags`.
4. A leaseholder that dies without returning the lease → § "Orphan recovery".

**Codex-runtime monitoring:** after granting a lease, wait in one 30-minute event-triggered window; a
tool cap or unrelated wake continues the same deadline. At the deadline check only that the leaseholder
is alive, then open another window. Do not duplicate its watcher or message it routinely. When Codex
main directly owns a process, use the same window with exact-PID/log probes ≥120 s apart.

## Dispatching sub-orchestrators

- **Codex runtime:** every orchestrator-initiated agent call (sub-orchestrators, consults, adjudicators,
  auditors, builders) goes through the managed channel (`spawn_agent`, then
  `followup_task`/`send_message`/`wait_agent`). Never shell-launch `codex exec` from an orchestrator; if
  managed slots are busy, wait or return the skill-defined escalation. Only the TypeScript pipeline
  launches `codex exec` workers through its adapter. Set model/effort explicitly: D math-facing
  orchestration `high`, routine orchestration `medium`.
- **Claude runtime:** dispatch with the Agent tool. Only main dispatches Claude subagents; subs return
  `dispatch-request`.
- **Warm reuse:** `followup_task` (Codex) / `SendMessage` (Claude) restarts an idle sub with its context;
  Codex `send_message` only amends a running turn and never starts a new one. State remains
  `decision_log` + `state.json`.
- **Re-seed:** default at D→F; also on `request-reseed` or orphan. Never respawn a sub mid-phase unless
  it returned the lease.

**Dispatch templates** (fill `<qid>`/`<spec>`/`<bool>`; the sub loads everything else from its skill):

> **D-orch:** You are the CausalSmith research **D-stage orchestrator** for run `<qid>`/`<spec>` and you
> HOLD THE RESUME-LEASE for discovery. Invoke skill `causalsmith-d` and follow it exactly, including its
> re-ground step and lease-return conditions. auto_mode=`<bool>`.

> **F-orch:** identical with **F-stage** / skill `causalsmith-f` / "formalization".

## Orphan recovery

(1) Inspect only this qid: `pgrep -f "causalsmith.ts research.*<qid>"` + heartbeat; let a live mid-run
finish, reap an idle linger (reference § "Liveness and stale processes"). (2) Re-ground from `state.json` and the
`decision_log.ts read` tail. (3) Re-dispatch from that log, grant the lease, log
`command`/`subtype:"lease-reclaim"`.

## Topic selection (no-qid `--propose`)

Dispatch a topic-selection subagent that invokes `causalsmith-topics`. Main owns ≤4 re-steers. On
`ESCALATION`, pick one highest-EV untried lever from its ranked list, warm-continue with accumulated
anti-constraints, and track burned levers; never redo its deep reads or gate. `DONE` → launch its
command. `BLOCKED` → fix tooling, retry the same round. No genuine headroom, or four rounds → hard user
stop even in `--auto`, reporting burned levers, the fallback, and remaining choices. Never instruct
the sub "never ask / fully autonomous" (it fights the bounce point). Never lower tier to manufacture
acceptance. Record the selection summary in the first decision-log entry.

## Handling escalations

Every escalation carries **verbatim receipts** (the reviewer phrase, the `.tex` line). Missing receipts
→ send it back.

| Escalation | By | Action |
|---|---|---|
| `go-no-go` (D0.5 PASS) | D | Decide commit-to-F (auto: decide; else may ask), `--resume` into F1, dispatch an F-orch, re-grant the lease. |
| `request-reseed` | D/F | Respawn a fresh sub for the SAME phase, seeded from the log; re-grant. |
| `dispatch-request` | D/F | Dispatch the Claude subagent, wait, warm-send the result, re-grant. |
| `codex-blocked` | D/F | Hard user stop even in `--auto`: quote the denial, exact command, impact. Harness-level permission is required; once granted, re-grant and re-issue the SAME command. Never accept a hand-proof or weakened-gate workaround. |
| `citation-verification` | D | Obtain lawful verbatim source evidence per node, then from the CausalSmith root: `npx --prefix tools tsx tools/bin/d0_attest_cited_source.ts <qid> <spec> --id <id> --expect-locator <locator> --verbatim <statement> --note <provenance> (--upstream <primary-citation> [--upstream-locator <text>] [--upstream-cite <bibkey>] \| --upstream-none)`. Re-grant D; plain `--resume` re-checks it. Never invent source text. |
| `terminal:tex-claim-wrong` / `terminal:laundering` | D/F | Codex-validity-gate → bank `failed`. |
| `terminal:below-floor` | D | Codex-validity-gate, then surface the achieved tier to the user (never silently lower `--novelty`): bank `downgraded`, or continue to F via `causalsmith research --downgrade-tier <achieved-tier> <qid> <spec>`. |
| `rewind:fix-source` | F | Verify necessity (§ "Cross-boundary rewind"), then dispatch a D-orch to execute it. |
| `cap-block` / `substrate-unbuildable` | D/F | Only main resets caps (exception: the D-1 leaseholder's persisted `--angle-action retry --extra-revisions N` lane). Diagnose the root first: scaffolder drift → `bin/f2_directive.ts`; reviewer wrong → `pipeline-bug`; plan wrong → rewind. `--clear-gate` only after a root change, and log it. Same defect after two resets → validity-gate, then user. |
| `build-substrate` (a.k.a. `substrate-build:study`) | F | The proof needs a lemma that does not exist. Never bank `failed` for this — route by REUSE: generally reusable (a Mathlib-shaped fact any run could want) → `--study` side-run (§ "study"), relay the Causalean path back; specific to this model and of manageable size → dispatch a subagent to build it under the run's own `Helpers/`. Escalate only if it is neither. A study halted at `BUILD_CAP` is out of ROUNDS, not necessarily out of reach — judge the final round's receipt and grant one more window with `--resume --clear-build-cap` when it is close (few sorries, shrinking). If that second window also halts, bank `failed`. |
| `citation-instantiation-overflow` | F | Apply the citation invariant. Source mismatch → correct the source; new reusable infrastructure → build/study; paper-specific residual → prove or correct the headline. F4 must still run. |
| `f5-clean` | F | Verify F4 ran (a this-round `stage 4 … dual-model convergence review completed` line in `pipeline.jsonl` plus one current receipt from each peer in `state.delivery_review_receipts` / `state.cited_review_receipts`; a loop escalation followed by stages 3/3.5/4 `skipped` voids it → send back to re-enter F2.5). Then run S6 for remaining `gated` debt, then CKPT 2 user stop with Lean/API/assumptions/F4/tier receipts and the planned F7 reusable-helper closure. One explicit acceptance authorizes the whole standard post-checkpoint sequence: accepted bank, scoped commit, F7, verification, and final scoped commit; do not ask again between those steps. |
| `reviewer-dispute` | F | Reproduce independently. Reviewer right → comply. Reviewer wrong → `pipeline-bug`: propose a concise GENERAL reviewer-prompt rule, ask the user before editing (hard stop 8), record in `PIPELINE_NOTES.md`, re-enter F2.5/F4. Never instance-exempt a node. Undecidable math → user. |
| `pipeline-bug` | D/F | Fix while stopped (§ "Pipeline-bug fixes"), re-dispatch. |

**Codex-validity-gate** (for `terminal:*` and `cap-block` only): before banking or a user escalation,
consult `gpt-5.6-sol` high (`CAUSALEAN_MODEL_CODEX_CONSULT`) with the raw halt, verbatim receipts, and a
neutral terminal-vs-fixable prompt that states the case to continue. Different load-bearing defects
resolving across rounds = keep going; the same recurring defect, laundering, or a wrong-direction pivot
may stop. A lower tier is not hopelessness — converge and bank `downgraded`. A concrete fix becomes a
dispatch/rewind/root-earned `--clear-gate`, not a bank. Codex cannot override faithfulness. D0.5
hygiene-only rotation while novelty/tier keeps passing is convergence, not terminal.

## Auto mode (`--auto`)

Pass `--auto` on the launch and every `--resume` (it latches `state.auto_mode`) and propagate
`auto_mode=<bool>` into every dispatch. Apply each rule unchanged, but decide yourself and act without
asking; only the "ask/offer/wait" half is overridden.

**Hard stops even in `--auto` — only these eight:**
1. **CKPT 2** — report per-gate and per-core outcomes and wait once for acceptance. Acceptance authorizes
   the standard accepted bank → scoped commit → F7 promotion → verification → final scoped commit
   sequence; do not insert another approval stop within that sequence.
2. **Kernel dead** — the math claim is refuted or unprovable (validity-gate confirmed).
3. **Serious pipeline defect** the run cannot self-resolve.
4. **`codex-blocked`.**
5. **Topic-selection exhaustion.**
6. **Below-floor tier choice.**
7. **Unresolvable reviewer dispute** after independent reproduction.
8. **Editing a STAGE PROMPT** — always ask; present the diagnosis, the exact rule text, and what it would
   now let through. Pipeline CODE fixes are not a stop.

**Not stops:** unfaithful scaffold / statement drift while the note is correct → ordinary F2 rewind
(`bin/f2_directive.ts`, rewind to F1.5/F2.5). Missing substrate or a gate S6 cannot discharge → build
paper-owned infrastructure for headline/headline-support; otherwise the citation rule. A core that won't
close → keep attacking with the substrate built; if it still won't, it is UNDELIVERED content reported
at CKPT 2, never gated.

**UNDELIVERED safeguard.** `delivery_status:"undelivered"` is allowed only for an independently
classified `secondary` theorem or a `cited` node; never for `headline`/`headline-support`, and no
delivered result may depend on it. Keep the node in core/plan/graph, emit no Lean declaration/`@node`,
exclude it from F2.5/F3 obligations, but both F4 reviewers must still independently audit its role
and full reverse closure and agree it is secondary/cited and unconsumed by delivered results. Presentation renders it as a disclosed `remarkv`.

No progress across successive resumes ⇒ terminal. An `⚙ AUTO MODE` banner on a checkpoint ⇒ decide and act.

## Cross-boundary rewind

On `rewind:fix-source` from F: reproduce the Lean↔`.tex` conflict yourself (reference § "Rewind
verification"). False → send it back (restore + fix reviewer/scaffolder is the sub's job). Real → log
`{type:"command",cmd:"rewind-D0",target:<node>,note:"incremental — patch the node + dependents, keep the
sound rest, re-validate"}` and dispatch a D-orch. Never re-derive the whole discovery. Rewind only for a
mathematical defect; every other mechanical error the D-orch fixes in place
(hand-edit `core.json`, then `bin/d0_vc.ts <qid> <spec> commit --note "…"` — no solver round).

## Bank

Always use `bank_entry.ts` (reference § "Bank"). `accepted` only after clean F5 + explicit CKPT 2
approval, and before F7. That one approval also covers the run-scoped acceptance commit and the ensuing
F7 promotion and final scoped commit; proceed continuously without asking again. Other tiers only on a
terminal outcome (hard REJECT, revise-exhausted NO-PASS,
validity-gate-confirmed hopeless topic) — never mid-pipeline. `failed` = math claim wrong;
`downgraded` = sound but not novel. Pass `--reraise-status` from the sub's receipts, `--achieved-tier` on
a below-floor bank, and `--orchestrator-tokens <exact cumulative host total>` when the host exposes it
(never estimate). Fill the README `gap_reasons` (verbatim reviewer phrases) + `proof_attempt_summary`.
After F7, refresh the total with `bin/token_usage.ts --run-dir <bank-dir> --orchestrator-tokens <exact
final total>`. Append a `terminal` decision-log entry.

## S6 — substrate attempt (main-owned; post-F5, before CKPT 2)

A second attempt at genuinely hard minimal `gated` debt after F1–F5 attempted every obligation. Triage
from contribution + downstream graph: attempt only `headline`/`headline-support` gates needed for an
unconditional headline; skip secondary-only and `oeq:`/deliberately-open gates unless the user elects
them, and disclose at CKPT 2. Do not send a source-matched cited theorem to S6; do send every
paper-owned bridge to the normal proof/build path.

Per gate choose a dedicated `gpt-5.6-sol` agent (run-specific) or `--study <slug>` (substantial reusable
primitive). One agent per gate, grouped by difficulty, separate `TMPDIR`/Codex sessions, no worktrees,
coupled import closures serialized. In `--auto` dispatch without asking. Each agent builds a general,
axiom-clean, zero-sorry lemma (leaves first; `lake build <module>` green), then
`causalsmith research --discharge-gate <qid> <spec> <node_id> --lean-name <BuiltLemmaName>` (re-passes
F4→F5). It reports `still-gated` — never guesses or re-gates — when attempts fail, the faithful general
statement is unclear, or discharge needs a theorem-statement change. Main owns the wait: monitor long
`sol` workers, re-seed on context bloat, and take every outcome to CKPT 2.

## F7 — substrate promotion (after an `accepted` bank)

Covered by the same explicit CKPT 2 acceptance as banking; never request a second F7 approval. Main
selects by reusability:
grep each helper for run types (`ParamSpace`, `CumVec`, class defs), ignoring vestigial imports.
Promote as-is if uncoupled or recurring; tag `generalize` when a faithful general object can decouple
(restate over a general ambient, re-import the run version as a specialization); leave coupled one-offs.
Present the `helper → target` list at CKPT 2 when already known. If final dependency inspection refines
the list after acceptance, report the run-derived list as a progress update and proceed without pausing;
ask only when the proposed action materially expands beyond the accepted run's reusable dependency
closure. Then dispatch a fresh bounded agent:

> **F7 promotion agent:** Read `.claude/skills/causalsmith/f7-substrate-promotion.md` and follow it
> exactly. Run `<qid>`/`<spec>`. Promotion SET: `<helper → target Causalean module list>`.

On return, verify yourself: `#print axioms` on the banked flagship unchanged, no new signature binder,
conjuncts intact, full build green, fit (no paper-named duplicate of a Mathlib/Causalean primitive; no
run jargon in shared names), `lint:nl-links` clean. Regression → back to the agent. Record
`reusable_artifacts` in the bank README and a `command` decision-log entry.

## Pipeline-bug fixes (main's job)

- **Read the agent's own I/O first** (`doc/research/_agent_logs/`, `_reviewer_calls.log`, stage
  stdout) and diff EMITTED vs PERSISTED before inferring cause from state or counts.
- **Only a blocking true bug earns a code change:** reproduced behaviour that is stopping or corrupting
  the run in front of you. An audit finding, a latent hazard or a defect you reasoned your way to is
  not one — note it and carry on. If the run proceeds without the change, do not make the change.
- **Every fix must be ROBUST, keep the design AS SIMPLE AS POSSIBLE, and be TOKEN EFFICIENT** — judged
  for the pipeline as a whole, not just the path in front of you. A fix that makes the run halt more
  often, adds a mechanism, or makes the model re-emit more is not a fix.
- **Minimal repair:** the smallest change that closes the reproduced defect — one general rule or one
  existing-boundary check, never a new stage/state field/lane. Ignore what is harmless (strip, do not
  reject), require only what the prompt mandates, and route what the model can correct through the
  existing bounded feedback loop — a hard throw is for corruption the model cannot repair. Code bug →
  fix the TS. Prompt problem → a concise GENERAL rule, user-approved first (hard stop 8). Prompts are
  re-read per dispatch: edit only while the run is stopped.
- Never route accepted mathematics back through an LLM to repair serialization, canonicalization,
  ordering, or store state; the D-orch edits `core.json` and commits it (`bin/d0_vc.ts commit`), or
  resets `main` to a known-good commit (`bin/d0_vc.ts reset`). Re-dispatch D0 only when content,
  authorship, or proof changes.
- **Independent audit before trusting any fix:** dispatch a fresh `gpt-5.6-sol` high read-only JSON
  audit on the changed artifact asking how someone obeying it exactly could still pass a wrong result;
  require per hole the quoted clause, a failing scenario, and a general fix. A not-sound verdict blocks:
  fix and re-audit until sound. Never carry a `false` verdict forward.
- **Recurrence threshold:** 1st occurrence → `CausalSmith/doc/research/PIPELINE_NOTES.md`; promote to a
  prompt/code rule on the 2nd instance or across two qids.

## Recording

`npx --prefix tools tsx tools/bin/decision_log.ts append <qid> <spec> --json '<entry>'`. Main's entry
types: `dispatch` (`{type:"dispatch",from:"main",phase,subtype:"lease-grant",note}`), `command`
(`{type:"command",from:"main",cmd,target,subtype,note}`; `subtype:"lease-reclaim"` on orphan recovery),
`terminal` (`{type:"terminal",from:"main",tier,reraise,why}`). This log + `state.json` is main's only
resumable state; the lease is soft state read from the tail (last `lease-grant`/`lease-reclaim` vs a
lease-return escalation).

## Argument forms

| Form | Effect |
|------|--------|
| *(none, or a bare area/interest)* | No qid to parse: § "Topic selection" first, then launch the form it returns. |
| `<qid> <spec>` | Cold start. |
| `--resume <qid> <spec>` | Resume after a checkpoint or block. |
| `--propose <topic> <qid> <spec>` | Run with D-1 proposal first. |
| `--propose <topic> --novelty <tier> --upgrade <parent_qid>_<parent_spec> --upgrade-axis <axis> <qid> <spec>` | Upgrade a banked parent; `<tier>` ≥ the parent's `banked_novelty_tier` (equal allowed — the delta is enforced by the D0.5 `upgrade_axis` rubric). |
| `--downgrade-tier <tier> <qid> <spec>` | Accept an achieved lower tier after `terminal:below-floor`: lowers the floor, re-passes D0.5, continues per `--auto`. `<tier>` must be strictly below the current floor and ≤ the reviewer-assessed tier. |
| `--angle-action <continue\|switch\|retry\|give-up> <qid> <spec>` | Resolve a persisted D-0.5 checkpoint; `retry --extra-revisions N`; add `--angle-directive <text\|->` to persist a repair. |

Pass-through flags: `--auto`; `--novelty <incremental|subfield|field|flagship>` (D0.5 floor, default
`field`; legacy `relative-to-repo`→`incremental`, `relative-to-literature`→`subfield`); `--upgrade
<parent>` + `--upgrade-axis <computation|estimation|generalization|mechanism>`; `--stop-after <stage>` and
`--from-stage <stage>` (stages `D-1.1`,`D-1.2`,`D-0.5`,`D0`,`D0.5`,`F1`,`F1.5`,`F2`,`F2.5`,`F3`,`F3.5`,`F4`,`F5`);
`--clear-gate <flag>` (resume-only, repeatable; flags `substrate_build_required`,
`scaffold_redirect_cap_hit`, `stage1_rewinds_cap_hit`, `theorem_splits_cap_hit`,
`stage0_budget_exhausted`, `general_review_halt`, `stage_neg1_fallback`, `d0_loop_cap_hit`,
`proof_loop_cap_hit` — the last covers every proof-review-loop budget in
`state.flags.proof_loop_counters`; clearing any cap is main's authority and legitimate only after the
root cause changed); `--proposer <codex|claude>`; `--dry-run` (state-machine
mechanics only — never on a live run: it fast-forwards `stage_completed`). Parsing failure → stop and
report; never invent a qid. Arguments that name no qid are the topic-selection entry above,
not a parsing failure.

## Launch

```bash
cd <AUTOID>/CausalSmith
source tools/scripts/node_env.sh
npx --prefix tools tsx tools/bin/causalsmith.ts research $ARGUMENTS
```

cwd must be the CausalSmith package root; `source tools/scripts/node_env.sh` is mandatory (never
hand-write `nvm use`). Run with `run_in_background: true` (not `... > log 2>&1 &`) and dispatch the
D-orch in the same turn — main does not watch the cold-start→first-halt window. Before launch check only
for a live owner of the SAME qid.

Run dir: `CausalSmith/doc/research/active/<qid>/` — `state.json` + `pipeline.jsonl` at the root,
reviews under `reviews/`, D0 artifacts under `discovery/`, the decision log under
`orchestrator/decision_log.jsonl`.

## After TS exits

After every exit (full run, `--stop-after`, crash): read `state.json` + the LAST `pipeline.jsonl` line
(the checkpoint signal; on a halt it carries `next_step_guidance`). Classify from `stage_completed`
(bare number), `next_action`, `flags.*`, `banked` (reference § "state.json" + recognition table). A halt
is not a clean result — a review-gated stage can dead-end (D-0.5 NO-PASS, D0.5 terminal REJECT) looking
identical to "stopped" until the verdict body is read; a single F1.5/F4 reject is iteration. Route to the
phase sub to read the verdict; bank unrecoverable terminations.

$ARGUMENTS

## `study` — substrate-build side-run

Builds a reusable Causalean module from a plain-English requirement, bypassing D/F. Main launches it
(it is a node process); the F-orch escalates `substrate-build:study` only for a substantial reusable
standard primitive, handing up the `requirement.md` content + slug.

```bash
npx --prefix tools tsx tools/bin/causalsmith.ts study <slug>           # cold start / re-run
npx --prefix tools tsx tools/bin/causalsmith.ts study <slug> --resume  # continue
# halted at BUILD_CAP / COORD_CAP: one more window, only after judging the last round's receipt
npx --prefix tools tsx tools/bin/causalsmith.ts study <slug> --resume --clear-build-cap|--clear-coordinate-cap
```

Run dir `CausalSmith/doc/study/<slug>/`. If `requirement.md` is absent the first run writes a blank
template and exits — fill it and re-run. State only the requirement; do **not** set a `## Target
module`: after review the coordinator searches Causalean, dedups, and chooses the narrowest faithful home.
The loop (scaffolder → fillers → reviewer → coordinator; build ≤10, review→revise ≤3) self-heals. The
placement passes a verify-or-rollback gate (`lake build` → `library_index` → `embed` →
`lint:embeddings` → `doc:gen` → `doc:check`); relay the pass + Causalean path (or failing step) to F.

**Layering invariant — no paper imports in reusable substrate.** Study files may import Mathlib,
Causalean, and the same temporary study tree, never `CausalSmith/*_Research`. If a needed helper exists
only in a paper folder, stop the study, extract/generalize it into the neutral staging tree
`CausalSmith/CausalSmith/Substrate/<Slug>/`, replace the paper copy with a thin re-export or
specialization, then resume. At promotion move the whole dependency closure;
`rg '^import CausalSmith\..*_Research'` over the promoted set must be empty.

## Mathlib helper staging

Mathlib-shaped helpers from F3 land in `CausalSmith/CausalSmith/Mathlib/`. Promotion to
`Causalean/Mathlib/` requires ≥2 independent call sites or a fully general statement, and no
CausalSmith-specific dependencies.
