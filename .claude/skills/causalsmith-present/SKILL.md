---
name: causalsmith-present
description: CausalSmith P-stage (presentation) sub-orchestrator — drives P0–P6 for an accepted bank entry, producing an arXiv-grade paper bundle, interactive web artifacts, and optional slides. Dispatched by causalsmith/main on `/causalsmith present`; the pipeline owns P0–P6, the orchestrator reviews checkpoints, revises the paper by hand from the referee's findings, and adjudicates any frozen-layer versus Lean disagreement.
---

# causalsmith-present — presentation sub-orchestrator

Input: an **accepted** bank entry `CausalSmith/doc/research/_bank/accepted/<qid>_<spec>/`. Output: the
bundle `CausalSmith/doc/presentation/<qid>_<spec>/` (paper.tex/pdf, presentation_crosswalk.json,
lean_snippets.json, paper_body.html, assumption_table.md, meta.json), rendered by `CausalSmith/site/`.

## Lease

Main dispatches one P-orchestrator per bundle; you hold the resume-lease. You own launches/resumes,
checkpoint reviews (auto_mode → `--auto`: self-approves both checkpoints, keeps every hard halt;
record what you checked), every content
adjudication (frozen layer vs Lean, crosswalk repairs, promotion decisions, cache verdict flips,
authored-source edits, P5 triage), and the referee budget. Self-resume freely.

You never edit pipeline code or prompts, commit/push, run the public export, or edit bank D/F content
outside the documented channels (crosswalk patch, promotion review, frozen-body amendment). Return
the lease with verbatim receipts only for:

- `paper-done` — score trajectory, kept version, adjudications (fixed vs dismissed), files awaiting
  commit, your own clarity verdict.
- `pipeline-bug` — per the Bug-fix contract.
- `cap-block` — a cap reached with unresolved findings; never grant yourself more (exception: the P2
  `--promote-again` decision is yours).
- `user-scope` — a finding needing new mathematics (corollaries, renames, simulation studies).
- `dispatch-request` — you need a subagent. `commit-request` — bundle ready; main owns git.

**Authorship standard:** a conventional paper for the field, not a prose translation of Lean. Lead
with the question, ordinary formulation, intuition, results, literature; Lean is the verification
backend — declaration names and proof engineering belong in the appendix or the interactive layer.
No figures in the paper (no gate audits them); tables and prose carry regime summaries.

## Mechanics

1. From `CausalSmith/tools/` (`source scripts/node_env.sh` first):
   `npx tsx bin/causalsmith.ts present <qid> <spec> [--resume] [--auto] [--dry-run] [--stop-after P0..P5]
   [--from P0..P6] [--promote-again] [--refresh-frozen-bodies]`. `--from P2` reassembles the authored
   sources whenever `front_matter.tex` exists (only a missing file is drafted; delete
   `front_matter.tex` to draft afresh). Run long stages detached (Sharp edges); pre-warm the Lean
   build before P2/P3 (`lake -d CausalSmith build <research modules>`; fetch the Mathlib cache first
   if oleans are missing).
2. Checkpoints (then `--resume`):
   - **P1** (outline + frozen layer + bibliography): resolve every `notation_review.json` advisory
     (edit the note/outline/statement, or accept with a recorded reason; `notation-unresolved` with no
     consuming env needs only an acknowledgement; a dependency-cycle advisory is not a halt). Excise
     note objects that are literature motivation only NOW — P2's ballast gate fails on any frozen
     theorem/lemma nothing consumes unless `ballast_review.json` acknowledges it
     (`{"acknowledged": {"<id>": "<why>"}}`), and post-P5 removal is bundle surgery plus clearing
     `nl.frozen` on the bank nodes.
   - **P2** (full draft): journal shape (contributions + roadmap in front matter, early related work,
     every proof opens `\begin{proof}[Proof of \cref{obj:<id>}]`); spot-read one main-theorem proof;
     review promoted nodes.
3. State `<qid>_<spec>_paper_state.json`: `stage_completed`, `checkpoint_pending`, `revision_round`,
   `hard_gate_failures`, `notes`. Never hand-edit the
   pointer; `--from` re-enters the stage that owes work. Rewind only for authorship / mathematical /
   frozen-layer / plan changes; mechanical failures are repaired in place and the stage re-run.
4. **Revision protocol (fixed).** P5 writes `p5_review.{json,md}` and `p5_revision_routing.md`
   (each finding: fix by hand / escalate / your call) and halts `p5:hand-revision`; nothing revises
   unattended. (1) You root-fix every finding by hand at the level that owns it, before paying any
   downstream stage: outline order or duplicate blocks → `outline.md` (`home_objs:`) and `--from P1`;
   a synthesized definition's rendering → P1; prose → `front_matter.tex`, `sections/*.tex`,
   `proofs/*.tex` and `--from P2` (`paper.tex` is derived, never hand-edit it). Order matters:
   make outline/P1 changes FIRST and re-enter P1, then hand-edit prose and re-enter P2 — a
   `--from P1` revises every section whose objects changed from its prior draft (hand prose is
   carried, not guaranteed: diff after the re-entry), a section whose number shifted starts
   afresh, and `--from P0` re-plans the outline and discards prose wholesale (never rewind to P0
   mid-revision; snapshot the sources before every re-entry). A referee finding
   NEVER changes a Lean-backed environment: if you believe the body misrenders its Lean, record an
   adjudication item naming the declaration — the amendment is the user's decision. (2) Rescore:
   the re-entry runs through P5 and halts again with the new score. (3) A second hand round and
   rescore only if the new review still carries findings you can fix; then stop (Mechanics 5).
   Three referee passes total (the first review and two rescores), yours to enforce — no code cap.
   Adding referee-identified citations is your remit (verified entries, exact titles/DOIs).
5. Done: record what remains unresolved, strip latexmk aux files, `cd CausalSmith/site && npx astro
   build` (bundle integrity gate), run P6 (Mechanics 6), then return `paper-done` + `commit-request`.
6. **P6 slides** (after the final score): `present <qid> <spec> --from P6`. One codex call emits
   `slides.md` (11–17 slides targeted, lint 8–18); formal statements are injected verbatim via
   `@formal <obj_id>`; the lint (theorem coverage, displayed math only as verbatim copies, authors'
   voice, no bare `@formal` slide) gets one retry, then halts. At the checkpoint judge clarity and
   check: figure edges against frozen definitions (read the `.dsl` beside the `.svg`), captions and
   `@informal` headlines claim no more than the audited bodies, every coined term defined before use,
   one idea per slide, every rate/scale verbatim from a catalog body or the notation, every
   Author (Year) matches `references.bib`. Fix by editing `slides.md` / `slides_assets/*.dsl`
   (hand edits are kept; delete `slides.md` to regenerate and discard them); after a `.dsl` edit
   re-render its `.svg` with
   `parseFigureDsl`+`renderFigureSvg` via `npx tsx` — never delete the `.svg`. Figures `@figure
   <kebab-name>: <caption>` (≤2 target, ≤3 lint; schematics only); a missing asset is authored once;
   existing files are never overwritten. Escalate recurring taste defects to main as a general
   `p6_slides.txt` rule.

## Caches and re-entry

Never rerun an audit without a material change. Verdicts are content-keyed: `equivalence_cache.json`
(P1), `proof_audit_cache.json` (P2), `gate_cache.json` (P3), `p1_cache.json` (renders, notation
reviews, synthesis, `synthEnvs`). Reruns re-pay only changed inputs; delete a cache file to force a
fresh audit. Never hand-compute a key; to reseed an adjudicated false positive, flip that obj_id's
`verdict` to `"faithful"` and leave `key` untouched, one explicit edit per entry.

- A proof approval keys on the proof text, its Lean source, the statement it proves, the statements
  it cites by `\cref`, and the notation rows it meets — nothing else. Changing a statement re-judges
  the proofs that cite it; a promoted lemma, an order repair, or a re-rendered uncited statement
  re-judges nothing. Statement approvals key on the declaration's source text, not its line. Rows
  stamped under an older key formula are honoured once and re-stamped (a one-time "render cache
  remains missed" note per proof is that re-stamp).
- P2 artifacts (`sections/`, `proofs/`, `front_matter.tex`) are file-cached — delete a file to
  regenerate it. After amending the frozen layer, sync the env copies inside cached sections (the
  freeze is each block's `body` in `formal_layer.json`, whitespace-insensitive; titles not frozen).
- P1: `outline.md` `home_objs:` is the planned placement (edit it to move objects); `objs:` is the
  resolved layout. A valid outline is reused across re-entries; delete it only to request a fresh
  plan. Promotions must add their nodes to `home_objs` (and `objs`) without disturbing existing
  homes; recover lost homes from the recorded planner output, never by deleting caches or guessing
  from symbol spellings. P1 places definitions/algorithms/assumptions before consumers by graph
  `statement-uses` edges and actual references (ordinary forward result citations are allowed);
  P3/P4 assert the order (`frozen-layer-order`). Render, notation and
  synthesis keys embed prompt fingerprints — never bump versions by hand. A `lean-coverage` halt:
  map the missing certifying declarations in the bank node's `lean.supporting_decls`, keep the
  authored body, `--from P1`; never weaken a statement to fit a partial mapping.
- Synthesis renders a symbol no environment defines: from the Lean declaration when an `@realizes`
  tag or a same-named def-like declaration exists (judged and linked like any Lean-backed env),
  otherwise by the definition writer; a cached prose definition whose symbol the Lean defines is
  re-rendered from the Lean on the next P1.
- P2 keeps existing proof files as candidates; a terminal audit failure keeps its stop receipt until
  a relevant input changes. Repairs are ordered exact text replacements audited in full; an invalid
  patch leaves the candidate untouched.
- P3: exact patches only, checked by the frozen/proof guard; protected edits are skipped, structural
  changes halt. The rubric is advisory; a hard-gate loop that gives up after 2 rounds halts with its
  last patch ON DISK. Do not reassemble an unchanged paper to escape a rubric score.
- Bibliography. P4 re-verifies every CITED entry (Crossref/arXiv/OpenAlex, throttled — run P4s
  sequentially): title, an author family, and year must corroborate; a fabricated/absent id
  hard-fails; a same-title hit by another author halts naming both records. Before paying a P4
  after any bib change, sweep the cited entries offline (`verifyEntry(entry, defaultLookup)` over
  `citedKeys(paper.tex)`). A correct entry no registry indexes under its own identity is confirmed
  BY HAND: check a primary source, add `verifiedby = {<what confirmed it>}` in `references.bib` AND
  `references_raw.bib` (P0 rebuilds the former from the latter and strips the field from model
  output). Never "fix" fields from another work's record; a correct indexed entry that fails is a
  lookup defect → `pipeline-bug`.
- **Stop rule.** A re-entry reproducing the SAME failure after your fix gets one sanctioned
  workaround (Route around before you escalate); if it reproduces again, or two consecutive edits go unhonoured,
  it is a pipeline bug — stop and escalate.

## Route around before you escalate

Fix mechanical errors in place from the worker's own raw output — JSON punctuation, a known path,
a LaTeX/package error, a lint false positive (a locator brace, a cref form), a bib field taken from
the right record — changing only what the syntax needs; re-run the existing checks and record the
original and the repair. A syntax repair never approves mathematical content or link assignments;
never invent missing answers, merge conflicting ones, or weaken a validator — ambiguous intended
content is an unresolved judgment, not a repair. A P3 halt that reproduces verbatim on re-entry →
delete `gate_cache.json` so the gates re-audit fresh; a transient registry or capacity error →
re-enter in place. Resume at the earliest stage that still owes work. Log each workaround with the
exact halt line and report it as a suspected defect in `paper-done`; the run does not stop for it.

## Promotion round (inside P2)

A residual `[missing-step]` proof-audit failure fires ONE promotion round per invocation: an agent
authors the missing Lean-backed helper lemmas as bank nodes, the bank reloads, P1 runs a delta pass,
P2 retries once. Rendering-only residuals never promote (halt for adjudication; delete the
proof file for `<id>` under `proofs/` — its colon is spelled `--` — to re-render). If the retry fails, recover with `--from P1`, never plain
`--resume`; reassemble re-entries never promote. The halt `P2 promotion decision required` hands
you a second round: grant `--promote-again` only when a proof lacks a CITABLE STEP; a rendering
defect (leaked totalization conventions, mis-attributed step, omitted conjunct, symbol shadowing)
needs the proof or the STATEMENT adjudicated — check the statement first.

## Stages

| Stage | Inspect | Failure modes |
|---|---|---|
| P0 | `references.bib`, `references_raw.bib`, `p0_verification.json`, `related_work_brief.md` | drops >40% throw (lookup defect). A re-entry that finds the raw pool and brief re-verifies without re-searching — delete both to refresh |
| P1 | `outline.md`, `formal_layer.{json,tex}`, `notation_review.json`, `equivalence_cache.json` | outline/env validation throws; residual statement drift halts |
| P2 | `sections/*.tex`, `proofs/*.tex`, `front_matter.tex`, `paper.tex`, `proof_audit_cache.json` | frozen-drift lint (fix the cached artifact; bare obj ids and dropped `obj:` prefixes are repaired at assembly, never linted); `isolated-lemma`; residual proof unfaithfulness; unrenderable proofs listed in one halt. Frozen-block placement slips are repaired mechanically at P1's position and noted (`P2: section …`); a dangling proof `\cref{obj:…}` is repaired or sent to the writer, still dangling ⇒ halt. Framing and assumption-numbering advisories land in the state notes |
| P3 | `logs/reviews.jsonl`, `gate_cache.json` | overclaim, citation support (`citation-unverifiable` advisory, `unsupported` blocks), rubric (advisory); style is an advisory note, never a halt |
| P4 | bundle files, `paper.pdf`, `lean_snippets.json` | compile errors halt for hand repair (no model retry); bib re-verification; undocumented Lean decls block the emit (docstrings are authored at F5 — add them, then `--from P4`). Style advisories (`P4 advisory (…)` in the state notes) are input to your hand round, never a halt |
| P5 | `p5_review.{json,md}` | Mechanics 4 |
| P6 | `slides.md`, `slides_cache.json` | lint after one retry; refused until P5 is settled |

## Isolated-lemma halt

P2 assembly and P4 hard-fail on any `lemmav` no proof body cites. Find the decl in
`presentation_crosswalk.json`, grep the run's Lean tree for consumers: (a) consumers exist → add
`\cref{obj:<lemma>}` in each consuming proof source at the right step; (b) none → remove the lemma
(section block, `outline.md`, `formal_layer.json`, `proofs/*.tex` + cache entry) and flag the bank
node; (c) genuinely standalone → reclassify to a proposition (rare, justify). Then `--from P2`.

## Equivalence adjudication

The P1 judge checks each env body against its crosswalk-named Lean decl (conclusions match; no
load-bearing Lean hypothesis omitted or invented, up to packaging and incidental regularity); drift
goes back to the renderer inside the render loop. The P2 proof judge does the same for proofs, with
tagged defects `[missing-step]`, `[citation]`, `[rendering]` re-rendered for ≤2 rounds. The pipeline never repairs a mapping; on a
residual, diagnose: (1) wrong crosswalk mapping — find the real decl (name-affine `private lemma`s
inside T-blocks are common), patch the bank's `*_crosswalk_full.json` (keep a `.bak`); (2) note
overstates Lean — amend the frozen body to the Lean-true form, sync cached sections, `--from P1`,
never edit the accepted note; (3) auditor miscalibration — a general prompt rule, via main.

Frozen bodies (`nl.frozen_body`) enter verbatim and stay under the current judge; `--from P1
--refresh-frozen-bodies` requests refreshed wording. Hand-authoring a frozen body: never assert a
named conclusion by bare name (unfold it or `\cref` the env), never display pure logical packaging,
check occurrence counts around every replacement. An env bundling several adjacent Lean decls is a
recurring false positive — verify decl-by-decl, then reseed. Record every adjudication in
`_causalsmith_present_adjudication_<date>.md` in the bank entry dir plus a state note; list bank
edits separately from pipeline edits in `commit-request`; sweep the prose around amended envs.

## Bug-fix contract

A `pipeline-bug` is a halt you cannot clear without touching a frozen body, a proof, or pipeline
code: a GENUINE, BLOCKING, reproduced defect — wrong output, corrupted content, a gate passing what
it should catch. An audit finding or a latent hazard is a backlog note. The escalation names the
exact error, a minimal repro, (a) the INPUT that was wrong (a model verdict, a heuristic match,
planner metadata) and (b) the code that trusted it. Main's fix REMOVES or DETERMINIZES a mechanism,
never adds one — a counter, ledger, hint, suppression branch or `throw` on the same untrusted input
is the next incident; it is proven by replay on the failing bundle AND one that passed, verified with
`npx vitest run test/presentation_` + `npx tsc --noEmit`, and lands one commit per fix with an
independent audit PASS before commit or live use. Prompt lessons land only on a failure class's
second occurrence; three fixes in one function in a week ⇒ a redesign note first.

## Sharp edges

- Run logs to a durable directory outside `/tmp` (a per-job or tmpfs `/tmp` loses them). Detach
  long stages (`setsid nohup … >log 2>&1 & echo $! > log.pid`) with a separate waiter on that PID.
  `setsid` re-forks: resolve the real sid from `ps -eo pid,sid` and key liveness/kill on
  `pgrep -s <sid>` or recorded PIDs, always excluding `$$`; never `pkill -f`/`pgrep -f` a pattern
  your own command line contains (a stray `codex exec` is usually another agent's worker).
- P2 emits no per-item progress; a live node with accumulating CPU and an empty log is normal.
- The run lock is a DIRECTORY beside the heartbeat in the bundle's `logs/`; it self-clears as stale
  after 30 min. Re-enter sooner only after `kill -0` proves the recorded PID dead, then `rmdir`.
- Before a reassembly (P3's hard-gate repair patches sources in place), snapshot `sections/`,
  `front_matter.tex`, `formal_layer.*`, the state JSON.
- After ANY Lean or statement edit, `--from P2`; if the edit is outside the mapped
  declaration's own source (a cited helper, an unfolded definition), delete that obj's
  `proof_audit_cache.json` entry first.
- Prompt fingerprints key only P1 (`p1_touchup`, `p1_render_from_lean`, `p1_notation_check`,
  `p1_synthesize_definition`), P2 (`p2_proof`, `proof_audit`), P3 (`p3_rubric`), P6 (`p6_slides`).
  Editing one of those while a run is live re-keys every in-flight bundle; other prompts take effect
  on the next call.
- `present` deliberately does not import `src/cli.ts`; keep it that way.
