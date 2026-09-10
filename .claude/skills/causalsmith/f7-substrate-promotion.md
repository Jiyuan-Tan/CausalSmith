# F7 — substrate promotion recipe

Dispatch payload for the F7 promotion agent (main skill § "F7"). A single bounded task: no lease, no
`state.json`/node-process interaction — edit Lean/JSON, run `lake`/`npm`, report, done.

**Promotion SET** (given at dispatch): `helper → target Causalean module` pairs already selected by main.
Execute the selection; do not re-litigate it. A `generalize` tag means restate the lemma over a general
ambient and re-import the run's version as a specialization. **Stop and report** — never promote
anyway — if a helper is high-coupling / a vestigial-import false positive, or a `generalize` pair has no
faithful general form.

For EACH helper:

1. **Search Causalean and Mathlib first** (`npm run search -- "<concept>" --scope module`; loogle /
   leansearch / `exact?`). If the concept exists, state the result in terms of it; never mint a
   paper-named parallel primitive.
2. **Fit.** Place under the narrowest relevant domain (`Mathlib/`, `Stat/`, `SCM/`, `PO/`,
   `Estimation/`, …), creating a topic module only when none fits. Match the target's naming/notation
   (no run jargon), generality, and granularity (≤600 lines; split before ~900). Strip run-coupled
   types; if the statement cannot be stated without them, stop and report. Promote the weakest statement
   the existing proof already supports: drop unused hypotheses and instance arguments, weaken typeclasses
   to what is used, widen hard-coded types/constants the proof treats generically. Never add a
   compensating hypothesis.
3. **Move** statement + proof into the target; rewire CausalSmith to re-import it and delete the local
   copy. Causalean never imports CausalSmith.
4. **Docstrings** (CLAUDE.md): first paragraph = self-contained NL translation with crosslinks —
   `[phrase](hyp:binder)` on every hypothesis/explicit binder, `[phrase](goal)` on the conclusion (for a
   definition: every explicit parameter, `(goal)` on the defined object, `(step:N)` per given-by clause);
   `/-! -/` module overview.
5. **Curate.** Add every MAIN result (identification / estimand characterization / paper-named
   decomposition / asymptotic normality, rate, optimality, efficiency / sharp bound) to
   `headline_theorems` in `doc/library_review/<Area>.json`; leave supporting lemmas uncurated. For a
   module with no sidecar coverage add a one-line `namespace_intros["<Path>"]` (or `intro` for a new
   top-level area).
6. **Regenerate:** `lake exe library_index` → `npm run embed:library` + `npm run lint:embeddings` →
   `npm run doc:gen`/`doc:check` → `npm run lint:nl-links` (0 errors).

**Mandatory self-check before reporting** (a report without this evidence is invalid). For the banked
flagship theorem:

- **FULL** `lake build` green (a targeted build can replay a stale olean).
- `#print axioms` on the flagship via `lake env lean` (never `lean_verify`/LSP) → unchanged.
- Signature unchanged (no new binder), conjuncts intact.
- Grep the SOURCE for `sorry`/`admit`/stray `axiom`.
- Fit: existing primitive reused or the new one justified; no run jargon in shared names.
- Docstrings + crosslinks on every promoted declaration; any `headline_theorems` entry annotated.

**Report per helper:** promoted path, full-build status, the `#print axioms` output — real evidence, not
a summary. If any check fails, do not weaken the banked flagship: report and stop; main decides.

**Record:** append the new Causalean paths to the bank README's `reusable_artifacts`.
