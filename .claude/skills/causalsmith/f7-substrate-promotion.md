# F7 — substrate promotion recipe

Dispatch payload for the F7 promotion agent (main skill § "F7"). A single bounded task: no lease, no
`state.json`/node-process interaction — edit Lean/JSON, run `lake`/`npm`, report, done.

**Promotion SET** (given at dispatch): `helper → target Causalean module` pairs already selected by main.
Execute the selection; do not re-litigate it. **Stop and report** — never promote anyway — if a helper
is high-coupling / a vestigial-import false positive, or has no faithful statement free of run types.

**Promotion only adds to the library.** You ADD declarations to Causalean — the helper generalized
wherever a faithful general statement exists, otherwise as it stands. You never edit the banked run:
nothing under its Lean directory, and not its module file, changes by a single byte — no declaration
moved, deleted, restated or re-proved, no import rewired. You never change an existing Causalean
declaration. The run keeps its own version of every helper beside the library one.

For EACH helper:

1. **Search Causalean and Mathlib first** (`npm run search -- "<concept>" --scope module`; loogle /
   leansearch / `exact?`). If Mathlib or Causalean already has the declaration, there is nothing to
   promote for this helper — the run already has its own copy; report it and go on. Never mint a
   parallel primitive.
2. **Fit and place it.** State the target layer and import only lower layers: Tactic < Mathlib <
   Graph < Stat/SCM.Model < PO/SCM core < PO/SCM identification < Estimation < Panel/Experimentation <
   ML < Discovery. Merge into an existing topic module by default, by insertion only; create one only
   when none fits, using Mathlib-style mathematical nouns, never a study/run or module-prefix name.
   Under `Causalean/Mathlib/`, use Mathlib directory names and no causal/statistical vocabulary. Match
   the target's notation and granularity (≤600 lines; split before ~900). Name the library declaration for the
   mathematics, in the namespace of the file it lands in.
3. **Generalize where faithful.** The library declaration is new, so its statement is free: state
   it without run-coupled types and give it the weakest statement the existing proof supports — drop
   unused hypotheses and instance arguments, weaken typeclasses to what is used, widen hard-coded
   types/constants the proof treats generically. Never add a compensating hypothesis. If it cannot be
   stated without run types, do not promote it; report. Add the helpers its proof needs along with it
   (the same rules apply to each); Causalean never imports CausalSmith. A new module uses `module`,
   contiguous `public import`s, a `/-! -/` docstring, one blanket `@[expose] public section`
   (def-bearing) or `public section` (theorem-only), and bare declarations; wire it into its directory
   barrel, not the root.
4. **Docstrings** (CLAUDE.md): first paragraph = self-contained NL translation with crosslinks —
   `[phrase](hyp:binder)` on every hypothesis/explicit binder, `[phrase](goal)` on the conclusion (for a
   definition: every explicit parameter, `(goal)` on the defined object, `(step:N)` per given-by clause);
   `/-! -/` module overview.
5. **Curate.** Every theorem-bearing file, including under `Mathlib/`, has 1–3
   `headline_theorems`; choose main results, never routine lemmas. Add `namespace_intros` only for a
   genuinely new namespace path without a roll-up module docstring.
6. **Regenerate:** `lake exe library_index` → `npm run embed:library` + `npm run lint:embeddings` →
   `npm run doc:gen`/`doc:check` → `npm run lint:nl-links` (0 errors).

**Mandatory self-check before reporting** (a report without this evidence is invalid):

- **FULL** `lake build` at the workspace root green, then `lake -d CausalSmith build
  CausalSmith.<Area>.<RUN>_Research` (the run's barrel: the root build does not rebuild the run, and a
  single-module build can replay a stale olean).
- The promotion gate, from `CausalSmith/tools` (`<bank entry dir>` is
  `CausalSmith/doc/research/_bank/accepted/<qid>_<spec>`, absolute or relative to the repository root):

      npm run promotion:invariance -- check --entry <bank entry dir>

  Exit 0 is required; paste its output. Exit 1 prints one line per file or declaration with its next
  step. A run file: restore the run's Lean to its banked state and redo the promotion as a pure
  addition. A run declaration (its file is unchanged): something you added to a module the run imports
  — an instance, notation or simp lemma — changed how it elaborates; move that addition to a module the
  run does not import, or remove it. A library declaration the run's statements use: if you changed it,
  undo that change; if you did not, edit nothing — stop and report. Never proceed past a failed check and
  never touch `promotion_snapshot.json`; an entry without one is not promoted: stop and report.
- `#print axioms` on the banked flagship and on each promoted theorem via `lake env lean` (never
  `lean_verify`/LSP) → the flagship's unchanged.
- Grep the SOURCE of the promoted files for `sorry`/`admit`/stray `axiom`.
- Fit: no existing primitive duplicated; no run jargon in shared names.
- Docstrings + crosslinks on every promoted declaration; any `headline_theorems` entry annotated.

**Report per helper:** promoted path, or the existing declaration that made promotion unnecessary; why
the statement is general; full-build status; the `promotion:invariance check` output; and the
`#print axioms` output — real evidence, not a summary. If any check fails, report and stop; main decides.

**Record:** append the new Causalean paths to the bank README's `reusable_artifacts`.
