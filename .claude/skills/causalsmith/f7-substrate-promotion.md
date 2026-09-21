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
   leansearch / `exact?`). A declaration Mathlib already has is reuse, not promotion; never mint a
   parallel primitive.
2. **Fit and place.** State the target layer and import only lower layers: Tactic < Mathlib < Graph <
   Stat/SCM.Model < PO/SCM core < PO/SCM identification < Estimation < Panel/Experimentation < ML <
   Discovery. Merge into an existing topic module by default; create one only when none fits, using
   Mathlib-style mathematical nouns, never a study/run or module-prefix name. Under
   `Causalean/Mathlib/`, use Mathlib directory names and no causal/statistical vocabulary. Match the
   target's notation and granularity (≤600 lines; split before ~900). Strip run-coupled types; if the
   statement cannot be stated without them, leave it in the run's `Helpers/` and report. Promote the
   weakest statement the existing proof already supports: drop unused hypotheses and instance arguments,
   weaken typeclasses to what is used, widen hard-coded types/constants the proof treats generically.
   Never add a compensating hypothesis.
3. **Move** statement + proof into the target; rewire CausalSmith to re-import it and delete the local
   copy. Causalean never imports CausalSmith. A new module uses `module`, contiguous `public import`s,
   a `/-! -/` docstring, one blanket `@[expose] public section` (def-bearing) or `public section`
   (theorem-only), and bare declarations; wire it into its directory barrel, not the root.
4. **Docstrings** (CLAUDE.md): first paragraph = self-contained NL translation with crosslinks —
   `[phrase](hyp:binder)` on every hypothesis/explicit binder, `[phrase](goal)` on the conclusion (for a
   definition: every explicit parameter, `(goal)` on the defined object, `(step:N)` per given-by clause);
   `/-! -/` module overview.
5. **Curate.** Every theorem-bearing file, including under `Mathlib/`, has 1–3
   `headline_theorems`; choose main results, never routine lemmas. Add `namespace_intros` only for a
   genuinely new namespace path without a roll-up module docstring.
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

**Report per helper:** promoted path; which existing module/run reuses it, or why it is general; full-build
status; and the `#print axioms` output — real evidence, not a summary. If any check fails, do not weaken
the banked flagship: report and stop; main decides.

**Record:** append the new Causalean paths to the bank README's `reusable_artifacts`.
