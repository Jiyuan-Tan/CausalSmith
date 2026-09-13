# Presentation adjudication — stat_proxy_effectlaw_eigencollision_frontier / v1 (2026-09-09)

P5 referee trajectory 5.8 → 5.3 → **6.4** (`major_revision`). The items below were raised by the
referee and are NOT repaired in the manuscript: each would require changing a Lean-backed frozen
environment, removing a Lean-backed bank node, or new research. Per the standing rule, a Lean-backed
environment is never changed on a referee finding; the paper clarifies these in prose only.

## 1. `raw-valid-quotient-typing` (major) — frozen body vs Lean carrier

**Referee.** The environment "Atomic law coordinates" denotes an unrestricted real coordinate
container by `\mathcal P_{\le k}([-L_\tau,L_\tau])`, although its weights need not be nonnegative or
sum to one and its locations need not lie in the displayed interval; later probability-law and
confidence-set statements reuse that notation as if it denoted valid laws.

**Finding is correct, and it is a rendering mismatch against the mapped declaration** — not a Lean
design flaw. `Helpers/AtomicLaw.lean` already separates the three levels under distinct names:

| Lean | line | role |
|---|---|---|
| `structure AtomicLaw (k) (radius)` | 18 | raw pair of coordinate vectors, unconstrained |
| `def Valid (ν)` | 38 | simplex + support constraints |
| `abbrev ProbabilityLaw := {ν : AtomicLaw // Valid ν}` | 104 | "the actual carrier of at-most-`k` probability laws" |
| `def LawModulo := Quotient (probabilityLawSetoid …)` | 201 | quotient by `toMeasure` |

**Environment.** `def:atomic-law-class`, `status: matched`,
decl `CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw`, file `Helpers/AtomicLaw.lean`.
**Carrier the Lean actually uses: `AtomicLaw` (raw).** The paper gives it the notation that belongs
to `ProbabilityLaw` (valid).

Blocks using the `\mathcal P` notation, with mapped declaration and carrier:

| block | status | mapped decl | carrier |
|---|---|---|---|
| `def:atomic-law-class` | matched | `AtomicLaw` | **raw** — the mismatch |
| `def:summary-space-repair` | matched | `summaryRepair` | **quotient** (returns `AtomicLaw.LawModulo`) |
| `thm:gap-free-positive-measure-modulus` | matched | `gap_free_positive_measure_modulus` | **quotient** (`LawModulo.wass1` of `quotientLaw`) |
| `def:summary-closure` | matched | `summaryClosureData` | via `SummaryClosureData` — unresolved |
| `thm:collision-uniform-root-n` | matched | `collision_uniform_root_n` | via `LatticeEstimator`/`SummaryRepairData` — unresolved |
| `def:wasserstein-confidence-set` | matched | `confidenceSets` | via `ConfidenceSetData` — unresolved |
| `thm:honest-root-n-confidence` | matched | `honest_root_n_confidence` | via the same wrappers — unresolved |
| `synth_21`, `synth_26` | presentation-synthesized | — | no Lean |

**Recommended amendment (needs authorisation).** Reserve `\mathcal P_{\le k}([-L_\tau,L_\tau])` for
`ProbabilityLaw`, give the raw structure its own symbol (e.g. `\mathcal A_k([-L_\tau,L_\tau])`) and
keep a third symbol for `LawModulo`, then re-render each block above against the carrier its own
declaration uses. Note `AtomicLaw.wass1` (line 359) is defined on the RAW carrier, so the paper's use
of `W_1` before validity is faithful and must not be "fixed". The four unresolved rows need
`SummaryClosureData`, `ConfidenceSetData` and `LatticeEstimator` unfolded before amendment.

**Interim mitigation in the manuscript (prose only).** A paragraph after `def:atomic-law-class`
names the three levels, states which objects live at which level, and explains that `\nu_\xi` is the
bridge and that `W_1` compares laws through it.

## 2. `oracle-contaminated-cluster-algorithm` (major) — frozen body

**Referee.** The cluster-report algorithm reads as data-computable while its own text says it is
"computed from `\widehat S_n`, `S(P)`, …" and its construction includes `E_P`, `K_C(P)`,
`\Delta_C(P)` — unknown population quantities.

**Environment.** `def:cluster-report` (frozen, Lean-backed). Splitting it into a sample-only
reporting algorithm plus separate validation definitions is a frozen-layer amendment and is NOT made.

**Recommended amendment.** Split the Lean definition into the sample-computable report and the
validity data, then re-render both environments from the split declarations.

**Interim mitigation (prose only).** The confidence section and front matter state that the
data-facing report uses the empirical lattice law, supplied constants and the algorithmic confidence
set, and that `K_C(P)` and `\Delta_C(P)` are the validity quantities used to state coverage and width.

## 3. `setup-dependency-order` (major) — structural, P1-owned

The Setup section leads with synthesized definitions (thresholded inverses, transport plans,
endpoint feasibility, candidate counts, matrix actions, lattice objectives) before the observed
record, model class, summary and estimand. Cause: `outline.md` `home_objs:` is ALREADY in dependency
order; the clutter comes from P1-placed synthesized definitions, which do not appear in `home_objs`.
Nine Setup synths have zero `\cref` consumers: `synth_8, synth_19, synth_21, synth_24, synth_29,
synth_33, synth_34, synth_7, synth_9` (plus `synth_15`, a duplicate Kullback–Leibler definition in the
lower-bound section, also with zero consumers). Removing a consumer-less synth is outline-only and
safe (`validateOutline` exempts synth ids); a synth whose SYMBOL is still used by another body must
stay — `synth_8`'s `(\cdot)^\dagger_{\ge s_0/2}` is used by `synth_33`, `synth_37` and
`lem:moore-penrose-product-cancellation`, so it is not removable on the cref count alone.
Not performed this session.

The referee also cites duplicate definitions. `synth_15` (KL) is presentation-synthesized with zero
consumers and is removable. `def:empirical-summary-primitives` is Lean-backed
(`empSummary`, `Basic.lean`, `status: matched`, 3 citations) and duplicates `def:empirical-summary`,
whose body is mathematically identical and strictly more complete (it adds the zero-matrix /
total-Borel clause). Removing it requires bank-node surgery: dropping it from `outline.md` alone makes
`validateOutline` (`p1_plan.ts:117-120`) report "placed 0 times", which fails validation and triggers
a fresh plan, discarding every curated home. **User-scope.**

## 4. `missing-numerical-demonstration` (minor, `simulation`) — user-scope

The referee asks for a reproducible two-class simulation reporting Wasserstein error, coverage,
diameter, component merges, mass-interval widths, candidate counts and runtime. This is new work
outside presentation rewriting. **User-scope, not performed.** The manuscript instead carries a
deterministic worked example derived from `def:two-class-witness` (effects `0.25 ∓ ε`, masses
`0.4/0.6`, gap `2ε`, `W_1(\nu_\varepsilon,\nu_0)=\varepsilon`), which the referee correctly
characterises as a reading guide rather than an evaluation.

## 5. `stale-verification-metadata` (major) — recurring, pipeline-shaped

Appendix C records commit `e8453d0e3f6a7dd3f8fe166f2ba0c12c0dd50678`; `verification_contract.json`
now records `89624484c86e86e2c4e2348f09f234a6aced1cf9`, because P4 re-pins the contract on each run
while the appendix carries a hand-written hash. Any hand-written commit id goes stale whenever HEAD
advances between runs. The referee's second claim — that no `% lean:` markers appear — is inaccurate
with respect to the sources: there are 260 in `proofs/*.tex` and 261 in `paper.tex`. They are LaTeX
comments, so they are invisible in the compiled PDF a referee reads. Not repaired this session.

## Not adjudication items — repaired by hand in the authored sources

`latent-class-effect-estimand`, `known-conditioning-inputs`, `two-class-sharpness-scope`,
`sharp-set-terminology`, `non-cleveref-cross-references`, `external-dependency-disclosure`,
`cluster-radius-factor`, `verification-sentence-repetition`, `confidence-inversion-attribution`,
`closest-rate-positioning` / `quantitative-competitor-positioning` (comparison table),
`worked-collision-example`.

## Bank edits

None. No bank node was added, removed or amended; no frozen body was changed (126/126 verified
byte-faithful); 40 of 41 proof files are byte-identical to the pre-session snapshot, the 41st a
`\cref` tidy in `lem:witness-observed-arm-mass` with its five `% lean:` markers intact.
