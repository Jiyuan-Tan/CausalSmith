# Presentation adjudications — eid_crl_coverratio_mmd_genericity / v1 (2026-09-10)

Score trajectory: **6.3 → 6.4 → 6.6** (three referee passes, budget spent).

## Bank edits (graph.json; `.bak` snapshots were removed after the run settled)

### B1. `lean.supporting_decls` added (P1 `lean-coverage` exits)

The P1 Lean-coverage judge named certifying declarations outside each object's mapped
component set. Following the documented exit (map the decls, keep the authored body), these
`supporting_decls` were added; every declaration was verified present in the run's Lean tree.

| node | added |
|---|---|
| `def:model-stratum` | `mechanismC2Coordinates`, `instTopologicalSpaceMechanism`, `StratumPoint` |
| `def:affine-path` | `affinePathExtension`, `embeddedSparseWitness` |
| `def:first-stage-ratio-contract` | `uniformC1RatioEvent` |
| `def:cover-separated-set` | `populationDiscrepancy`, `canonicalObservedWorld` |

The anonymous `instance : TopologicalSpace (Mechanism n G)` at `Basic.lean:63` resolves to
`…EID_CrlCoverratioMmdGenericity.instTopologicalSpaceMechanism` (checked with `exact?` against a
built olean).

### B2. `nl.frozen_body` amendments (statement misrendered its Lean)

- **`def:population-decoder`, `thm:exact-ratio-decoder`** — the ratio graph was displayed as
  `H_D = {j→i : D_ji > 0}`, with no self-edge exclusion. Lean's `observedLawRatioGraph` is
  `fun j i => j ≠ i ∧ 0 < observedLawDiscrepancy U laws j i`, and without the exclusion the
  displayed graph carries self-loops (the own-environment discrepancy `D_ii` is generically
  positive), so no topological order exists. Amended to
  `H_D = {j→i : j ≠ i and D_ji > 0}` in both frozen bodies. Independently raised by the P2 proof
  auditor and by the P5 referee.
- **`def:edge-separated-set`** — the second-moment contrast integrated against `dP^{π(a)}`.
  Lean's `secondMomentContrast W j i` integrates against `W.law j.succ`, i.e. the environment
  **label** `a`; since the paper's convention is `P^e = do(π(e))θ`, `dP^{π(a)}` applied the
  permutation twice. Amended to `dP^{a}`. Raised by the P5 referee.
- **Citation keys** — the frozen bodies cited `vonKugelgen2023`, `Wendong2023`, `Yao2025`, which
  are not the verified pool's keys; repointed to `vonKugelgenEtAl2023UnknownInterventions`,
  `WendongEtAl2023CauCA`, `YaoEtAl2025InvariancePrinciple`.

*Note on where a frozen body lives.* An edit to the rendered body in `p1_cache.json` or to
`formal_layer.tex` is discarded once P1 has frozen the layer onto the graph; `nl.frozen_body` on
the bank node is the authority. One H_D fix was lost this way before being re-applied correctly.

## Bundle adjudications (no bank change)

### P1 `mangled-word` on `thm:exact-ratio-decoder` — lint false positive

Halt: `bare single-letter word "D" in prose`. The "D" is the locator in
`\citet[Corollary~D.1]{Yao2025}`. `lintClarity`'s `noMath` chain strips `\cite…{key}` only when
the brace group follows immediately, so with an optional argument only the control word is
removed, leaving `[Corollary~D.1]{…}` and `~D.` matches the single-letter rule. Confirmed by
running the lint with that one citation removed: 0 findings. Repaired at source with zero
rendering change — the locator is written `Corollary~{D}.1`. Backlog for the pipeline: the
mangled-word strip should reuse the optional-argument-aware pattern the `lean-identifier` strip
already uses.

### P2 ballast gate — three frozen statements acknowledged

`thm:generic-cover-separation`, `thm:simultaneous-confidence-edges` and
`def:sample-split-confidence-graph` are delivered headline results (and the algorithm the
inference theorem certifies); they read as unconsumed only because they are terminal. Recorded in
`ballast_review.json`.

### P1 notation advisory — dependency cycle, and a rendering defect behind it

`synth_11` (the simultaneous MMD radius) opened with `In the setting of \cref{obj:synth_1,…}`
listing every object in the paper, which both read badly and created the
`def:sample-split-confidence-graph ↔ synth_11` cycle. Rewritten to cite `\cref{obj:synth_5}`
(the sample-split experiment), which precedes it. The cycle advisory cleared.

### P1 notation findings — symbols carrying their arguments

`𝒰_{G,s,π}` now carries its feature-map argument and names the Gaussian map; `D_{ji}` is defined
world-indexed as `D_{ji}(W)` with an explicit abbreviation clause; `P^e` carries its mechanism
argument. `synth_29` was rewritten so `ρ_i^τ` is only the Borel retraction onto the realized score
range and the inverse is written `(Λ_i^τ)^{-1}`, resolving the type incoherence the P5 referee
flagged between that definition and `lem:equation-eleven-kernel-factorization`.

### P2 promotion — one granted second round

Round 1 (automatic) promoted `lem:equation-ten-intervention-marginal`,
`lem:equation-ten-fiber-product`, `lem:equation-eleven-kernel-factorization`. The retry still
failed with `[missing-step]` on `lem:analytic-edge-perturbation` (the conditional-independence
cross-product equivalence and causal-minimality stability carried by
`affinePathExtension_eventually_modelStratum`), which genuinely lacked a citable step, so
`--promote-again` was granted. `thm:exact-ratio-decoder`'s residuals were re-render/citation
defects and its proof file was deleted to be re-authored instead.

### P2 proof hand-fixes on `thm:exact-ratio-decoder`

- the relabeling was written `σ = π^{-1}∘π̃`; Lean aligns edges with
  `targetPerm.symm.trans W'.targetPerm`, i.e. `π̃∘π^{-1}` from `G`-labels to `G'`-labels. Corrected.
- the comparison paragraph omitted `FullRnC1NoncoverageClause`; the compact-cube / `C²`-vs-`C¹`
  scope boundary was added.
- the selected-version continuity step now cites `\cref{obj:synth_18}`, which states the selection
  convention it relies on.
- the 26 labelled displays in that proof were unnumbered `\[…\label{…}\]`; converted to
  `equation` environments so the cleveref targets are real.

### P4 LaTeX repairs (mechanical)

`\leanref{sym:F_{ji]}{…}` (a `]` for a `}`) and `d(\zeta_i^\tau_{\#}\mu_i)` (double subscript).
Both repaired at source; `latexmk` then compiled clean locally before re-entry.

### Bibliography

- `references.bib` carried a degraded `@misc` stub for `vonKugelgenEtAl2023UnknownInterventions`
  (author field = the key, title field = the whole citation string) while `references_raw.bib`
  held the correct record. Deleting `references.bib` and re-entering `--from P0` rebuilt it from
  the raw pool with the committed identity fix, restoring that entry and also
  `VariciEtAl2025ScoreBasedCRL`, `AcarturkEtAl2024SampleComplexityCRL`, `Hyvarinen2001/2023`.
- `Sun2024` had a title typo: "Multimodal **Biological** Observations". arXiv:2411.06518 gives
  "Multimodal **Biomedical** Observations" (same authors). Corrected from the right record in both
  bib files.
- `VariciEtAl2025ScoreBasedCRL` (JMLR 26(112):1–90, 2025) was confirmed by hand against the
  arXiv:2402.00849 journal-ref before the pipeline-side normalizer fix landed; the `verifiedby`
  field added at that point was removed once the fix made it unnecessary.

## Unresolved findings (referee budget spent at 6.6)

1. **Manuscript architecture** (raised in all three passes). The conceptual argument is still
   preceded by many bookkeeping definitions — observed-world packaging, totalization conventions,
   fiber products, score-range retractions. Mitigated by an orientation paragraph in the
   introduction that states the two-step logic and points the reader at the decoder and the main
   theorem first, but not by a restructure, which would be an outline-level rewrite.
2. **Decoder totality.** The paper now says explicitly that `𝒟` is a population oracle whose order
   and pruning steps are well posed on the cover-separated set. The referee would prefer the
   displayed definition itself be total (as the Lean implementation is). That is a frozen-statement
   change and was not made.
3. **Fixed-sign stratum.** A substantive discussion of how restrictive the sign condition is —
   whether `s` is known or merely indexes the class, and which mechanisms populate `Θ_{G,s}` — was
   written in revision round 1 and lost when the P0 re-entry re-planned the outline and re-drafted
   that section; the referee re-raised it in the final pass and it was not re-applied.
4. **Sample-complexity comparison.** The related work now gives the verified intervention counts
   for the score-based comparators (one stochastic hard intervention per node under linear
   transformations, two under general transformations) but not the sample-complexity orders of the
   cited linear-CRL work, which could not be confirmed from a primary source in this run.
5. **`Θ_{G,s}` nonemptiness.** Open density is proved relative to a nonempty stratum; the paper
   does not establish nonemptiness in general.
6. **Notation reuse in the limitations section** (`K` for both the evaluation set and a generic
   Hölder domain; the structural conditional-ratio CDF conditioned on `z` in one place and `v` in
   another). Frozen-layer items, left as recorded.

## Pipeline defects encountered (three fixed by the coordinator during the run)

1. `P1 component …instTopologicalSpaceMechanism is not present in the crosswalk, the run
   declaration index, or the library index` — anonymous Lean instances had no name in any source
   index. Fixed on main (`8edf6dfe9`).
2. `P4: bib entry VariciEtAl2025ScoreBasedCRL failed re-verification` — the Turkish dotless `ı` in
   the registry's "Varıcı" was deleted rather than folded to `i`. Fixed on main (`037dc03d2`);
   the same class had earlier caused the degraded `vonKugelgen…` stub.
3. `P3 revision round 1 broke the frozen layer (restored)` — the overclaim reviewer returned
   rewrites identical to the original text except that `\cref{obj:X}` was stripped to `\cref{X}`,
   which the frozen-layer guard then rejected; the halt reproduced verbatim on a plain re-entry.
   Cleared by deleting `gate_cache.json` to force a fresh audit, after which P3 passed. Worth a
   look: the repair path applied a no-op rewrite that can only ever break the layer.
