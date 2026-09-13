# P-stage adjudication — 2026-09-09 (hand revision round, referee 6.6)

Operator-directed single round of HAND revision of `p5_review.{json,md}` (6.6, major_revision,
11 findings, 4 major), followed by ONE rescore. No automatic reviser pass was used on this bundle.

## 1. Structure finding (major) — diagnosis and root fix

Referee: "Setup and assumptions — the logical order is inverted and substantially duplicated."

Plain diagnosis: the Setup section opened with nine machine-synthesized definitions, four of which
nothing in the paper ever used again, and those four dragged four more to the front with them. The
result was that the causal risk, the dense Poisson kernel and the lower-bound machinery were printed
before the observed model they are built from, and the dense/Jackson objects were then defined a
second time in the appendices.

Mechanism (this is NOT planned placement — `home_objs` cannot move a synth):
`tools/src/presentation/p1_order.ts:73-89` (`insertSynths`) places each synthesized definition
immediately before the FIRST environment that uses one of its registered symbols, and a synth that
no environment visibly uses is spliced at index 0. Two consequences produced the referee's finding:

- Four synths had no user anywhere in the paper (their symbol occurs only inside their own body):
  `synth_8` (`\operatorname{Obs}_{n,d}`, dense Poisson observation kernel), `synth_10`
  (`\operatorname{DenseMean}_{n,d,\epsilon}`), `synth_17` (`\mathsf J_{\epsilon,K,Q_x}`),
  `synth_19` (`\mathrm{Mean}_{j,n,d}^{\mathrm{dense}}`). All four restate content already carried by
  `def:dense-moment-matching-construction` (Lean-backed) or by `synth_20`. They were removed from
  `p1_cache.json` `synthEnvs` (backup: `p1_cache.json.bak-20260909`); no environment, prose passage
  or proof `\cref`s any of them (verified before removal).
- Because a provider is inserted before its consumer, the four consumer-less synths pulled
  `synth_15`, `synth_16`, `synth_18` to the head of the paper as well. With the four removed, those
  three resolved to their proper homes with no further action.
- `synth_4` (Causal minimax risk) had no matching user only because its registered symbol was the
  fully decorated `\mathfrak R^{\mathrm{causal}}_{n,d,\epsilon}` while the consuming theorem writes
  `\mathfrak R^{\mathrm{causal}}_{n,d_n,\epsilon}`. The family STEM
  `\mathfrak R^{\mathrm{causal}}` was ADDED to its `symbols` list (the decorated spelling is kept, so
  the notation reviewer's request stays covered). It now lands immediately before
  `thm:consistency-and-parametric-boundaries`, its only consumer.

Resolved order after `--from P1` (`outline.md` `objs:`): Setup now runs assumptions → observed
margin → observed model class → target → minimax risk → causal class → cone → global extension →
oracle value → identification; the dense-prior, likelihood-tail and Poisson-risk objects moved into
the moment-matching appendix; the Jackson coordinate set moved into Main results.

Backlog note (not escalated as a bug — the pipeline gave a way to continue): a synthesized
definition whose symbol nothing matches is silently promoted to the FIRST position in the paper,
and it takes its providers with it. A symbol-match miss caused by decoration (`d` vs `d_n`) is
therefore indistinguishable, at the reader's end, from "this definition belongs first".

## 2. Statement findings — adjudication items (no Lean-backed body was changed)

- **`def:minimax-risk` (Lean: `CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.minimaxRisk`,
  `Basic.lean`).** The displayed body writes the loss expectation as `E_{\mathbb P}[\{\widehat
  V(O_1,\ldots,O_n)-\Psi(\mathbb P)\}^2]` although the estimator consumes `n` observations. The Lean
  is unambiguous: `observedRisk` is `Causalean.Stat.sqRisk (productLaw P.1 n) …`, the `n`-fold
  product law. RECOMMENDED AMENDMENT (user's decision): write `E_{\mathbb P^{\otimes n}}`.
  Handled in prose only for this round.
- **`prop:parent-reduction` (Lean: `…parent_reduction`, `TParentReduction.lean`), bullet titled
  "Matched frontier".** The bullet displays the predecessor's NONMATCHING bracket
  (`\sqrt d/n + d/[n\log(en)]` below, `Cd/n` above). RECOMMENDED AMENDMENT (user's decision):
  rename the clause "Predecessor bracket implied by the matched frontier", and consider retitling
  the proposition "Comparison with the predecessor bounds". Both live inside a Lean-backed
  environment body/title, so neither was changed; the discussion prose now states explicitly that
  the clause is a consequence of the matched frontier and that its two bounds do not meet.
- **Crosswalk gap (informational).** A Lean declaration
  `…DiscreteOptimalValueMinimaxMatched.causalMinimaxRisk` exists in `Basic.lean` and is exactly what
  the presentation-synthesized `synth_4` renders. It carries no `@realizes` tag, so the pipeline
  synthesized a prose definition instead of rendering from Lean. Adding the tag would move this
  definition into the Lean-backed group.

## 3. Presentation-synthesized bodies amended (no Lean declaration attached)

- `synth_4` (Causal minimax risk): expectation now written under `\operatorname{Obs}(P)^{\otimes n}`,
  with the product law named in words. This is the Lean-true form (`causalRisk` uses
  `productLaw (observedMarginal Q.1) n`).
- `synth_3` (Fixed-law squared risk): expectation now written under `\mathbb P^{\otimes n}`, with
  the product law named in words, so the fixed-law and causal risks use one visible convention.

## 4. P2 proof-audit halt during the restructure re-entry

`--from P1` re-ran P2 in DRAFT mode, which re-rendered five proofs whose render key had moved with
the layer, and two of the fresh renders were judged unfaithful, producing the halt
`P2 promotion decision required` (3 promotion rounds already spent). The same halt is the last
recorded state note from 2026-09-08, i.e. it is a standing condition of this bundle rather than a
regression introduced here; the 2026-09-08 orchestrator passed it by re-entering with `--from P2`,
which never promotes.

Resolution taken, per the skill's "check the statement first / rendering defects never promote":
`--promote-again` was NOT granted (only one of the three issues was `[missing-step]`, and a fourth
promotion round would grow the frozen layer again immediately before the final rescore). Instead the
two proofs were restored to the exact text that the judge had previously certified faithful and that
the referee scored, recovered verbatim from the untouched 2026-09-08 `paper.tex`:

- `proofs/lem:centered-factorial-pilot-control.tex` — restored unchanged.
- `proofs/thm:jackson-factorial-upper.tex` — restored, plus one hand fix of the defect the judge
  named: the Poisson prefix count written `\omega` in Step 5 shadowed the notation table's
  coordinate index `\omega \in \mathcal J`. It is now written `M`, the symbol the notation table
  already assigns to the auxiliary Poisson inclusion count `M \sim \operatorname{Pois}(n/4)`
  (11 occurrences, all the same object).

Note for the record: the `\omega` shadowing was present in the previously CERTIFIED text too and had
been passed by the judge several times; the fresh judgement that surfaced it is a re-draw, not a new
defect. The superseded fresh renders are kept at `<tmp>/newproofs/` for this session only.

## 5. Prose findings fixed by hand (authored sources only; `paper.tex` never edited)

| Referee finding | Where fixed |
|---|---|
| major·prose — footnote/verification-appendix overclaim | `sections/07_appendix_verification_note.tex`, rewritten: scope split into 40 Lean-backed environments (incl. every theorem/proposition/lemma) and 11 presentation-level definitions listed by name; artifact directory, commit `603f7dc86a4e2a3229b27f104bedc7ca63e062a6`, Lean toolchain `v4.33.0`, Mathlib rev `db584cd6…`, build command; sorry/axiom status as recorded by the bank's F5 receipts and re-checked by source grep; the two conditional published inputs isolated in their own subsection. The author `\thanks` footnote itself is emitted by the pipeline (`tools/src/presentation/stages/p2_draft.ts:750`) and is not an authored source, so the appendix was made true to the footnote instead. |
| major·citation — quantitative engagement with competitors | `sections/01_related_work.tex`, last three paragraphs rewritten by hand from `related_work_brief.md` using only existing verified keys: Zeng et al. target/rates (`d²/n²+1/n`, `d²/{n² log² n}+1/n`, structured `d/n²+1/n`) against this paper's `min{1, d/[n log(ed)]}`; Jiao–Han–Weissman's own estimator-and-converse result separated from the single ingredient inherited here, with the three features (unknown arm denominators, unequal fixed-overlap propensities, grouped four-atom cells) requiring new work. No bib entry added. |
| minor·prose — limitations scope | `sections/04_discussion_and_limitations.tex`, new opening paragraph of "Limitations and future work": binary treatment, binary outcome, finite alphabet, fixed `ε` with `ε`-dependent constants, scalar target under squared loss, two fixed arms; then vanishing overlap, growing arm count, broader outcome/covariate models, uniform confidence procedures as outside directions. |
| minor·statement — "Matched frontier" bullet | prose clarification in `sections/04_…` (see §2 for the adjudication item). |
| minor·prose — "constructive"/"explicit" estimator | `front_matter.tex`: "constructive" replaced by "written out in closed form", plus an explicit statement that the estimator is a rate-achieving decision-theoretic construction and that no computational-cost claim is made. |
| minor·prose — "each cell has enough information" sentence | the sentence is gone: `sections/03_main_results.tex` was re-drafted under the corrected order and no longer contains it (nor "constructive"). |
| minor·prose — contrasts with absent objects | `front_matter.tex` ("welfare level achieved by the unrestricted cellwise oracle assignment, the benchmark against which any learned rule is measured"), `sections/01_related_work.tex`, `sections/04_…` (two passages). No `rather than` construction remains in any assembled authored source. |
| minor·structure — title breadth | USER-SCOPE. Not retitled. Referee's suggestion on record: qualify with binary treatment and fixed overlap, or add a subtitle. |
| nit·prose — terminology/typography | "Jackson--factorial"/"Jackson-factorial" normalized to the frozen layer's spelling "Jackson factorial" throughout every authored source. RESIDUAL, recorded not fixed: three Lean-backed frozen bodies spell it "Jackson factorial" while two environment TITLES still read "Jackson-factorial"; titles are restored from the layer by `normalizeFrozenEnvs`, so a section-file edit cannot change them. The prose "L1" the referee flagged occurs only in the environment title "Equal-propensity L1 reduction" (same constraint) and inside bib keys/macro names. |

## 6. Files touched

Bundle (`doc/presentation/stat_discrete_optimal_value_minimax_matched_jackson_factorial/`):
`p1_cache.json` (+ `.bak-20260909`), `outline.md` (+ `.bak-20260909`, `objs:` lines rewritten by P1),
`formal_layer.{json,tex}`, `sections/{01,02,03,04,05,06,07}*.tex`, `front_matter.tex`,
`proofs/{thm:jackson-factorial-upper,lem:centered-factorial-pilot-control}.tex`,
`proof_audit_cache.json`, `notation_review.json`, `equivalence_cache.json`, state JSON.
Bank: this file only. No pipeline code and no prompt file was edited. Nothing was committed.

## 7. Halts during the rescore entry, and their resolutions

1. **`P2 promotion decision required` (during `--from P1`).** Resolved without a fourth promotion round
   — see §4. Not escalated: the skill gave a documented way to continue.
2. **`P4: bib entry JiaoHanWeissman2018L1 failed re-verification: title does not match external
   record`.** The entry is CORRECT. The Crossref record for DOI `10.1109/TIT.2018.2846245` returns
   the title as
   `Minimax Estimation of the &lt;inline-formula&gt; &lt;tex-math notation="LaTeX"&gt;$L_{1}$ &lt;/tex-math&gt; &lt;/inline-formula&gt; Distance`
   — IEEE's escaped inline-formula markup, which the title normalizer does not strip, so a plain-text
   comparison can never match. Same class, same run: `JiaoVenkatHanWeissman2015Functionals` failed
   `major` because the record puts the full given-plus-family name `Jiantao Jiao` in the author-family
   slot, which cannot match the entry's `Jiao`. Both were kept on hand authority with an explicit
   `verifiedby` field in `references.bib` AND `references_raw.bib` naming exactly what confirmed them
   and why the automatic comparison fails. Neither entry's fields were changed. This is the skill's
   "a correct indexed entry that fails is a lookup defect" case; it is reported to main as a
   `pipeline-bug` candidate, not repaired in code here. The full offline sweep of all 25 cited keys
   is clean of `major` verdicts after the two `verifiedby` marks.
3. Nothing else halted. P3 passed with 3 citation-support advisories; P4 kept `Hirano2009`,
   `Hirano2012` (registry lists no author) and `Valiant2017` (registry title is the short form) with
   caveats — all pre-existing and correct as written.

## 8. Rescore result and what remains unresolved

Score **6.6 → 7.2**, recommendation still `major_revision`, findings 11 → 8, majors 4 → 2.
Per the operator's instruction this score is final; no further revision cycle was run. After the
rescore, two FACTUAL repairs were made and the bundle re-emitted through P4 only (no second referee
pass):

- the verification appendix cited commit `603f7dc8…`, which P4 had superseded — corrected to the
  pinned commit `881a4d27aaf42f02b1f71128db9f0c6d2184c790`;
- the sentence "This paper inherits their converse and nothing else", written in this round, tripped
  the affirmative-framing contract and was rewritten affirmatively.

Unresolved findings from the 7.2 review, for the user:

- **[major·prose] the author `\thanks` footnote.** "The displayed formal statements and proofs are
  Lean-verified" overstates what the appendix (correctly) says: the printed proofs are audited prose
  renderings of kernel-checked Lean proofs. The footnote is emitted verbatim by the pipeline at
  `tools/src/presentation/stages/p2_draft.ts:750` and is NOT an authored source, so no orchestrator
  can fix it in a bundle. This is the second referee round in which this footnote is a MAJOR finding
  on this bundle (it was also the top finding at 6.6). It needs a pipeline-level wording change.
- **[minor·prose]** the estimator's computational status is still judged blurred ("written out in
  closed form" plus "complete statistical specification"); the referee wants either pseudocode with
  a complexity bound or a flat statement that no computational claim is made.
- **[minor·statement]** the "Matched frontier" bullet title (adjudication item, §2).
- **[minor·citation]** pinpoint locators wanted on the two rate comparisons in Related work, plus the
  sampling/regime gates of the Jiao–Han–Weissman converse.
- **[minor·statement]** `prop:equal-propensity-l1-reduction` introduces `P0` and `mu_n`, which the
  reader cannot connect to the embedded law; they instantiate the global sampling interface. This is
  a Lean-backed environment: a prose clarifying sentence, or an amendment, is the user's call.
- **[minor·structure]** residual duplication (two `L_1`-embedding definitions, repeated Jackson
  kernel / good-pilot / risk notation) and full renderings of mechanical proofs in the main appendix.
  This is the same class as §1 and would be closed by the same lever (the remaining synthesized
  definitions whose content a Lean-backed environment already carries).

## 9. P6 slides

`slides.md` was KEPT (hand edits are preserved) and hand-updated for consistency with the revised
paper: "Jackson–factorial" → "Jackson factorial" (4 places), "constructive upper bound" → "explicit
estimator's upper bound", and the Related-literature slide gained the two quantitative comparison
lines matching the rewritten related-work section. Checkpoint review: 15 slides; both figures are
schematics whose `.dsl` nodes match `def:jackson-factorial-estimator` and
`prop:equal-propensity-l1-reduction`; every displayed rate is verbatim from a catalog body; every
Author (Year) resolves in `references.bib`; no bare `@formal` slide. No `.dsl` was edited, so no
`.svg` re-render was needed.

## 10. Final state

`stage_completed = P4`, `pinned_commit = 881a4d27aaf42f02b1f71128db9f0c6d2184c790`, score 7.2 in
`meta.json`. `paper.pdf` rebuilt, latexmk aux files stripped, `npx astro build` green (305 pages).
Nothing committed.
