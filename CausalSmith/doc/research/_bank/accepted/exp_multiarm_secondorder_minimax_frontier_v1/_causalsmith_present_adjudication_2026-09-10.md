# Presentation adjudications — exp_multiarm_secondorder_minimax_frontier / v1

Date: 2026-09-10. P-stage orchestrator run (first presentation of this bank entry).

## Bank edits (graph.json; `.bak` kept beside it)

### 1. `def:k3-rational-lp` — `lean.supporting_decls` added (P1 `lean-coverage` halt)

The P1 Lean judge returned `missing-coverage`: the mapped declaration
`gridLPValueK3` alone does not certify the authored body. The LP rows come from
`GridLPFeasible` / `gridLPValueRaw` / `cDaggerQ` / `gammaMC`, and the body's
"minimum" clause is supported by the attainment bridge
`gridProgram_optimal_primal_dual_exists` / `gridLP_rational_value_exists`.

Resolution: the six certifying declarations were mapped into the node's
`lean.supporting_decls` (all in namespace
`CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier`). The authored
statement was **not** weakened. The judge then returned `faithful`.

### 2. Three frozen bodies — `\cref` lead-ins added (P1 `xref-missing` advisories)

`thm:multiarm-strict-extension`, `thm:rational-contrast-grid-certificate-sandwich`
and `thm:attainment-and-k3-certified-converse` used the symbols `\rho_n(c)` and
`G_n(c)` without pointing at the environments that define them. One purely
referential clause was added to each opening sentence
("… is the labeled-schedule minimax risk of \cref{obj:def:labeled-schedule-game}
and \(G_n(c)\) the finite orbit-game value of \cref{obj:def:finite-orbit-game}").
No mathematical content changed; all three re-judged `faithful`.

## Bundle edits

### 3. Synthesized definitions `synth_18` and `synth_19` rewritten by hand

- `synth_18` was emitted with a 41-item `\cref{...}` preamble listing every object
  in the paper (a synthesis artifact) and closed by *asserting* the certificate
  sandwich `B <= rho_n(c) = G_n(c) <= U <= Lambda` inside a definition
  environment. Rewritten as a definition of the "exact rational grid-certificate
  cluster" that references `\cref{obj:synth_12}` for the certificate data and
  asserts nothing.
- `synth_19` restated `synth_4` almost verbatim. Trimmed to the notation clause it
  is actually for (`m(z) = counts(z)`, coordinates `m_t(z)`), retitled
  "Notation for response-type counts".

### 4. Bibliography — six entries recovered, none invented

P0 dropped six correct entries. Each was diagnosed and repaired at the level that
owned the defect; no field was ever copied from another work's record.

| key | defect | repair |
|---|---|---|
| `dasgupta_2015` | DOI `10.1111/rssb.12082` belongs to a different RSS-B paper (Zheng & Zhou, mediation) | corrected to `10.1111/rssb.12085` (Dasgupta, Pillai & Rubin, RSS-B 77(4), 727–753) → verdict `exact` |
| `levit_1981_second_order` | model-invented title; author/journal/volume/issue/pages all matched Crossref `10.1137/1125066` | title corrected to "On Asymptotic Minimax Estimates of the Second Order", DOI + issue added → `exact` |
| `pinsker_1980` | not indexed by any registry under its own identity (Russian translation journal) | hand-confirmed against Math-Net.Ru record `ppi1441`; `verifiedby` added |
| `fisher_1935` | book; registries index only later editions and reviews | hand-confirmed against the Open Library catalogue record + archive.org scan; `verifiedby` added |
| `hansen_1953` | book; article registries return an unrelated 1954 record | hand-confirmed against the Open Library catalogue record; `verifiedby` added |
| `ibragimov_1981` | Springer monograph; registries index only reviews **of** it | hand-confirmed against the LMS Bulletin (`10.1112/blms/14.6.565`) and Le Cam BAMS (`10.1090/S0273-0979-1984-15326-6`) reviews, which quote the book's imprint; `verifiedby` added |

All six were then re-verified offline with `verifyEntry(entry, defaultLookup)`.
The four restored anchors (Fisher, Hansen–Hurwitz–Madow, Ibragimov–Has'minskii,
Levit) were added to the relevant `bib:` lines in `outline.md`; a typo'd key
`sudijono_dobriban_tchetgen_2022026_sharp` in the outline's Related-work
description was corrected.

### 5. P2 ballast gate — four headline theorems acknowledged

`ballast_review.json` acknowledges `thm:multiarm-strict-extension`,
`thm:first-order-saddle`, `thm:second-order-rate-and-certificate-frontier` and
`thm:attainment-and-k3-certified-converse`. All four are delivered results the
contribution statement claims; a terminal theorem is consumed by nothing by
construction. None is literature motivation, so none was excised.

## Accepted without change

- `notation-mutual-definition synth_3 ↔ synth_10` (design-based risk vs
  orbit-procedure risk). The skill records a dependency-cycle advisory as
  not-a-halt; the two definitions are genuinely mutually referential in
  presentation order and each is self-contained mathematically.
- P0 `minor` caveats of the edition/short-title kind (`imbens_rubin_2015`
  subtitle, `van_trees_1968` 1968 vs the 2001 reissue, `rao_1945` vs a 2021
  reprint, `harshaw_2024` / `basse_2023` journal-vs-preprint year,
  `athey_imbens_2017` author-less registry record). The entries are correct as
  written; the registry records are the derived ones.

---

## Further bank edits (P5 revision rounds)

### 6. Three frozen environment TITLES changed (bodies untouched)

Titles are not part of the freeze. The referee found three titles that promised
more than the theorem delivers; each was renamed in `graph.json`
(`nl.frozen_title`) and in the bundle's `formal_layer.json`:

| obj | old title | new title |
|---|---|---|
| `thm:multiarm-strict-extension` | Multiarm strict extension | Two-arm specialization and the fixed-$K$ orbit game |
| `thm:first-order-saddle` | First-order saddle value | First-order minimax constant and attaining procedure |
| `thm:attainment-and-k3-certified-converse` | Attainment and certificates | Two-arm value transfer and finite brackets |

The first suggested a bounded-outcome extension the theorem does not prove; the
second suggested an explicit saddle point and least-favorable prior that the
statement does not exhibit; the third suggested attainment of the second-order
constant, which is bracketed rather than attained.

## Adjudication items for the user (frozen statements — NOT changed here)

These are referee findings that would require amending a Lean-backed
environment. Per the skill they are recorded, not acted on.

1. **`thm:second-order-rate-and-certificate-frontier` is ill-typed in its paper
   rendering.** The statement asserts "there exist sequences \(G_n, P_n, L_n\)
   such that \(G_n\) is an exact rational grid-certificate cluster for \(q\),
   and \(G_n - x_n(c)\to0\)". A cluster is a tuple of LP data; subtracting it
   from a real number is a category error. Both P5 passes raised this, and the
   proof repeats it. Declaration:
   `CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier.second_order_rate_and_certificate_frontier`.
   The fix is to name the cluster and its induced scalar separately in the Lean
   statement.
2. **`thm:multiarm-strict-extension`: two vacuous clauses.** "Hull risk-value
   inclusion" is discharged by choosing the same design and estimator; "strict
   treatment-domain separation" holds because the two schedule domains have
   different codomains, independently of \(K\) and \(n\). Three separate reviews
   asked for their deletion. Prose now frames them as scope bookkeeping, but they
   remain theorem clauses. Declaration:
   `...multiarm_strict_extension`.
3. **Elementary clauses stated as theorem conclusions.** The "(Mesh-rate
   scaling.)" clauses of `thm:rational-contrast-grid-certificate-sandwich` and
   `thm:k3-grid-certificate-sandwich`, and the closing limit clause of
   `prop:k3-lp-certificate`, are a multiplication by a constant and an
   elementary power limit.
4. **`thm:universal-second-order-rate` exposes an internal proof threshold** as a
   clause, and reuses \(m\) (a response-count vector everywhere else) as an
   integer index; \(s_n=n^{4/3}\) is introduced in its preamble and never used.
5. **`prop:k3-lp-certificate` weakens its own proof**: the statement gives
   \(\Lambda^\dagger_{n,M}\le\rho^\dagger_n+2/M+1/M^2\) while the proof
   establishes \(\rho^\dagger_n+1/(4M^2)\).
6. **`def:labeled-schedule-game` omits the estimator's codomain.** The Lean
   `Estimator` maps into `Set.Icc (-L_c/2) (L_c/2)`; the frozen body writes a
   bare \(\inf_{\mathcal D,\widehat\tau}\). The restriction is provably without
   loss (projection onto \(I_c\) never increases squared error at a target in
   \(I_c\)), and the paper now says so in prose immediately before the
   definition, but the frozen body still under-specifies the class.

## Unresolved at hand-off (out of presentation scope)

- **Competitor engagement.** Both P5 passes ask for the actual content of
  Sudijono–Dobriban–Tchetgen Tchetgen (scalar reduction, the expansion
  \(\rho_n=n^{-1}-C_A n^{-4/3}+o(n^{-4/3})\), the Airy constant, the attaining
  nonlinear rule and least-favorable prior) and of Hull's optimality results.
  Writing that requires reading those papers; it is citation research, not
  presentation.
- **Citation locators.** The citation contract wants section/theorem/page
  locators on substantive literature claims. Same reason.
- **No solved LP instance.** The paper presents the grid programs as computable
  but reports no generated instance, certificate artifact, runtime, or scaling
  evidence beyond the \(n=3\) lookup rule. Producing one is new work.

## Reviewer-calibration note (not a bug, but recurring cost)

The P3 rubric reviewer and the P5 referee both read the LaTeX SOURCE, and both
repeatedly flagged `\leanref{S-1}{...}` / `\leanref{sym:...}` wrappers as
"placeholder anchors" and "internal identifiers" visible to the reader. They are
not: `paper_macros.tex` defines `\newcommand{\leanref}[2]{#2}`, so the PDF shows
only the display text. Roughly six findings per pass were spent on this false
positive across three passes.
