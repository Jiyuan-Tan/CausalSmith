# Presentation adjudications — pid_slate_benefit_partialtransport / v1 (2026-09-09)

P-orchestrator record. Bank edits are listed separately from bundle edits.

## Bank edits (this directory)

### 1. `graph.json` — `lean.supporting_decls` added to six frozen nodes (P1 `lean-coverage`)
Backup: `graph.json.bak`. The P1 Lean judge reported that six frozen bodies made clauses no
mapped declaration certified. Per the skill's `lean-coverage` remedy the authored bodies were
preserved and the missing certifying declarations were mapped. All names verified to exist in
`CausalSmith/PartialID/PID_SlateBenefitPartialtransport_Research`:

| node | added `supporting_decls` | file |
|---|---|---|
| `def:observable-capacities` | `q0`, `q1`, `gap`, `mass` | Helpers/Capacities.lean |
| `def:plugin-endpoint-estimator` | `empiricalConditional`, `empiricalCellMass`, `rawCapacities`, `projectedCapacities`, `screenedCell` | Helpers/Estimator.lean |
| `def:face-aware-inference-handle` | `GuardEventIndex`, `guardEvent`, `guardEvents`, `maxDeviation` | Helpers/Estimator.lean |
| `def:identified-interval` | `sharp_exact_mass_threshold_interval` | TSharpExactMassThresholdInterval.lean |
| `def:threshold-flow-construction` | `thresholdFlow_endpoint_spec`, `thresholdFlow_spec`, `full_law_endpoint_attainment` | Helpers/Transport.lean, TFullLawEndpointAttainment.lean |
| `def:structural-law-class` | `capacity_identification`, `sharp_exact_mass_threshold_interval` | TCapacityIdentification.lean, TSharpExactMassThresholdInterval.lean |

No statement was weakened; no frozen body was amended. After the additions the P1 Lean judge
returned **all 31 envs faithful**.

### 2. `graph.json` — S1 mapping: patched, then REVERTED (no net change)
S1 maps to the Causalean library structure `Causalean.PO.POSystem`. P1 halted because component
resolution consulted only the run crosswalk and the run's own Lean tree, so a library declaration
could never resolve. I first patched S1 to the run's own `POSlateSystem` (Basic.lean:27). Main
then landed the real fix (83a72baee, component resolution now consults the library index) and
that commit confirms `Causalean.PO.POSystem` is the intended mapping, so **I reverted my patch**.
The bank's S1 node is byte-identical to its banked form. Recorded here only because the `.bak`
predates the revert.

## Bundle edits (`doc/presentation/pid_slate_benefit_partialtransport_v1/`)

### 3. `p1_cache.json` — stripped an `obj:` prefix from the notation reviewer's `used_in` ids
Backup: `p1_cache.json.bak`. Mechanical repair of the worker's own raw output, not a content
judgment. Review round 1 returned bare obj_ids (`ass:iv-independence`) and routed normally,
creating six synthesized definitions. Round 2 returned the same ids in `\cref` label form
(`obj:ass:iv-independence`); `routeNotationProblems` compares `used_in` against bare ids, so all
ten findings fell into the "missing symbol or invalid using environment" halt branch instead of
routing to synthesis. Stripping the leading `obj:` restored routing; the loop then converged in
five iterations and synthesized 19 definitions covering `X, Z, D, S, Y, D_z, S_d, Y_d, p_x,
\widehat p_x` and the rest. No finding was dropped or answered on the model's behalf.

### 4. `components_cache.json` — obsolete edit, superseded
Backup: `components_cache.json.bak`. Before locating the real cause I stripped the unresolvable
`Causalean.PO.POSystem` from the cached component lists. That cache is derived: `graph-first`
component sets overwrite it on every run, so the edit never took effect and is superseded by
main's fix. Recorded for completeness; the file on disk is pipeline output.

## Accepted advisories (P1 checkpoint — `notation_review.json`, `ok: true`)

Four `xref-missing` advisories, all one pattern, all **accepted, no edit**:

- `thm:full-law-endpoint-attainment` → `def:structural-law-class`
- `thm:full-law-endpoint-attainment` → `prop:capacity-identification`
- `thm:branch-free-pointwise-directional-limit` → `def:structural-law-class`
- `thm:uniform-deterministic-guard` → `prop:capacity-identification`

Reason: each theorem **unfolds** the aggregating law class into the individual assumption
environments it actually needs (`\cref{obj:ass:iv-independence, …, obj:ass:positive-aggregate-survivors}`)
rather than asserting membership in `\mathcal M` by bare name — the form the skill's frozen-body
rule prefers. `prop:capacity-identification` is likewise not load-bearing in these statements: the
capacities enter through `def:observable-capacities`, which each theorem does cite. Adding the
cross-references would name a result the statements do not use.

## Ballast acknowledgements (P1 checkpoint, for the P2 gate)

`ballast_review.json` acknowledges six unconsumed frozen statements. None is literature
motivation; each is a deliverable the accepted claim names explicitly (deterministic guard, sparse
threshold-flow algorithm, three-level witness with interval [0,0.7], no-selection sanity
reduction) or a definition feeding one. Reasons are recorded per id in that file.

---

# P2 adjudications

The P2 proof audit halted twice with residual `[rendering]` defects. In all three cases the root
cause was a **frozen statement that overstated or hid its Lean**, not a defective proof. Each was
amended to the Lean-true form under the equivalence-adjudication procedure (diagnosis (2)): the
amendment was made to `nl.frozen_body` on the bank node AND to `formal_layer.json`, the cached
section copy was synced, and the stage was re-entered with `--from P1`. The accepted note was never
edited, and no statement was weakened to fit a proof.

### A. `thm:no-selection-reduction` — the upper endpoint was missing Lean's cap at 1
Lean (`no_selection_reduction`, TNoSelectionReduction.lean:129) states the normalized upper
endpoint as an `inf'` over `Option (Fin K)` whose `none` branch is `1`, i.e.
`min{1, min_t (ℓ_{<t}(x)+h_{>t}(x))/m(x)}`. The frozen body printed the **cap-free** minimum.
The two are not equal: at `t = K-1` the candidate is `ℓ_{<K-1}(x)/m(x)`, which can exceed 1 when
`q_0(x) > q_1(x) = m(x)`. The auditor caught this indirectly — the proof's Step 4 had invented an
argument that the least candidate is ≤ 1 and so removes the cap, which Lean neither proves nor uses.
**Amended** the frozen body to display the capped form. The proof then audited clean.

### B. `thm:branch-free-pointwise-directional-limit` — the recovered support was too large
Lean's `positiveSupport c p` (Helpers/Estimator.lean:107) is `{x : 0 < p x * c.mass x}`, and the
theorem concludes recovery of exactly that set. The frozen body printed
`𝒳₊(P) = {x : m(x) > 0}`, which additionally contains every cell with `m(x) > 0` and `p_x = 0`.
**Amended** to `{x : p_x m(x) > 0}`.

### C. `prop:capacity-identification` — a load-bearing conclusion hidden behind a bare name
The frozen body said the observed law "is compatible with the maintained capacity domain" without
displaying what that domain is. Lean's `ValidCapacities c` (Helpers/Capacities.lean:53) is exactly
`(∀ x i, 0 ≤ ℓ_i(x)) ∧ (∀ x j, 0 ≤ h_j(x))`. Two later proofs cited this proposition for all-cell
capacity nonnegativity, which the printed statement did not support — the skill's "never assert a
named conclusion by bare name" rule. **Amended** to unfold the phrase into the displayed
nonnegativity conditions. No Lean content was added: the unfolded form is `ValidCapacities` verbatim.

### D. Proof prose repaired by hand (no statement involved)
`proofs/thm:branch-free-pointwise-directional-limit.tex` Step 1 described the finite multinomial
CLT output as "a probability law" where the Lean gate supplies `IsGaussian Q` and the theorem
concludes a Gaussian law. Changed "probability law" to "Gaussian law". This is prose fixed at the
level that owns it, per the skill's revision protocol.

## Promotion round (1, automatic)

The first P2 pass fired one promotion round for a residual `[missing-step]`: the deterministic-guard
proof lacked a citable step for the homogeneity of mass and of the two threshold cuts under
nonnegative cell reweighting. Three lemmas were promoted —
`lem:weighted-capacity-mass-homogeneity`, `lem:weighted-capacity-lower-cut-homogeneity`,
`lem:weighted-capacity-upper-cut-homogeneity` — mapping to `weightedCapacities_mass`,
`weightedCapacities_benefitLower`, `weightedCapacities_benefitUpper` in
`Helpers/UniformGuardBounds.lean`. **Reviewed and accepted:** all three are pre-existing, sorry-free
Lean declarations (the run's Lean tree is unmodified by this presentation run), and all three are
consumed by `proofs/thm:uniform-deterministic-guard.tex`. The gap was a genuine missing citable
step, which is what a promotion round is for.

## P2 checkpoint review (what I checked)

- **Journal shape.** Section order is Introduction → Related work → Setup → Sharp benefit bounds →
  Computation and witness → Estimation and guarded inference → Limitations → Appendix → Proofs.
  Related work is early; the introduction threads the contributions and closes with an explicit
  roadmap paragraph.
- **Proof headers.** All 12 proofs open `\begin{proof}[Proof of \cref{obj:<id>}]`.
- **Spot-read.** `proofs/thm:sharp-exact-mass-threshold-interval.tex` (322 lines): both inclusions
  of the polytope-projection argument are argued explicitly, dependencies are cited by `\cref`
  rather than asserted, and the cellwise-to-aggregate step is separated from the sharpness step.

---

# P5 / P6 outcome

**Score trajectory: 6.2 → 6.2 (automatic pass) → 6.3 (final).** Recommendation stayed
`major_revision` throughout.

## Fixed by hand (bundle sources only; no frozen statement touched)

1. **Verification disclosure corrected.** The title-page footnote promised that the appendix records
   "the exact scope, toolchain, and commit"; it recorded none of them, and did not disclose the
   presentation-synthesized definitions. The appendix now states the toolchain
   (`leanprover/lean4:v4.33.0`), the commit, the module tree, and the object accounting: of the 56
   displayed formal objects, 48 are matched to the Lean development, 7 are presentation-level
   restatements (named individually), and 1 — the direction margin — is stated only to pose the open
   problem and is used by no verified theorem.
2. **Closest competitor added.** `PossebomRiva2025` was dropped at P0 as unverifiable. Re-checked by
   hand: Crossref returns the same work under DOI `10.1080/07350015.2024.2388639`, but the registry
   title embeds HTML italic markup the matcher cannot normalize, and the record gives the coauthor
   as **Riva, Flavio** — the entry said "Francesco". Corrected the given name, added
   `verifiedby` to `references.bib` and `references_raw.bib`, and cited the paper in related work
   with a result-level distinction (binary outcome + always-observed stratum, versus ordered outcome
   + survivor compliers with unequal arm totals, which is what forces the transport formulation).
3. **Guard-width candour.** The referee's arithmetic is right and I reproduced it: at
   \(K=3, |\mathcal X|=1, \varepsilon_Z=1/4, \alpha=0.05, m_\star=1/4\) the guard radius is
   \(\approx 4.3\times10^{5}n^{-1/2}\), so the reported interval is all of \([0,1]\) below
   \(n\approx10^{11}\). The limitations section now says this outright and states that the result is
   an existence claim, not a recommended procedure. The same caveat was hand-added to the slides.
4. **Guard exposition.** The prose before the algorithm now separates the three objects the referee
   said were conflated: the implementable interval, the non-computable \(\delta_n\) (analysis only),
   and the multiplier face envelope (diagnostic only, no calibration claim).
5. **Direction margin.** The prose now states that \(\kappa_\sigma>0\) is what the analysis uses, and
   that the displayed inequality is vacuous for \(\kappa_\sigma\le0\).
6. **Broken cross-references.** Six roadmap `\Cref{sec:...}` references had no `\label` target
   (P3 had rewritten the roadmap to `\Cref` without adding labels). Added the six labels; the final
   PDF has zero undefined references.

## Unresolved — recorded, not fixed

- **Simulation study of achievable guard widths** (referee finding 3). Needs new work; out of
  presentation scope.
- **Complete threshold-flow pseudocode** (finding 4). The proof contains the details but the
  reader-facing algorithm does not specify traversal order, tie handling, or output encoding.
  Writing it is authoring new content against a Lean-backed algorithm environment.
- **Operational definition of \(\ell_i(x), h_j(x)\) at first use** (finding 2, and the P3 rubric).
  The displayed instrument contrasts live only in the appendix proof. Moving them into
  `def:observable-capacities` amends a Lean-backed frozen environment
  (`paperObservableCapacities`) — the user's decision, not mine.
- **Redundant / out-of-order synthesized definitions** (finding 11, and the P3 rubric). Merging the
  one-line potential-outcome definitions and deleting the empty guard-event definition is an outline
  change requiring `--from P1` and a re-pay of the proof audits.
- **`O=(X,Z,D,S,SY)` versus \(\widetilde Y\)** (finding 10). With outcome level 0 in the support,
  `SY` conflates a genuine zero with an unobserved outcome. This is inside a frozen setup
  environment; adjudication item for the user.

## Adjudication items for the user (Lean-backed environments I did not touch)

- `def:face-aware-inference-handle` → `guardedConfidenceSet`: the algorithm environment lists
  \(\delta_n\) as a step although \(\delta_n\) depends on the unknown \(P_{\mathrm{obs}}\) and is not
  used to compute the reported interval. I clarified the surrounding prose instead.
- `def:observable-capacities` → `paperObservableCapacities`: does not display the instrument
  contrasts that define its own objects.
- The `O=(X,Z,D,S,SY)` versus \(\widetilde Y\) inconsistency noted above.

## P6 slides checkpoint (what I checked)

18 slides (lint range 8–18), 2 schematic figures. Verified: both `.dsl` figures' edges against the
frozen definitions (the IV pipeline \(Z\to D\to S\to Y\) with survivor compliers as compliers ∩
always-selected; the capacity/transport chain with \(m(x)=\min\{q_0,q_1\}\) fed by both arms); every
`Author (Year)` on the two literature slides against `references.bib` (11/11 exact); rates on the
computation slide verbatim from the theorem body. One hand edit: added the guard-width caveat so the
deck claims no more than the audited paper.
