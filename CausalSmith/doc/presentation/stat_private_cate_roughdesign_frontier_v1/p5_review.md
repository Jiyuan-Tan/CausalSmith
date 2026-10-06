# Referee review

**Recommendation:** minor_revision
**Overall score:** 7.8/10 — The paper delivers a substantial, carefully scoped private minimax characterization with honest inference, while several presentation and cross-reference defects require editorial repair.

For a precisely specified scalar binary observational model, the paper characterizes pure-private pointwise absolute-error risk and uniformly honest connected-interval expected length by the same three-term benchmark. Its substantive contributions are density-robust occupancy-weighted attainment and matching causal testing comparisons across privacy regimes. Accepting the verified statements, the surrounding claims faithfully preserve their scope, and the closest literature receives a careful comparison. The paper merits publication after focused improvements to organization, wording, and references.

## Strengths
- The estimation and interval conclusions cover every admissible measurable design density and the full binary arm-mean range.
- The occupancy-weighted ratio provides a concrete connection between nuisance approximation, usable pairs, replacement sensitivity, and privacy noise.
- The lower-bound comparisons apply to all admissible private randomized procedures, with an explicit simultaneous-containment argument for honest interval length.
- The manuscript distinguishes the closest nonprivate comparison's experiment and attainment conditions from its own model.
- The limitations candidly quantify the extremely conservative interval constants and distinguish exact-real guarantees from implementation certification.

## Findings
- **[minor·structure] Introduction; Causal records and observational sampling** — The introduction references \cref{sec:related-work}, but the supplied Related work section has no corresponding label. The sentence saying that coordinate conventions are 'recorded in Appendix~A' uses a manually numbered reference and points away from the conventions actually presented immediately afterward in the main text.
  - *Fix:* Add \label{sec:related-work} to the Related work section. Correct the coordinate-convention pointer to its actual location, using an exact structural label and \cref, or remove the pointer after consolidating the definitions. Check all reader-facing structural references for the same requirements.
- **[minor·structure] Observation model, identification, and decision criteria** — The observation model repeatedly introduces the same record coordinates through an opening paragraph, separate outcome, treatment, and covariate definitions, and another full-coordinate definition. This interrupts the progression from observational sampling to identification and the decision problems.
  - *Fix:* Present the full causal record and observed marginal together in one concise main-text passage. Relocate the standalone coordinate conventions and elementary probability-space definitions to an appendix while preserving their anchored environments and mathematical content.
- **[minor·prose] Discussion and limitations, before Limitations and future work** — The sentences 'These are order comparisons for the specified model, rather than finite-sample design recommendations' and 'This argument explains the common frontier without reducing honest inference to a point-estimation slogan' use contrastive non-coverage framing outside the explicitly titled limitations subsection. The latter also introduces an unnecessarily dismissive description of an alternative argument.
  - *Fix:* Write affirmatively that the regime comparisons characterize optimal dependence on sample size and privacy budget, and that simultaneous containment establishes the interval converse directly. Place any qualification about practical design recommendations in Limitations and future work.
- **[minor·prose] Discussion and limitations** — Two consecutive paragraphs explain essentially the same interval mechanism: transferred coverage produces simultaneous containment, and connectedness converts separation into length. This repeats explanations already supplied in the introduction and main-results section.
  - *Fix:* Merge the two discussion paragraphs into one concise account connecting the interval argument to the paper's broader statistical interpretation. Retain the detailed explanation in the main-results section.
- **[nit·prose] A private release based on within-cell pairs; Population pair moments and occupancy** — The phrases 'following frozen algorithm' and 'following frozen statement' introduce unexplained editorial terminology into the mathematical exposition.
  - *Fix:* Remove 'frozen' and state directly that b denotes the public error-envelope bias component in the inversion algorithm and the cellwise bias certificate in the occupancy lemma.

