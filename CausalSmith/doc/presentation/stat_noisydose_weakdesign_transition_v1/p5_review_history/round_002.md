# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results establish a substantial and carefully scoped uniform characterization, while repetition and insufficiently concentrated explanation of the central inversion mechanism reduce the manuscript's effectiveness.

The paper establishes matching minimax absolute-error and honest connected-interval-length orders for a scalar causal mean under polynomial dose-density envelopes and known Gaussian measurement error. Its three-regime characterization, uniform transitions, observable construction, and finite-sample coverage form a coherent theoretical contribution. The principal prose claims faithfully reflect the verified results, and the closest literature receives substantive treatment. Publication is warranted after focused revisions to exposition and navigation.

## Strengths
- The characterization treats estimation and honest interval length over the same structural class, uniformly across the known measurement-error scale.
- The results distinguish finite-sample coverage from sufficiently-large-sample risk and length guarantees accurately.
- The observed-law witnesses establish statistical difficulty within the bounded causal class used for achievability.
- Related work discusses competitors' actual rates, losses, and conditions, with careful boundaries around comparisons across experiments.
- The manuscript consistently preserves fixed smoothness, design-decay, measurement-channel, and scalar-target conditions.

## Findings
- **[minor·structure] Introduction; Related work; Optimal estimation and interval length; Discussion** — The central characterization and its qualifications are repeated extensively across these sections. The introduction also reproduces much of the detailed literature discussion, while several later paragraphs restate theorem quantifiers already displayed. This repetition obscures the contribution's hierarchy and substantially increases the reading burden.
  - *Fix:* Keep the introduction focused on the question, three-regime characterization, and principal novelty. Consolidate detailed competitor comparisons in Related work, shorten post-theorem recaps, and reserve Discussion for implications of the rates. Preserve the verified statements and their conditions.
- **[minor·prose] Setup and assumptions — Design and response restrictions** — The motivating prose emphasizes local dose scarcity, whereas the density envelopes in \cref{obj:ass:weak-design} apply throughout the entire centered support interval. That distinction matters for interpreting the structural class and its relationship to the local direct-regression benchmark.
  - *Fix:* Immediately after the assumption, state affirmatively that the envelopes hold throughout the known dose support, impose polynomial scarcity around the evaluation dose, and permit otherwise irregular measurable densities within those bounds. Explain briefly why this global specification is useful for the uniform inversion characterization.
- **[minor·prose] Optimal estimation and interval length; Observable estimation and honest intervals** — The compact-support branch is described primarily through the statement that known support 'supports polynomial localization.' The manuscript's most consequential departure from conventional Gaussian Fourier localization would benefit from a concentrated explanation connecting polynomial degree, inverse-weight variability, and attainable localization.
  - *Fix:* Add a short explanatory paragraph using the existing polynomial certificate: localization width scales as inverse degree, Gaussian inversion enlarges the second moment with degree, and the available degree scales as L_n/log(e+sigma^2 L_n). Connect this balance directly to the compact-support branch and its transition to the Fourier branch, referring readers to the existing detailed certificate.
- **[minor·structure] Optimal estimation and interval length — Error-free weak-design reduction** — The lengthy secondary Gaussian-response benchmark occupies substantial space between the main characterization and the estimator. Its extensive experiment-specific conditions interrupt the principal causal argument even though the running text correctly presents it as a separate rate comparison.
  - *Fix:* Move the complete benchmark proposition and its local formalization disclosure to the technical material, retaining a concise main-text explanation of the error-free deduction and exponent comparison through \cref{obj:prop:error-free-reduction}. Keep the benchmark's polynomial-approximation class and degree-one endpoint intact.
- **[nit·prose] Global — Structural navigation** — Several reader-facing structural references use phrases such as 'the technical appendix' and 'the two technical appendices' without cleveref targets. The introductory roadmap likewise names sections manually, making navigation less precise than the otherwise careful object references.
  - *Fix:* Label the relevant section and appendix headings and use \cref or \Cref for structural navigation. Use \cref{sec:deferred-proofs} when directing readers to the existing main-proof section.

## Questions for authors
- What substantive treatment-assignment setting best motivates polynomial density envelopes across the entire known dose support?
- Which part of the contribution should readers regard as the principal methodological advance: the uniform transition characterization, the weak-design compact-support analysis, or their joint estimation-and-inference formulation?

