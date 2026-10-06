# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.2/10 — The verified joint minimax characterization delivers a substantial and carefully positioned theoretical contribution, with remaining revisions concerning sampling language, estimator interpretation, and presentation.

The paper establishes the minimax squared-error rate for optimal population treatment value over a finite categorical observational model with unknown cell masses and propensities, uniformly as overlap shrinks. Its contribution extends the same-target fixed-overlap characterization through universal overlap dependence, an attaining deterministic statistic, and an exact consistency criterion. Taking the verified results as established, the manuscript earns a favorable assessment; targeted exposition revisions would improve its readiness for publication.

## Strengths
- The universal comparison constants establish a meaningful joint characterization of growing support and shrinking overlap across the full stated parameter range.
- The abstract and main discussion accurately preserve the model's uniformity over null cells, boundary means, exact ties, and heterogeneous unknown propensities.
- The dedicated early related-work section engages competitors' actual rates, conditions, and statistical targets, and identifies the fixed-overlap predecessor clearly.
- Identification and causal completion connect the observed minimax problem precisely to the causal oracle-value problem.
- The estimator is explicitly defined as a deterministic observed-data statistic, and the labelled limitations section candidly explains its computational scope.
- The approximation and lower-bound exposition identifies the distinctive roles of common-mean priors, normalization, and the full observed likelihood.

## Findings
- **[minor·prose] abstract** — The opening sentence describes estimation 'from independent observational data.' The verified experiment assumes independent and identically distributed observations; independence alone describes a broader sampling domain.
  - *Fix:* Replace this phrase with 'from independent and identically distributed observational data' so the abstract states the sampling condition supporting the characterization.
- **[minor·prose] Identification and upper-bound proofs — Risk analysis by estimator branch** — The subsection says the components supply the uniform risk bound 'across all three branches' and discusses the empirical branch's contribution to that guarantee. The displayed calibration takes D_0=2, so the empirical branch has an empty admissible parameter range. Although the main estimator section acknowledges this, the appendix wording suggests a substantive guarantee for a nonempty empirical branch under another cutoff.
  - *Fix:* Describe the guarantee for the calibrated saturated and active branches, including bounded alphabets. Identify the empirical branch consistently as part of the general parameterized definition, with an empty range under the displayed calibration, and remove language implying that the theorem establishes its performance for other cutoffs.
- **[minor·structure] global — appendices and Proofs of the main results** — The exposition repeatedly restates the matched risk and consistency conclusions, while the omnibus weighted-separation theorem combines approximation, statistical bounds, and asymptotic consequences. The statistical lower-bound appendix gives a descriptive roadmap, but its detailed sparse, dense, and transfer arguments appear inside the weighted-separation proof in the final appendix. This disperses the argument a reader needs to understand the central statistical contribution.
  - *Fix:* Organize the detailed arguments into clearly named approximation, upper-bound, sparse-comparison, dense-comparison, and fixed-sample-transfer subsections. Place the statistical comparisons alongside their lower-bound exposition, add a concise dependency roadmap using the existing exact cleveref labels, and compress repeated rate interpretations and routine algebra while preserving the verified statements and their conditions.
- **[minor·prose] Introduction and An attaining estimator** — The construction is explained primarily through its ingredients—localization, Jackson approximation, factorial statistics, and clipping. The economic and statistical reason that optimizing within cells creates the approximation problem receives less explanation than the repeated statements of the resulting rate.
  - *Fix:* Add a short conceptual paragraph expressing the cellwise maximum as half the sum of the two means and their absolute difference. Explain how treatment-effect ties create the absolute-value cusp and how localized polynomial estimation addresses that difficulty while armwise sensitivity accounts for overlap. Use this paragraph to replace some repeated rate commentary.

## Questions for authors
- What explanatory role is intended for the general-cutoff empirical branch and the separate multinomial factorial construction, given that the displayed attaining calibration uses the saturated and active capped-Poisson branches?

