# Referee review

**Recommendation:** major_revision
**Overall score:** 7.2/10 — The verified identification and rate results are substantial, but the closest methodological comparisons and the definition of the proposed external-log interval need work before publication.

The paper characterizes worst-case ATE ambiguity from deterministic score labels, derives optimal label-design rates and a high-resolution constant, and establishes honest-interval rates with known scores or an independent score log. These are meaningful contributions under clearly stated model conditions. The main revisions concern positioning the design results against quantization research and making the external-log projection fully legible to a reader.

## Strengths
- The exact ambiguity formula includes endpoint attainment under one released law and covers atomic score distributions and disconnected cells.
- The paper connects identification, finite-label design, and honest interval length through distinct, explicit criteria.
- The related-work section credits the fixed-law sharp interval to its antecedent and states the conditions for the main rates.

## Findings
- **[major·citation] Related work** — The closest design comparison, scalar quantization, receives only a general citation when the density assumption is introduced. Readers cannot tell which part of the inverse-budget rate and high-resolution companding calculation follows established quantization theory and which part comes from the paper's paired ATE distortion.
  - *Fix:* Add a substantive comparison with scalar absolute-loss quantization: state the relevant established rate and high-resolution result with precise citations, derive the paired local weight used here, and identify the contribution of optimizing the sharp ATE width over released outcome laws.
- **[major·statement] Inference with an independent score log** — The definition of the central projection procedure says, “For each b∈B_{n,m}, let I(b) be the interval given by its two quantile-transport average treatment effect endpoints.” Because sieve arrays need not arise from one score law, this sentence leaves the candidate interval and its zero-mass convention implicit.
  - *Fix:* Display the candidate cell mass, normalized outcome measure, pushed-forward reciprocal-weight measure, and both endpoint sums for an arbitrary sieve array; specify zero-mass terms explicitly. Then explain how the clipped hull uses those candidate intervals.
- **[minor·prose] Designing a finite-label release** — “A positive density floor ensures that every K-label design leaves ambiguity of inverse-budget order” overstates the result: the floor supplies an inverse-budget lower bound for every design, while a poorly chosen design can have larger ambiguity.
  - *Fix:* State that every release has ambiguity at least a constant times K^{-1}, and that the equal-width release supplies a matching upper bound for the optimal ambiguity.
- **[minor·prose] Related work** — “Our experiment deletes the row-level score while retaining only its deterministic label and assumes a known score marginal” describes the known-score experiments but omits the paper's external-log experiment, in which the score marginal is sampled.
  - *Fix:* Qualify the sentence as referring to identification and known-score design, then describe the external-log extension in a second clause.
- **[minor·prose] Inference with an independent score log** — “It need not itself arise from a common population score law and release rule” uses contribution-by-negation outside a permitted limitations or open-questions section.
  - *Fix:* Describe the admitted candidate class affirmatively: the sieve combines cellwise measures with matched masses, including arrays assembled independently across cells, which makes the projection conservative.
- **[minor·structure] Trial setup and the sharp identified interval** — The generalized quantile is formally defined after the endpoint and sharp-interval definitions that use it. An informal formula appears earlier, but the sequence makes the core notation harder to follow.
  - *Fix:* Move the generalized-quantile definition immediately before the arm-cell and endpoint definitions, and retain one short explanation of its atom convention.

## Questions for authors
- Can you give a precise comparison between the paired ATE distortion and the closest published scalar quantization result?
- Do you intend the external-log projection as an abstract confidence procedure, or can you supply a finite computation rule with a coverage-preserving approximation bound?
