# Referee review

**Recommendation:** minor_revision
**Overall score:** 7.4/10 — The verified results deliver a meaningful and carefully scoped theoretical contribution, with revisions needed chiefly for exposition, attribution, and interpretation of the calibration.

The paper establishes the rate-sharp honest expected-length frontier for transported complier effects in an equal-size, scalar-covariate model with fixed rough smoothness. Its strongest contribution combines an observable cubic estimator with a matching confidence-set lower bound realized by causally admissible instrumental-variable laws. The principal claims faithfully represent the verified results, and the early related-work section engages close competitors substantively. Publication would benefit from a more economical presentation and several targeted corrections.

## Strengths
- The frontier distinguishes global coverage from precision evaluated on strength slices and supplies one procedure across all evaluation floors.
- The lower construction preserves monotonicity, probability-law admissibility, and both transport restrictions while supporting arbitrary measurable confidence sets.
- The observable estimator, sample splitting, resolutions, and finite-sample calibration are specified explicitly.
- The related-work section compares actual rates, observation schemes, and nuisance conditions rather than relying on broad citations.
- The discussion provides a useful numerical disclosure of the conservative calibration constant.

## Findings
- **[minor·structure] Model, transport restrictions and inference criterion; Comparator definitions and verification scope** — Repeated explanations of individual assumptions and repeated complete model-restriction lists obscure the statistical experiment and the central inference criterion. The comparator subclasses each reproduce restrictions already incorporated through model membership.
  - *Fix:* Consolidate the running explanation into short paragraphs covering sampling, regularity, instrument validity, and transport. Describe comparator subclasses through membership in \cref{obj:def:model-class} followed by their additional geometry restrictions, preserving the exact anchored definitions and their conditions.
- **[minor·structure] Lower-bound construction and proof** — Several transitions describe objects that have already appeared or announce the wrong next object. For example, “Before forming those laws, we specify the baseline receipt--outcome probabilities” follows the baseline definition, and “We use the following distance conventions” follows the distance definition. The bump definition also appears after the lemma that uses it.
  - *Fix:* Present the bump and cells before the tiled perturbation, the baseline probabilities before the mixture construction, and the distance conventions before the distance result. Rewrite the surrounding transitions to match that order and retain exact cleveref targets.
- **[minor·prose] Comparator definitions and verification scope** — The opening claim that “the continuous witness confirms that the rough ambient geometry is nonempty” attributes a membership conclusion to a comparator supplied as a definition. The verification contract distinguishes these comparator definitions from proved conclusions.
  - *Fix:* Describe \cref{obj:def:continuous-geometry-witness} as an explicit comparison construction. Attribute established model nonemptiness to the component membership conclusion in \cref{obj:lem:legal-iv-mixture-full-elbow}, and keep the comparator's definitional role explicit.
- **[minor·prose] Discussion and open questions** — The sentence “These values exceed the effect-domain diameter” compares a tolerance in affine-score units with a diameter in effect units. Acceptance geometry depends jointly on the tolerance and both estimated contrasts, so this comparison does not directly describe the reported interval.
  - *Fix:* Explain conservatism through the score geometry: the full effect domain is accepted when the absolute estimated outcome contrast plus the absolute estimated receipt contrast is at most the score tolerance. Separately report the deterministic length cap of two and explain the numerical informativeness of the expected-length certificate.
- **[minor·prose] Discussion and open questions** — The clause “but that realized length is not the uniform certificate” uses ordinary negative scope framing outside the explicitly titled limitations subsection.
  - *Fix:* Replace it with an affirmative description, such as: “Reported length varies with the observed scores. The uniform certificate bounds expected length under repeated sampling across the declared model.”
- **[minor·prose] Introduction; Main results and an attaining interval; Supporting length bounds** — The roadmap says “Full proofs of the anchored results are collected” in the final proof section, while identification, observable reduction, mean-square control, and mixture proofs appear in earlier appendices. The later phrase “Full proof scripts for the anchored statements” similarly misdescribes the material collected there.
  - *Fix:* Specify that proofs of the frontier and supporting length theorems appear in \cref{sec:deferred-proofs}, with identification and estimation proofs in \cref{sec:upper-appendix} and the mixture proof in \cref{sec:lower-appendix}. Use “proofs” for the manuscript arguments.
- **[minor·citation] Related work; Lower-bound construction and proof** — The positioning of the converse emphasizes linear-functional expected-length theory, while the sign-mixture comparison for multiple nonlinear nuisance components deserves direct methodological attribution. The supplied literature context identifies a closely relevant nonlinear-functional mixture literature.
  - *Fix:* Add a precise comparison with the mixture methodology in Van der Vaart, Tchetgen, Robins, and Li's Semiparametric minimax rates, using a verified locator. Explain that the present additional contribution is the compatible principal-stratum realization and admissibility conditions within the transported-IV model.
- **[nit·other] Main results and an attaining interval** — The opening frontier display contains the literal text “quad” in “n\ge n_0,quad 0<a\le1/4,” which will render as mathematical letters.
  - *Fix:* Replace “quad” with the LaTeX spacing command \quad.

## Questions for authors
- Which feature of the admissible principal-stratum construction should readers regard as the main technical advance over existing nonlinear-functional mixture lower bounds?
- For the displayed calibration examples, what numerical interpretation of the expected-length certificate best communicates its usefulness alongside the deterministic length cap?

