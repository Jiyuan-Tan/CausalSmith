# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified universal overlap-dependent frontier provides a substantial theoretical contribution, with faithful substantive claims and careful positioning, while several presentation and citation details require repair.

The paper characterizes minimax squared-error risk for optimal cellwise treatment value uniformly over categorical observational laws with unknown masses and propensities, including shrinking overlap. It constructs an attaining deterministic statistic, establishes matching lower bounds, and obtains an exact uniform-consistency criterion with a causal interpretation under the stated assumptions. The substantive prose accurately represents the verified results; publication merits rest primarily on the universal overlap dependence extending the same-target fixed-overlap benchmark.

## Strengths
- The matched rate has universal constants across sample size, alphabet size, and overlap, yielding a clear joint consistency threshold.
- The uniformity domain explicitly accommodates unknown heterogeneous propensities, null cells, boundary outcome means, and treatment-effect ties.
- Identification and causal completion justify transferring the observed-law risk characterization to the causal oracle-value problem.
- The dedicated early related-work section engages competitors' actual rates, conditions, and estimands.
- The limitations section clearly distinguishes statistical attainment, computational questions, and leading-constant calibration.

## Findings
- **[minor·citation] Introduction and Related work** — The decisive same-target predecessor is cited using the locator 'matched minimax theorem'. This descriptive locator leaves the exact result and version underlying the novelty comparison insufficiently identifiable, particularly for an archival reference.
  - *Fix:* Establish an exact theorem identifier and stable archived version for the fixed-overlap predecessor, include complete bibliographic access information, and state its precise overlap range in the comparison. Preserve the distinction between overlap-dependent predecessor constants and the present universal constants.
- **[minor·prose] An attaining estimator and appendices** — The sentence '\Cref{sec:appendix-upper} develops the sensitivity argument and the detailed risk proof' directs readers to an appendix containing sensitivity results and a risk-analysis overview; the detailed observable-upper proof appears in 'Proofs of the main results'. Similar separation of overview material and detailed arguments creates repeated navigation through the appendices.
  - *Fix:* Update the sentence to distinguish the analytic overview in \cref{sec:appendix-upper} from the detailed proof in \cref{sec:deferred-proofs}. Add equally direct pointers from the approximation and statistical-lower-bound overviews to their detailed arguments, and consolidate repeated dependency summaries.
- **[minor·prose] An attaining estimator** — The main estimator presentation gives positivity restrictions on its calibration parameters and an existential attainment guarantee, while a concrete proved calibration is buried in the deferred proof. Readers seeking a fully specified attaining statistic must search through that long proof.
  - *Fix:* Immediately after the algorithm, report the supplied proved choice H_0=1025, kappa=1/17952, and D_0=2, with a reference to the calibration argument. Explain that this choice uses the saturated and active branches throughout the admissible alphabet range, while the displayed parameterized definition also includes an empirical branch.
- **[minor·prose] An attaining estimator** — The sentence 'The formula therefore defines a finite deterministic theoretical statistic; no claim of computationally efficient exact evaluation is made' uses absent-deliverable framing outside the explicitly titled limitations subsection.
  - *Fix:* Replace it with an affirmative scope statement, such as 'The formula defines a deterministic theoretical statistic through finite averaging over auxiliary counts and mark allocations.' Keep the computational-efficiency discussion in 'Limitations and future work'.
- **[minor·structure] Observational model and causal interpretation — Observed experiment and loss** — Several transitions describe a different object from the environment that follows. The 'following presentation definition' promises sampling notation and cell quantities but defines the alphabet and atoms; 'the following public floor' immediately precedes that alphabet definition; and 'Sampling from each law follows a common independence condition' precedes the observed-class definition.
  - *Fix:* Place the alphabet introduction directly before its definition, the public-floor motivation directly before the overlap assumption, and the independence explanation beside the sampling assumption. Remove duplicated transitions so the sequence clearly introduces indices, cell quantities, overlap, and the observed class.

## Questions for authors
- Which stable archived version and exact theorem identifier support the same-target fixed-overlap comparison?

