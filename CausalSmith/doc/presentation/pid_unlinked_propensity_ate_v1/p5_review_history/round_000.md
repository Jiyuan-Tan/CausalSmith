# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The verified identification and design results are substantial, but the manuscript needs more accurate proof-scope language, clearer exposition, and a substantive comparison with close competitors.

The paper characterizes worst-case ATE ambiguity from deterministic score labels, derives optimal label-design rates and a high-resolution constant, and establishes honest-interval rates with known and logged score laws. These are meaningful contributions to partial identification and disclosure design. The verified results support the central claims, but the presentation currently overstates one proof ingredient and gives readers too little basis to assess novelty against nearby work.

## Strengths
- The all-label ambiguity formula has an attainable common released law and covers atomic score distributions and disconnected cells.
- The finite-label bounds, high-resolution constant, and known-score honest-length rate give a coherent design analysis.
- The external-log result states its law class, risk criterion, and two sampling directions precisely.

## Findings
- **[major·citation] Related work** — The section names data combination, subclassification, and interval-inference literatures but does not compare the paper's bounds, rates, and information structure with the closest results available to the authors, including coarse inverse weighting, limited pooling of linked covariates, and disclosure-risk analysis. A reader cannot judge which conditions or conclusions distinguish the contribution.
  - *Fix:* Add a focused comparison of the observation scheme, target, assumptions, and bound or rate for the closest papers, especially Kalavasis et al., Lee and Weidner, Komarova, and Fan et al.; use precise locators and keep priority claims within what those sources establish.
- **[major·structure] Ambiguity and finite-label design** — The sentence “the high-resolution argument uses an intervalization step” and the formal “High-resolution handle” present an uncrossing or intervalization result as part of the argument. The displayed proof instead applies paired quantization directly to arbitrary measurable partitions; the verified high-resolution result supplies asymptotically attaining interval cells, without a finite-budget intervalization result.
  - *Fix:* Remove the handle as a formal mathematical object and describe the actual proof route: optimize paired distortion over measurable partitions, apply the paired quantization lemma, and construct asymptotically attaining ordered cells.
- **[major·prose] Proofs and verification scope** — The sentence “The published fixed-law result of FanShermanShum2014 is used as a cited input” describes a formal dependency that the current verification contract does not record: the fixed-law declaration has no external dependency and has a checked, faithful proof. Similar wording before the fixed-law lemma blurs prior-art attribution with proof dependency.
  - *Fix:* State that the fixed-law interval is attributed to the published result and that its displayed formal proof is checked under the current declaration. Retain the source citation and its theorem and equation locators.
- **[minor·structure] Trial setup and the sharp identified interval** — The endpoint formulas use generalized quantiles before the generalized-quantile definition appears. The ATE functional θ(P) is likewise used in the setup before its definition in the inference section.
  - *Fix:* Move the generalized-quantile definition ahead of the endpoint formulas and define θ(P) with the target in the trial setup.
- **[minor·prose] Introduction** — The companding integral first uses ε, e, and f before giving the requested plain-word glosses for those symbols; the abstract first introduces n inside a rate before identifying it as trial size.
  - *Fix:* Introduce ε as the overlap margin, e as a score value, and f as the score density before the integral; identify n as trial size at its first use in the abstract.
- **[minor·prose] Related work** — The sentence describing external excess length as “the additional length associated with learning the score distribution” omits the trial-sampling contribution that the external-log theorem explicitly bounds below.
  - *Fix:* Describe the criterion as excess length beyond the population sharp interval from estimation with both released trial rows and the independent score log.
- **[minor·structure] Inference with an independent score log** — The “External projection confidence interval” is presented as an algorithm, yet its stated candidate set is a countably infinite rational sieve followed by closure and convexification. The manuscript does not explain how a reader would compute its endpoints to a specified tolerance.
  - *Fix:* Present it explicitly as a mathematical confidence construction and explain the role of the sieve in the proof; reserve computational claims for a specified finite approximation.
- **[minor·citation] Proofs and verification scope** — The source attribution at the fixed-law lemma's use gives FanShermanShum2014 without the theorem and equation locators supplied elsewhere; the related-work description of Fan et al.'s conditional-transport result likewise lacks its available section locator.
  - *Fix:* Use the precise published theorem, equation, and section locators at those local uses.

## Questions for authors
- Is the rational-sieve projection intended as an existence construction, or do you plan to provide a finite computational procedure?
- Which closest result do you view as the primary benchmark for the known-score honest-length theorem, and how do its observation scheme and conditions compare?
