# Referee review

**Recommendation:** major_revision
**Overall score:** 7.1/10 — The verified identification and label-design results are substantial, but the information structure, comparison with close work, and presentation of the external-log procedure need substantial revision.

The paper characterizes sharp ATE ambiguity from deterministic score labels, derives optimal label-budget rates and a high-resolution constant, and establishes honest interval rates for known scores and an independent score log. These are meaningful theoretical contributions. The manuscript needs a clearer account of when the score law is known, a more direct comparison with competing coarsening results, and a more accessible presentation of its inference construction.

## Strengths
- The exact ambiguity formula and common released law attaining it give the label-design problem a sharp causal interpretation, including for atoms and disconnected cells.
- The inverse-budget bounds and high-resolution constant connect identification to an explicit allocation rule.
- The inference results state distinct criteria for known-score length and external-log excess length, with separate sampling lower bounds.

## Findings
- **[major·prose] Trial setup and the sharp identified interval** — The setup says “A known score law H ... determine[s] the released label” and describes the score-marginal condition as a known-marginal condition. In the external-log experiment, H is learned from sampled scores. This makes the information available to the analyst appear inconsistent across the paper.
  - *Fix:* Introduce H as the population score law. State explicitly that it is known to the analyst in the identification, design, and known-score inference experiments, while the external-log experiment observes an independent sample from H.
- **[major·citation] Related work** — The comparison with coarse inverse weighting describes the competing estimator and conditions but omits its stated error rate; the quantization discussion gives little account of which part of the high-resolution result follows established companding ideas. These are the closest comparisons for assessing the contribution.
  - *Fix:* Compare the Kalavasis–Mehrotra–Zampetakis rate and its score-error conditions directly with the paper’s inverse-label-budget ambiguity and honest-length rates. Situate the paired distortion and its constant against the cited high-resolution quantization literature, with precise locators and a clear account of the additional causal-design step.
- **[major·other] Inference with an independent score log** — The countable rational sieve defines a measurable projection interval, while the text says computing its endpoints to a prescribed tolerance requires a finite truncation and optimization scheme. Readers seeking to use the stated interval have no finite procedure or error control for approximating it.
  - *Fix:* Give a finite approximation algorithm and bounds connecting its optimization tolerance to coverage and excess length, including atomic score laws and measurable label cells.
- **[major·structure] global** — The main line of argument is obscured by the number of displayed formal objects and by the full sieve specification before the external-log rate theorem. A reader must work through extensive notation before seeing how the ambiguity formula or projection behaves in a simple release.
  - *Fix:* Add a small worked score-cell example and a compact comparison of the paper’s three criteria: sharp width, known-score expected length, and external-log excess length. Move the rational coding details to the appendix while retaining the empirical measures, confidence balls, and resulting interval in the main text.
- **[minor·statement] Honest intervals with a known score law** — The displayed definitions of uniformly honest procedures and minimax length write P^{\otimes n} for probabilities and expectations of released-row samples, although P denotes a law on full rows. The verified definition uses the product of the released-row law.
  - *Fix:* Replace P^{\otimes n} in those displays with \mathcal L_P(R,A,Y)^{\otimes n}, or define an explicit released-row product-law abbreviation before using it.
- **[minor·structure] Trial setup and the sharp identified interval** — The endpoint definitions use Q_F before the generalized quantile is formally defined. The ATE functional \theta(P) is also introduced formally several sections after its first use.
  - *Fix:* Place the generalized-quantile definition before the endpoint formulas and the ATE-functional definition in the trial setup.
- **[minor·prose] Information retained by a score label** — “For an atomic score law, distinct atoms can therefore receive distinct labels” overlooks the finite label count: an atomic law may have more than J atoms.
  - *Fix:* Qualify the example as a finite-support law with at most J distinct atoms, or state that point identification requires each positive-mass atom to have its own label.
- **[minor·prose] abstract** — “The largest sharp average treatment effect interval attainable across released outcome laws” could mean an interval ordered by inclusion. The defined criterion maximizes interval width.
  - *Fix:* Say “the maximum width of the sharp average treatment effect interval across compatible released outcome laws.”
- **[minor·prose] Proofs and verification scope** — “No finite-budget intervalization claim is used” frames the result through an absent claim outside a permitted limitations or open-questions section. The computational qualification in the external-log section likewise belongs with the open questions.
  - *Fix:* Describe the proved high-resolution lemma affirmatively as an asymptotic result for arbitrary measurable partitions with an attaining sequence of interval cells. Move the computational qualification to Open questions, where its scope can be stated directly.

## Questions for authors
- What finite approximation of the external projection interval can preserve the stated uniform coverage guarantee at a specified numerical tolerance?
- Can the related-work comparison isolate how score-estimation error in coarse inverse weighting differs from ambiguity caused by releasing a fixed number of score labels?
