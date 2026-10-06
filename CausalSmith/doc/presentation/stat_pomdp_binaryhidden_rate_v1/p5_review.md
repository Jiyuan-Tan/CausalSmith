# Referee review

**Recommendation:** minor_revision
**Overall score:** 7.7/10 — The submission establishes a substantial and carefully scoped functional-stability result and matching minimax rate, with remaining weaknesses concentrated in organization and notation.

The paper characterizes stationary policy evaluation from one behavior trajectory in a fixed binary partially observed experiment under known observed-state policies, action overlap, and contraction. Its central contribution combines seven observable intervention moments with uniform stationary-value stability across reduced-rank four-state realizations to establish matched T^{-1} mean-squared-error bounds. Taking the verified results as established, the manuscript largely represents their scope faithfully and engages the closest literature carefully. Publication would benefit from a more focused presentation and clearer minimax quantification.

## Strengths
- Uniform stability of the stationary reward across reduced-rank realizations gives the rate characterization substantive content beyond regular latent-parameter estimation.
- The estimator and testing pair operate within the same explicitly defined observed-data experiment.
- The manuscript carefully distinguishes fixed hidden cardinality from the growing-cardinality comparison classes.
- Related work discusses competitors' estimands, sampling designs, rates, and identification conditions in a dedicated early section.
- The external manuscript dependency and the candidate-count scope receive explicit disclosures.

## Findings
- **[minor·prose] Main results — paragraph preceding the minimax risk definition** — The sentence 'The supremum ranges over the binary experiment class ... with those supplied inputs' suggests that the supremum fixes the behavior and target policies. Elsewhere, the class allows both policies to vary, with each experiment supplying its own pair to an indexed estimator. These are different decision problems.
  - *Fix:* State explicitly that the infimum ranges over families of observed-data procedures indexed by the supplied policies, while the supremum ranges over all admissible kernels, policies, and trajectory laws at fixed regime parameters. Describe evaluation at each experiment's supplied policy pair.
- **[minor·structure] Main results — fixed binary minimax rate; Discussion; appendices** — The central theorem combines the binary risk bound, extensive testing-witness details, and a lengthy externally sourced cardinality comparison. Repeated explanations of the seven moments, contraction mechanism, testing pair, and candidate counts across subsequent sections dilute the main statistical contribution.
  - *Fix:* Present the binary risk characterization prominently, organize the testing witnesses as supporting material, and give the external comparison a separate clearly identified block with its citation and formalization disclosure preserved. Consolidate repeated explanations, retaining one substantive account of each mechanism and using cross-references elsewhere.
- **[minor·prose] Introduction** — The sentence 'this is a candidate-count statement, not a runtime bound' explains the contribution through an absent deliverable outside the limitations section, contrary to the affirmative framing contract.
  - *Fix:* Replace it with an affirmative statement such as 'The proposition quantifies exhaustive search through the number of candidate realizations at fixed mixing scale.' Keep the runtime and precision discussion in Limitations and future work.
- **[minor·statement] Appendix — pair-polynomial identity and value modulus** — The lemma calls all six vectors, including the reward vectors, 'real row vectors,' while the setup and neighboring exposition use rewards as columns in scalar matrix products. The coordinate-sum interpretation resolves the mathematics but leaves conflicting orientation instructions.
  - *Fix:* Describe the objects as real coordinate vectors, explicitly interpreting initial and stationary distributions as rows and reward functions as columns. Preserve the displayed coordinate sums and the verified conclusions.

## Questions for authors
- Is the intended minimax experiment the class-wide problem with policies supplied separately for each experiment? Please make that quantification explicit throughout the risk discussion.

