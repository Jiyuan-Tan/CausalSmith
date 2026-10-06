# Referee review

**Recommendation:** minor_revision
**Overall score:** 7.5/10 — The paper delivers a useful uniform functional-stability result and a matched minimax characterization, with remaining revisions concentrated on positioning, organization, and notation.

The paper establishes minimax mean-squared-error order T^{-1} for stationary policy evaluation in a fixed binary POMDP experiment under known observed-state randomized policies, bounded action ratios, stationary sampling, and contraction of both policy kernels. Its central contribution is a uniform stationary-value modulus based on seven intervention moments, including across reduced-rank realizations. The verified results support the principal prose claims, and the manuscript carefully distinguishes candidate counts from runtime guarantees and identifies its external comparison dependency. Publication is warranted after focused revisions that sharpen the closest methodological comparisons and streamline the exposition.

## Strengths
- The uniform stationary-value modulus establishes functional stability across reduced-rank and repeated-root realizations.
- The observable intervention moments, stable-grid upper bound, and observed-data testing pair form a coherent matched minimax argument.
- The manuscript consistently states the fixed-parameter, fixed-alphabet scope and correctly extends the rate characterization to stationary-overlap subclasses.
- The early related-work section discusses competitors' estimands, sampling schemes, conditions, and rates.
- The computational discussion faithfully identifies the verified O(T^{19}) guarantee as a candidate-list bound.

## Findings
- **[minor·citation] Related work** — The realization-theoretic positioning emphasizes observable-sequence learning and latent-parameter estimation. Observable-value approaches such as Uehara et al. (2023) and Zhang et al. (2024) provide a closer comparison for the paper's scalar-functional contribution and deserve direct engagement.
  - *Fix:* Add a concise comparison with the future-dependent value result in Uehara et al. (2023, Theorem 3) and the observable-value coverage result in Zhang et al. (2024, Theorem 7). Establish their precise estimands, sampling conditions, and stability or coverage requirements, then identify the contribution of uniform stationary-value control across reduced-rank contracting realizations.
- **[minor·structure] Main results** — The fixed binary minimax theorem combines the core risk characterization, detailed testing-pair properties, and lengthy externally sourced reset-family clauses. This organization obscures the central result and the different evidentiary roles of its components.
  - *Fix:* Organize the existing theorem into clearly identified blocks for the binary risk bound, testing-pair properties, and cited cardinality comparison. Give the risk characterization visual priority and explicitly associate the comparator block with its source, while preserving all conditions and the theorem-local formalization disclosure.
- **[minor·prose] Global** — The seven-moment mechanism, degree-six comparison polynomial, sampling controls, and candidate-count interpretation receive substantially overlapping explanations in the introduction, main results, discussion, and both proof appendices. The repetition dilutes an otherwise clear argument.
  - *Fix:* Assign each location a distinct purpose: motivation in the introduction, a compact argument roadmap beside the results, parameter and statistical implications in the discussion, and technical details in the appendices. Compress the appendix's repeated result summaries and routine arithmetic explanations while retaining a self-contained mathematical argument and the verification disclosures.
- **[minor·prose] Discussion** — The discussion emphasizes the parametric exponent, while the displayed upper-bound multiplier B_alpha^2(112V_{alpha,L}+2) determines the finite-sample scale and can be large under slow contraction or substantial action reweighting.
  - *Fix:* Add a short interpretation of the explicit multiplier, including the horizon at which the displayed guarantee improves on the unit squared-loss bound. Explain how contraction and action overlap affect that threshold, and retain the fixed-parameter qualification when interpreting the rate.
- **[minor·statement] Main results — Minimax risk definition** — The display uses the random observed vector as the domain in '\widetilde\theta\colon \mathsf O_T\to[0,1]' and expresses measurability through '\sigma(\mathsf O_T,b,e,t_0,\zeta)'. The supplied policies vary across experiments, so the intended family of observed-data maps deserves a precise domain and indexing convention.
  - *Fix:* Define the observed sample space explicitly and write estimators as maps indexed by the supplied policies and fixed regime parameters. State measurability in the trajectory argument for each supplied policy pair, matching the estimator convention in the verification contract.
- **[minor·citation] Introduction, related work, and main results** — The nonarchival comparator receives varying locators: 'Theorem 1', 'Main minimax theorem', 'signed-depth lower-bound construction', and 'reset-chain lower-bound construction'. A source conclusion used inside the main theorem should have a consistent, reader-resolvable locator.
  - *Fix:* Check the cited manuscript's exact theorem and construction numbering and standardize the ordinary citations accordingly. Identify the version and stable public location in the bibliography, while preserving the required generated theorem-local formalization-scope footnote.

## Questions for authors
- What motivates the binary specialization scientifically, given that the argument's central organizing feature is fixed joint-state dimension?
- Which observable-value results provide the closest comparison for uniform stability across reduced-rank realizations under the stated contraction conditions?

