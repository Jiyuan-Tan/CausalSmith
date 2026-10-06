# Referee review

**Recommendation:** major_revision
**Overall score:** 7.3/10 — The verified matched rate is a substantial contribution, but the central statistical mechanism needs a clearer explanation before the paper is ready for a leading journal.

The paper establishes a finite-sample minimax rate for estimating the population treatment-value curve over symmetric budget intervals, including the full range of capacities. A dual representation supports a simultaneous upper bound, while a capacity-active family yields the matching lower bound at half capacity. The claims largely track the verified results, but the main text gives too little intuition for the estimator and its logarithmic rate gain.

## Strengths
- The matched bound covers every stated sample size and alphabet size, including null cells, ties, and boundary outcome means.
- The half-capacity lower-bound family isolates allocation difficulty while fixing the full-capacity value.
- The paper identifies the published lower-bound input and states its formalization scope at the affected results.

## Findings
- **[major·structure] Minimax risk for the budget-value curve** — The main text names pilot localization, Jackson approximation, and factorial moments but gives little explanation of how they produce the logarithmic improvement or control all shadow prices. Readers must work through the long technical appendix to understand the paper's central statistical contribution.
  - *Fix:* Add a concise explanation of the approximation, bias, and fluctuation scales across the estimator's regimes, and use a small paired-cell example to show why half-capacity value depends on benefit ranking.
- **[minor·prose] Related work; minimax risk for the budget-value curve; discussion** — Ordinary prose uses contribution-by-negation, including “it does not impose a regular-value condition” and “simultaneous curve estimation incurs no additional rate cost.”
  - *Fix:* State the positive scope directly: the class permits positive-mass ties, and simultaneous curve estimation attains the unrestricted scalar minimax order under the stated conditions.
- **[minor·statement] Setup and assumptions** — The cell-mean definition displays a conditional expectation for every cell, while the zero representative for null cells appears only afterward.
  - *Fix:* State the occupied-cell condition and zero convention within the definition so the symbol is well specified at first use.
- **[minor·statement] Process estimates** — The notation for the uniform process handle is indexed by sample and alphabet size, although membership requires one constant to satisfy the bounds simultaneously across all eligible sizes.
  - *Fix:* Use notation reflecting the fixed overlap parameter, or explicitly explain that the indexed notation denotes a single uniform criterion.
- **[minor·citation] Related work** — Several substantive comparisons rely on citations located only to an abstract, particularly the characterization of Qini-curve inference.
  - *Fix:* Replace abstract locators with the relevant sections or results, and specify the pointwise scope of the cited Qini inference.
- **[minor·prose] Introduction** — The sentence attributing the factor-one transfer of process error to the uniform upper-bound theorem points readers away from the proposition that states the contraction.
  - *Fix:* Cite the dual-representation proposition for the factor-one contraction and the upper-bound theorem for the estimator's risk guarantee.

## Questions for authors
- Can the exact conditional average be evaluated from observed contingency counts without enumerating all permutations and markings, and what computational cost would that require?
