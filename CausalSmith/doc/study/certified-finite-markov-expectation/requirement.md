# Substrate requirement: certified-finite-markov-expectation

## Goal
Build reusable Lean substrate for certified expectations of finite-state Markov chains whose transition entries are enclosed by rational intervals.

## Provides (API contract)
- A sound rational enclosure interface for the standard normal CDF at rational endpoints, suitable for certifying transition probabilities formed as differences of CDF values.
- The normal-CDF checker must scale to caller-supplied cells of width `1e-12` at rational endpoints with absolute value up to `193/5`; it must not use a uniform mesh whose node count is proportional to the reciprocal target width.
- Sound matrix/vector interval operations for finite stochastic matrices and reward vectors.
- A generic theorem combining a checked finite iterate or recurrence certificate with a quantitative contraction or minorization bound to enclose a stationary distribution and its stationary reward expectation.
- A comparison theorem for two policy kernels that turns certified stationary-expectation enclosures into a certified strict bias inequality.

## Statement / milestones
For a finite state type, a stochastic transition kernel, a bounded reward vector, explicit rational interval certificates for all entries, and a checked exact rational finite-iterate recurrence, prove that a supplied contraction or minorization coefficient yields a rigorous interval containing the stationary reward expectation. For two such kernels, prove that disjoint certified expectation intervals imply the corresponding strict expectation or bias comparison.

The verifier must check explicit rational endpoint tables and exact integer/rational recurrence data supplied by a caller. Normal-CDF endpoint bounds must be justified inside Lean; generated decimals or unverified external computations are not certificates.

For normal-CDF certificates, provide a proof-producing scalable route using symmetry, a rational alternating or power-series integral enclosure on a bounded central range with an exact remainder bound (and range splitting or argument reduction where needed), and a Mills-ratio tail enclosure for `|x| > 8`. The tail certificate must reduce to finite exponential-series checks and rational bounds for `1 / sqrt (2 * pi)`. Its verification cost should be polynomial or logarithmic in the requested precision rather than enumerating `O(1 / epsilon)` quadrature cells.

## Standard reference
Standard finite-state Markov-chain contraction/minorization theory, interval arithmetic, and rigorous enclosure methods for the Gaussian error function/CDF. The result is infrastructure rather than a new probabilistic rate theorem.

## Intended reuse
Finite-state causal and sequential-decision examples needing kernel probabilities built from Gaussian threshold differences and machine-checkable stationary expectation comparisons. The immediate consumer is `insulinGrid_bias_certificate` in the `stat_pomdp_latent_overlap_minimax` research run, but every declaration must remain generic in the finite state type and independent of that paper's model.

## May assume / must derive
May assume caller-supplied rational endpoints, rational enclosure values, exact integer/rational matrices and recurrence vectors, stochasticity certificates, bounded rewards, and an explicit contraction or minorization bound. Must derive soundness of the normal-CDF enclosures—including the central-series remainder, symmetry transport, Mills-tail bound, exponential enclosure, and rational normalization constant—sound interval propagation through matrix/vector operations, the finite-iterate-to-stationary error bound, the stationary expectation enclosure, and the strict comparison rule.

## Non-goals (optional)
Do not generate the caller's endpoint table, transition matrices, recurrence vectors, or final paper-specific bias expression. Do not trust floating-point values, external computation, or paper-specific axioms. Do not import any CausalSmith research module. Do not treat the existing uniform-mesh quadrature interface as sufficient for high-precision normal-CDF cells; retain it only as an optional coarse fallback.

## Known building blocks (optional)
Reuse Causalean's certified rational arithmetic and scalar exponential enclosure facilities where applicable, plus Mathlib's finite sums, matrices, probability kernels, standard normal distribution, and total-variation/contraction results.
