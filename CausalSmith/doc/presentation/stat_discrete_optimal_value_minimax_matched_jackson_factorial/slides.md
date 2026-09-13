# Minimax Estimation of Optimal Treatment Values

With \(n\) observations and \(d\) discrete covariate cells, an explicit estimator attains the finite-sample minimax squared-risk order \(\min\{1,d/[n\log(ed)]\}\) under fixed overlap.

---

## Overview

For \(\epsilon\), the fixed overlap parameter, the minimax squared risk has order \(\min\{1,d/[n\log(ed)]\}\).

- The characterization covers binary treatments and outcomes, arbitrary cell masses, unequal propensities, and exact treatment-effect ties.
- A Jackson factorial estimator attains the upper bound.
- An embedded two-sample \(L_1\) problem supplies the matching converse.
- The same frontier applies to the identified causal optimal-treatment value.

---

## Motivation

Consider a clinic choosing between two treatments within each of \(d\) diagnostic risk groups.

- The outcome is binary recovery.
- Each patient receives the treatment with the higher conditional recovery probability in that group.
- The target is the population recovery rate attained by these group-specific choices.
- A rich classification system creates many rare groups, even when the total sample is large.
- How accurately can we estimate the value of the optimal treatment choices?

---

## Research question

The value takes the larger of two estimated outcome means in every cell.

- At a treatment-effect tie, the maximum has an absolute-value cusp.
- Sampling noise then creates upward bias in the cellwise plug-in maximum.
- With many rare cells, these local errors accumulate across the alphabet.
- Fixed overlap supplies observations from both arms but leaves the tie-induced difficulty intact.
- What is the best possible worst-case squared error?

---

## Setup

We observe independent triples \(O_i=(X_i,A_i,Y_i)\).

- \(X_i\) is one of \(d\) covariate categories.
- \(A_i\) and \(Y_i\) are binary treatment and outcome indicators.
- Cell \(x\) has mass \(p_x\), treatment propensity \(\pi_x\), and arm means \(\mu_{0x},\mu_{1x}\).
- The target \(\Psi(\mathbb P)\), the observed-law optimal value, averages \(\max_a\mu_{ax}\) using the cell masses.
- Risk is worst-case mean-squared error over all observed laws satisfying fixed overlap.

---

## Assumptions

- The \(n\) observed triples are independent and identically distributed.
- Consistency links the observed outcome to \(Y(a)\), the potential outcome under the received arm.
- Conditional exchangeability makes treatment independent of each potential outcome given the covariate cell.
- Fixed overlap keeps both treatment arms represented in every occupied cell.

@formal ass:fixed-overlap

---

## Identification

@informal prop:identification-and-extension: For \(d\ge2\) under fixed overlap, the observed optimal value is a sum of globally Lipschitz cell contributions, and every admissible observed law has a consistent, conditionally exchangeable causal completion.

@informal prop:causal-optimal-value-corollary: Under consistency, conditional exchangeability, and fixed overlap, the causal optimal-treatment value equals the observed-law optimal-regression value.

For the clinic, each cell contribution is its population share times the better arm’s recovery probability.

---

## Related literature

- Robins (1986) and Rosenbaum and Rubin (1983) provide the causal identification foundations.
- Manski (2004), Murphy (2003), Kitagawa and Tetenov (2018), and Athey and Wager (2021) study treatment rules, welfare, and policy learning.
- Hirano and Porter (2012) and Luedtke and van der Laan (2016) analyze nonregular optimal-value inference.
- Cai and Low (2011), Jiao et al. (2015), and Jiao et al. (2018) develop approximation and moment-matching methods for nonsmooth functionals.
- Jiao et al. (2018) settle the two-sample \(L_1\) distance with matching \(d/[n\log(en)]\) bounds; we transfer their converse through an equal-propensity embedding and build the estimator side here.
- Zeng et al. (2024) give \(d^2/n^2+1/n\) upper and \(d^2/[n^2\log^2 n]+1/n\) lower rates for a linear treatment mean over a discrete alphabet; the cellwise maximum changes the frontier to \(\min\{1,d/[n\log(ed)]\}\).
- We connect these strands by characterizing the finite-sample minimax risk of the scalar optimal value over a growing categorical alphabet.

---

## Key idea

The direct plug-in estimator becomes unreliable when many cells are sparse and their treatment means are nearly tied.

- Pilot counts locate each cell’s four treatment–outcome probabilities at their own noise scale.
- A local Jackson polynomial replaces the maximum’s cusp by a degree proportional to \(\log(ed)\).
- Centered factorial moments estimate the polynomial’s monomials without plug-in ratio bias.
- Clipping controls rare pilot failures and unstable high-degree terms.
- The logarithmic polynomial degree reduces the accumulated nonsmooth error to the \(d/[n\log(ed)]\) scale.

---

## Estimator

@figure jackson-factorial-pipeline: Boxes labeled “Observed treatment–outcome counts,” “Independent pilot and evaluation counts,” “Pilot-local rectangles,” “Jackson polynomial,” “Factorial-moment cell estimates,” “Clipped aggregate,” and “All-data estimator,” connected by left-to-right arrows.

- Small alphabets use the empirical-ratio estimator.
- Pilot counts determine a local rectangle for each cell’s four atom probabilities.
- Evaluation counts lift the local polynomial through centered factorial moments.
- Cell estimates are clipped, summed, and projected to the value range.
- Rao–Blackwellization averages over the auxiliary split and returns an estimator based on all \(n\) observations.

---

## Upper bound

@informal thm:jackson-factorial-upper: Under i.i.d. sampling and fixed overlap, the Jackson factorial estimator has squared risk at most \(C_\epsilon\min\{1,d/[n\log(ed)]\}\) uniformly over every \(n\ge1\), \(d\ge2\), and admissible observed law.

The guarantee includes unknown unequal propensities, rare or null cells, boundary outcome means, and exact ties.

In the clinic example, the same estimator covers highly imbalanced risk-group frequencies as long as both treatments retain fixed overlap within occupied groups.

---

## Lower bound

@informal prop:equal-propensity-l1-reduction: Under i.i.d. sampling and fixed overlap, an equal-propensity submodel makes the optimal value equal to one half plus one quarter of a two-sample \(L_1\) distance and transfers at least one sixteenth of its minimax squared risk.

@figure l1-lower-bound: Boxes labeled “Two unknown categorical distributions,” “Equal-propensity treatment table,” “Optimal value containing \(L_1\) distance,” and “Minimax lower bound,” connected by left-to-right arrows.

@informal thm:all-estimator-lower: Under i.i.d. sampling and fixed overlap, every estimator has worst-case squared error at least \(c_\epsilon\min\{1,d/[n\log(ed)]\}\).

How can two observational worlds have separated optimal values while remaining statistically difficult to distinguish?

---

## Proof sketch

- Construct equal-mass cells with propensity \(1/2\) and small treatment-effect contrasts around exact ties.
- Choose two symmetric contrast priors whose moments agree through logarithmic degree but whose average absolute contrasts differ.
- Poissonized cell counts have nearly identical mixtures because their likelihood expansions agree through the matched moments.
- The optimal values remain separated because the cellwise maximum depends on the absolute contrast.
- A testing argument converts this separation into the \(d/[n\log(ed)]\) lower bound, with a constant bound in the saturated regime.

---

## Main result

The explicit estimator’s upper bound and the all-estimator converse meet over the full fixed-overlap class.

@formal thm:matched-minimax-frontier

Thus the observed-law and causal-completion formulations have exactly the same finite-sample minimax order.

---

## Implications

Let \(d_n\) denote the covariate-alphabet size at sample size \(n\).

@informal thm:consistency-and-parametric-boundaries: For fixed overlap, both observed and causal minimax risks converge to zero exactly when \(d_n=o\{n\log(en)\}\), and they have the parametric \(n^{-1}\) order exactly when \(d_n=O(1)\).

- Bounded alphabets recover the usual parametric squared-risk scale.
- Growing alphabets remain uniformly learnable throughout the stated consistency region.
- In the clinic example, increasingly refined risk groups preserve uniform consistency when their number satisfies \(d_n=o\{n\log(en)\}\).

---

## Additional result

@informal prop:parent-reduction: With universal estimator tuning, the predecessor risk bracket remains valid, the Jackson factorial estimator equals the empirical-ratio estimator for \(2\le d<D_0\), and bounded-alphabet sequences attain the \(n^{-1}\) minimax scale.

This comparison anchors the construction to the familiar cellwise estimator at small \(d\).

---

## Conclusion

- The optimal-treatment value is a nonsmooth large-alphabet functional generated by cellwise treatment-effect ties.
- Its finite-sample minimax squared risk is of order \(\min\{1,d/[n\log(ed)]\}\) under fixed overlap.
- The Jackson factorial estimator attains this order using local approximation and unbiased polynomial lifting.
- Equal-propensity \(L_1\) embeddings and moment matching establish optimality over all estimators.
- The result yields exact consistency and parametric-rate boundaries for both observed and causal formulations.
- The rate characterization is uniform over all \(n\ge1\) and \(d\ge2\), with constants depending on fixed overlap.
