# One Intervention per Latent Variable

Under smooth invertible observations, compact overlap, causal minimality, and fixed intervention-sign strata, one perfect intervention per scalar latent variable recovers the latent DAG, target alignment, and representation up to relabeling and componentwise smooth coordinate changes.

---

## Overview

- We observe an observational environment and \(n\) interventional environments.
- Each intervention perfectly replaces one scalar latent mechanism.
- The intervention targets are unknown.
- The observations are nonlinear mixtures of the latent variables through one shared diffeomorphism.
- We use likelihood-ratio laws across environments to recover ancestry, ranks, target labels, and parents.

---

## Motivation

- Econometric environments often shift one latent structural component at a time.
- The analyst sees high-dimensional observables, not the structural variables.
- The labels of the shifted components may be unknown.
- The central question is whether one shifted environment per latent variable carries enough information for nonlinear causal representation learning.
- Our answer is affirmative on a smooth compact-support regime with generic ratio-law separation.

---

## Setup

- \(V=(V_1,\ldots,V_n)\) is the scalar latent causal vector on a DAG \(G\).
- \(X=f(V)\) is observed through the same smooth invertible map in every environment.
- \(P^0\) is observational; \(P^1,\ldots,P^n\) are single-target intervention laws.
- \(\pi\), the unknown target permutation, maps environment labels to latent targets.
- \(R_i=dP^i/dP^0\), the likelihood ratio for environment \(i\), is the observable one-dimensional coordinate we compare.

@formal ass:shared-diffeomorphic-mixing

---

## Intervention design

- A perfect intervention replaces the target conditional density by a parent-independent density.
- In latent coordinates, the ratio for environment \(e\) depends on the target \(\pi(e)\) and its parents.
- The ratio therefore carries local graph information through its distribution across environments.

@formal ass:one-perfect-intervention-per-node

---

## Assumptions

- Smooth positive mechanisms give common compact support and well-defined ratios.
- Fixed own-coordinate derivative signs make each target ratio monotone in its own latent coordinate.
- Causal minimality makes every graph parent statistically active under the observational law.
- These conditions define the fixed-sign model stratum \(\Theta_{G,s}\).

@formal ass:fixed-own-derivative-sign

---

## Key idea

- Compare the law of \(R_i\) under \(P^0\) with its law under each \(P^j\).
- If intervening on \(j\) changes the law of \(R_i\), draw \(j\to i\) in the ratio-discrepancy graph.
- Gaussian maximum mean discrepancy makes this comparison observable from one-dimensional ratio samples.
- A positive discrepancy reveals ancestral information after the target permutation.

@figure ratio-discrepancy-pipeline: Box-and-arrow schematic showing observed environment laws feeding likelihood ratios, likelihood ratios feeding Gaussian MMD comparisons, comparisons feeding a ratio-discrepancy graph, and the graph feeding rank decoding.

---

## Generic separation

@informal prop:sparse-witness-certificate: A smooth three-node separating witness has strictly positive direct-edge ratio discrepancy, while a smooth cancellation witness has zero discrepancy on the same edge.

- The witness pair shows both strict separation and exact cancellation inside regular mechanisms.
- Analytic perturbations move mechanisms away from the cancellation boundary.
- This supports a topological genericity statement in each fixed-sign stratum.

@informal thm:generic-cover-separation: In every nonempty fixed-sign causal-minimal stratum, Gaussian ratio-law separation of transported ancestral covers holds on an open dense set.

---

## Decoder

- Build \(H_D=\{j\to i:j\ne i\text{ and }D_{ji}>0\}\), the observable ratio-discrepancy graph.
- Choose a topological order of \(H_D\).
- For each node, condition its log-ratio on earlier log-ratios.
- Convert the conditional log-ratio into a rank coordinate.
- Prune parents by conditional independence under the observational law.

@formal def:population-decoder

---

## Main result

@informal thm:exact-ratio-decoder: Under the stated smoothness and separation conditions, the decoder recovers the transported DAG, target alignment, and latent coordinates up to allowed componentwise changes.

- The ratio graph gives the ancestral order.
- Conditional ranks recover monotone transforms of the intervened latent variables.
- Conditional-independence pruning turns ancestry into exact parents.
- The recovered graph is the environment-label DAG \(G^\pi\).

---

## Comparison

- von Kügelgen et al. (2023) identify the bivariate unknown-target case from one perfect intervention per node under a law-separation condition.
- In arbitrary dimension, their paired-intervention theorem uses two perfect interventions per node.
- On the overlapping positive \(C^3\) compact-cube faithful regime, our ratio-law route gives one perfect intervention per node in every dimension.
- Wendong et al. (2023) and Yao et al. (2025) use supplied graph, order, or target-alignment inputs; here the ratio laws recover those objects.

---

## Why ranks work

- The fixed-sign condition makes the target log-ratio monotone in its own latent coordinate.
- Once earlier ratio coordinates encode predecessor information, conditioning removes parent variation.
- The conditional distribution transform maps the target log-ratio to the intervention distribution rank.
- Thus \(U_i\) agrees with a monotone transform of \(V_{\pi(i)}\).
- This converts an observed likelihood-ratio object into a latent coordinate.

---

## Why parents prune exactly

- The ratio graph may contain ancestral arrows rather than parent arrows.
- After rank recovery, the \(U_i\)'s behave like componentwise transforms of the latent variables.
- Under causal minimality and positivity, conditioning on the true parents screens off earlier nonparents.
- Any missing parent leaves a conditional dependence.
- The unique minimal admissible predecessor set is therefore the transported parent set.

---

## Confidence edges

- The finite-sample layer splits data into training and evaluation folds.
- Training folds estimate ratios \(\widehat R_i\).
- Independent evaluation folds compute empirical Gaussian-MMD discrepancies \(\widehat D_{ji}\).
- Thresholding \(\widehat D_{ji}\) by \(\varepsilon_N(\alpha,\eta)\) gives confidence edges for ancestry.

@formal def:sample-split-confidence-graph

---

## Statistical guarantee

@informal thm:simultaneous-confidence-edges: Conditional on a simultaneous first-stage \(L^1\) ratio-error event, the sample-split MMD event holds with probability at least \(1-\alpha\), selected arrows are true transported ancestral discoveries, and separated ancestral covers recover the transported transitive closure.

- The guarantee is simultaneous over all ordered pairs.
- Marginally, the MMD event has probability at least \(1-\alpha-\eta\).
- When every transported ancestral cover clears the stated radius, the confidence graph recovers the same transitive closure as the population decoder.

---

## Future work

- The next statistical target is coordinate uncertainty for the recovered rank variables.
- The bounded Hölder subclass records smoothness, support, margin, geometry, regularity, and design envelopes.
- The proposed handle adapts local-linear conditional-CDF estimation to generated log-ratio responses and generated conditioning covariates.
- The frontier rate is stated as a uniform generated-rank target on compact interior sets.

@informal oeq:generated-rank-frontier: Under the stated first-stage contract and bandwidth scale, the target is a cross-fitted generated-rank estimator with sup-norm error at most \(r_N\) uniformly over the bounded Hölder subclass.

---

## Conclusion

- One unknown-target perfect intervention per scalar latent variable can identify nonlinear causal representations in the fixed-sign compact-support regime.
- Generic Gaussian ratio-law separation supplies the observable ancestral order.
- Conditional ranks align intervention labels with latent coordinates.
- Observational conditional independence prunes ancestry to the exact transported DAG.
- Sample splitting adds simultaneous confidence edges for ancestral discoveries under a first-stage ratio-error contract.
