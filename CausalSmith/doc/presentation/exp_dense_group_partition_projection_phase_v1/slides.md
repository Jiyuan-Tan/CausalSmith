# Random Groups And Finite-Population Variance

For fixed-size random group-formation experiments, we characterize the exact design variance and show when the equal-group CR2 cluster-robust variance statistic tracks the right scale.

---

## Overview

- We study experiments where units are first formed into disjoint groups of a common size, then groups are assigned to treatment or control.
- The estimand is a finite-population average over all possible groups of that size.
- The realized groups are dependent because they are drawn without replacement from the same population.
- We express that dependence exactly using Kneser disjointness geometry.
- The equal-group CR2 statistic estimates the independent-group variance scale.
- The exact variance also contains a finite-population correction when grouped units occupy a positive population fraction.

---

## Motivation

- Think of a peer-effect experiment that forms study groups of size \(M\), the common group size.
- A unit’s outcome can depend on both treatment and the peers in its realized group.
- If many units are grouped, seeing one group removes its members from the pool available to other groups.
- That removal creates dependence across realized group outcomes.
- Standard cluster-robust logic treats groups as the sampling units.
- The design question is what that logic estimates after the groups themselves are randomly formed.

---

## Research question

- We want the exact design variance of the group-level treated-control difference in means.
- The target is the partition-average marginal effect \(\tau_n\), the finite-population average contrast over all possible groups of size \(M\).
- The estimator \(\widehat\tau_n\) compares treated and control realized group means.
- The variance target averages over both random group formation and balanced group treatment assignment.
- What correction is created by drawing disjoint groups from a finite population?

---

## Setup

- The finite population has size \(n\).
- The design draws \(G_n\), the number of realized groups, as pairwise-disjoint groups of common size \(M\).
- The grouped-unit count is \(N_n=MG_n\).
- The treated-group fraction is \(p_n=G_{1n}/G_n\).
- The grouped-unit sampling fraction is \(N_n/n\), with limit \(\rho\).
- In the study-group example, \(\rho\) is the share of students placed into groups.

@figure random-partition-design: Box-and-arrow schematic showing a finite population, a random disjoint grouping step into equal-size groups, a balanced group treatment assignment step, and observed group outcomes.

---

## Assumptions

- The number of realized groups grows.
- The treated-group fraction converges to an interior limit.
- The grouped-unit sampling fraction converges to \(\rho\in[0,1]\), the limiting grouped-unit fraction.
- Potential outcomes are uniformly bounded.
- For ratio statements and lower bounds, the scaled exact variance stays away from zero.

@formal ass:group-count-growth

@formal ass:stable-treatment-fraction

@formal ass:sampling-fraction

@formal ass:bounded-potential-outcomes

---

## Estimand and statistic

- For each treatment arm, \(h_{z,n}(A)\) is the group mean potential outcome for candidate group \(A\).
- The partition-average marginal effect averages \(h_{1,n}(A)-h_{0,n}(A)\) over the uniform slice of possible groups.
- The estimator is the treated-minus-control difference in realized group means.
- The scalar equal-group CR2 statistic is the sum of within-arm group-mean sample variances divided by arm group counts.

@formal def:pame-estimator

@formal def:cr2-statistic

---

## Key idea

- Random disjoint groups are sampled without replacement from the uniform slice.
- The Kneser operator averages a group table over groups disjoint from a given group.
- Johnson degrees decompose a group table into orthogonal finite-population components.
- Disjointness acts diagonally on those components.
- Degree one captures the part of the arm contrast tied to individual units’ marginal participation in groups.

---

## Exact geometry

@informal thm:exact-kneser-identity: Disjoint-group covariance decomposes exactly by Johnson degree, with each degree weighted by its Kneser eigenvalue.

@formal thm:exact-kneser-identity

---

## Exact variance

@informal thm:exact-pame-variance: The group-level difference in means is unbiased, and its exact design variance differs from expected equal-group CR2 by the Kneser covariance of the arm-difference table.

@formal thm:exact-pame-variance

---

## Dense asymptotics

- In dense arrays, \(G_n\) grows while \(N_n/n\) converges to a possibly positive \(\rho\).
- The independent-group scale is \(R_n\).
- The dense correction is governed by \(E_{\tau,1,n}\), the degree-one Johnson energy of the arm-difference table.
- Higher Johnson degrees have a smaller pooled contribution under fixed \(M\) and bounded outcomes.

@informal thm:dense-projection-limit: Under the stated dense-array conditions, \(G_n\sigma_n^2\) is \(R_n-\rho E_{\tau,1,n}\) up to a term that vanishes.

@formal thm:dense-projection-limit

---

## CR2 frontier

- Equal-group CR2 estimates \(R_n/G_n\), the independent-group variance scale.
- The exact variance subtracts the dense correction.
- Thus the one-sided conservativeness statement is a direct consequence of the projection expansion.
- Ratio consistency is characterized by the correction’s size relative to the corrected variance scale.

@informal thm:cr2-phase-frontier: Under the dense bounded schedule class, CR2 is asymptotically conservative in the stated one-sided probability sense and is ratio-consistent exactly when the dense correction is negligible.

@formal thm:cr2-phase-frontier

---

## Sparse regime

- When \(\rho=0\), the first-order finite-population correction vanishes at the variance-ratio scale.
- This covers regimes where the grouped population share goes to zero.
- The named benchmark is \(N_n=M\lfloor n^{3/4}/M\rfloor\), for which \(N_n/n\to0\) while \(N_n^2/n\to\infty\).
- The study-group interpretation is that the grouped share becomes small, even if the number of realized groups grows quickly.

@informal thm:sparse-beyond-birthday: For fixed \(M\), zero limiting grouped-unit fraction gives CR2 ratio consistency, including the stated birthday-count benchmark.

@formal thm:sparse-beyond-birthday

---

## Related literature

- The design-based foundation follows Splawa-Neyman et al. (1990), Fisher (1935), Cox (1958), Rubin (1974), and Holland (1986).
- The triangular-array and finite-population asymptotic language follows Hajek (1960), Cochran (1977), Ohlsson (1989), Fuller (2009), and Li and Ding (2017).
- The Johnson and Kneser tools come from Delsarte (1973), Brouwer et al. (1989), Filmus (2016), and Brouwer et al. (2018).
- CR2 connects to White (1980), Liang and Zeger (1986), Bell and McCaffrey (2002), Pustejovsky and Tipton (2018), and Abadie et al. (2023).
- The closest theorem-level comparison is Fu et al. (2026), where sparse whole-tuple conditions deliver CR2 ratio consistency.

---

## Software and witness

- The scalar statistic we analyze is the treatment-coordinate entry from a versioned equal-group `clubSandwich` CR2 calculation.
- The software identity ties the finite-population target to the regression workflow used in practice.
- The eight-unit witness gives a finite balanced design where exact variance and expected CR2 can be computed directly.
- In that witness, the exact variance is \(1/7\) and expected CR2 is \(2/7\).

@informal prop:clubsandwich-consumer: For the stated unweighted intercept-plus-treatment regression and versioned software call, the treatment-coordinate CR2 entry equals the scalar equal-group CR2 statistic.

@informal prop:eight-unit-witness: In the balanced eight-unit witness, the exact variance is \(1/7\) and the expected equal-group CR2 statistic is \(2/7\).

---

## Lower-bound intuition

- The lower bound compares two randomized schedule priors.
- In the same-sign prior, a unit carries the same sign across arms.
- In the independent-sign prior, a unit’s signs are drawn separately by arm.
- A single realization reveals only the assigned-arm outcomes.
- The observed-data mixture is the same for every statistic, while the exact variance limits separate when \(\rho>0\).

@figure rademacher-mixture: Box-and-arrow schematic showing same-sign schedules and independent-sign schedules flowing into the same one-realization observation law, while their scaled exact variances point to two separated limits.

---

## Lower bound

@informal prop:rademacher-mixture-separation: At positive limiting grouped-unit fraction, the two Rademacher mixtures have equal one-realization expectations for every statistic while their scaled exact-variance limits differ by \(2\rho/M\).

@informal thm:qv-diagonal-impossibility: For the dense bounded schedule class, every measurable one-realization variance statistic has nonvanishing worst-case relative error with probability at least one half in the stated limit sense.

@formal thm:qv-diagonal-impossibility

---

## Conclusion

- We give exact finite-sample variance identities for homogeneous random group formation.
- The Kneser covariance decomposition identifies the design dependence created by disjoint groups.
- The dense asymptotic expansion isolates \(\rho E_{\tau,1,n}\) as the first-order correction to the independent-group scale.
- Equal-group CR2 estimates that independent-group scale and is ratio-consistent precisely under the stated correction criterion.
- At positive density, the lower bound explains why one realized grouping cannot uniformly recover the exact variance ratio over the full bounded schedule class.
