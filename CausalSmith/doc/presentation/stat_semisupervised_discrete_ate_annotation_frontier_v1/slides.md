# Outcome Annotation for Discrete Treatment Effects

With \(n\) outcome-labeled records and \(m\) extra treatment-covariate records, we characterize the minimax mean-squared risk for finite-alphabet ATE estimation under fixed overlap.

---

## Overview

We study a two-sample causal experiment:

- \(n\) complete records: \((X,A,Y)\).
- \(m\) additional records: \((X,A)\).
- \(X\) takes \(d\) known values.
- \(A\) and \(Y\) are binary.
- The target is the average treatment effect \(\tau(P)\).

The sharp rate is the annotation-frontier rate, with \(N=n+m\) and \(\ell_n=\log(en)\):
\[
r_\epsilon(n,m,d)
:=
\min\!\left\{
1,\frac1n+\frac{d^2}{N^2\ell_n^2}
\right\}.
\]

The first term is outcome-label information; the second is treatment-covariate marginal information.

---

## Motivation

Think of a chart-review study.

- Treatment and baseline covariates are broadly available.
- Outcomes require manual annotation.
- We can label \(n\) outcomes, while \(n+m\) records reveal treatment and covariates.
- The question is how much the unlabeled treatment-covariate records help.

For a discrete covariate adjustment problem, the answer depends on how many cells must be stabilized.

---

## Research question

We ask for the best possible uniform mean-squared error.

- The estimator may use both samples.
- The nuisance functions are unrestricted cell by cell.
- The covariate alphabet is known and finite.
- Occupied cells satisfy fixed overlap.
- The benchmark is minimax risk over the full finite-cell model.

The key question: how do \(n\), \(m\), and \(d\) jointly determine the attainable ATE accuracy?

---

## Setup

The observed record is \((X,A,Y)\).

- \(X\in[d]\) is a finite covariate cell.
- \(A\in\{0,1\}\) is treatment.
- \(Y\in\{0,1\}\) is outcome.
- The covariate cell mass is \(p_x\).
- The treatment propensity in cell \(x\) is \(e_x\).

@formal ass:overlap

In the chart-review example, every occupied covariate cell has both treated and control units represented.

---

## Causal interpretation

We use the usual potential-outcomes link from observed data to the ATE.

@formal ass:consistency

@formal ass:conditional-exchangeability

Under these conditions and overlap, the observed cell-level treated-control contrast identifies the causal contrast inside each covariate cell.

---

## Annotation experiment

The experiment has two independent samples from the same population.

- Labeled sample: \(n\) complete outcome-bearing records.
- Auxiliary sample: \(m\) outcome-unlabeled treatment-covariate records.
- The auxiliary sample sharpens the treatment-covariate table \(P_{XA}\).
- The labeled sample is the source of outcome information.

@figure annotation-pipeline: Box-and-arrow schematic with boxes for population law, labeled records (X,A,Y), auxiliary records (X,A), treatment-covariate table, outcome regressions, and ATE estimate.

---

## Related literature

Potential-outcomes identification follows Rubin (1974), Rosenbaum and Rubin (1983), and Imbens and Rubin (2015).

Semiparametric ATE theory studies regular asymptotic estimation, including Robins et al. (1994), Hahn (1998), Hirano et al. (2003), Bang and Robins (2005), and Chernozhukov et al. (2018).

Semi-supervised treatment-effect work includes Cheng et al. (2021), Chakrabortty and Dai (2024), Kallus and Mao (2025), Hou et al. (2025), and Kato (2025).

The closest discrete-covariate benchmark is Zeng et al. (2026).

---

## Key idea

The ATE has two statistical bottlenecks.

- Outcome regressions require outcome labels.
- Treatment-covariate weights require accurate cell frequencies.
- Auxiliary records improve the second bottleneck through \(n+m\).
- They preserve the first bottleneck at scale \(n\).

The rate separates these two resources rather than merging them into a single sample size.

---

## Known marginal benchmark

If the full treatment-covariate table \(P_{XA}\) is known, the remaining difficulty is outcome learning.

@informal thm:known-marginal-boundary: With the treatment-covariate marginal known, the minimax mean-squared risk is bounded above and below by constants times \(1/n\).

@formal thm:known-marginal-boundary

This is the limiting benchmark for abundant treatment-covariate information.

---

## Estimator

Our estimator splits the data into three roles.

- An outcome block estimates outcome-marked masses.
- A pilot block decides whether a covariate cell is light or heavy.
- A factorial block builds the cell weights.
- Heavy cells use stabilized inverse counts.
- Light cells use a Chebyshev polynomial correction at degree \(L\).
- The final sum is clipped to the natural ATE range.

@figure hybrid-estimator: Box-and-arrow schematic with boxes for labeled sample split, auxiliary sample split, pilot light-heavy decision, light-cell polynomial weights, heavy-cell inverse-count weights, and clipped ATE estimate.

---

## Upper bound

The hybrid estimator attains the annotation-frontier rate uniformly over the overlap class.

@informal thm:uniform-mixed-upper: Under fixed overlap, the hybrid estimator has worst-case mean-squared error at most a constant times \(r_\epsilon(n,m,d)\).

@formal thm:uniform-mixed-upper

Mechanically, polynomial correction improves sparse-cell weighting, while inverse counts handle cells with enough treatment-covariate mass.

---

## Converse

The lower bound uses two priors with the same random \(P_{XA}\) table.

- Both branches generate the same treatment-covariate marginal information.
- They differ in rare-cell outcome regressions.
- The auxiliary sample therefore sees the same marginal table distribution.
- Distinguishing the branches requires outcome labels.

@informal thm:common-marginal-converse: Under fixed overlap, the minimax risk is at least a constant times the annotation-frontier rate.

@formal thm:common-marginal-converse

---

## Main result

The upper and lower bounds match up to constants depending on \(\epsilon\).

@informal thm:sharp-annotation-frontier: For fixed overlap, the minimax risk is bracketed by constants times \(r_\epsilon(n,m,d)\), with consistency, parametric-rate, strict-improvement, supervised-endpoint, and known-marginal consequences.

@formal thm:sharp-annotation-frontier

For chart review, \(m\) helps exactly through the treatment-covariate table term.

---

## Interpretation

The theorem gives three regimes.

- Consistency occurs exactly when \(d_n/(N_n\ell_n)\to0\).
- Parametric mean-squared risk occurs exactly when \(d_n=O(N_n\ell_n/\sqrt n)\).
- Strict improvement over the labeled-only endpoint occurs when the alphabet is large enough for marginal information to matter and the auxiliary sample sufficiently enlarges \(N_n\).

Here \(N_n=n+m_n\) and \(\ell_n=\log(en)\).

---

## Further consequences

@informal thm:known-marginal-limit: For fixed \(n\) and \(d\), as \(m\to\infty\), the annotation risk converges to the known-marginal minimax risk.

@informal thm:inverse-count-baseline: A clipped inverse-count estimator attains a two-resource upper bound with marginal term at most \(d^2/(n+m)^2\).

@informal prop:binary-alphabet-parametric-rate: At binary alphabet size \(d=2\), the minimax risk is bounded above and below by constants times \(1/n\) for every \(m\).

These results locate the sharp frontier between our simple stabilized baseline, the binary-cell specialization, and the known-marginal endpoint.

---

## Proof sketch

The upper bound follows a cellwise bias-variance story.

- Poisson prefixes make the outcome, pilot, and factorial counts independent.
- In heavy cells, stabilized inverse counts have controlled moments.
- In light cells, Chebyshev approximation removes the sparse-cell inverse-weight bias.
- Pilot tails keep cells routed to the appropriate branch.
- Fixed-sample averaging transfers the Poisson bound back to the original samples.

The lower bound builds common-marginal alternatives whose ATEs separate while the auxiliary evidence remains matched.

---

## Conclusion

We characterize the finite-sample minimax value of outcome annotation for discrete ATE estimation.

- Outcome labels contribute the \(1/n\) floor.
- Treatment-covariate records contribute through \(n+m\).
- The sharp frontier is \(r_\epsilon(n,m,d)\), with \(N=n+m\) and \(\ell_n=\log(en)\).
- The hybrid estimator attains the frontier, and common-marginal priors prove the matching converse.

The result gives a clean allocation benchmark for finite-cell causal studies with costly outcome annotation.
