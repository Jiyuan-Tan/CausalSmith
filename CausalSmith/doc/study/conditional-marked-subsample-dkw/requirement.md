# Substrate requirement: conditional-marked-subsample-dkw

## Goal
Build a reusable Causalean theorem that lifts a fixed-size iid empirical-CDF tail bound through independent Boolean marking and random subsampling.

## Provides (API contract)
- A reusable conditional selected-subsample empirical-CDF tail theorem.
- Supporting public lemmas for exact Boolean-word conditioning, reindexing selected coordinates, their conditional iid law, and finite aggregation when those lemmas are independently reusable.
- An interface directly instantiable with the DKW–Massart bound and a count-dependent radius.

## Statement / milestones
Let `(A_i,Y_i)` be a finite iid family with common probability law `nu`, where `A_i : Bool`. Fix a mark `a` with probability `e > 0`, and a probability law `rho` such that for every measurable `B`,

    nu {z | z.1 = a ∧ z.2 ∈ B} = e * rho B.

Let `M` be the selected count and define the selected empirical CDF as the normalized sum of indicators over indices with `A_i = a`. Assume every deterministic sample size `m >= 1` of iid `rho` observations obeys a supplied uniform empirical-CDF tail bound `beta` at radius `epsilon m`. Prove

    P(M > 0 ∧ sup_y |Fhat_selected(y) - rho((-∞,y])| > epsilon M) ≤ beta.

Construct the exact-word conditioning, selected-coordinate reindexing, conditional iid law, and finite aggregation. Expose a corollary instantiable with DKW–Massart and

    epsilon(m) = sqrt(log(4/alpha) / (2m)).

## Standard reference
The proof is the standard finite conditioning-on-the-mark-word argument combined with conditional independence and the Dvoretzky–Kiefer–Wolfowitz–Massart inequality. Relevant Mathlib infrastructure includes `ProbabilityTheory.iIndepFun.cond`.

## Intended reuse
Any causal/statistical formalization that estimates a conditional outcome CDF from an iid sample after random treatment-arm or Boolean-mark selection. The result must be paper-agnostic and reusable beyond the originating propensity-bound run.

## May assume / must derive
May assume the fixed-size iid empirical-CDF tail bound through a theorem-valued hypothesis (and provide a DKW-instantiated corollary if the library exposes the needed theorem). Must derive the conditional selected-sample iid law, reindexing, and aggregation from the iid pair sample, Boolean mark factorization, and probability-law hypotheses. The final declarations must contain zero `sorry` and introduce no axioms.

## Non-goals (optional)
Do not import any `CausalSmith/*_Research` or paper module. Do not choose a paper-specific theorem shape or target module. General marks beyond a finite/Boolean partition, asymptotic empirical-process theory, and dependent observations are out of scope.

## Known building blocks (optional)
- `Mathlib.Probability.ConditionalProbability`
- `Mathlib.Probability.Independence.Basic`, especially `ProbabilityTheory.iIndepFun.cond`
- `Mathlib.Data.Finset.Sort`
- Narrow Causalean sample and empirical-CDF modules selected by the coordinator
- The private `FiniteMarkedPoissonPartition/Partition/Splitting.lean` development may be consulted for proof ideas only; the result here must expose a clean independent reusable API.
