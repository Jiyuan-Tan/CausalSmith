# Substrate requirement: positive-mechanism-c2-stratum-openness

## Goal
Build neutral stability interfaces showing that edgewise causal minimality and fixed own-coordinate log-ratio derivative sign are locally open properties of strictly positive finite-DAG mechanisms in a uniform `C¹`/`C²` topology.

## Provides (API contract)
- A positive finite-DAG edge characterization: for a normalized strictly positive parent-local product-density mechanism and edge `j → i`, conditional independence of coordinate `i` and coordinate `j` given `(G.parents i).erase j` is equivalent to independence of the local factor `p i` from coordinate `j`, or to an explicit local cross-product contrast vanishing.
- A contrapositive/witness corollary: a nonzero local factor contrast at two compact-domain points implies failure of the edge conditional independence.
- A continuity theorem for `(q,p) ↦ derivWithin (fun x => log (q x / p x))` in uniform `C¹` coordinates when `p` and `q` share a uniform positive lower bound.
- A local sign-stability corollary: a continuous log-ratio derivative uniformly bounded away from zero with fixed sign on a compact interval retains that sign under a sufficiently small uniform `C¹` or `C²` perturbation.
- If natural, finite-product corollaries saying these edgewise/sign properties are open in the induced product topology.

## Statement / milestones
1. Prove the factor-level conditional-law formula for a strictly positive normalized finite-DAG product density.
2. For an edge `j → i`, prove CI given the other parents iff the local conditional factor is independent of `j`; an equivalent four-point cross-product equality is acceptable.
3. Package a finite witness form whose nonzero value is stable under uniform convergence.
4. Prove continuity of reciprocal, quotient, logarithm, and `derivWithin` under uniform `C¹` convergence with a common positive lower bound.
5. Derive compact fixed-sign stability from a strict derivative margin.
6. Provide small neutral finite-DAG and scalar interval examples exercising both APIs.

## Standard reference
The edge-CI characterization is the standard causal-minimality characterization for strictly positive Bayesian-network densities: an edge is redundant exactly when the child's local conditional density does not depend on that parent. The analytic statement is the standard openness of strict inequalities under uniform convergence, combined with continuity of reciprocal/logarithmic differentiation away from zero.

## Intended reuse
The immediate consumer is a finite-DAG perturbation argument that must remain inside causal-minimal and fixed-own-derivative-sign strata while moving along an affine mechanism path. The APIs should be reusable for other positive finite Bayesian-network models and compact-domain likelihood-ratio perturbations, without mentioning the motivating paper's contrast, MMD, sparse witness, or genericity theorem.

## May assume / must derive
May assume a finite DAG, compact coordinate domains, normalized parent-local factors, strict positivity with an explicit uniform lower bound, measurable/continuous factors, and uniform `C¹` or `C²` control in the topology used by the continuity theorem.

Must derive the edgewise CI/local-factor equivalence from the positive product-density law and derive derivative-sign stability from the uniform topology and positive margins. Do not assume causal minimality, fixed derivative sign, local stratum preservation, or openness as premises of their own proofs.

## Non-goals (optional)
- Do not import or mention `CausalSmith.ExactID.*_Research`.
- Do not prove `analytic_edge_perturbation`, `generic_cover_separation`, density of any paper-specific separated set, or any MMD claim.
- Do not construct the paper's sparse/cancellation witnesses or affine perturbation.
- Do not add assumptions to any research theorem.

## Known building blocks (optional)
- `Causalean.Graph.FiniteDensity` factorization and conditional-independence APIs.
- `Causalean.Mathlib.CondIndep.ThreeBlockDensity` and positive-density intersection results.
- Mathlib compactness, extreme-value, uniform convergence, `ContDiffOn`, `derivWithin`, reciprocal/log derivative, and finite-product topology APIs.
- The existing ordered local-Markov theorem supplies factorization-to-CI; the missing edge-specific converse must be proved, not assumed.

No research-folder prerequisite needs extraction. The neutral study must have zero `sorry`, `admit`, errors, or nonstandard axioms; semantic review must check both directions of the edge characterization and the genuine common positive margin.
