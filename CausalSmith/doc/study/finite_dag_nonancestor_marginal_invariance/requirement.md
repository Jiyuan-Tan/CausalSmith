# Substrate requirement: finite_dag_nonancestor_marginal_invariance

## Goal
Build a reusable finite Bayesian-network theorem showing that replacing one normalized conditional density by a normalized parent-independent intervention density preserves every marginal supported on variables that are not descendants of the intervention target.

## Provides (API contract)
- A product-density factorization interface over a finite DAG, with each factor measurable, parent-local, nonnegative, and normalized in its own coordinate on a finite product cube.
- A normalized leaf-elimination lemma for integrals of finite products of DAG-local conditional densities.
- A reverse-topological ancestral-marginal theorem: observational and single-target interventional product measures agree on the ancestral closure of a node whenever the intervention target is distinct from and not an ancestor of that node.
- A mapping corollary: any measurable function depending only on that ancestral closure has the same pushforward law under the observational and interventional measures.

## Statement / milestones
For a finite DAG `G`, product domain `Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)`, parent-local conditional densities `p i`, and normalized parent-independent density `q j`, define the observational density as `∏ i, p i v` and the target-`j` intervention density as `q j (v j) * ∏ l in Finset.univ.erase j, p l v`.

Prove, by reverse topological leaf elimination or an equivalent finite-product Fubini argument, that if `j ≠ i` and `¬ G.isAncestor j i`, then the two induced measures agree after projection to the ancestral closure of `i`. Deduce equality after mapping any measurable function whose value is determined by `i` and its ancestors. All declarations must be sorry-free and axiom-clean.

The implementation should expose enough intermediate API to instantiate this theorem for a ratio coordinate `q_i(v_i) / p_i(v)`, whose parent locality makes it a function of `i` and its parents, and to transport the resulting equality through a common measurable mixing map.

## Standard reference
This is the standard truncated-factorization property of finite Bayesian networks: an intervention at a node outside the ancestral set of queried variables cannot change their marginal distribution. The proof is the finite-density analogue of the usual ancestral sampling argument, obtained by successively integrating normalized leaf conditionals in reverse topological order.

## Intended reuse
Primary consumer: `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.ratio_nonancestor_zero`. It needs equality of the canonical ratio pushforward laws under the observational environment and an intervention at a distinct non-ancestor, then applies `populationDiscrepancy_eq_zero_of_ratioLaw_eq`.

The result should live in a general Causalean probability/SCM module and be reusable for density-factorized DAG models that are not packaged as `Causalean.SCM` kernel objects.

## May assume / must derive
May assume finiteness of the vertex type, a DAG/topological order, a finite product of standard Borel coordinate spaces, measurability and nonnegativity of every density factor, parent locality, normalization of each conditional factor in its own coordinate, normalization of the intervention density, and the finite-measure/integrability conditions required for Fubini/Tonelli.

Must derive leaf elimination, equality of the relevant ancestral marginals, and the measurable-map pushforward corollary. Must not assume the desired marginal or ratio-law equality, import a paper-specific `CausalSmith/*_Research` module, or require an existing `Causalean.SCM` representation.

## Non-goals (optional)
Do not formalize arbitrary infinite Bayesian networks, general do-calculus, conditional-distribution uniqueness, or the paper's population decoder. Do not prove Radon--Nikodym identification for arbitrary off-support representatives; the consumer already uses a canonical measurable observed-law ratio and supplies its model-specific identification.

## Known building blocks (optional)
- Mathlib `MeasureTheory.Measure.lmarginal`, `lmarginal_insert`, and `lmarginal_union`.
- Finite-product Fubini/Tonelli and `Measure.withDensity` integration lemmas.
- `Measure.withDensity_absolutelyContinuous'` and measurable-map congruence for downstream transport.
- `Causalean.DAG.topoOrder`, ancestry, and parent-local structure.
- Causalean's SCM-typed `condDistrib_intervention_ancestral_eq` and `ancestralFactorization` are conceptual near-matches, but the new theorem must not require an SCM/SWIG carrier.
