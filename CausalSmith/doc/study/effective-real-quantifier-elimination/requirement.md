# Substrate requirement: effective-real-quantifier-elimination

## Goal
Provide a reusable, executable Lean interface for eliminating quantifiers from finite first-order formulas over the real ordered field whose atoms are sign conditions on rational-coefficient multivariate polynomials.

## Provides (API contract)
- A finite syntax for rational polynomial sign formulas with named free and bound real variables, Boolean connectives, and existential/universal quantifiers.
- A semantics interpreting those formulas over real assignments.
- `eliminateQuantifiers`: a terminating construction returning a quantifier-free rational polynomial sign formula with the same free variables.
- A semantic-correctness theorem: every assignment satisfies the input formula if and only if it satisfies the eliminated formula.
- A decision procedure and correctness theorem for closed formulas.
- A projection corollary: existentially projecting a rational semialgebraic formula yields a computable quantifier-free rational semialgebraic description.

## Statement / milestones
1. Define substitution, renaming, free-variable bookkeeping, and semantics for the finite formula syntax and prove the required structural lemmas.
2. Implement a sound terminating quantifier-elimination algorithm for the real closed field of real numbers. The implementation may use a standard constructive route such as sign determination or cylindrical algebraic decomposition, but it must remain kernel-checked Lean code and may not introduce an axiom for quantifier elimination.
3. Prove the output is quantifier-free, uses rational-coefficient polynomial sign atoms, and is semantically equivalent to the input for every assignment.
4. Derive decidability of closed formulas and the effective projection interface used by downstream semialgebraic feasibility problems.
5. Verify the public headline declarations with a full module build, source grep for `sorry`, `admit`, `native_decide`, and `axiom`, and `#print axioms`.

## Standard reference
Saugata Basu, “Algorithms in Real Algebraic Geometry: A Survey,” arXiv:1409.1534, Section 2, especially theorem `14:the:tqe`; and Basu, Pollack, and Roy, *Algorithms in Real Algebraic Geometry*, 2nd edition, the effective real quantifier-elimination development cited there.

## Intended reuse
The immediate consumer is the CausalSmith run `eid_robust_backshift_uniform_distance/v1`, where exact compatibility-set projection, empty/singleton/multiple classification, and a universal margin audit are rational semialgebraic formulas. The API must be paper-agnostic and reusable for future identification, partial-identification, optimization, and certification results that reduce finite-dimensional real feasibility to rational polynomial sign formulas.

## May assume / must derive
May use existing Mathlib definitions and proved theorems about multivariate polynomials, real closed fields, algebraic numbers, finite data structures, and computability/decidability. Must derive termination and semantic correctness of the elimination procedure. Must not assume the target quantifier-elimination theorem, introduce a new axiom, or use an opaque external solver result as proof.

## Non-goals (optional)
- No BACKSHIFT, covariance, causal-model, confidence-region, or research-run-specific declarations.
- No complexity-optimality theorem is required; a correct terminating construction is sufficient.
- No numerical approximate solver or tactic frontend is required.
- No imports from `CausalSmith/*_Research` or any paper module.

## Known building blocks (optional)
Mathlib contains first-order syntax/model-theory infrastructure, multivariate polynomials, ordered fields, and Presburger quantifier elimination, but the focused F1 search found no existing effective real-closed-field quantifier-elimination implementation. Reuse any genuinely matching pieces after confirming their semantics and import closure; do not duplicate a hidden existing interface.
