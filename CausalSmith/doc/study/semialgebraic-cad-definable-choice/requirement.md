# Substrate requirement: semialgebraic-cad-definable-choice

## Goal
Build a reusable, paper-agnostic Lean development for semialgebraic cylindrical decomposition and definable choice over finite-dimensional real coordinate spaces.

## Provides (API contract)
- A canonical predicate for semialgebraic subsets of `(i → ℝ)` for finite `i`, closed under finite Boolean operations, coordinate products, and coordinate projections.
- A finite cylindrical algebraic decomposition interface along a supplied finite coordinate order, whose nonempty cells form a semialgebraic partition.
- A definable-choice theorem for a semialgebraic relation `R ⊆ (i → ℝ) × (k → ℝ)` with every input fiber nonempty, producing a selector whose graph is semialgebraic and which selects inside every fiber.
- A measurability theorem for that selector.
- A first-nonempty-cell formulation or bridge exposing enough partition, cylindricity, within-cell choice, and global graph structure to instantiate downstream certified-CAD records.

## Statement / milestones
1. Define polynomial sign conditions and semialgebraic sets/maps in a finite-coordinate normal form, then prove finite union/intersection/complement, product, and projection closure.
2. Prove that every semialgebraic subset of `(i ⊕ k → ℝ)` admits a finite partition into nonempty semialgebraic cells cylindrical for a chosen coordinate order.
3. From such a decomposition, prove semialgebraic definable choice for every total semialgebraic relation.
4. Derive Borel measurability of semialgebraic sets and the chosen selector.
5. Package a first-nonempty-cell bridge suitable for constructing a finite certified CAD and selected map.

The result must be proved at proposition/existence level with zero `sorry`, `admit`, or new `axiom`; ordinary Lean/Mathlib classical choice is allowed.

## Standard reference
Tarski–Seidenberg quantifier elimination and semialgebraic selection/definable choice; cylindrical algebraic decomposition as in Collins and standard real algebraic geometry treatments such as Bochnak–Coste–Roy.

## Intended reuse
The immediate consumer is `eid_covshift_profilequotient_targets/v1`: it must construct `FixedCertifiedCAD` in `Helpers/Selector.lean` from a proved semialgebraic, nonempty witness-augmented approximate-minimizer relation and discharge `measurable_certified_selection`. The API must remain independent of covariance models and research-run types.

## May assume / must derive
May use Mathlib multivariate polynomials, topology, Borel measurability, finite types, classical choice, and any existing real-closed-field or quantifier-elimination theorem. Must derive semialgebraic closure, CAD/selection consequences, graph semialgebraicity, and selector measurability from imported proved results; do not postulate CAD or selection as an axiom.

## Non-goals (optional)
No executable high-performance CAD implementation, complexity-optimality theorem, covariance-specific inference, model-specific LAN claim, or paper-folder dependency is required.

## Known building blocks (optional)
Start from `Mathlib.Algebra.MvPolynomial.Eval`, `Mathlib.Topology.Algebra.MvPolynomial`, `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`, and real-closed-field/quantifier-elimination modules if present. Generic prototypes currently live in the research helper `Helpers/Semialgebraic.lean` (`PolynomialSignCondition`, its `Holds` predicate, `IsSemialgebraicSet`, `IsSemialgebraicMap`, finite-union closure, and measurability); extract/generalize them without importing any `CausalSmith/*_Research` module.
