# Substrate requirement: affine-sign-cell-closure

## Goal
Build a reusable, axiom-clean Lean API for finite systems of weak and strict real affine inequalities: strict feasibility is equivalent to a positive common-slack value, and the weak relaxation of a nonempty strict cell is its closure, so bounded linear-coordinate infima and suprema are preserved.

## Provides (API contract)
- A paper-independent representation of a finite affine constraint system on `Fin n → ℝ`, with each constraint marked weak (`f x ≤ 0`) or strict (`f x < 0`), and definitions of its strict cell and weak relaxation.
- A common-slack feasible set/value, with every strict constraint replaced by `f x ≤ -δ` and `0 ≤ δ ≤ 1` while weak constraints remain weak.
- A theorem `strictFeasible_iff_commonSlackValue_pos` (name may vary) proving that the strict cell is nonempty iff the common-slack supremum is positive. Derive both directions, including the supremum argument; do not assume the equivalence as a premise and do not invoke an external LP solver.
- A segment theorem showing that, given one strict feasible point, every point of the weak relaxation is the limit of convex combinations with that strict point that remain in the strict cell.
- A closure theorem identifying the closure of a nonempty strict affine cell with its weak relaxation. Any necessary closedness proof for the weak cell must be included.
- For a continuous linear/affine coordinate functional, theorems that its image over the strict cell and weak relaxation have equal `sInf` and equal `sSup`, under the minimal explicit nonemptiness and `BddBelow`/`BddAbove` hypotheses required by Mathlib. Equivalent formulations via equality of closures are acceptable if they specialize directly to these two extrema equalities.
- If `MvPolynomial` is used as the input representation, a checked bridge from total degree at most one to the affine-constraint representation. Otherwise expose a simple affine-map representation plus a specialization lemma that makes a finite list of degree-≤1 real `MvPolynomial` constraints usable without assuming the compiler's conclusion.

## Statement / milestones
1. Define `strictCell` and `weakCell` for a finite list of real affine functions and strictness flags.
2. Prove `strictCell ⊆ weakCell` and that `weakCell` is closed and convex.
3. From `x° ∈ strictCell`, prove that `(1-ε) • x + ε • x° ∈ strictCell` for every `x ∈ weakCell` and `0 < ε ≤ 1`; handle strict and weak constraints separately by affine algebra.
4. Deduce `closure strictCell = weakCell` whenever `strictCell.Nonempty`.
5. Define the common-slack value with `δ ∈ [0,1]` and prove strict feasibility iff its value is positive, including edge cases with no strict constraints and with an empty weak system.
6. Deduce equality of bounded linear-coordinate `sInf` and `sSup` between the strict cell and weak cell.
7. Supply a small compiled example or specialization demonstrating a finite sign cell with both strict and weak inequalities.

## Standard reference
This is the elementary relative-interior/closure fact for a feasible finite polyhedron together with the standard Phase-I common-slack formulation for strict linear feasibility. The proof should be self-contained from finite affine algebra, continuity, convex interpolation, and complete-lattice properties of `sInf`/`sSup`.

## Intended reuse
The immediate consumer is the fixed-accuracy sign-cell layer of `pid_imperfectref_cutoff_regret`, where each cell is a finite conjunction of real affine equalities/inequalities and regret coordinates are linear. The API must remain general enough for other finite-dimensional partial-identification and optimization developments; it must not mention cutoff policies, regret, reference tests, or any `CausalSmith/*_Research` type.

## May assume / must derive
May assume a finite dimension, a finite constraint list, one supplied strict feasible point for closure/extrema results, and explicit boundedness of the objective image when required for real-valued `sInf`/`sSup`. May use Mathlib facts about continuous affine/linear maps, closed halfspaces, convex combinations, closure, `csInf`, and `csSup`. Must derive common-slack positivity, segment feasibility, weak-cell closedness, closure equality, and extremum preservation. No `sorry`, `admit`, new `axiom`, classical choice of an optimizer, rational-coefficient restriction, or quantifier-elimination theorem.

## Non-goals
Do not implement a numerical LP solver, simplex algorithm, Tarski--Seidenberg theorem, general semialgebraic optimization, or the paper's sign-mask enumeration. Do not prove the paper's projection corollary or import its research folder.

## Known building blocks
Likely useful Mathlib material includes finite intersections of closed sets, continuity of affine/linear evaluation, convexity of affine halfspaces, `Set.mem_closure_iff_seq_limit`, `sSup_eq_closure_sSup`, the corresponding infimum result or an order-dual derivation, and standard `csSup`/`csInf` approximation lemmas. A qid-local prototype `strict_to_weak_closure_segment` exists only as evidence that the segment construction is feasible; reusable substrate must not import it.
