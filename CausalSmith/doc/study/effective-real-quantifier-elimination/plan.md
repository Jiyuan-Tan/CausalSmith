## Done
- Ground-truth audit found no pre-existing target directory.
- Library search (`npm run search`, LeanSearch/local search, bounded Mathlib grep) found no effective real-closed-field QE implementation; Mathlib has only general real-closed-field/model-theory infrastructure and no verified Sturm/CAD stack.
- Fetched and read the arXiv LaTeX for Basu 1409.1534, especially §2 and theorem `14:the:tqe`; the survey states the algorithm but explicitly omits its numerous technical details.
- Added `Syntax.lean`, `OneVariable.lean`, `Elimination.lean`, and `Main.lean`: named finite syntax, rational/real evaluation, substitution/renaming APIs, separate quantifier-free syntax, full-QE recursion, closed decision API, and projection API.
- `lake build CausalSmith.Substrate.EffectiveRealQuantifierElimination.Main` succeeds with only sorry warnings; LSP reports zero errors.

## Remaining
- `Syntax.lean` (14): `vars_rename`, `vars_subst_subset`, `evalReal_subst`, `evalReal_congr`, `evalReal_ofRat`, `Sign.holdsRat_eq_true_iff`, the three `QFFormula` structural/semantic lemmas, and the five `Formula` embedding/substitution/renaming lemmas.
- `OneVariable.lean` (3): executable `eliminateExists`, `freeVars_eliminateExists`, and `satisfies_eliminateExists`.
- `Elimination.lean` (7): `Formula.satisfies_congr`, full-QE free-variable/correctness theorems, closed-formula independence/decision correctness, and projection free-variable/correctness theorems.
- Source scan finds exactly 24 `sorry`s and no `admit`, `native_decide`, or axiom declarations.

## Blocked
- The central `eliminateExists` requires formalizing a complete exact rational CAD or equivalent sign-determination algorithm, including polynomial projection, specialization/nullification handling, certified real-root isolation, sign invariance, lifting, termination, and semantic correctness. None of these foundations exists in Mathlib here.
- A paper-specific CAD file found elsewhere in CausalSmith is forbidden as a dependency and only packages the desired external result as a `Prop`; it contains no kernel-checked construction that can be extracted.

## Decisions
- Use `String` names with explicit free/bound-variable bookkeeping and capture conditions.
- Represent rational polynomials by finite expression trees and quantifier-free output by a separate inductive type, making the output grammar guaranteed by construction.
- Define full QE structurally from one-variable existential elimination; derive universals by Boolean duality.
- Do not disguise the missing algorithm using classical choice, an assumed interface, an opaque solver, or a vacuous certificate.