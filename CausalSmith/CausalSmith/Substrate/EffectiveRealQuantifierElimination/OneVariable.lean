import CausalSmith.Substrate.EffectiveRealQuantifierElimination.Syntax

/-!
# One-variable effective elimination kernel

This module isolates the hard algebraic core: eliminating one named real variable from a
quantifier-free rational polynomial sign formula.  The implementation must be a concrete,
terminating rational CAD/sign-determination program; its correctness may not be postulated.

The reference construction is Basu--Pollack--Roy block elimination plus sign determination, as
summarized in Basu, *Algorithms in Real Algebraic Geometry: A Survey*, §2.1.2, Theorem 2.4
(`14:the:tqe` in the arXiv source).
-/

namespace CausalSmith.Substrate.EffectiveRealQuantifierElimination

/-- Eliminate one existentially quantified named variable from a quantifier-free rational sign
formula by a terminating exact rational real-algebraic algorithm.

This definition is the central implementation hole of the round-one scaffold.  A filler must
replace it with kernel-checked code (for example a verified CAD projection/lifting computation),
not with classical choice, an oracle, or a theorem asserting quantifier elimination. -/
def eliminateExists (name : VarName) (body : QFFormula) : QFFormula := by
  sorry

/-- One-variable elimination removes exactly the quantified name and introduces no other free
variables. -/
theorem freeVars_eliminateExists (name : VarName) (body : QFFormula) :
    (eliminateExists name body).freeVars = body.freeVars.erase name := by
  sorry

/-- One-variable elimination is semantically equivalent over the reals to existential
quantification of that variable. -/
theorem satisfies_eliminateExists (name : VarName) (body : QFFormula)
    (assignment : VarName → ℝ) :
    (eliminateExists name body).Satisfies assignment ↔
      ∃ value : ℝ, body.Satisfies (Function.update assignment name value) := by
  sorry

end CausalSmith.Substrate.EffectiveRealQuantifierElimination
