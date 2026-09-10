import CausalSmith.Substrate.EffectiveRealQuantifierElimination.OneVariable

/-!
# Effective real quantifier elimination

This module derives the executable full quantifier-elimination, closed-decision, and existential
projection interfaces from the concrete one-variable elimination kernel.
-/

namespace CausalSmith.Substrate.EffectiveRealQuantifierElimination

namespace Formula

/-- Satisfaction depends only on the values assigned to the formula's free variables. -/
theorem satisfies_congr (φ : Formula) {left right : VarName → ℝ}
    (h : ∀ x ∈ φ.freeVars, left x = right x) :
    φ.Satisfies left ↔ φ.Satisfies right := by
  sorry

end Formula

namespace Formula

/-- Recursively eliminate every real quantifier, using `eliminateExists` for existential binders
and Boolean duality for universal binders. -/
def eliminateQuantifiers : Formula → QFFormula
  | .atom p sign => .atom p sign
  | .falsum => .falsum
  | .and φ ψ => .and φ.eliminateQuantifiers ψ.eliminateQuantifiers
  | .or φ ψ => .or φ.eliminateQuantifiers ψ.eliminateQuantifiers
  | .not φ => .not φ.eliminateQuantifiers
  | .exists_ name φ => eliminateExists name φ.eliminateQuantifiers
  | .forall_ name φ => .not (eliminateExists name (.not φ.eliminateQuantifiers))

/-- Full quantifier elimination preserves exactly the free-variable names of the input formula. -/
theorem freeVars_eliminateQuantifiers (φ : Formula) :
    φ.eliminateQuantifiers.freeVars = φ.freeVars := by
  sorry

/-- Full quantifier elimination preserves real semantics for every assignment. -/
theorem satisfies_eliminateQuantifiers (φ : Formula) (assignment : VarName → ℝ) :
    φ.eliminateQuantifiers.Satisfies assignment ↔ φ.Satisfies assignment := by
  sorry

/-- A closed rational polynomial sign formula bundled with the proof that it has no free names. -/
structure ClosedFormula where
  /-- The underlying first-order formula. -/
  formula : Formula
  /-- The formula contains no free variable names. -/
  isClosed : formula.IsClosed

/-- Decide a closed formula by quantifier elimination followed by exact rational sign evaluation. -/
def decideClosed (φ : ClosedFormula) : Bool :=
  φ.formula.eliminateQuantifiers.evalRat (fun _ => 0)

/-- The truth of a closed formula does not depend on the ambient assignment. -/
theorem closed_satisfaction_independent (φ : ClosedFormula)
    (left right : VarName → ℝ) :
    φ.formula.Satisfies left ↔ φ.formula.Satisfies right := by
  sorry

/-- The executable decision returns true exactly when the closed formula is true over the reals. -/
theorem decideClosed_eq_true_iff (φ : ClosedFormula) (assignment : VarName → ℝ) :
    decideClosed φ = true ↔ φ.formula.Satisfies assignment := by
  sorry

/-- Prefix a formula by a finite list of named existential quantifiers. -/
def existsOver : List VarName → Formula → Formula
  | [], φ => φ
  | name :: names, φ => .exists_ name (existsOver names φ)

/-- Remove a finite list of names from a finite variable set. -/
def eraseNames (names : List VarName) (namesSet : Finset VarName) : Finset VarName :=
  names.foldl (fun remaining name => remaining.erase name) namesSet

/-- Compute a quantifier-free rational semialgebraic description of the existential projection
that forgets the listed coordinates. -/
def project (names : List VarName) (body : QFFormula) : QFFormula :=
  (existsOver names (ofQF body)).eliminateQuantifiers

/-- Effective projection introduces no coordinates and removes precisely the projected names. -/
theorem freeVars_project (names : List VarName) (body : QFFormula) :
    (project names body).freeVars = eraseNames names body.freeVars := by
  sorry

/-- The computed quantifier-free formula defines exactly the existential projection of the input
rational semialgebraic set. -/
theorem satisfies_project (names : List VarName) (body : QFFormula)
    (assignment : VarName → ℝ) :
    (project names body).Satisfies assignment ↔
      (existsOver names (ofQF body)).Satisfies assignment := by
  sorry

end Formula

end CausalSmith.Substrate.EffectiveRealQuantifierElimination
