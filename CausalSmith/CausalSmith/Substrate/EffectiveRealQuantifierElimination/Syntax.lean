import Mathlib.Data.Real.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Finite syntax for rational polynomial sign formulas

This module defines an executable expression syntax for rational-coefficient multivariate
polynomials and first-order formulas over named real variables.  Binding is represented by names;
`freeVars` and `boundVars` make capture conditions explicit for substitution and renaming.
-/

namespace CausalSmith.Substrate.EffectiveRealQuantifierElimination

/-- A variable name used by both free occurrences and quantifier binders. -/
abbrev VarName := String

/-- A finite expression denoting a multivariate polynomial with rational coefficients. -/
inductive RatPolynomial where
  /-- A rational constant polynomial. -/
  | const (q : ℚ)
  /-- A named coordinate variable. -/
  | var (x : VarName)
  /-- The sum of two rational polynomial expressions. -/
  | add (p q : RatPolynomial)
  /-- The product of two rational polynomial expressions. -/
  | mul (p q : RatPolynomial)
  /-- The additive inverse of a rational polynomial expression. -/
  | neg (p : RatPolynomial)
  deriving DecidableEq, Repr

namespace RatPolynomial

/-- Evaluate a rational polynomial expression in a real assignment. -/
def evalReal (p : RatPolynomial) (assignment : VarName → ℝ) : ℝ :=
  match p with
  | .const q => q
  | .var x => assignment x
  | .add p q => p.evalReal assignment + q.evalReal assignment
  | .mul p q => p.evalReal assignment * q.evalReal assignment
  | .neg p => -p.evalReal assignment

/-- Evaluate a rational polynomial expression in a rational assignment. -/
def evalRat (p : RatPolynomial) (assignment : VarName → ℚ) : ℚ :=
  match p with
  | .const q => q
  | .var x => assignment x
  | .add p q => p.evalRat assignment + q.evalRat assignment
  | .mul p q => p.evalRat assignment * q.evalRat assignment
  | .neg p => -p.evalRat assignment

/-- The finite set of variable names occurring in a polynomial expression. -/
def vars : RatPolynomial → Finset VarName
  | .const _ => ∅
  | .var x => {x}
  | .add p q => p.vars ∪ q.vars
  | .mul p q => p.vars ∪ q.vars
  | .neg p => p.vars

/-- Simultaneously rename every variable occurrence in a polynomial expression. -/
def rename (ρ : VarName → VarName) : RatPolynomial → RatPolynomial
  | .const q => .const q
  | .var x => .var (ρ x)
  | .add p q => .add (p.rename ρ) (q.rename ρ)
  | .mul p q => .mul (p.rename ρ) (q.rename ρ)
  | .neg p => .neg (p.rename ρ)

/-- Replace every occurrence of `x` by the rational polynomial expression `replacement`. -/
def subst (x : VarName) (replacement : RatPolynomial) : RatPolynomial → RatPolynomial
  | .const q => .const q
  | .var y => if y = x then replacement else .var y
  | .add p q => .add (subst x replacement p) (subst x replacement q)
  | .mul p q => .mul (subst x replacement p) (subst x replacement q)
  | .neg p => .neg (subst x replacement p)

/-- Renaming maps the variable support of a polynomial to the image of its old support. -/
theorem vars_rename (p : RatPolynomial) (ρ : VarName → VarName) :
    (p.rename ρ).vars = p.vars.image ρ := by
  sorry

/-- Substitution removes the target name and can introduce only variables from the replacement. -/
theorem vars_subst_subset (p replacement : RatPolynomial) (x : VarName) :
    (p.subst x replacement).vars ⊆ p.vars.erase x ∪ replacement.vars := by
  sorry

/-- Renaming a polynomial and then evaluating it equals evaluation in the pulled-back assignment. -/
@[simp] theorem evalReal_rename (p : RatPolynomial) (ρ : VarName → VarName)
    (assignment : VarName → ℝ) :
    (p.rename ρ).evalReal assignment = p.evalReal (assignment ∘ ρ) := by
  induction p <;> simp [rename, evalReal, *]

/-- Polynomial substitution agrees with updating the value of the substituted variable. -/
@[simp] theorem evalReal_subst (p replacement : RatPolynomial) (x : VarName)
    (assignment : VarName → ℝ) :
    (p.subst x replacement).evalReal assignment =
      p.evalReal (Function.update assignment x (replacement.evalReal assignment)) := by
  sorry

/-- A variable not listed by `vars` cannot affect real evaluation. -/
theorem evalReal_congr (p : RatPolynomial) {left right : VarName → ℝ}
    (h : ∀ x ∈ p.vars, left x = right x) :
    p.evalReal left = p.evalReal right := by
  sorry

/-- Rational evaluation followed by the canonical embedding into the reals agrees with real
evaluation after embedding the assignment. -/
@[simp] theorem evalReal_ofRat (p : RatPolynomial) (assignment : VarName → ℚ) :
    p.evalReal (fun x => (assignment x : ℝ)) = (p.evalRat assignment : ℝ) := by
  sorry

end RatPolynomial

/-- The exact three-valued sign requested of a polynomial atom. -/
inductive Sign where
  /-- Strictly negative. -/
  | negative
  /-- Equal to zero. -/
  | zero
  /-- Strictly positive. -/
  | positive
  deriving DecidableEq, Repr

namespace Sign

/-- The proposition that a real number has the specified exact sign. -/
def Holds : Sign → ℝ → Prop
  | .negative, value => value < 0
  | .zero, value => value = 0
  | .positive, value => 0 < value

/-- Executably test the exact sign of a rational number. -/
def holdsRat : Sign → ℚ → Bool
  | .negative, value => decide (value < 0)
  | .zero, value => decide (value = 0)
  | .positive, value => decide (0 < value)

/-- Rational sign testing is equivalent to testing the sign after embedding into the reals. -/
theorem holdsRat_eq_true_iff (sign : Sign) (value : ℚ) :
    sign.holdsRat value = true ↔ sign.Holds (value : ℝ) := by
  sorry

end Sign

/-- A quantifier-free Boolean formula whose atoms are exact signs of rational polynomials. -/
inductive QFFormula where
  /-- An exact rational-polynomial sign atom. -/
  | atom (polynomial : RatPolynomial) (sign : Sign)
  /-- Boolean falsity. -/
  | falsum
  /-- Conjunction. -/
  | and (left right : QFFormula)
  /-- Disjunction. -/
  | or (left right : QFFormula)
  /-- Negation. -/
  | not (body : QFFormula)
  deriving DecidableEq, Repr

namespace QFFormula

/-- The finite set of names occurring in a quantifier-free formula. -/
def freeVars : QFFormula → Finset VarName
  | .atom p _ => p.vars
  | .falsum => ∅
  | .and φ ψ => φ.freeVars ∪ ψ.freeVars
  | .or φ ψ => φ.freeVars ∪ ψ.freeVars
  | .not φ => φ.freeVars

/-- Interpret a quantifier-free formula in a real assignment. -/
def Satisfies (assignment : VarName → ℝ) : QFFormula → Prop
  | .atom p sign => sign.Holds (p.evalReal assignment)
  | .falsum => False
  | .and φ ψ => φ.Satisfies assignment ∧ ψ.Satisfies assignment
  | .or φ ψ => φ.Satisfies assignment ∨ ψ.Satisfies assignment
  | .not φ => ¬φ.Satisfies assignment

/-- Executably evaluate a quantifier-free formula in a rational assignment. -/
def evalRat (assignment : VarName → ℚ) : QFFormula → Bool
  | .atom p sign => sign.holdsRat (p.evalRat assignment)
  | .falsum => false
  | .and φ ψ => φ.evalRat assignment && ψ.evalRat assignment
  | .or φ ψ => φ.evalRat assignment || ψ.evalRat assignment
  | .not φ => !(φ.evalRat assignment)

/-- Rational Boolean evaluation agrees with real semantics under the rational embedding. -/
theorem evalRat_eq_true_iff (φ : QFFormula) (assignment : VarName → ℚ) :
    φ.evalRat assignment = true ↔
      φ.Satisfies (fun x => (assignment x : ℝ)) := by
  sorry

/-- Simultaneously rename every name in a quantifier-free formula. -/
def rename (ρ : VarName → VarName) : QFFormula → QFFormula
  | .atom p sign => .atom (p.rename ρ) sign
  | .falsum => .falsum
  | .and φ ψ => .and (φ.rename ρ) (ψ.rename ρ)
  | .or φ ψ => .or (φ.rename ρ) (ψ.rename ρ)
  | .not φ => .not (φ.rename ρ)

/-- Renaming maps the free-variable set of a quantifier-free formula to its image. -/
theorem freeVars_rename (φ : QFFormula) (ρ : VarName → VarName) :
    (φ.rename ρ).freeVars = φ.freeVars.image ρ := by
  sorry

/-- Renaming a quantifier-free formula pulls its real assignment back along the renaming. -/
theorem satisfies_rename (φ : QFFormula) (ρ : VarName → VarName)
    (assignment : VarName → ℝ) :
    (φ.rename ρ).Satisfies assignment ↔ φ.Satisfies (assignment ∘ ρ) := by
  sorry

end QFFormula

/-- A finite first-order formula over named real variables and rational polynomial sign atoms. -/
inductive Formula where
  /-- An exact rational-polynomial sign atom. -/
  | atom (polynomial : RatPolynomial) (sign : Sign)
  /-- Boolean falsity. -/
  | falsum
  /-- Conjunction. -/
  | and (left right : Formula)
  /-- Disjunction. -/
  | or (left right : Formula)
  /-- Negation. -/
  | not (body : Formula)
  /-- Existential quantification of a named real variable. -/
  | exists_ (name : VarName) (body : Formula)
  /-- Universal quantification of a named real variable. -/
  | forall_ (name : VarName) (body : Formula)
  deriving DecidableEq, Repr

namespace Formula

/-- The finite set of free variable names of a first-order formula. -/
def freeVars : Formula → Finset VarName
  | .atom p _ => p.vars
  | .falsum => ∅
  | .and φ ψ => φ.freeVars ∪ ψ.freeVars
  | .or φ ψ => φ.freeVars ∪ ψ.freeVars
  | .not φ => φ.freeVars
  | .exists_ x φ => φ.freeVars.erase x
  | .forall_ x φ => φ.freeVars.erase x

/-- The finite set of names used as quantifier binders in a first-order formula. -/
def boundVars : Formula → Finset VarName
  | .atom _ _ => ∅
  | .falsum => ∅
  | .and φ ψ => φ.boundVars ∪ ψ.boundVars
  | .or φ ψ => φ.boundVars ∪ ψ.boundVars
  | .not φ => φ.boundVars
  | .exists_ x φ => insert x φ.boundVars
  | .forall_ x φ => insert x φ.boundVars

/-- Interpret a first-order formula in a real assignment, with quantifiers ranging over all reals. -/
def Satisfies (assignment : VarName → ℝ) : Formula → Prop
  | .atom p sign => sign.Holds (p.evalReal assignment)
  | .falsum => False
  | .and φ ψ => φ.Satisfies assignment ∧ ψ.Satisfies assignment
  | .or φ ψ => φ.Satisfies assignment ∨ ψ.Satisfies assignment
  | .not φ => ¬φ.Satisfies assignment
  | .exists_ x φ => ∃ value : ℝ, φ.Satisfies (Function.update assignment x value)
  | .forall_ x φ => ∀ value : ℝ, φ.Satisfies (Function.update assignment x value)

/-- Embed a quantifier-free formula into the general first-order syntax. -/
def ofQF : QFFormula → Formula
  | .atom p sign => .atom p sign
  | .falsum => .falsum
  | .and φ ψ => .and (ofQF φ) (ofQF ψ)
  | .or φ ψ => .or (ofQF φ) (ofQF ψ)
  | .not φ => .not (ofQF φ)

/-- Embedding a quantifier-free formula preserves its free-variable set. -/
@[simp] theorem freeVars_ofQF (φ : QFFormula) : (ofQF φ).freeVars = φ.freeVars := by
  sorry

/-- Embedding a quantifier-free formula preserves its semantics. -/
@[simp] theorem satisfies_ofQF (φ : QFFormula) (assignment : VarName → ℝ) :
    (ofQF φ).Satisfies assignment ↔ φ.Satisfies assignment := by
  sorry

/-- Capture-avoiding substitution of a polynomial for a free variable, provided callers keep the
replacement variables fresh for binders as required by `satisfies_subst`. -/
def subst (x : VarName) (replacement : RatPolynomial) : Formula → Formula
  | .atom p sign => .atom (p.subst x replacement) sign
  | .falsum => .falsum
  | .and φ ψ => .and (φ.subst x replacement) (ψ.subst x replacement)
  | .or φ ψ => .or (φ.subst x replacement) (ψ.subst x replacement)
  | .not φ => .not (φ.subst x replacement)
  | .exists_ y φ => if y = x then .exists_ y φ else .exists_ y (φ.subst x replacement)
  | .forall_ y φ => if y = x then .forall_ y φ else .forall_ y (φ.subst x replacement)

/-- Formula substitution agrees with assigning the substituted polynomial's value when no binder
can capture a variable of the replacement expression. -/
theorem satisfies_subst (φ : Formula) (replacement : RatPolynomial) (x : VarName)
    (assignment : VarName → ℝ)
    (fresh : Disjoint (φ.boundVars.erase x) replacement.vars) :
    (φ.subst x replacement).Satisfies assignment ↔
      φ.Satisfies (Function.update assignment x (replacement.evalReal assignment)) := by
  sorry

/-- Simultaneously rename every occurrence and binder in a first-order formula. -/
def rename (ρ : VarName → VarName) : Formula → Formula
  | .atom p sign => .atom (p.rename ρ) sign
  | .falsum => .falsum
  | .and φ ψ => .and (φ.rename ρ) (ψ.rename ρ)
  | .or φ ψ => .or (φ.rename ρ) (ψ.rename ρ)
  | .not φ => .not (φ.rename ρ)
  | .exists_ x φ => .exists_ (ρ x) (φ.rename ρ)
  | .forall_ x φ => .forall_ (ρ x) (φ.rename ρ)

/-- Injective renaming maps the free-variable set of a first-order formula to its image. -/
theorem freeVars_rename (φ : Formula) (ρ : VarName → VarName)
    (injective : Function.Injective ρ) :
    (φ.rename ρ).freeVars = φ.freeVars.image ρ := by
  sorry

/-- Injective simultaneous renaming pulls real semantics back along the renaming map. -/
theorem satisfies_rename (φ : Formula) (ρ : VarName → VarName)
    (injective : Function.Injective ρ) (assignment : VarName → ℝ) :
    (φ.rename ρ).Satisfies assignment ↔ φ.Satisfies (assignment ∘ ρ) := by
  sorry

/-- A formula is closed when it has no free variable names. -/
def IsClosed (φ : Formula) : Prop := φ.freeVars = ∅

end Formula

end CausalSmith.Substrate.EffectiveRealQuantifierElimination
