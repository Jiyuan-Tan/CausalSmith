import CausalSmith.Substrate.SemialgebraicCadDefinableChoice.RootData
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Semialgebraic sets in finite real coordinate spaces

This module gives a finite, quantifier-free normal form for semialgebraic subsets of spaces
`ι → ℝ`, proves its elementary Boolean and coordinate closure properties, and isolates the
Tarski--Seidenberg projection theorem.  Coefficients are real, as in the standard definition of
semialgebraic sets used in real algebraic geometry.
-/

open Set

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

/-- The three possible exact signs of a real polynomial value. -/
inductive PolynomialSign where
  | negative
  | zero
  | positive
  deriving DecidableEq

/-- The three exact polynomial signs form a finite type. -/
instance : Fintype PolynomialSign where
  elems := {.negative, .zero, .positive}
  complete sign := by cases sign <;> simp

namespace PolynomialSign

/-- A real number satisfies an exact sign when it is respectively negative, zero, or positive. -/
def Holds : PolynomialSign → ℝ → Prop
  | .negative, value => value < 0
  | .zero, value => value = 0
  | .positive, value => 0 < value

/-- Numbers with the same exact sign satisfy exactly the same prescribed sign condition. -/
theorem holds_iff_of_sameExactSign (sign : PolynomialSign) {left right : ℝ}
    (h : SameExactSign left right) : sign.Holds left ↔ sign.Holds right := by
  cases sign with
  | negative => exact h.1
  | zero => exact h.2.1
  | positive => exact h.2.2

/-- Every exact-sign condition defines a Borel subset of the real line. -/
theorem measurableSet_holds (sign : PolynomialSign) :
    MeasurableSet {value : ℝ | sign.Holds value} := by
  cases sign with
  | negative =>
      change MeasurableSet (Iio (0 : ℝ))
      exact measurableSet_Iio
  | zero =>
      change MeasurableSet ({0} : Set ℝ)
      exact measurableSet_singleton 0
  | positive =>
      change MeasurableSet (Ioi (0 : ℝ))
      exact measurableSet_Ioi

end PolynomialSign

/-- A polynomial sign condition pairs a multivariate real polynomial with one exact sign. -/
structure PolynomialSignCondition (ι : Type*) where
  polynomial : MvPolynomial ι ℝ
  sign : PolynomialSign

namespace PolynomialSignCondition

/-- A point satisfies a polynomial sign condition when evaluation has its prescribed sign. -/
def Holds (condition : PolynomialSignCondition ι) (x : ι → ℝ) : Prop :=
  condition.sign.Holds (MvPolynomial.eval x condition.polynomial)

/-- The solution set of one polynomial sign condition is Borel measurable. -/
theorem measurableSet_holds [Finite ι] (condition : PolynomialSignCondition ι) :
    MeasurableSet {x : ι → ℝ | condition.Holds x} := by
  let _ := Fintype.ofFinite ι
  exact (condition.sign.measurableSet_holds.preimage
    (MvPolynomial.continuous_eval condition.polynomial).measurable)

end PolynomialSignCondition

/-- A finite quantifier-free Boolean formula built from polynomial exact-sign conditions. -/
inductive SemialgebraicFormula (ι : Type*) where
  | atom (condition : PolynomialSignCondition ι)
  | falsum
  | and (left right : SemialgebraicFormula ι)
  | or (left right : SemialgebraicFormula ι)
  | not (body : SemialgebraicFormula ι)

namespace SemialgebraicFormula

/-- A point satisfies a semialgebraic formula according to its finite Boolean syntax. -/
def Holds (x : ι → ℝ) : SemialgebraicFormula ι → Prop
  | .atom condition => condition.Holds x
  | .falsum => False
  | .and left right => left.Holds x ∧ right.Holds x
  | .or left right => left.Holds x ∨ right.Holds x
  | .not body => ¬ body.Holds x

/-- Renaming polynomial variables pulls a formula back along the corresponding coordinate map. -/
noncomputable def rename (coordinate : κ → ι) :
    SemialgebraicFormula κ → SemialgebraicFormula ι
  | .atom condition => .atom
      { polynomial := MvPolynomial.rename coordinate condition.polynomial
        sign := condition.sign }
  | .falsum => .falsum
  | .and left right => .and (left.rename coordinate) (right.rename coordinate)
  | .or left right => .or (left.rename coordinate) (right.rename coordinate)
  | .not body => .not (body.rename coordinate)

/-- Formula renaming agrees with restriction of the point to the renamed coordinates. -/
@[simp] theorem holds_rename (formula : SemialgebraicFormula κ) (coordinate : κ → ι)
    (x : ι → ℝ) :
    (formula.rename coordinate).Holds x ↔ formula.Holds (fun k => x (coordinate k)) := by
  induction formula with
  | atom condition =>
      simp [rename, Holds, PolynomialSignCondition.Holds, MvPolynomial.eval_rename,
        Function.comp_def]
  | falsum => simp [rename, Holds]
  | and left right ihLeft ihRight => simp [rename, Holds, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [rename, Holds, ihLeft, ihRight]
  | not body ih => simp [rename, Holds, ih]

/-- The realization of every finite semialgebraic formula is Borel measurable. -/
theorem measurableSet_holds [Finite ι] (formula : SemialgebraicFormula ι) :
    MeasurableSet {x : ι → ℝ | formula.Holds x} := by
  induction formula with
  | atom condition => exact condition.measurableSet_holds
  | falsum => simp [Holds]
  | and left right ihLeft ihRight =>
      simpa only [Holds, Set.ofPred_and] using ihLeft.inter ihRight
  | or left right ihLeft ihRight =>
      simpa only [Holds, Set.ofPred_or] using ihLeft.union ihRight
  | not body ih =>
      convert ih.compl using 1
      ext x
      simp [Holds]

end SemialgebraicFormula

/-- A conjunctive polynomial sign clause is a finite list of exact-sign conditions, all of which
must hold at the same point. -/
abbrev PolynomialSignClause (ι : Type*) := List (PolynomialSignCondition ι)

namespace PolynomialSignClause

/-- A point satisfies a conjunctive sign clause when it satisfies every condition in the list. -/
def Holds (clause : PolynomialSignClause ι) (x : ι → ℝ) : Prop :=
  ∀ condition ∈ clause, condition.Holds x

/-- Turn a finite conjunction of polynomial sign conditions into the corresponding Boolean
semialgebraic formula; the empty conjunction is true. -/
def toFormula : PolynomialSignClause ι → SemialgebraicFormula ι
  | [] => .not .falsum
  | condition :: rest => .and (.atom condition) (toFormula rest)

/-- The formula associated with a sign clause holds exactly when every condition in the clause
holds. -/
@[simp] theorem toFormula_holds (clause : PolynomialSignClause ι) (x : ι → ℝ) :
    clause.toFormula.Holds x ↔ clause.Holds x := by
  induction clause with
  | nil => simp [toFormula, Holds, SemialgebraicFormula.Holds]
  | cons condition rest ih =>
      simp [toFormula, Holds, SemialgebraicFormula.Holds, ih]

end PolynomialSignClause

/-- A disjunctive polynomial sign normal form is a finite list of conjunctive sign clauses. -/
abbrev PolynomialSignDNF (ι : Type*) := List (PolynomialSignClause ι)

namespace PolynomialSignDNF

/-- A point satisfies a sign DNF when it satisfies at least one of its conjunctive clauses. -/
def Holds (normalForm : PolynomialSignDNF ι) (x : ι → ℝ) : Prop :=
  ∃ clause ∈ normalForm, clause.Holds x

end PolynomialSignDNF

namespace SemialgebraicFormula

private theorem clauseAppend_holds (left right : PolynomialSignClause ι) (x : ι → ℝ) :
    (left ++ right).Holds x ↔ left.Holds x ∧ right.Holds x := by
  constructor
  · intro h
    constructor
    · intro condition hmem
      exact h condition (List.mem_append_left right hmem)
    · intro condition hmem
      exact h condition (List.mem_append_right left hmem)
  · rintro ⟨hLeft, hRight⟩ condition hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hLeft condition hmem
    · exact hRight condition hmem

private def dnfAnd (left right : PolynomialSignDNF ι) : PolynomialSignDNF ι :=
  left.flatMap fun leftClause => right.map fun rightClause => leftClause ++ rightClause

private theorem dnfAnd_holds (left right : PolynomialSignDNF ι) (x : ι → ℝ) :
    (dnfAnd left right).Holds x ↔ left.Holds x ∧ right.Holds x := by
  simp [dnfAnd, PolynomialSignDNF.Holds, clauseAppend_holds]
  aesop

private theorem dnfAppend_holds (left right : PolynomialSignDNF ι) (x : ι → ℝ) :
    (left ++ right).Holds x ↔ left.Holds x ∨ right.Holds x := by
  simp [PolynomialSignDNF.Holds]
  aesop

private theorem eq_zero_or_pos_iff_not_neg (value : ℝ) :
    value = 0 ∨ 0 < value ↔ ¬ value < 0 := by
  rw [not_lt]
  constructor
  · rintro (h | h)
    · exact le_of_eq h.symm
    · exact le_of_lt h
  · intro h
    rcases h.eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr h

private theorem neg_or_eq_zero_iff_not_pos (value : ℝ) :
    value < 0 ∨ value = 0 ↔ ¬ 0 < value := by
  rw [not_lt]
  constructor
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq h
  · intro h
    exact h.lt_or_eq

private theorem atom_signDNF_and_not (condition : PolynomialSignCondition ι) :
    ∃ positive negative : PolynomialSignDNF ι,
      (∀ x, positive.Holds x ↔ (SemialgebraicFormula.atom condition).Holds x) ∧
      (∀ x, negative.Holds x ↔ ¬ (SemialgebraicFormula.atom condition).Holds x) := by
  rcases condition with ⟨polynomial, sign⟩
  cases sign with
  | negative =>
      refine ⟨[[⟨polynomial, .negative⟩]],
        [[⟨polynomial, .zero⟩], [⟨polynomial, .positive⟩]], ?_, ?_⟩
      · intro x
        simp [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds,
          PolynomialSignCondition.Holds, PolynomialSign.Holds]
      · intro x
        simpa [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds,
          PolynomialSignCondition.Holds, PolynomialSign.Holds] using
          eq_zero_or_pos_iff_not_neg (MvPolynomial.eval x polynomial)
  | zero =>
      refine ⟨[[⟨polynomial, .zero⟩]],
        [[⟨polynomial, .negative⟩], [⟨polynomial, .positive⟩]], ?_, ?_⟩
      · intro x
        simp [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds,
          PolynomialSignCondition.Holds, PolynomialSign.Holds]
      · intro x
        simp [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds,
          PolynomialSignCondition.Holds, PolynomialSign.Holds]
  | positive =>
      refine ⟨[[⟨polynomial, .positive⟩]],
        [[⟨polynomial, .negative⟩], [⟨polynomial, .zero⟩]], ?_, ?_⟩
      · intro x
        simp [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds,
          PolynomialSignCondition.Holds, PolynomialSign.Holds]
      · intro x
        simpa [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds,
          PolynomialSignCondition.Holds, PolynomialSign.Holds] using
          neg_or_eq_zero_iff_not_pos (MvPolynomial.eval x polynomial)

private theorem exists_signDNF_and_not (formula : SemialgebraicFormula ι) :
    ∃ positive negative : PolynomialSignDNF ι,
      (∀ x, positive.Holds x ↔ formula.Holds x) ∧
      (∀ x, negative.Holds x ↔ ¬ formula.Holds x) := by
  classical
  induction formula with
  | atom condition =>
      exact atom_signDNF_and_not condition
  | falsum =>
      refine ⟨[], [[]], ?_, ?_⟩
      · intro x
        simp [PolynomialSignDNF.Holds, Holds]
      · intro x
        simp [PolynomialSignDNF.Holds, PolynomialSignClause.Holds, Holds]
  | and left right ihLeft ihRight =>
      rcases ihLeft with ⟨leftPos, leftNeg, hLeftPos, hLeftNeg⟩
      rcases ihRight with ⟨rightPos, rightNeg, hRightPos, hRightNeg⟩
      refine ⟨dnfAnd leftPos rightPos, leftNeg ++ rightNeg, ?_, ?_⟩
      · intro x
        rw [dnfAnd_holds, hLeftPos x, hRightPos x]
        rfl
      · intro x
        rw [dnfAppend_holds, hLeftNeg x, hRightNeg x]
        by_cases hLeft : left.Holds x <;> by_cases hRight : right.Holds x <;>
          simp [hLeft, hRight, Holds]
  | or left right ihLeft ihRight =>
      rcases ihLeft with ⟨leftPos, leftNeg, hLeftPos, hLeftNeg⟩
      rcases ihRight with ⟨rightPos, rightNeg, hRightPos, hRightNeg⟩
      refine ⟨leftPos ++ rightPos, dnfAnd leftNeg rightNeg, ?_, ?_⟩
      · intro x
        rw [dnfAppend_holds, hLeftPos x, hRightPos x]
        rfl
      · intro x
        rw [dnfAnd_holds, hLeftNeg x, hRightNeg x]
        simp [Holds]
  | not body ih =>
      rcases ih with ⟨positive, negative, hPositive, hNegative⟩
      refine ⟨negative, positive, ?_, ?_⟩
      · intro x
        simpa [Holds] using hNegative x
      · intro x
        rw [hPositive x]
        simp [Holds]

/-- Every finite Boolean formula in exact polynomial signs has an equivalent finite disjunction
of conjunctions of exact polynomial signs.

The proof is the purely propositional normalization layer before real quantifier elimination:
push negations to atoms, replace the negation of one exact sign by the disjunction of the other
two signs, and distribute conjunction over disjunction. -/
theorem exists_signDNF (formula : SemialgebraicFormula ι) :
    ∃ normalForm : PolynomialSignDNF ι,
      ∀ x, normalForm.Holds x ↔ formula.Holds x := by
  rcases exists_signDNF_and_not formula with
    ⟨positive, _negative, hPositive, _hNegative⟩
  exact ⟨positive, hPositive⟩

end SemialgebraicFormula

/-- Extend a finite-coordinate point by one final real coordinate. -/
def appendLastCoordinate {ι : Type*} (x : ι → ℝ) (last : ℝ) : Sum ι Unit → ℝ :=
  Sum.elim x (fun _ => last)

/-- Reindex a parameter block followed by one final coordinate as an optional parameter index,
with `none` representing the final coordinate. -/
def sumUnitEquivOption (ι : Type*) : Sum ι Unit ≃ Option ι where
  toFun
    | .inl i => some i
    | .inr _ => none
  invFun
    | some i => .inl i
    | none => .inr ()
  left_inv coordinate := by
    cases coordinate with
    | inl i => rfl
    | inr u => cases u; rfl
  right_inv coordinate := by
    cases coordinate <;> rfl

/-- View a polynomial in parameter coordinates and one final coordinate as a univariate
polynomial in the final coordinate whose coefficients are parameter polynomials. -/
noncomputable def polynomialInLastCoordinate {ι : Type*}
    (polynomial : MvPolynomial (Sum ι Unit) ℝ) : Polynomial (MvPolynomial ι ℝ) :=
  MvPolynomial.optionEquivLeft ℝ ι
    (MvPolynomial.renameEquiv ℝ (sumUnitEquivOption ι) polynomial)

/-- Specialize the parameter coefficients of a polynomial in the final coordinate at a given
parameter point, leaving an ordinary real univariate polynomial. -/
noncomputable def specializePolynomialInLastCoordinate {ι : Type*}
    (x : ι → ℝ) (polynomial : MvPolynomial (Sum ι Unit) ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval x) (polynomialInLastCoordinate polynomial)

/-- Evaluating the specialized univariate polynomial at the final coordinate agrees with
evaluating the original multivariate polynomial at the extended point.

This is the first conversion lemma needed by the Sturm/subresultant projection layer: every
later root, derivative, and sign argument should pass through this equality rather than unfold
the multivariate representation directly. -/
theorem eval_specializePolynomialInLastCoordinate {ι : Type*}
    (x : ι → ℝ) (last : ℝ) (polynomial : MvPolynomial (Sum ι Unit) ℝ) :
    Polynomial.eval last (specializePolynomialInLastCoordinate x polynomial) =
      MvPolynomial.eval (appendLastCoordinate x last) polynomial := by
  change Polynomial.eval last
      (Polynomial.map (MvPolynomial.eval x)
        (MvPolynomial.optionEquivLeft ℝ ι
          (MvPolynomial.rename (sumUnitEquivOption ι) polynomial))) =
      MvPolynomial.eval (appendLastCoordinate x last) polynomial
  rw [← MvPolynomial.optionEquivLeft_elim_eval, MvPolynomial.eval_rename]
  apply congrArg (fun f : Sum ι Unit → ℝ => MvPolynomial.eval f polynomial)
  funext coordinate
  cases coordinate with
  | inl i => rfl
  | inr u => cases u; rfl

/-- Specializing the parameter coefficients cannot increase the degree in the final coordinate.

Together with `eval_specializePolynomialInLastCoordinate`, this transfers the syntactic degree
bound used by elimination to the ordinary real univariate polynomials on which Sturm arguments
operate. -/
theorem natDegree_specializePolynomialInLastCoordinate_le {ι : Type*}
    (x : ι → ℝ) (polynomial : MvPolynomial (Sum ι Unit) ℝ) :
    (specializePolynomialInLastCoordinate x polynomial).natDegree ≤
      polynomial.degreeOf (Sum.inr ()) := by
  calc
    (specializePolynomialInLastCoordinate x polynomial).natDegree ≤
        (polynomialInLastCoordinate polynomial).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf none
        (MvPolynomial.rename (sumUnitEquivOption ι) polynomial) :=
      MvPolynomial.natDegree_optionEquivLeft ℝ _
    _ = polynomial.degreeOf (Sum.inr ()) :=
      MvPolynomial.degreeOf_rename_of_injective
        (sumUnitEquivOption ι).injective (Sum.inr ())

/-- A sign clause has last-coordinate degree at most a bound when every polynomial occurring in
the clause has at most that degree in the distinguished `Unit` coordinate. -/
def LastCoordinateDegreeLE {ι : Type*} (degreeBound : ℕ)
    (clause : PolynomialSignClause (Sum ι Unit)) : Prop :=
  ∀ condition ∈ clause,
    condition.polynomial.degreeOf (Sum.inr ()) ≤ degreeBound

namespace PolynomialSignClause

/-- Substitute zero for the final coordinate of a polynomial while retaining all parameter
coordinates as polynomial variables. -/
noncomputable def eraseLastPolynomial {ι : Type*}
    (polynomial : MvPolynomial (Sum ι Unit) ℝ) : MvPolynomial ι ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun _ => 0)) polynomial

/-- If a polynomial has final-coordinate degree zero, erasing that coordinate preserves its
value at every parameter point and every value of the final coordinate. -/
theorem eval_eraseLastPolynomial_of_degreeOf_last_eq_zero {ι : Type*}
    (polynomial : MvPolynomial (Sum ι Unit) ℝ)
    (hDegree : polynomial.degreeOf (Sum.inr ()) = 0)
    (x : ι → ℝ) (last : ℝ) :
    MvPolynomial.eval x (eraseLastPolynomial polynomial) =
      MvPolynomial.eval (appendLastCoordinate x last) polynomial := by
  classical
  have hEval :
      MvPolynomial.eval x (eraseLastPolynomial polynomial) =
        MvPolynomial.eval (Sum.elim x (fun _ : Unit => 0)) polynomial := by
    rw [eraseLastPolynomial]
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_eval₂]
    have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℝ := by
      ext r
      simp
    have hX :
        (fun s : Sum ι Unit =>
          MvPolynomial.eval x (Sum.elim MvPolynomial.X (fun _ : Unit => 0) s)) =
          Sum.elim x (fun _ : Unit => 0) := by
      funext s
      cases s <;> simp
    rw [hC, hX, MvPolynomial.eval₂_id]
  rw [hEval, ← MvPolynomial.eval₂_id]
  apply MvPolynomial.eval₂_congr
  intro i monomial hi hCoefficient
  cases i with
  | inl i => rfl
  | inr lastIndex =>
      cases lastIndex
      have hle := MvPolynomial.monomial_le_degreeOf (Sum.inr ())
        (MvPolynomial.mem_support_iff.mpr hCoefficient)
      rw [hDegree] at hle
      exact False.elim
        ((Finsupp.mem_support_iff.mp hi) (Nat.eq_zero_of_le_zero hle))

/-- The maximum degree in the final coordinate among the finitely many polynomials in a sign
clause.  The empty clause has bound zero. -/
noncomputable def lastCoordinateDegreeBound {ι : Type*} :
    PolynomialSignClause (Sum ι Unit) → ℕ
  | [] => 0
  | condition :: rest =>
      max (condition.polynomial.degreeOf (Sum.inr ())) (lastCoordinateDegreeBound rest)

/-- Every polynomial occurring in a sign clause has final-coordinate degree bounded by the
clause's syntactic maximum. -/
theorem degreeOf_last_le_lastCoordinateDegreeBound {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit))
    {condition : PolynomialSignCondition (Sum ι Unit)} (hCondition : condition ∈ clause) :
    condition.polynomial.degreeOf (Sum.inr ()) ≤ clause.lastCoordinateDegreeBound := by
  induction clause with
  | nil => simp at hCondition
  | cons head rest ih =>
      rw [lastCoordinateDegreeBound]
      rw [List.mem_cons] at hCondition
      rcases hCondition with rfl | hCondition
      · exact Nat.le_max_left _ _
      · exact (ih hCondition).trans (Nat.le_max_right _ _)

end PolynomialSignClause

/-- Up-to-degree elimination says that every simultaneous exact-sign problem in one real
variable, with parameter-polynomial coefficients and final degree at most the supplied bound,
has a quantifier-free polynomial-sign description of its parameter set. -/
def LastSignClauseEliminableUpTo (ι : Type*) (degreeBound : ℕ) : Prop :=
  ∀ clause : PolynomialSignClause (Sum ι Unit),
    LastCoordinateDegreeLE degreeBound clause →
      ∃ result : SemialgebraicFormula ι, ∀ x,
        result.Holds x ↔ ∃ last : ℝ, clause.Holds (appendLastCoordinate x last)

/-- Degree-zero simultaneous sign clauses can be eliminated: none of their polynomials depends
on the final coordinate, so evaluation at any fixed final coordinate gives the required formula.

The proof should use `MvPolynomial.degreeOf_le_iff` (or `mem_vars_iff_degreeOf_ne_zero`) to remove
the final variable, then translate the finite conjunction to `SemialgebraicFormula`. -/
theorem lastSignClauseEliminableUpTo_zero (ι : Type*) :
    LastSignClauseEliminableUpTo ι 0 := by
  unfold LastSignClauseEliminableUpTo
  intro clause hDegree
  induction clause with
  | nil =>
      refine ⟨.not .falsum, ?_⟩
      intro x
      simp [SemialgebraicFormula.Holds, PolynomialSignClause.Holds]
  | cons head rest ih =>
      have hHeadDegree : head.polynomial.degreeOf (Sum.inr ()) = 0 :=
        Nat.eq_zero_of_le_zero (hDegree head (by simp))
      have hRestDegree : LastCoordinateDegreeLE 0 rest := by
        intro condition hCondition
        exact hDegree condition (by simp [hCondition])
      rcases ih hRestDegree with ⟨restFormula, hRestFormula⟩
      let erasedHead : PolynomialSignCondition ι :=
        { polynomial := PolynomialSignClause.eraseLastPolynomial head.polynomial
          sign := head.sign }
      refine ⟨.and (.atom erasedHead) restFormula, ?_⟩
      intro x
      simp only [SemialgebraicFormula.Holds]
      have hHead (last : ℝ) :
          PolynomialSignCondition.Holds erasedHead x ↔
            PolynomialSignCondition.Holds head (appendLastCoordinate x last) := by
        unfold erasedHead PolynomialSignCondition.Holds
        rw [PolynomialSignClause.eval_eraseLastPolynomial_of_degreeOf_last_eq_zero
          head.polynomial hHeadDegree x last]
      constructor
      · rintro ⟨hErasedHead, hRest⟩
        rcases (hRestFormula x).mp hRest with ⟨last, hRestLast⟩
        refine ⟨last, ?_⟩
        intro condition hCondition
        rw [List.mem_cons] at hCondition
        rcases hCondition with rfl | hCondition
        · exact (hHead last).mp hErasedHead
        · exact hRestLast condition hCondition
      · rintro ⟨last, hClause⟩
        refine ⟨(hHead last).mpr ?_, (hRestFormula x).mpr ⟨last, ?_⟩⟩
        · exact hClause head (by simp)
        · intro condition hCondition
          exact hClause condition (by simp [hCondition])

/-- A finite family of parameter polynomials controls a last-coordinate sign clause when two
parameter points with the same exact signs on that family either both have, or both lack, a
last-coordinate witness for the clause.

This is the finite sign-stratification conclusion supplied by the projection-polynomial part of
CAD.  It deliberately records only the invariant needed by Boolean assembly: concrete
coefficient, discriminant, and subresultant constructions belong in the proof of existence. -/
def LastSignClauseProjectionControl {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit))
    (projectionFamily : Finset (MvPolynomial ι ℝ)) : Prop :=
  ∀ left right : ι → ℝ,
    (∀ polynomial ∈ projectionFamily,
      SameExactSign (MvPolynomial.eval left polynomial)
        (MvPolynomial.eval right polynomial)) →
      ((∃ last : ℝ, clause.Holds (appendLastCoordinate left last)) ↔
        ∃ last : ℝ, clause.Holds (appendLastCoordinate right last))

/-- The realizable sign table of a specialized last-coordinate clause records, for every
assignment of exact signs to its polynomial occurrences, whether one real last coordinate
simultaneously realizes those signs. -/
def RealizesLastSignPattern {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit)) (x : ι → ℝ)
    (pattern : PolynomialSignCondition (Sum ι Unit) → PolynomialSign) : Prop :=
  ∃ last : ℝ, ∀ condition ∈ clause,
    (pattern condition).Holds
      (MvPolynomial.eval (appendLastCoordinate x last) condition.polynomial)

/-- Two parameter points have the same specialized sign table when every simultaneous exact-sign
assignment to the clause polynomials is realizable over one point exactly when it is realizable
over the other.  This is the section/sector invariant supplied by delineability. -/
def SameLastSignTable {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit)) (left right : ι → ℝ) : Prop :=
  ∀ pattern : PolynomialSignCondition (Sum ι Unit) → PolynomialSign,
    RealizesLastSignPattern clause left pattern ↔ RealizesLastSignPattern clause right pattern

/-- Two specialized polynomial families have the same ordered root data when one increasing
equivalence preserves every degree, leading sign, and real-root multiplicity. -/
def SameLastRootData {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit)) (left right : ι → ℝ) : Prop :=
  ∃ transport : ℝ ≃o ℝ, ∀ condition ∈ clause,
    PolynomialRootDataTransportedBy transport
      (specializePolynomialInLastCoordinate left condition.polynomial)
      (specializePolynomialInLastCoordinate right condition.polynomial)
/-- Two parameter points give every clause polynomial the same specialized degree and leading
coefficient sign. -/
def SameLastDegreeLeadingData {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit)) (left right : ι → ℝ) : Prop :=
  ∀ condition ∈ clause,
    (specializePolynomialInLastCoordinate left condition.polynomial).natDegree =
      (specializePolynomialInLastCoordinate right condition.polynomial).natDegree ∧
    SameExactSign (specializePolynomialInLastCoordinate left condition.polynomial).leadingCoeff
      (specializePolynomialInLastCoordinate right condition.polynomial).leadingCoeff
/-- One increasing equivalence transports the real-root multiplicities of every polynomial in a
clause, recording the common order, coincidences, and multiplicities of all real roots. -/
def SameLastRootMultiplicitiesTransportedBy {ι : Type*} (transport : ℝ ≃o ℝ)
    (clause : PolynomialSignClause (Sum ι Unit)) (left right : ι → ℝ) : Prop :=
  ∀ condition ∈ clause, ∀ root : ℝ,
    (specializePolynomialInLastCoordinate left condition.polynomial).rootMultiplicity root =
    (specializePolynomialInLastCoordinate right condition.polynomial).rootMultiplicity
      (transport root)
/-- Common degree and leading-sign data together with one simultaneous root-multiplicity
transport give the full transported root data for a last-coordinate clause. -/
theorem sameLastRootData_of_degreeLeading_and_rootMultiplicities {ι : Type*}
    {clause : PolynomialSignClause (Sum ι Unit)} {left right : ι → ℝ}
    (hDegreeLeading : SameLastDegreeLeadingData clause left right)
    {transport : ℝ ≃o ℝ}
    (hRoots : SameLastRootMultiplicitiesTransportedBy transport clause left right) :
    SameLastRootData clause left right := by
  refine ⟨transport, ?_⟩
  intro condition hCondition
  exact ⟨(hDegreeLeading condition hCondition).1,
    (hDegreeLeading condition hCondition).2, hRoots condition hCondition⟩
/-- A finite family containing all parameter coefficients controls every specialized degree and
leading sign, including identically-zero specializations. -/
theorem exists_lastDegreeLeadingProjectionFamily {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit)) :
    ∃ projectionFamily : Finset (MvPolynomial ι ℝ),
      ∀ left right : ι → ℝ,
        (∀ polynomial ∈ projectionFamily,
          SameExactSign (MvPolynomial.eval left polynomial) (MvPolynomial.eval right polynomial)) →
        SameLastDegreeLeadingData clause left right := by
  classical
  induction clause with
  | nil =>
      refine ⟨∅, ?_⟩
      intro left right hSigns condition hCondition
      simp at hCondition
  | cons head rest ih =>
      let coefficients := polynomialInLastCoordinate head.polynomial
      let headFamily : Finset (MvPolynomial ι ℝ) :=
        coefficients.support.image coefficients.coeff
      rcases ih with ⟨restFamily, hRestFamily⟩
      refine ⟨headFamily ∪ restFamily, ?_⟩
      intro left right hSigns condition hCondition
      rw [List.mem_cons] at hCondition
      rcases hCondition with rfl | hCondition
      · let leftPolynomial :=
          specializePolynomialInLastCoordinate left condition.polynomial
        let rightPolynomial :=
          specializePolynomialInLastCoordinate right condition.polynomial
        have hCoefficientSign (degree : ℕ) :
            SameExactSign (leftPolynomial.coeff degree) (rightPolynomial.coeff degree) := by
          simp only [leftPolynomial, rightPolynomial,
            specializePolynomialInLastCoordinate, Polynomial.coeff_map]
          change SameExactSign (MvPolynomial.eval left (coefficients.coeff degree))
            (MvPolynomial.eval right (coefficients.coeff degree))
          by_cases hCoefficient : coefficients.coeff degree = 0
          · rw [hCoefficient]
            simp [SameExactSign]
          · have hDegreeSupport : degree ∈ coefficients.support :=
              Polynomial.mem_support_iff.mpr hCoefficient
            have hCoefficientMem : coefficients.coeff degree ∈ headFamily :=
              Finset.mem_image.mpr ⟨degree, hDegreeSupport, rfl⟩
            exact hSigns (coefficients.coeff degree)
              (Finset.mem_union_left restFamily hCoefficientMem)
        have hSupport : leftPolynomial.support = rightPolynomial.support := by
          ext degree
          simp only [Polynomial.mem_support_iff]
          exact not_congr (hCoefficientSign degree).2.1
        have hDegree : leftPolynomial.natDegree = rightPolynomial.natDegree :=
          Polynomial.natDegree_eq_of_degree_eq (by unfold Polynomial.degree; rw [hSupport])
        refine ⟨hDegree, ?_⟩
        have hLeading := hCoefficientSign leftPolynomial.natDegree
        rw [Polynomial.coeff_natDegree, hDegree, Polynomial.coeff_natDegree] at hLeading
        exact hLeading
      · exact hRestFamily left right
          (fun polynomial hPolynomial =>
            hSigns polynomial (Finset.mem_union_right headFamily hPolynomial))
          condition hCondition
/-- Assuming elimination through degree `d`, a finite principal-subresultant family controls the
simultaneous ordered real-root multiplicities of a degree-`d + 1` clause once coefficient data is
fixed. -/
theorem exists_lastRootMultiplicityTransportProjectionFamily_succ {ι : Type*} (d : ℕ)
    (hLower : LastSignClauseEliminableUpTo ι d)
    (clause : PolynomialSignClause (Sum ι Unit))
    (hDegree : LastCoordinateDegreeLE (d + 1) clause) :
    ∃ projectionFamily : Finset (MvPolynomial ι ℝ),
      ∀ left right : ι → ℝ,
        (∀ polynomial ∈ projectionFamily,
          SameExactSign (MvPolynomial.eval left polynomial) (MvPolynomial.eval right polynomial)) →
        SameLastDegreeLeadingData clause left right →
        ∃ transport : ℝ ≃o ℝ,
          SameLastRootMultiplicitiesTransportedBy transport clause left right := by
  sorry
/-- Simultaneously transported ordered root data preserves every realizable exact-sign pattern of
a specialized last-coordinate polynomial family. -/
theorem sameLastSignTable_of_sameLastRootData {ι : Type*}
    {clause : PolynomialSignClause (Sum ι Unit)} {left right : ι → ℝ}
    (h : SameLastRootData clause left right) : SameLastSignTable clause left right := by
  rcases h with ⟨transport, hTransport⟩
  intro pattern
  constructor
  · rintro ⟨last, hLast⟩
    refine ⟨transport last, ?_⟩
    intro condition hCondition
    have hSign := sameExactSign_eval_of_rootDataTransportedBy transport _ _
      (hTransport condition hCondition) last
    rw [eval_specializePolynomialInLastCoordinate,
      eval_specializePolynomialInLastCoordinate] at hSign
    exact ((pattern condition).holds_iff_of_sameExactSign hSign).mp
      (hLast condition hCondition)
  · rintro ⟨last, hLast⟩
    refine ⟨transport.symm last, ?_⟩
    intro condition hCondition
    have hSign := sameExactSign_eval_of_rootDataTransportedBy transport.symm _ _
      (hTransport condition hCondition).symm last
    rw [eval_specializePolynomialInLastCoordinate,
      eval_specializePolynomialInLastCoordinate] at hSign
    exact ((pattern condition).holds_iff_of_sameExactSign hSign).mp
      (hLast condition hCondition)

/-- A finite coefficient/subresultant family controls the ordered root data of every
last-coordinate degree-`d + 1` clause, assuming elimination through degree `d`. -/
theorem exists_lastSignClauseRootDataProjectionFamily_succ {ι : Type*} (d : ℕ)
    (hLower : LastSignClauseEliminableUpTo ι d)
    (clause : PolynomialSignClause (Sum ι Unit))
    (hDegree : LastCoordinateDegreeLE (d + 1) clause) :
    ∃ projectionFamily : Finset (MvPolynomial ι ℝ),
      ∀ left right : ι → ℝ,
        (∀ polynomial ∈ projectionFamily,
          SameExactSign (MvPolynomial.eval left polynomial)
            (MvPolynomial.eval right polynomial)) →
        SameLastRootData clause left right := by
  classical
  rcases exists_lastDegreeLeadingProjectionFamily clause with
    ⟨degreeFamily, hDegreeFamily⟩
  rcases exists_lastRootMultiplicityTransportProjectionFamily_succ d hLower clause hDegree with
    ⟨rootFamily, hRootFamily⟩
  refine ⟨degreeFamily ∪ rootFamily, ?_⟩
  intro left right hSigns
  have hDegreeLeading : SameLastDegreeLeadingData clause left right :=
    hDegreeFamily left right fun polynomial hPolynomial =>
      hSigns polynomial (Finset.mem_union_left rootFamily hPolynomial)
  rcases hRootFamily left right
      (fun polynomial hPolynomial =>
        hSigns polynomial (Finset.mem_union_right degreeFamily hPolynomial))
      hDegreeLeading with ⟨transport, hRoots⟩
  exact sameLastRootData_of_degreeLeading_and_rootMultiplicities hDegreeLeading hRoots

/-- A finite parameter-polynomial family controls the complete specialized sign table of every
clause of degree at most `d + 1`, assuming elimination through degree `d`.

This is the focused delineability kernel.  Following Hong's projection theorem, the proof must
adjoin coefficient polynomials and the principal subresultant coefficients of each reduced
polynomial with its derivative and with every other clause polynomial.  Constant exact signs of
that family fix degree drops, root multiplicities, common roots, root order, and hence all signs
on the resulting sections and sectors. -/
theorem exists_lastSignClauseSignTableProjectionFamily_succ {ι : Type*} (d : ℕ)
    (hLower : LastSignClauseEliminableUpTo ι d)
    (clause : PolynomialSignClause (Sum ι Unit))
    (hDegree : LastCoordinateDegreeLE (d + 1) clause) :
    ∃ projectionFamily : Finset (MvPolynomial ι ℝ),
      ∀ left right : ι → ℝ,
        (∀ polynomial ∈ projectionFamily,
          SameExactSign (MvPolynomial.eval left polynomial)
            (MvPolynomial.eval right polynomial)) →
        SameLastSignTable clause left right := by
  rcases exists_lastSignClauseRootDataProjectionFamily_succ d hLower clause hDegree with
    ⟨projectionFamily, hRootData⟩
  exact ⟨projectionFamily, fun left right hSigns =>
    sameLastSignTable_of_sameLastRootData (hRootData left right hSigns)⟩

private noncomputable def exactSignOfReal (value : ℝ) : PolynomialSign :=
  if value < 0 then .negative else if value = 0 then .zero else .positive

private theorem exactSignOfReal_holds (value : ℝ) :
    (exactSignOfReal value).Holds value := by
  by_cases hneg : value < 0
  · simp [exactSignOfReal, hneg, PolynomialSign.Holds]
  · by_cases hzero : value = 0
    · simp [exactSignOfReal, hzero, PolynomialSign.Holds]
    · have hpos : 0 < value :=
        lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
      simp [exactSignOfReal, hneg, hzero, PolynomialSign.Holds, hpos]

private theorem sameExactSign_of_sign_holds {sign : PolynomialSign} {left right : ℝ}
    (hleft : sign.Holds left) (hright : sign.Holds right) :
    SameExactSign left right := by
  cases sign with
  | negative =>
      simp only [PolynomialSign.Holds] at hleft hright
      refine ⟨iff_of_true hleft hright, ?_, ?_⟩
      · constructor <;> intro hzero <;> linarith
      · constructor <;> intro hpos <;> linarith
  | zero =>
      simp only [PolynomialSign.Holds] at hleft hright
      subst left
      subst right
      simp [SameExactSign]
  | positive =>
      simp only [PolynomialSign.Holds] at hleft hright
      refine ⟨?_, ?_, iff_of_true hleft hright⟩
      · constructor <;> intro hneg <;> linarith
      · constructor <;> intro hzero <;> linarith

private noncomputable def signAssignmentClause {ι : Type*}
    (projectionFamily : Finset (MvPolynomial ι ℝ))
    (assignment : projectionFamily → PolynomialSign) : PolynomialSignClause ι :=
  projectionFamily.attach.toList.map fun polynomial =>
    { polynomial := polynomial.1
      sign := assignment polynomial }

private theorem signAssignmentClause_holds {ι : Type*}
    (projectionFamily : Finset (MvPolynomial ι ℝ))
    (assignment : projectionFamily → PolynomialSign) (x : ι → ℝ) :
    (signAssignmentClause projectionFamily assignment).Holds x ↔
      ∀ polynomial : projectionFamily,
        (assignment polynomial).Holds (MvPolynomial.eval x polynomial.1) := by
  constructor
  · intro h polynomial
    apply h { polynomial := polynomial.1, sign := assignment polynomial }
    apply List.mem_map.mpr
    exact ⟨polynomial, by simp, rfl⟩
  · intro h condition hCondition
    rcases List.mem_map.mp hCondition with ⟨polynomial, _, hPolynomial⟩
    subst condition
    exact h polynomial

private def disjoinSignClauses {ι : Type*} :
    List (PolynomialSignClause ι) → SemialgebraicFormula ι
  | [] => .falsum
  | clause :: rest => .or clause.toFormula (disjoinSignClauses rest)

private theorem disjoinSignClauses_holds {ι : Type*}
    (clauses : List (PolynomialSignClause ι)) (x : ι → ℝ) :
    (disjoinSignClauses clauses).Holds x ↔
      ∃ clause ∈ clauses, clause.Holds x := by
  induction clauses with
  | nil =>
      simp [disjoinSignClauses, SemialgebraicFormula.Holds]
  | cons clause rest ih =>
      simp [disjoinSignClauses, SemialgebraicFormula.Holds, ih]

/-- If feasibility of a last-coordinate sign clause is constant on the exact-sign strata of a
finite parameter-polynomial family, then feasibility is described by a quantifier-free
semialgebraic formula.

The proof is finite Boolean assembly.  Enumerate the three-valued sign assignments on the
projection family, retain the assignments realized by a feasible parameter point, and disjoin
their conjunctions of exact-sign atoms. -/
theorem exists_formula_of_lastSignClauseProjectionControl {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit))
    (projectionFamily : Finset (MvPolynomial ι ℝ))
    (hControl : LastSignClauseProjectionControl clause projectionFamily) :
    ∃ result : SemialgebraicFormula ι, ∀ x,
      result.Holds x ↔ ∃ last : ℝ, clause.Holds (appendLastCoordinate x last) := by
  classical
  let feasibleAssignments :=
    (Finset.univ : Finset (projectionFamily → PolynomialSign)).filter fun assignment =>
      ∃ representative : ι → ℝ,
        (∃ last : ℝ, clause.Holds (appendLastCoordinate representative last)) ∧
          (signAssignmentClause projectionFamily assignment).Holds representative
  let result :=
    disjoinSignClauses
      (feasibleAssignments.toList.map (signAssignmentClause projectionFamily))
  refine ⟨result, ?_⟩
  intro x
  rw [disjoinSignClauses_holds]
  constructor
  · rintro ⟨signClause, hSignClause, hClauseX⟩
    rcases List.mem_map.mp hSignClause with ⟨assignment, hAssignment, rfl⟩
    have hAssignment' : assignment ∈ feasibleAssignments := by
      exact Finset.mem_toList.mp hAssignment
    rcases (Finset.mem_filter.mp hAssignment').2 with
      ⟨representative, hFeasibleRepresentative, hClauseRepresentative⟩
    apply (hControl representative x ?_).mp hFeasibleRepresentative
    intro polynomial hPolynomial
    let polynomial' : projectionFamily := ⟨polynomial, hPolynomial⟩
    exact sameExactSign_of_sign_holds
      ((signAssignmentClause_holds projectionFamily assignment representative).mp
        hClauseRepresentative polynomial')
      ((signAssignmentClause_holds projectionFamily assignment x).mp hClauseX polynomial')
  · intro hFeasibleX
    let assignment : projectionFamily → PolynomialSign :=
      fun polynomial => exactSignOfReal (MvPolynomial.eval x polynomial.1)
    have hClauseX : (signAssignmentClause projectionFamily assignment).Holds x := by
      rw [signAssignmentClause_holds]
      intro polynomial
      exact exactSignOfReal_holds _
    have hAssignment : assignment ∈ feasibleAssignments := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ assignment, x, hFeasibleX, hClauseX⟩
    refine ⟨signAssignmentClause projectionFamily assignment, ?_, hClauseX⟩
    apply List.mem_map.mpr
    exact ⟨assignment, Finset.mem_toList.mpr hAssignment, rfl⟩

/-- Assuming elimination through degree `d`, every clause of final degree at most `d + 1` has a
finite family of parameter projection polynomials whose exact-sign strata control whether its
last-coordinate fiber is nonempty.

This is the delineability/projection-family kernel of the induction step.  Its proof must build
the relevant coefficient, derivative, principal-subresultant, and resultant polynomials, split
off degree drops, and use the lower-degree eliminator to show that root order and all simultaneous
clause signs are constant on every resulting parameter sign stratum. -/
theorem exists_lastSignClauseProjectionControl_succ {ι : Type*} (d : ℕ)
    (hLower : LastSignClauseEliminableUpTo ι d)
    (clause : PolynomialSignClause (Sum ι Unit))
    (hDegree : LastCoordinateDegreeLE (d + 1) clause) :
    ∃ projectionFamily : Finset (MvPolynomial ι ℝ),
      LastSignClauseProjectionControl clause projectionFamily := by
  rcases exists_lastSignClauseSignTableProjectionFamily_succ d hLower clause hDegree with
    ⟨projectionFamily, hSignTable⟩
  refine ⟨projectionFamily, ?_⟩
  intro left right hProjectionSigns
  have hTable := hSignTable left right hProjectionSigns (fun condition => condition.sign)
  simpa [RealizesLastSignPattern, PolynomialSignClause.Holds,
    PolynomialSignCondition.Holds] using hTable

/-- The degree-induction step for one-variable simultaneous sign elimination.  Assuming all
clauses of final degree at most `d` can be eliminated, clauses of degree at most `d + 1` can be
eliminated as well.

This is the algebraic heart of Tarski elimination.  A proof must split on leading coefficients
and use derivatives together with a finite subresultant/Sturm projection family; the signs of
that family reduce all recursive final-coordinate obligations to degree at most `d`. -/
theorem lastSignClauseEliminableUpTo_succ {ι : Type*} (d : ℕ)
    (hLower : LastSignClauseEliminableUpTo ι d) :
    LastSignClauseEliminableUpTo ι (d + 1) := by
  intro clause hDegree
  rcases exists_lastSignClauseProjectionControl_succ d hLower clause hDegree with
    ⟨projectionFamily, hControl⟩
  exact exists_formula_of_lastSignClauseProjectionControl clause projectionFamily hControl

/-- Simultaneous sign clauses of every finite final-coordinate degree support one-variable
elimination. -/
theorem lastSignClauseEliminableUpTo_all (ι : Type*) (d : ℕ) :
    LastSignClauseEliminableUpTo ι d := by
  induction d with
  | zero => exact lastSignClauseEliminableUpTo_zero ι
  | succ d ih =>
      simpa [Nat.succ_eq_add_one] using lastSignClauseEliminableUpTo_succ d ih

/-- One-variable Tarski elimination for a conjunction of exact polynomial sign conditions:
the set of parameters for which the final-coordinate fiber realizes the clause is definable by a
quantifier-free polynomial sign formula.

This is the first genuinely algebraic projection kernel.  A proof must construct the finite
coefficient/discriminant/subresultant projection family controlling realizable sign patterns of
the specialized univariate polynomials; choosing a root or witness does not prove the required
quantifier-free conclusion. -/
theorem exists_formula_eliminating_last_signClause {ι : Type*}
    (clause : PolynomialSignClause (Sum ι Unit)) :
    ∃ result : SemialgebraicFormula ι, ∀ x,
      result.Holds x ↔ ∃ last : ℝ, clause.Holds (appendLastCoordinate x last) := by
  exact lastSignClauseEliminableUpTo_all ι clause.lastCoordinateDegreeBound clause
    (fun condition hCondition =>
      clause.degreeOf_last_le_lastCoordinateDegreeBound hCondition)

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice
