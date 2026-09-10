import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Finite sign-condition semialgebraic sets

A small normal-form API sufficient to state that a finite nearest-net selector
has a semialgebraic graph. No projection or quantifier-elimination theorem is
postulated.
-/

open Set

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- A weak or strict polynomial sign condition. -/
structure PolynomialSignCondition (ι : Type*) where
  polynomial : MvPolynomial ι ℝ
  strict : Bool

/-- Evaluation of a polynomial sign condition. -/
def PolynomialSignCondition.Holds (a : PolynomialSignCondition ι) (x : ι → ℝ) : Prop :=
  if a.strict then 0 < MvPolynomial.eval x a.polynomial
  else 0 ≤ MvPolynomial.eval x a.polynomial

/-- A set in finite real coordinates is semialgebraic when it is represented
as a finite union of finite intersections of polynomial sign conditions. -/
def IsSemialgebraicSet [Fintype ι] (S : Set (ι → ℝ)) : Prop :=
  ∃ clauses : List (List (PolynomialSignCondition ι)),
    S = {x | ∃ clause ∈ clauses, ∀ atom ∈ clause, atom.Holds x}

/-- The graph of a finite-coordinate map is semialgebraic. -/
def IsSemialgebraicMap [Fintype ι] [Fintype κ]
    (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  IsSemialgebraicSet
    {z : Sum ι κ → ℝ | ∀ j, z (Sum.inr j) = f (fun i => z (Sum.inl i)) j}

/-- Semialgebraic sign-condition normal forms are Borel sets. -/
lemma IsSemialgebraicSet.measurableSet [Fintype ι] {S : Set (ι → ℝ)}
    (hS : IsSemialgebraicSet S) : MeasurableSet S := by
  rcases hS with ⟨clauses, rfl⟩
  have hatom : ∀ a : PolynomialSignCondition ι, MeasurableSet {x | a.Holds x} := by
    intro a
    unfold PolynomialSignCondition.Holds
    split
    · change MeasurableSet ((fun x => MvPolynomial.eval x a.polynomial) ⁻¹' Set.Ioi 0)
      exact (MvPolynomial.continuous_eval a.polynomial).measurable measurableSet_Ioi
    · change MeasurableSet ((fun x => MvPolynomial.eval x a.polynomial) ⁻¹' Set.Ici 0)
      exact (MvPolynomial.continuous_eval a.polynomial).measurable measurableSet_Ici
  have hclause : ∀ c : List (PolynomialSignCondition ι),
      MeasurableSet {x | ∀ atom ∈ c, atom.Holds x} := by
    intro c
    induction c with
    | nil => simp
    | cons a c ih =>
      convert (hatom a).inter ih using 1 <;> ext x <;> simp
  induction clauses with
  | nil => simp
  | cons c cs ih =>
    convert (hclause c).union ih using 1 <;> ext x <;> simp

/-- A finite union of normal-form semialgebraic sets remains semialgebraic. -/
lemma isSemialgebraicSet_iUnion_finset [Fintype ι] {κ : Type*}
    (F : Finset κ) (S : κ → Set (ι → ℝ))
    (hS : ∀ k ∈ F, IsSemialgebraicSet (S k)) :
    IsSemialgebraicSet (⋃ k ∈ F, S k) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨[], ?_⟩
      simp
  | @insert a F ha ih =>
      rcases hS a (by simp) with ⟨ca, hca⟩
      rcases ih (fun k hk => hS k (by simp [hk])) with ⟨cF, hcF⟩
      refine ⟨ca ++ cF, ?_⟩
      rw [show (⋃ k ∈ insert a F, S k) = S a ∪ ⋃ k ∈ F, S k by simp]
      rw [hca, hcF]
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
      aesop

end CausalSmith.ExactID.CovshiftProfilequotientTargets
