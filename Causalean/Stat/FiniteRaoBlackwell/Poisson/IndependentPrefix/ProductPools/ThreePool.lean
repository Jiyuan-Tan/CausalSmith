/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools.Risk

/-!
# Direct finite-alphabet three-pool specialization

This module specializes the finite-family risk theorem to one pool on an
alphabet `A` and two distinct, independently prefixed pools sharing alphabet
`B` and observation law `Q`.  Capacities and Poisson intensities remain fully
heterogeneous across the three coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat

universe uX

/-- [The three-pool index](goal) distinguishes one complete pool from two independently
randomized shared-alphabet pools. [Its complete coordinate is available](step:complete),
[its left shared coordinate is available](step:sharedLeft), and [its right shared coordinate
is available](step:sharedRight). -/
inductive ThreePoolIndex
  | complete
  | sharedLeft
  | sharedRight

/-- [Decidable equality for the three-pool index](goal) distinguishes exactly its equal and
unequal coordinate labels. [It is given by the nine constructor comparisons](step:1). -/
instance : DecidableEq ThreePoolIndex := fun x y => by
  cases x <;> cases y
  · exact isTrue rfl
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · exact isTrue rfl
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · exact isTrue rfl

/-- [The three-pool index has a finite enumeration](goal). [The enumeration is given](step:1) and
[its completeness certificate is given](step:2). -/
instance : Fintype ThreePoolIndex where
  elems := {.complete, .sharedLeft, .sharedRight}
  complete i := by cases i <;> simp

/-- Given [the complete-pool alphabet](hyp:A) and [the shared-pool alphabet](hyp:B), [the
three-pool alphabet family](goal) assigns the latter independently to both shared coordinates.
[It is given by the coordinate case split](step:1). -/
abbrev ThreePoolAlphabet (A : Type uX) (B : Type uX) : ThreePoolIndex → Type uX :=
  fun i ↦ match i with
    | .complete => A
    | .sharedLeft => B
    | .sharedRight => B

/-- Given [a complete-pool alphabet](hyp:A) and [a shared-pool alphabet](hyp:B), [the
coordinatewise measurable-space structure](goal) is inherited from the corresponding alphabet.
[It is given by the three coordinate cases](step:1). -/
instance threePoolAlphabetMeasurableSpace
    {A : Type uX} {B : Type uX} [MeasurableSpace A] [MeasurableSpace B] :
    (i : ThreePoolIndex) → MeasurableSpace (ThreePoolAlphabet A B i)
  | .complete => inferInstance
  | .sharedLeft => inferInstance
  | .sharedRight => inferInstance

/-- Given [a complete-pool alphabet](hyp:A) and [a shared-pool alphabet](hyp:B), [the
coordinatewise finite-type structure](goal) is inherited from the corresponding alphabet.
[It is given by the three coordinate cases](step:1). -/
instance threePoolAlphabetFintype
    {A : Type uX} {B : Type uX} [Fintype A] [Fintype B] :
    (i : ThreePoolIndex) → Fintype (ThreePoolAlphabet A B i)
  | .complete => inferInstance
  | .sharedLeft => inferInstance
  | .sharedRight => inferInstance

/-- Given [a complete-pool alphabet](hyp:A) and [a shared-pool alphabet](hyp:B), [the
coordinatewise decidable-equality structure](goal) is inherited from the corresponding alphabet.
[It is given by the three coordinate cases](step:1). -/
instance threePoolAlphabetDecidableEq
    {A : Type uX} {B : Type uX} [DecidableEq A] [DecidableEq B] :
    (i : ThreePoolIndex) → DecidableEq (ThreePoolAlphabet A B i)
  | .complete => inferInstance
  | .sharedLeft => inferInstance
  | .sharedRight => inferInstance

/-- Given [a complete-pool alphabet](hyp:A) and [a shared-pool alphabet](hyp:B), [the
coordinatewise measurable-singleton structure](goal) is inherited from the corresponding alphabet.
[It is given by the three coordinate cases](step:1). -/
instance threePoolAlphabetMeasurableSingletonClass
    {A : Type uX} {B : Type uX} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (i : ThreePoolIndex) → MeasurableSingletonClass (ThreePoolAlphabet A B i)
  | .complete => inferInstance
  | .sharedLeft => inferInstance
  | .sharedRight => inferInstance

/-- Given [the complete-pool law](hyp:P) and [the shared-pool law](hyp:Q), [the three-pool
observation-law family](goal) assigns the shared law separately to both shared coordinates.
[It is given by the coordinate case split](step:1). -/
def threePoolObservationLaw {A : Type uX} {B : Type uX}
    [MeasurableSpace A] [MeasurableSpace B] (P : Measure A) (Q : Measure B) :
    (i : ThreePoolIndex) → Measure (ThreePoolAlphabet A B i)
  | .complete => P
  | .sharedLeft => Q
  | .sharedRight => Q

/-- Given [the complete-pool law](hyp:P), [the shared-pool law](hyp:Q), and [a coordinate](hyp:i),
[the assigned observation law is a probability measure](goal). [It is given by the coordinate
case split](step:1). -/
instance threePoolObservationLawIsProbabilityMeasure
    {A : Type uX} {B : Type uX} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (i : ThreePoolIndex) : IsProbabilityMeasure (threePoolObservationLaw P Q i) := by
  cases i <;> simp only [threePoolObservationLaw] <;> infer_instance

/-- Given [the complete-pool capacity](hyp:NComplete), [the left shared-pool
capacity](hyp:NLeft), and [the right shared-pool capacity](hyp:NRight), [the three-pool
capacity function](goal) records all three without identifying the shared pools. [It is given
by the coordinate case split](step:1). -/
def threePoolCapacity (NComplete NLeft NRight : ℕ) : ThreePoolIndex → ℕ
  | .complete => NComplete
  | .sharedLeft => NLeft
  | .sharedRight => NRight

/-- Given [the complete-pool intensity](hyp:lambdaComplete), [the left shared-pool
intensity](hyp:lambdaLeft), and [the right shared-pool intensity](hyp:lambdaRight),
[the three-pool intensity function](goal) records all three independently. [It is given
by the coordinate case split](step:1). -/
def threePoolIntensity
    (lambdaComplete lambdaLeft lambdaRight : ℝ≥0) : ThreePoolIndex → ℝ≥0
  | .complete => lambdaComplete
  | .sharedLeft => lambdaLeft
  | .sharedRight => lambdaRight

/-- Given [the complete-pool law](hyp:P), [the shared-pool law](hyp:Q),
[three Poisson intensities](hyp:lambdaComplete,lambdaLeft,lambdaRight),
[three pool capacities](hyp:NComplete,NLeft,NRight), [a measurable prefix statistic](hyp:hT),
[an ordered outcome interval](hyp:hab), [a statistic confined to it](hyp:hTmem),
[a target in it](hyp:htheta), and [an overflow value in it](hyp:hzOver),
[the three-pool Rao--Blackwell risk is bounded by untruncated risk plus three upper-tail
terms](goal). [The finite-family bound supplies this conclusion](step:1). -/
theorem finiteAlphabet_threePoolSharedLaw_risk_le
    {A : Type uX} {B : Type uX}
    [MeasurableSpace A] [Finite A] [MeasurableSingletonClass A] [DecidableEq A]
    [MeasurableSpace B] [Finite B] [MeasurableSingletonClass B] [DecidableEq B]
    (P : Measure A) [IsProbabilityMeasure P]
    (Q : Measure B) [IsProbabilityMeasure Q]
    (lambdaComplete lambdaLeft lambdaRight : ℝ≥0)
    (NComplete NLeft NRight : ℕ)
    {T : PrefixFamily (ThreePoolAlphabet A B) → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    let P₃ := threePoolObservationLaw P Q
    let lambda₃ := threePoolIntensity lambdaComplete lambdaLeft lambdaRight
    let N₃ := threePoolCapacity NComplete NLeft NRight
    sqRisk (fixedPoolsLaw P₃ N₃)
        (prefixRaoBlackwellStatistic lambda₃ T zOver) theta ≤
      sqRisk (independentPoissonPrefixLaw P₃ lambda₃) T theta +
        (b - a) ^ 2 *
          ((poissonMeasure lambdaComplete).real (Set.Ioi NComplete) +
            (poissonMeasure lambdaLeft).real (Set.Ioi NLeft) +
            (poissonMeasure lambdaRight).real (Set.Ioi NRight)) := by
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  -- Instantiate `sqRisk_prefixRaoBlackwellStatistic_le`; simplify the finite
  -- sum by cases on `ThreePoolIndex` and normalize real addition.
  dsimp only
  have h := sqRisk_prefixRaoBlackwellStatistic_le
    (I := ThreePoolIndex) (X := ThreePoolAlphabet A B)
    (threePoolObservationLaw P Q)
    (threePoolIntensity lambdaComplete lambdaLeft lambdaRight)
    (threePoolCapacity NComplete NLeft NRight)
    hT hab hTmem htheta hzOver
  have hsum :
      (∑ i : ThreePoolIndex,
        (poissonMeasure (threePoolIntensity lambdaComplete lambdaLeft lambdaRight i)).real
          (Set.Ioi (threePoolCapacity NComplete NLeft NRight i))) =
        (poissonMeasure lambdaComplete).real (Set.Ioi NComplete) +
          (poissonMeasure lambdaLeft).real (Set.Ioi NLeft) +
          (poissonMeasure lambdaRight).real (Set.Ioi NRight) := by
    rw [show (Finset.univ : Finset ThreePoolIndex) =
        {.complete, .sharedLeft, .sharedRight} by
      ext i
      cases i <;> simp]
    simp [threePoolIntensity, threePoolCapacity, add_assoc]
  rwa [hsum] at h

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
