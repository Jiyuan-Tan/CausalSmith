module
public import Mathlib.MeasureTheory.Integral.Pi

/-! Reindexing the three independent Poisson pools inside one hybrid cell. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory

/-- Evaluate a Boolean-indexed vector in the order `false, true`.  [the stated conditions](hyp:f) [the stated conclusion](goal). -/
def boolPair {X : Type*} (f : Bool → X) : X × X := (f false, f true)

/-- The two-coordinate finite product is the ordinary product under
`boolPair`.  [the stated conclusion](goal). -/
lemma boolPair_measurePreserving {X : Type*} [MeasurableSpace X]
    (mu : Bool → Measure X) [∀ a, IsProbabilityMeasure (mu a)] :
    MeasurePreserving boolPair (Measure.pi mu) ((mu false).prod (mu true)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Bool ↦ X) finTwoEquiv
  have h₁ : MeasurePreserving e
      (Measure.pi fun i : Fin 2 ↦ mu (finTwoEquiv i)) (Measure.pi mu) :=
    measurePreserving_piCongrLeft mu finTwoEquiv
  have h₂ := measurePreserving_piFinTwo
    (fun i : Fin 2 ↦ mu (finTwoEquiv i))
  let eTotal := e.symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ X))
  have h := h₂.comp h₁.symm
  have he : (eTotal : (Bool → X) → X × X) = boolPair := by
    funext f
    apply Prod.ext
    · change f (finTwoEquiv 0) = f false
      rfl
    · change f (finTwoEquiv 1) = f true
      rfl
  rw [← he]
  exact h

/-- Split every cell's Boolean-indexed paired coordinates into two
Boolean-indexed pools.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def splitPairedCellPools {I X Y : Type*}
    (z : I → Bool → X × Y) : I → (Bool → X) × (Bool → Y) :=
  fun i ↦ (fun a ↦ (z i a).1, fun a ↦ (z i a).2)

/-- Coordinatewise finite-product reindexing for paired arm counts.  [the stated conclusion](goal). -/
lemma splitPairedCellPools_measurePreserving
    {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]
    (mu : I → Bool → Measure X) (nu : I → Bool → Measure Y)
    [∀ i a, IsProbabilityMeasure (mu i a)]
    [∀ i a, IsProbabilityMeasure (nu i a)] :
    MeasurePreserving splitPairedCellPools
      (Measure.pi fun i ↦ Measure.pi fun a ↦ (mu i a).prod (nu i a))
      (Measure.pi fun i ↦ (Measure.pi (mu i)).prod (Measure.pi (nu i))) := by
  have h := measurePreserving_pi
    (fun i ↦ Measure.pi fun a ↦ (mu i a).prod (nu i a))
    (fun i ↦ (Measure.pi (mu i)).prod (Measure.pi (nu i)))
    (fun i ↦ measurePreserving_arrowProdEquivProdArrow X Y Bool (mu i) (nu i))
  change MeasurePreserving
    (fun (z : I → Bool → X × Y) i ↦
      (fun a ↦ (z i a).1, fun a ↦ (z i a).2)) _ _
  simpa [MeasurableEquiv.arrowProdEquivProdArrow] using h

/-- Separate a function of arm-indexed triples into its outcome, pilot, and
factorial coordinate functions.  [the stated conditions](hyp:Z) [the stated conclusion](goal). -/
def splitHybridPools (Z : Bool → Nat × (Nat × Nat)) :
    (Bool → Nat) × ((Bool → Nat) × (Bool → Nat)) :=
  (fun a ↦ (Z a).1, fun a ↦ (Z a).2.1, fun a ↦ (Z a).2.2)

/-- Move the middle (pilot) pool in front, leaving outcome and factorial pools
together as the estimator input.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def pilotFirstPools {S J K : Type*} (z : S × (J × K)) : J × (S × K) :=
  (z.2.1, z.1, z.2.2)

/-- Split the three armwise pools and put the independent pilot pool first.  [the stated conditions](hyp:Z) [the stated conclusion](goal). -/
def pilotFirstSplitHybridPools (Z : Bool → Nat × (Nat × Nat)) :
    (Bool → Nat) × ((Bool → Nat) × (Bool → Nat)) :=
  pilotFirstPools (splitHybridPools Z)

/-- The middle-first permutation preserves the correspondingly permuted
three-factor product law.  [the stated conclusion](goal). -/
lemma pilotFirstPools_measurePreserving {S J K : Type*}
    [MeasurableSpace S] [MeasurableSpace J] [MeasurableSpace K]
    (muS : Measure S) (muJ : Measure J) (muK : Measure K)
    [SFinite muS] [SFinite muJ] [SFinite muK] :
    MeasurePreserving pilotFirstPools (muS.prod (muJ.prod muK))
      (muJ.prod (muS.prod muK)) := by
  let hUnassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc muS muJ muK)
  let hSwap : MeasurePreserving
      (Prod.map Prod.swap id) ((muS.prod muJ).prod muK)
        ((muJ.prod muS).prod muK) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id muK)
  let hAssoc := measurePreserving_prodAssoc muJ muS muK
  have h := hAssoc.comp (hSwap.comp hUnassoc)
  change MeasurePreserving (fun z : S × (J × K) ↦ (z.2.1, (z.1, z.2.2)))
    (muS.prod (muJ.prod muK)) (muJ.prod (muS.prod muK))
  simpa [Function.comp_def, MeasurableEquiv.prodAssoc] using h

/-- Finite-product reindexing proves that the outcome, pilot, and factorial
pools in one cell are mutually independent.  [the stated conclusion](goal). -/
lemma splitHybridPools_measurePreserving
    (muS muJ muK : Bool → Measure Nat)
    [∀ a, IsProbabilityMeasure (muS a)]
    [∀ a, IsProbabilityMeasure (muJ a)]
    [∀ a, IsProbabilityMeasure (muK a)] :
    MeasurePreserving splitHybridPools
      (Measure.pi fun a : Bool ↦ (muS a).prod ((muJ a).prod (muK a)))
      ((Measure.pi muS).prod ((Measure.pi muJ).prod (Measure.pi muK))) := by
  let hOuter := measurePreserving_arrowProdEquivProdArrow
    Nat (Nat × Nat) Bool muS (fun a ↦ (muJ a).prod (muK a))
  let hInner := measurePreserving_arrowProdEquivProdArrow
    Nat Nat Bool muJ muK
  have hProduct : MeasurePreserving
      (Prod.map id (MeasurableEquiv.arrowProdEquivProdArrow Nat Nat Bool))
      ((Measure.pi muS).prod
        (Measure.pi fun a : Bool ↦ (muJ a).prod (muK a)))
      ((Measure.pi muS).prod ((Measure.pi muJ).prod (Measure.pi muK))) :=
    (MeasurePreserving.id (Measure.pi muS)).prod hInner
  have hComp := hProduct.comp hOuter
  unfold splitHybridPools
  simpa [Function.comp_def,
    MeasurableEquiv.arrowProdEquivProdArrow] using hComp

/-- Combined armwise splitting and middle-pool permutation.  [the stated conclusion](goal). -/
lemma pilotFirstSplitHybridPools_measurePreserving
    (muS muJ muK : Bool → Measure Nat)
    [∀ a, IsProbabilityMeasure (muS a)]
    [∀ a, IsProbabilityMeasure (muJ a)]
    [∀ a, IsProbabilityMeasure (muK a)] :
    MeasurePreserving pilotFirstSplitHybridPools
      (Measure.pi fun a : Bool ↦ (muS a).prod ((muJ a).prod (muK a)))
      ((Measure.pi muJ).prod ((Measure.pi muS).prod (Measure.pi muK))) := by
  have h := (pilotFirstPools_measurePreserving
    (Measure.pi muS) (Measure.pi muJ) (Measure.pi muK)).comp
      (splitHybridPools_measurePreserving muS muJ muK)
  change MeasurePreserving (fun Z ↦ pilotFirstPools (splitHybridPools Z))
    (Measure.pi fun a : Bool ↦ (muS a).prod ((muJ a).prod (muK a)))
    ((Measure.pi muJ).prod ((Measure.pi muS).prod (Measure.pi muK)))
  exact h

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
