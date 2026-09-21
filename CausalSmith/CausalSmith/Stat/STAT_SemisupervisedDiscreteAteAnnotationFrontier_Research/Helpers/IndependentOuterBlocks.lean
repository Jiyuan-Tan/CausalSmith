module
public import Causalean.Stat.Sample.PiTransport

/-! Law of two outer blocks selected from a finite iid array. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory

/-- Keep the first and last blocks of an array split into lengths `a,b,c`.  [the stated conditions](hyp:a,b,c,z) [the stated conclusion](goal). -/
def independentOuterBlocks {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) : (Fin a → X) × (Fin c → X) :=
  let e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let zs := Equiv.piCongrLeft (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) ↦ X) e.symm z
  (fun i ↦ zs (.inl i), fun i ↦ zs (.inr (.inr i)))

/-- For block lengths [a, b, and c](hyp:a,b,c), the first outer block of [an array](hyp:z) at [an index](hyp:i) [is the array entry at that index](goal). -/
@[simp] theorem independentOuterBlocks_fst_apply {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) (i : Fin a) :
    (independentOuterBlocks a b c z).1 i =
      z ⟨i.1, by omega⟩ := by
  let e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  change (Equiv.piCongrLeft (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) => X) e.symm z)
    (.inl i) = _
  rw [Equiv.piCongrLeft_apply]
  rw [eqRec_eq_cast, cast_eq]
  apply congrArg z
  apply Fin.ext
  rfl

/-- For block lengths [a, b, and c](hyp:a,b,c), the second outer block of [an array](hyp:z) at [an index](hyp:i) [is the array entry offset by the first two block lengths](goal). -/
@[simp] theorem independentOuterBlocks_snd_apply {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) (i : Fin c) :
    (independentOuterBlocks a b c z).2 i =
      z ⟨a + b + i.1, by omega⟩ := by
  let e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  change (Equiv.piCongrLeft (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) => X) e.symm z)
    (.inr (.inr i)) = _
  rw [Equiv.piCongrLeft_apply]
  rw [eqRec_eq_cast, cast_eq]
  apply congrArg z
  apply Fin.ext
  simp [e]
  omega

/-- Selecting outer blocks with [lengths a, b, and c](hyp:a,b,c) [is measurable](goal). -/
@[fun_prop] theorem measurable_independentOuterBlocks {X : Type*}
    [MeasurableSpace X] (a b c : Nat) :
    Measurable (independentOuterBlocks (X := X) a b c) := by
  unfold independentOuterBlocks
  let e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) ↦ X) e.symm
  exact (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (.inl i)).comp reindex.measurable).prodMk
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply (.inr (.inr i))).comp reindex.measurable)
/-- The formal statement establishes [the stated conclusion](goal). -/

theorem map_pi_independentOuterBlocks {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (a b c : Nat) :
    Measure.map (independentOuterBlocks (X := X) a b c)
        (Measure.pi fun _ : Fin (a + (b + c)) ↦ mu) =
      (Measure.pi fun _ : Fin a ↦ mu).prod
        (Measure.pi fun _ : Fin c ↦ mu) := by
  let I := Fin a ⊕ (Fin b ⊕ Fin c)
  let e : I ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : I ↦ X) e.symm
  let splitA := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) ↦ X)
  let splitBC := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin b ⊕ Fin c ↦ X)
  let muA := Measure.pi fun _ : Fin a ↦ mu
  let muB := Measure.pi fun _ : Fin b ↦ mu
  let muC := Measure.pi fun _ : Fin c ↦ mu
  have hreindex : Measure.map reindex
      (Measure.pi fun _ : Fin (a + (b + c)) ↦ mu) =
      Measure.pi fun _ : I ↦ mu := by
    exact (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : I ↦ mu) e.symm).map_eq
  have hsplitA : Measure.map splitA (Measure.pi fun _ : I ↦ mu) =
      muA.prod (Measure.pi fun _ : Fin b ⊕ Fin c ↦ mu) := by
    exact (MeasureTheory.measurePreserving_sumPiEquivProdPi
      (fun _ : I ↦ mu)).map_eq
  have hsplitBC : Measure.map splitBC
      (Measure.pi fun _ : Fin b ⊕ Fin c ↦ mu) = muB.prod muC := by
    exact (MeasureTheory.measurePreserving_sumPiEquivProdPi
      (fun _ : Fin b ⊕ Fin c ↦ mu)).map_eq
  have htriple : Measure.map
      (fun z : I → X =>
        ((fun i => z (.inl i)),
          ((fun i => z (.inr (.inl i))), (fun i => z (.inr (.inr i))))))
      (Measure.pi fun _ : I ↦ mu) = muA.prod (muB.prod muC) := by
    calc
      _ = Measure.map (Prod.map id splitBC)
          (Measure.map splitA (Measure.pi fun _ : I ↦ mu)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = Measure.map (Prod.map id splitBC)
          (muA.prod (Measure.pi fun _ : Fin b ⊕ Fin c ↦ mu)) := by
        rw [hsplitA]
      _ = muA.prod (muB.prod muC) := by
        rw [← Measure.map_prod_map _ _ measurable_id splitBC.measurable,
          Measure.map_id, hsplitBC]
  calc
    Measure.map (independentOuterBlocks (X := X) a b c)
        (Measure.pi fun _ : Fin (a + (b + c)) ↦ mu) =
      Measure.map (fun z => (z.1, z.2.2))
        (Measure.map
          (fun z : I → X =>
            ((fun i => z (.inl i)),
              ((fun i => z (.inr (.inl i))), (fun i => z (.inr (.inr i))))))
          (Measure.map reindex
            (Measure.pi fun _ : Fin (a + (b + c)) ↦ mu))) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = Measure.map (fun z => (z.1, z.2.2)) (muA.prod (muB.prod muC)) := by
      rw [hreindex, htriple]
    _ = muA.prod muC := by
      change Measure.map (Prod.map id Prod.snd) (muA.prod (muB.prod muC)) = _
      rw [← Measure.map_prod_map _ _ measurable_id measurable_snd,
        Measure.map_id]
      exact congrArg (muA.prod ·) MeasureTheory.measurePreserving_snd.map_eq

/-- Concatenating two independent iid arrays gives the iid law on their summed length.  [the stated conclusion](goal). -/
theorem map_prod_finAppend {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (a b : Nat) :
    Measure.map (fun z : (Fin a → X) × (Fin b → X) => Fin.append z.1 z.2)
        ((Measure.pi fun _ : Fin a ↦ mu).prod
          (Measure.pi fun _ : Fin b ↦ mu)) =
      Measure.pi fun _ : Fin (a + b) ↦ mu := by
  let joinSum := (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin a ⊕ Fin b ↦ X)).symm
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (a + b) ↦ X) finSumFinEquiv
  have hjoin : Measure.map joinSum
      ((Measure.pi fun _ : Fin a ↦ mu).prod
        (Measure.pi fun _ : Fin b ↦ mu)) =
      Measure.pi fun _ : Fin a ⊕ Fin b ↦ mu :=
    (MeasureTheory.measurePreserving_sumPiEquivProdPi
      (fun _ : Fin a ⊕ Fin b ↦ mu)).symm.map_eq
  calc
    _ = Measure.map reindex (Measure.map joinSum
        ((Measure.pi fun _ : Fin a ↦ mu).prod
          (Measure.pi fun _ : Fin b ↦ mu))) := by
      symm
      rw [Measure.map_map reindex.measurable joinSum.measurable]
      apply congrArg (fun f => Measure.map f
        ((Measure.pi fun _ : Fin a ↦ mu).prod
          (Measure.pi fun _ : Fin b ↦ mu)))
      funext z i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      · dsimp [reindex, joinSum, Function.comp_def,
          MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]
        rw [Equiv.piCongrLeft_apply]
        simp [reindex, joinSum, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
          Equiv.piCongrLeft_apply_apply]
      · dsimp [reindex, joinSum, Function.comp_def,
          MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]
        rw [Equiv.piCongrLeft_apply]
        simp [reindex, joinSum, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
          Equiv.piCongrLeft_apply_apply]
    _ = Measure.map reindex (Measure.pi fun _ : Fin a ⊕ Fin b ↦ mu) := by
      rw [hjoin]
    _ = Measure.pi fun _ : Fin (a + b) ↦ mu :=
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Fin (a + b) ↦ mu) finSumFinEquiv).map_eq

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
