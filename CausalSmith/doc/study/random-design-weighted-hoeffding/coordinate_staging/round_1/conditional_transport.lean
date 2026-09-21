namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability

private theorem map_pi_compProd_arrowProdEquivProdArrow
    {N : Nat} {D : Type*} [MeasurableSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Real) [IsMarkovKernel K] :
    (Measure.pi (fun _ : Fin N => Q ⊗ₘ K)).map
        (MeasurableEquiv.arrowProdEquivProdArrow D Real (Fin N)) =
      Measure.pi (fun _ : Fin N => Q) ⊗ₘ Causalean.Stat.finProductKernel N K := by
  let split := MeasurableEquiv.arrowProdEquivProdArrow D Real (Fin N)
  let pairLaw : Measure (D × Real) := Q ⊗ₘ K
  let designLaw : Measure (Fin N → D) := Measure.pi (fun _ : Fin N => Q)
  let markKernel := Causalean.Stat.finProductKernel N K
  letI : IsProbabilityMeasure pairLaw := by
    dsimp only [pairLaw]
    infer_instance
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin N => pairLaw)) := inferInstance
  letI : IsProbabilityMeasure designLaw := by
    dsimp only [designLaw]
    infer_instance
  letI : IsMarkovKernel markKernel := by
    dsimp only [markKernel]
    infer_instance
  let lhs := (Measure.pi (fun _ : Fin N => pairLaw)).map split
  let rhs := designLaw ⊗ₘ markKernel
  change lhs = rhs
  refine Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi) ?_ ?_
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin N => Q.toFiniteSpanningSetsIn)).isCountablySpanning
    · exact (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin N => (volume : Measure Real).toFiniteSpanningSetsIn)).isCountablySpanning
  · let base := (Measure.pi (fun _ : Fin N => Q)).prod
        (Measure.pi (fun _ : Fin N => (volume : Measure Real)))
    let hbase := (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin N => Q.toFiniteSpanningSetsIn)).prod
      (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin N => (volume : Measure Real).toFiniteSpanningSetsIn))
    exact ⟨hbase.set, hbase.set_mem, fun i => measure_lt_top _ _, hbase.spanning⟩
  · rintro _ ⟨s, ⟨s, hs, rfl⟩, ⟨_, ⟨t, ht, rfl⟩, rfl⟩⟩
    have hs' : ∀ i, MeasurableSet (s i) := fun i => hs i (Set.mem_univ i)
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (Set.mem_univ i)
    have hdesignSet : MeasurableSet (Set.univ.pi s) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => hs' i)
    have hmarkSet : MeasurableSet (Set.univ.pi t) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => ht' i)
    simp only [lhs, rhs]
    rw [Measure.map_apply split.measurable (hdesignSet.prod hmarkSet)]
    rw [show split ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
        Set.univ.pi (fun i => s i ×ˢ t i) by
      ext x
      simp only [split, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.coe_mk, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
        Set.mem_univ, true_implies, Equiv.arrowProdEquivProdArrow_apply, forall_and]]
    rw [Measure.pi_pi, Measure.compProd_apply_prod hdesignSet hmarkSet]
    simp_rw [pairLaw, Measure.compProd_apply_prod (hs' _) (ht' _)]
    simp only [markKernel]
    simp_rw [Causalean.Stat.finProductKernel_apply, Measure.pi_pi]
    let X : Fin N → (Fin N → D) → ENNReal := fun i d =>
      Set.indicator (s i) (fun x => K x (t i)) (d i)
    have hXmeas : ∀ i, Measurable (X i) := fun i =>
      ((K.measurable_coe (ht' i)).indicator (hs' i)).comp (measurable_pi_apply i)
    have hXindep : iIndepFun X designLaw := by
      have heval : iIndepFun (fun i (d : Fin N → D) => d i) designLaw := by
        simpa only [designLaw, id_eq] using
          (iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable))
      change iIndepFun (fun i =>
        (fun x => Set.indicator (s i) (fun z => K z (t i)) x) ∘
          fun d : Fin N → D => d i) designLaw
      exact heval.comp
        (fun i x => Set.indicator (s i) (fun z => K z (t i)) x)
        (fun i => (K.measurable_coe (ht' i)).indicator (hs' i))
    rw [← lintegral_indicator hdesignSet]
    change (∏ i, ∫⁻ x in s i, K x (t i) ∂Q) =
      ∫⁻ d, Set.indicator (Set.univ.pi s)
        (fun d => ∏ i, K (d i) (t i)) d ∂designLaw
    rw [show (fun d => Set.indicator (Set.univ.pi s)
          (fun d => ∏ i, K (d i) (t i)) d) =
        fun d => ∏ i, X i d by
      funext d
      by_cases hd : ∀ i, d i ∈ s i
      · rw [Set.indicator_of_mem (show d ∈ Set.univ.pi s from fun i _ => hd i)]
        exact Finset.prod_congr rfl fun i _ => by simp [X, hd i]
      · rw [Set.indicator_of_notMem (show d ∉ Set.univ.pi s by
          intro hmem
          exact hd fun i => hmem i (Set.mem_univ i))]
        push Not at hd
        obtain ⟨i, hi⟩ := hd
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [X, hi])]
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ X hXindep hXmeas]
    apply Finset.prod_congr rfl
    intro i _
    calc
      (∫⁻ x in s i, K x (t i) ∂Q) =
          ∫⁻ x, Set.indicator (s i) (fun z => K z (t i)) x ∂Q :=
        (lintegral_indicator (hs' i) _).symm
      _ = ∫⁻ d, X i d ∂designLaw :=
        ((measurePreserving_eval (fun _ : Fin N => Q) i).lintegral_comp
          ((K.measurable_coe (ht' i)).indicator (hs' i))).symm

/-- Under [a probability observation law](hyp:P), [a measurable design map](hyp:design,hdesign),
and [a measurable outcome](hyp:Y,hY), [mapping an i.i.d. observation product to its complete
design and outcome vectors produces the retained-design law with the product conditional-mark
kernel](goal). -/
theorem product_observation_law_map_design_outcome
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y) :
    (Measure.pi (fun _ : Fin N => P)).map
        (fun z => (designVector design z, fun i => Y (z i))) =
      Causalean.Stat.attachKernel
        (Measure.pi (fun _ : Fin N => P.map design))
        (Causalean.Stat.finProductKernel N (condDistrib Y design P)) := by
  let pair : Omega → D × Real := fun omega => (design omega, Y omega)
  let split := MeasurableEquiv.arrowProdEquivProdArrow D Real (Fin N)
  have hpair : Measurable pair := hdesign.prodMk hY
  have hcoordinate := Causalean.Stat.map_pi_finCoordinatewise N P hpair
  have hdisintegrate :
      P.map pair = P.map design ⊗ₘ condDistrib Y design P :=
    (compProd_map_condDistrib hY.aemeasurable).symm
  letI : IsProbabilityMeasure (P.map design) :=
    Measure.isProbabilityMeasure_map hdesign.aemeasurable
  calc
    (Measure.pi (fun _ : Fin N => P)).map
        (fun z => (designVector design z, fun i => Y (z i))) =
      ((Measure.pi (fun _ : Fin N => P)).map
        (fun z => fun i => pair (z i))).map split := by
          rw [Measure.map_map split.measurable
            (Causalean.Stat.measurable_finCoordinatewise N hpair)]
          rfl
    _ = (Measure.pi (fun _ : Fin N => P.map pair)).map split := by
      rw [hcoordinate]
    _ = (Measure.pi (fun _ : Fin N =>
        P.map design ⊗ₘ condDistrib Y design P)).map split := by
      rw [hdisintegrate]
    _ = Causalean.Stat.attachKernel
        (Measure.pi (fun _ : Fin N => P.map design))
        (Causalean.Stat.finProductKernel N (condDistrib Y design P)) := by
      exact map_pi_compProd_arrowProdEquivProdArrow
        (P.map design) (condDistrib Y design P)

end Causalean.Stat.Concentration
