/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.Basic
import Causalean.Stat.Concentration.TailBounds.Hoeffding
import Causalean.Stat.Minimax.ChiSquaredKernel
import Causalean.Stat.Sample.PiTransport

/-!
# Self-normalized random-design weighted Hoeffding tails

This module transports the conditional random-design MGF bound to a retained-design law and
then to an i.i.d. observation product. It provides two-sided self-normalized Hoeffding tails
for weights that depend measurably on every observed design coordinate.
-/

namespace Causalean.Stat.Concentration.RandomDesignWeightedHoeffding

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory
open Causalean.Mathlib.Probability
/-- Splitting a finite product of attached one-coordinate laws into its two coordinate
vectors gives the attached product law with the coordinatewise product kernel. -/
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

/-- A probability law [P](hyp:P), [measurable design](hyp:design,hdesign), and [measurable
outcome](hyp:Y,hY) map an i.i.d. observation product to [the retained-design law with the finite
product of its one-observation conditional mark kernels](goal). -/
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
  -- First use `compProd_map_condDistrib` for one observation.  Tensorize that equality
  -- with `map_pi_finCoordinatewise`, then split the vector of pairs into the pair of
  -- vectors; prove the resulting product-kernel identity on measurable rectangles.
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

/-- Under a [probability design law](hyp:Q) and [Markov marking kernel](hyp:K) whose [conditional
mean is the measurable regression](hyp:mD,hmD,hmean), whose [marks lie in the
unit interval
almost surely on almost every fibre](hyp:hbound), with [measurable complete-design
weights](hyp:w,hw)
of [positive realized energy almost surely](hyp:henergy), every [nonnegative threshold](hyp:t,ht)
obeys [the
two-sided self-normalized Hoeffding tail bound for the retained-design law](goal). -/
theorem product_weighted_centered_attachKernel_tail_le
    {N : Nat} {D : Type*} [MeasurableSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Real) [IsMarkovKernel K]
    (mD : D -> Real) (hmD : Measurable mD)
    (hmean : ∀ᵐ d ∂Q, ∫ y, y ∂K d = mD d)
    (hbound : ∀ᵐ d ∂Q, ∀ᵐ y ∂K d, y ∈ Set.Icc (0 : Real) 1)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w)
    (henergy : ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
      0 < realizedWeightEnergy w d)
    {t : Real} (ht : 0 <= t) :
    (Causalean.Stat.attachKernel
      (Measure.pi (fun _ : Fin N => Q))
      (Causalean.Stat.finProductKernel N K)).real
        {p | t * Real.sqrt (realizedWeightEnergy w p.1) <=
          |weightedCenteredMarkSum mD w p.1 p.2|} <=
      2 * Real.exp (-2 * t ^ 2) := by
  let designLaw : Measure (Fin N -> D) := Measure.pi (fun _ : Fin N => Q)
  let markKernel := Causalean.Stat.finProductKernel N K
  let B : Real := 2 * Real.exp (-2 * t ^ 2)
  have hB : 0 <= B := by positivity
  have hevent : MeasurableSet
      {p : (Fin N -> D) × (Fin N -> Real) |
        t * Real.sqrt (realizedWeightEnergy w p.1) <=
          |weightedCenteredMarkSum mD w p.1 p.2|} := by
    exact measurableSet_le
      (measurable_const.mul
        ((measurable_realizedWeightEnergy hw).comp measurable_fst).sqrt)
      (measurable_weightedCenteredMarkSum hmD hw).abs
  have hfibre : ∀ᵐ d ∂designLaw,
      (markKernel d).real
          {y | t * Real.sqrt (realizedWeightEnergy w d) <=
            |weightedCenteredMarkSum mD w d y|} <= B := by
    filter_upwards [product_weighted_centered_attachKernel_hasSubgaussianMGF
      Q K mD hmD hmean hbound w hw, henergy] with d hd hdenergy
    have henergy_nonneg : 0 <= realizedWeightEnergy w d := le_of_lt hdenergy
    have hepsilon : 0 <= t * Real.sqrt (realizedWeightEnergy w d) :=
      mul_nonneg ht (Real.sqrt_nonneg _)
    have hcoe :
        (Real.toNNReal (realizedWeightEnergy w d / 4) : Real) =
          realizedWeightEnergy w d / 4 :=
      Real.coe_toNNReal _ (div_nonneg henergy_nonneg (by norm_num))
    have hexponent :
        -(t * Real.sqrt (realizedWeightEnergy w d)) ^ 2 /
            (2 * (realizedWeightEnergy w d / 4)) = -2 * t ^ 2 := by
      rw [mul_pow, Real.sq_sqrt henergy_nonneg]
      field_simp [ne_of_gt hdenergy]
      ring
    have hup := hd.measure_ge_le hepsilon
    rw [hcoe, hexponent] at hup
    have hup' :
        (markKernel d).real
            {y | t * Real.sqrt (realizedWeightEnergy w d) <=
              weightedCenteredMarkSum mD w d y - 0} <=
          Real.exp (-2 * t ^ 2) := by
      simpa only [sub_zero, markKernel] using hup
    have hlow0 := hd.neg.measure_ge_le hepsilon
    rw [hcoe, hexponent] at hlow0
    have hlow :
        (markKernel d).real
            {y | t * Real.sqrt (realizedWeightEnergy w d) <=
              -weightedCenteredMarkSum mD w d y + 0} <=
          Real.exp (-2 * t ^ 2) := by
      simpa only [Pi.neg_apply, add_zero] using hlow0
    have htwo := Causalean.Stat.Concentration.measureReal_abs_dev_le_two_sided
      (μ := markKernel d) (weightedCenteredMarkSum mD w d) 0
      (Real.exp (-2 * t ^ 2)) (Real.exp (-2 * t ^ 2))
      (t * Real.sqrt (realizedWeightEnergy w d)) hup' hlow
    simpa only [sub_zero, B, two_mul] using htwo
  have hfibreENN : ∀ᵐ d ∂designLaw,
      markKernel d (Prod.mk d ⁻¹'
        {p : (Fin N -> D) × (Fin N -> Real) |
          t * Real.sqrt (realizedWeightEnergy w p.1) <=
            |weightedCenteredMarkSum mD w p.1 p.2|}) <= ENNReal.ofReal B := by
    filter_upwards [hfibre] with d hd
    have hd' :
        (markKernel d).real (Prod.mk d ⁻¹'
          {p : (Fin N -> D) × (Fin N -> Real) |
            t * Real.sqrt (realizedWeightEnergy w p.1) <=
              |weightedCenteredMarkSum mD w p.1 p.2|}) <= B := by
      simpa only [Set.mem_setOf_eq, Set.preimage_setOf_eq, Function.comp_apply] using hd
    rw [measureReal_def] at hd'
    rw [← ENNReal.ofReal_toReal (measure_ne_top (markKernel d) _)]
    exact ENNReal.ofReal_le_ofReal hd'
  have hjoint :
      (designLaw ⊗ₘ markKernel)
          {p : (Fin N -> D) × (Fin N -> Real) |
            t * Real.sqrt (realizedWeightEnergy w p.1) <=
              |weightedCenteredMarkSum mD w p.1 p.2|} <= ENNReal.ofReal B := by
    rw [Measure.compProd_apply hevent]
    calc
      (∫⁻ d, markKernel d (Prod.mk d ⁻¹'
          {p : (Fin N -> D) × (Fin N -> Real) |
            t * Real.sqrt (realizedWeightEnergy w p.1) <=
              |weightedCenteredMarkSum mD w p.1 p.2|}) ∂designLaw) <=
          ∫⁻ _ : Fin N -> D, ENNReal.ofReal B ∂designLaw :=
        lintegral_mono_ae hfibreENN
      _ = ENNReal.ofReal B := by simp [designLaw]
  change (designLaw ⊗ₘ markKernel).real
      {p | t * Real.sqrt (realizedWeightEnergy w p.1) <=
        |weightedCenteredMarkSum mD w p.1 p.2|} <= B
  rw [measureReal_def]
  calc
    ((designLaw ⊗ₘ markKernel)
      {p | t * Real.sqrt (realizedWeightEnergy w p.1) <=
        |weightedCenteredMarkSum mD w p.1 p.2|}).toReal <=
        (ENNReal.ofReal B).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hjoint
    _ = B := ENNReal.toReal_ofReal hB

/-- A probability law [P](hyp:P), [measurable design](hyp:design,hdesign), and [measurable
outcome](hyp:Y,hY) that is [almost surely in the unit interval](hyp:hY_nonneg,hY_le_one),
together with a [measurable regression equal almost surely to the conditional expectation given
the design](hyp:mD,hmD,hcond), [measurable complete-design weights](hyp:w,hw) of [positive
realized energy almost surely](hyp:henergy), and a [nonnegative threshold](hyp:t,ht), yield [the
two-sided self-normalized Hoeffding tail bound for
the finite i.i.d. sample](goal). -/
theorem product_weighted_centered_tail_le
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : ∀ᵐ omega ∂P, 0 <= Y omega)
    (hY_le_one : ∀ᵐ omega ∂P, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w)
    (henergy : ∀ᵐ z ∂Measure.pi (fun _ : Fin N => P),
      0 < realizedWeightEnergy w (designVector design z))
    {t : Real} (ht : 0 <= t) :
    (Measure.pi (fun _ : Fin N => P)).real
        {z | t * Real.sqrt
            (realizedWeightEnergy w (designVector design z)) <=
          |weightedCenteredSum design Y mD w z|} <=
      2 * Real.exp (-2 * t ^ 2) := by
  have hY_mem : ∀ᵐ omega ∂P, Y omega ∈ Set.Icc (0 : Real) 1 :=
    hY_nonneg.and hY_le_one
  have hY_int : Integrable Y P :=
    Integrable.of_mem_Icc 0 1 hY.aemeasurable hY_mem
  have hmean_comp :
      (fun omega => ∫ y, y ∂condDistrib Y design P (design omega)) =ᵐ[P]
        mD ∘ design :=
    (condExp_ae_eq_integral_condDistrib' hdesign hY_int).symm.trans hcond
  have hmean :
      ∀ᵐ d ∂P.map design, ∫ y, y ∂condDistrib Y design P d = mD d := by
    rw [ae_map_iff hdesign.aemeasurable]
    · filter_upwards [hmean_comp] with x hx
      exact hx
    · exact measurableSet_eq_fun
        (((stronglyMeasurable_id.comp_measurable measurable_snd).integral_condDistrib
          (X := design) (Y := Y) (μ := P)).measurable)
        hmD
  have hpair :
      ∀ᵐ p ∂(P.map design ⊗ₘ condDistrib Y design P),
        p.2 ∈ Set.Icc (0 : Real) 1 := by
    rw [compProd_map_condDistrib hY.aemeasurable]
    rw [ae_map_iff (hdesign.prodMk hY).aemeasurable]
    · simpa using hY_mem
    · exact measurableSet_Icc.preimage measurable_snd
  have hrange :
      ∀ᵐ d ∂P.map design,
        ∀ᵐ y ∂condDistrib Y design P d, y ∈ Set.Icc (0 : Real) 1 :=
    Measure.ae_ae_of_ae_compProd hpair
  let obsLaw : Measure (Fin N -> Omega) := Measure.pi (fun _ : Fin N => P)
  let designLaw : Measure (Fin N -> D) :=
    Measure.pi (fun _ : Fin N => P.map design)
  let designVec : (Fin N -> Omega) -> (Fin N -> D) := designVector design
  have hdesignVec : Measurable designVec := by
    simpa only [designVec] using measurable_designVector design hdesign
  have henergySet : MeasurableSet
      {d : Fin N -> D | 0 < realizedWeightEnergy w d} :=
    measurableSet_lt measurable_const (measurable_realizedWeightEnergy hw)
  have hmapDesign : obsLaw.map designVec = designLaw := by
    change (Measure.pi (fun _ : Fin N => P)).map
        (fun z : Fin N -> Omega => fun i => design (z i)) =
      Measure.pi (fun _ : Fin N => P.map design)
    exact Causalean.Stat.map_pi_finCoordinatewise N P hdesign
  have henergyDesign : ∀ᵐ d ∂designLaw, 0 < realizedWeightEnergy w d := by
    rw [← hmapDesign, ae_map_iff hdesignVec.aemeasurable henergySet]
    simpa only [obsLaw, designVec] using henergy
  letI : IsProbabilityMeasure (P.map design) :=
    Measure.isProbabilityMeasure_map hdesign.aemeasurable
  have hattached := product_weighted_centered_attachKernel_tail_le
    (N := N) (P.map design) (condDistrib Y design P) mD hmD hmean hrange w hw
    henergyDesign ht
  let jointMap : (Fin N -> Omega) -> (Fin N -> D) × (Fin N -> Real) :=
    fun z => (designVector design z, fun i => Y (z i))
  have hjointMap : Measurable jointMap := by
    exact (measurable_designVector design hdesign).prodMk
      (Causalean.Stat.measurable_finCoordinatewise N hY)
  let event : Set ((Fin N -> D) × (Fin N -> Real)) :=
    {p | t * Real.sqrt (realizedWeightEnergy w p.1) <=
      |weightedCenteredMarkSum mD w p.1 p.2|}
  have hevent : MeasurableSet event := by
    exact measurableSet_le
      (measurable_const.mul
        ((measurable_realizedWeightEnergy hw).comp measurable_fst).sqrt)
      (measurable_weightedCenteredMarkSum hmD hw).abs
  have hpull : jointMap ⁻¹' event =
      {z | t * Real.sqrt
          (realizedWeightEnergy w (designVector design z)) <=
        |weightedCenteredSum design Y mD w z|} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, jointMap, event]
    change
      t * Real.sqrt (realizedWeightEnergy w (designVector design z)) <=
          |∑ i, w (designVector design z) i *
            (Y (z i) - mD (design (z i)))| ↔ _
    rfl
  have hlaw := product_observation_law_map_design_outcome
    (N := N) P design hdesign Y hY
  have hmapReal := map_measureReal_apply (μ := obsLaw) hjointMap hevent
  rw [hlaw] at hmapReal
  change obsLaw.real
      {z | t * Real.sqrt
          (realizedWeightEnergy w (designVector design z)) <=
        |weightedCenteredSum design Y mD w z|} <=
      2 * Real.exp (-2 * t ^ 2)
  rw [← hpull, ← hmapReal]
  simpa only [designLaw] using hattached

end Causalean.Stat.Concentration.RandomDesignWeightedHoeffding
