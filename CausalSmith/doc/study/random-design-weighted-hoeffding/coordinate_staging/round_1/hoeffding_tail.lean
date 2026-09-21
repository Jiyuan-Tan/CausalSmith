/-! ### Random-design weighted Hoeffding tails

These retained-design and i.i.d.-sample corollaries turn the conditional product
MGF bound into a self-normalized two-sided Hoeffding inequality.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability

/-- Under [a probability design law](hyp:Q), [a Markov marking kernel](hyp:K), [a
measurable conditional mean](hyp:mD,hmD) satisfying [the kernel mean identity](hyp:hmean),
[unit-interval marks on almost every kernel fibre](hyp:hbound), [a measurable complete-design
coefficient array](hyp:w,hw) with [almost surely positive realized energy](hyp:henergy), and
[a nonnegative threshold](hyp:t,ht), [the retained-design weighted centered sum has the
two-sided self-normalized Hoeffding tail bound](goal). -/
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
    have htwo := measureReal_abs_dev_le_two_sided
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

/-- Under [a probability observation law](hyp:P), [a measurable design map](hyp:design,hdesign),
[a measurable unit-interval outcome](hyp:Y,hY,hY_nonneg,hY_le_one), [a measurable regression](hyp:mD,hmD)
equal to [its conditional expectation given the design](hyp:hcond), [a measurable complete-design
coefficient array](hyp:w,hw) with [almost surely positive realized energy](hyp:henergy), and [a
nonnegative threshold](hyp:t,ht), [the finite i.i.d. weighted centered sum obeys the two-sided
self-normalized Hoeffding tail bound](goal). -/
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

end Causalean.Stat.Concentration
