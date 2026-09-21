/-! ### Random-design weighted concentration

The following definitions and fibrewise bound support concentration arguments whose
coefficients are measurable functions of the complete observed design vector.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability

/-- The realized weight energy is the sum of squared coefficients evaluated at a
complete design vector. -/
def realizedWeightEnergy {N : Nat} {D : Type*}
    (w : (Fin N -> D) -> Fin N -> Real) (d : Fin N -> D) : Real :=
  ∑ i, (w d i) ^ 2

/-- The weighted centered mark sum combines a frozen complete design vector with a
mark vector by subtracting each design-specific mean before applying its coefficient. -/
def weightedCenteredMarkSum {N : Nat} {D : Type*}
    (mD : D -> Real) (w : (Fin N -> D) -> Fin N -> Real)
    (d : Fin N -> D) (y : Fin N -> Real) : Real :=
  ∑ i, w d i * (y i - mD (d i))

/-- The self-normalized weighted centered sum divides the weighted residual sum by the
square root of its realized weight energy, assigning zero through totalized division at
zero energy. -/
noncomputable def selfNormalizedWeightedCenteredSum {N : Nat} {Omega D : Type*}
    (design : Omega -> D) (Y : Omega -> Real) (mD : D -> Real)
    (w : (Fin N -> D) -> Fin N -> Real) (z : Fin N -> Omega) : Real :=
  weightedCenteredSum design Y mD w z /
    Real.sqrt (realizedWeightEnergy w (designVector design z))

/-- [A measurable coefficient array](hyp:hw) has [measurable realized squared
energy](goal). -/
@[fun_prop] theorem measurable_realizedWeightEnergy
    {N : Nat} {D : Type*} [MeasurableSpace D]
    {w : (Fin N -> D) -> Fin N -> Real} (hw : Measurable w) :
    Measurable (realizedWeightEnergy w) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp hw).pow_const 2

/-- [A measurable design-specific mean](hyp:hmD) and [a measurable coefficient
array](hyp:hw) give [a jointly measurable frozen-design weighted centered sum](goal). -/
@[fun_prop] theorem measurable_weightedCenteredMarkSum
    {N : Nat} {D : Type*} [MeasurableSpace D]
    {mD : D -> Real} (hmD : Measurable mD)
    {w : (Fin N -> D) -> Fin N -> Real} (hw : Measurable w) :
    Measurable (fun p : (Fin N -> D) × (Fin N -> Real) =>
      weightedCenteredMarkSum mD w p.1 p.2) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (hw.comp measurable_fst)).mul
    (((measurable_pi_apply i).comp measurable_snd).sub
      (hmD.comp ((measurable_pi_apply i).comp measurable_fst)))

/-- [A measurable design map](hyp:hdesign), [measurable outcome](hyp:hY), [measurable
regression](hyp:hmD), and [measurable full-design coefficient array](hyp:hw) give [a
measurable weighted centered sum on the finite observation product](goal). -/
@[fun_prop] theorem measurable_weightedCenteredSum
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    {design : Omega -> D} (hdesign : Measurable design)
    {Y : Omega -> Real} (hY : Measurable Y)
    {mD : D -> Real} (hmD : Measurable mD)
    {w : (Fin N -> D) -> Fin N -> Real} (hw : Measurable w) :
    Measurable (weightedCenteredSum design Y mD w) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp
      (hw.comp (measurable_designVector design hdesign))).mul
    ((hY.comp (measurable_pi_apply i)).sub
      (hmD.comp (hdesign.comp (measurable_pi_apply i))))

/-- [A measurable design map](hyp:hdesign), [measurable outcome](hyp:hY), [measurable
regression](hyp:hmD), and [measurable full-design coefficient array](hyp:hw) give [a
measurable self-normalized weighted centered sum, including at zero energy](goal). -/
@[fun_prop] theorem measurable_selfNormalizedWeightedCenteredSum
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    {design : Omega -> D} (hdesign : Measurable design)
    {Y : Omega -> Real} (hY : Measurable Y)
    {mD : D -> Real} (hmD : Measurable mD)
    {w : (Fin N -> D) -> Fin N -> Real} (hw : Measurable w) :
    Measurable (selfNormalizedWeightedCenteredSum design Y mD w) := by
  exact (measurable_weightedCenteredSum hdesign hY hmD hw).div
    (((measurable_realizedWeightEnergy hw).comp
      (measurable_designVector design hdesign)).sqrt)

/-- [A measurable design map](hyp:hdesign), [measurable outcome](hyp:hY), [measurable
regression](hyp:hmD), [measurable full-design coefficient array](hyp:hw), and [a fixed
threshold](hyp:t) give [a measurable self-normalized deviation event](goal). -/
theorem measurableSet_selfNormalizedDeviation
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    {design : Omega -> D} (hdesign : Measurable design)
    {Y : Omega -> Real} (hY : Measurable Y)
    {mD : D -> Real} (hmD : Measurable mD)
    {w : (Fin N -> D) -> Fin N -> Real} (hw : Measurable w) (t : Real) :
    MeasurableSet {z : Fin N -> Omega |
      t <= |selfNormalizedWeightedCenteredSum design Y mD w z|} := by
  exact measurableSet_le measurable_const
    (measurable_selfNormalizedWeightedCenteredSum hdesign hY hmD hw).abs

/-- Under [a probability observation law](hyp:P), [a measurable design map](hyp:design,hdesign),
[a measurable outcome](hyp:Y,hY) that is [almost surely in the unit interval](hyp:hY_nonneg,hY_le_one),
[a measurable regression](hyp:mD,hmD) equal to [the outcome's conditional expectation given the
design](hyp:hcond), [the centered conditional-distribution exponential moment is bounded by
the unit-interval Hoeffding bound on almost every design fibre](goal). -/
theorem centered_condDistrib_mgf_le
    {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : ∀ᵐ omega ∂P, 0 <= Y omega)
    (hY_le_one : ∀ᵐ omega ∂P, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design) :
    ∀ᵐ d ∂P.map design, ∀ s : Real,
      ∫ y, Real.exp (s * (y - mD d)) ∂condDistrib Y design P d <=
        Real.exp (s ^ 2 / 8) := by
  have hY_mem : ∀ᵐ omega ∂P, Y omega ∈ Set.Icc (0 : ℝ) 1 :=
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
        p.2 ∈ Set.Icc (0 : ℝ) 1 := by
    rw [compProd_map_condDistrib hY.aemeasurable]
    rw [ae_map_iff (hdesign.prodMk hY).aemeasurable]
    · simpa using hY_mem
    · exact measurableSet_Icc.preimage measurable_snd
  have hrange :
      ∀ᵐ d ∂P.map design,
        ∀ᵐ y ∂condDistrib Y design P d, y ∈ Set.Icc (0 : ℝ) 1 :=
    Measure.ae_ae_of_ae_compProd hpair
  filter_upwards [hmean, hrange] with d hdmean hdrange
  intro s
  have hsub := hasSubgaussianMGF_of_mem_Icc
    (μ := condDistrib Y design P d) (X := id)
    measurable_id.aemeasurable hdrange
  have hmgf := hsub.mgf_le s
  simp only [mgf, id_eq, hdmean] at hmgf
  convert hmgf using 1 <;> norm_num <;> ring

end Causalean.Stat.Concentration
