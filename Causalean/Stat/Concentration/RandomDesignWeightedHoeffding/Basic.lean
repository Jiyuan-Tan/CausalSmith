/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.WeightedProduct
import Causalean.Stat.Minimax.MarkovKernelTransport
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional Hoeffding MGFs with random-design weights

This module proves conditional Hoeffding exponential-moment bounds for finite i.i.d.
samples whose coefficient array is a measurable function of the complete design vector.
It supplies a kernel-native formulation and a regular-conditional-distribution corollary,
deriving rather than assuming conditional independence of the marks.
-/

namespace Causalean.Stat.Concentration.RandomDesignWeightedHoeffding

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory
open Causalean.Mathlib.Probability

/-- For [a coefficient array determined by a complete design vector](hyp:w) and [a complete design vector](hyp:d), [the realized weight energy](goal) is the sum of the squares of the coefficients selected by that design vector. -/
def realizedWeightEnergy {N : Nat} {D : Type*}
    (w : (Fin N -> D) -> Fin N -> Real) (d : Fin N -> D) : Real :=
  ∑ i, (w d i) ^ 2

/-- For [a real-valued conditional mean function of a design value](hyp:mD), [a coefficient array determined by a complete design vector](hyp:w), [a complete design vector](hyp:d), and [a vector of real marks](hyp:y), [the weighted centered mark sum](goal) is the sum over sample positions of the selected coefficient times the mark minus its conditional mean at the corresponding design value. -/
def weightedCenteredMarkSum {N : Nat} {D : Type*}
    (mD : D -> Real) (w : (Fin N -> D) -> Fin N -> Real)
    (d : Fin N -> D) (y : Fin N -> Real) : Real :=
  ∑ i, w d i * (y i - mD (d i))

/-- For [a design map](hyp:design), [a real-valued outcome map](hyp:Y), [a real-valued conditional mean function of the design](hyp:mD), [a coefficient array determined by a complete design vector](hyp:w), and [a finite vector of sampled units](hyp:z), [the self-normalized weighted centered sum](goal) is the weighted centered sum divided by the square root of the realized weight energy of the sampled design vector; when that energy is zero, this value is zero. -/
noncomputable def selfNormalizedWeightedCenteredSum {N : Nat} {Omega D : Type*}
    (design : Omega -> D) (Y : Omega -> Real) (mD : D -> Real)
    (w : (Fin N -> D) -> Fin N -> Real) (z : Fin N -> Omega) : Real :=
  weightedCenteredSum design Y mD w z /
    Real.sqrt (realizedWeightEnergy w (designVector design z))

/-- The sum of squared coefficients selected by a [measurable complete-design weight
array](hyp:w,hw) is [itself measurable](goal). -/
@[fun_prop] theorem measurable_realizedWeightEnergy
    {N : Nat} {D : Type*} [MeasurableSpace D]
    {w : (Fin N -> D) -> Fin N -> Real} (hw : Measurable w) :
    Measurable (realizedWeightEnergy w) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp hw).pow_const 2

/-- A [measurable regression](hyp:mD,hmD) and [measurable complete-design weights](hyp:w,hw)
make [the weighted centered mark sum jointly measurable](goal). -/
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

/-- A [measurable design](hyp:design,hdesign), [measurable outcome](hyp:Y,hY), [measurable
regression](hyp:mD,hmD), and [measurable complete-design weights](hyp:w,hw) make [the finite-sample
weighted centered sum measurable](goal). -/
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

/-- A [measurable design](hyp:design,hdesign), [measurable outcome](hyp:Y,hY), [measurable
regression](hyp:mD,hmD), and [measurable complete-design weights](hyp:w,hw) make [the
self-normalized weighted centered sum measurable, including at zero energy](goal). -/
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

/-- A [measurable design](hyp:design,hdesign), [measurable outcome](hyp:Y,hY), [measurable
regression](hyp:mD,hmD), and [measurable complete-design weights](hyp:w,hw) make [the event that
the absolute self-normalized sum exceeds the fixed threshold](hyp:t) [measurable](goal). -/
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

/-- A probability law [P](hyp:P), [measurable design](hyp:design,hdesign), and [measurable
outcome](hyp:Y,hY) that is [almost surely nonnegative and at most one](hyp:hY_nonneg,hY_le_one),
together with a [measurable regression equal almost surely to its conditional expectation given
the design](hyp:mD,hmD,hcond), yield [the
conditional Hoeffding exponential-moment bound on almost every design fibre](goal). -/
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
  -- Proof route: boundedness gives `Integrable Y P`; identify the conditional fibre mean
  -- with `mD` using `condExp_ae_eq_integral_condDistrib'` and `hcond`, disintegrate the
  -- ambient interval bound with `compProd_map_condDistrib`, then apply Mathlib's
  -- `hasSubgaussianMGF_of_mem_Icc` on each good fibre (whose interval width is one).
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

/-- Under a [probability design law](hyp:Q) and [Markov marking kernel](hyp:K) whose
[conditional mean is the measurable regression](hyp:mD,hmD,hmean), whose [marks lie in the
unit interval almost surely on almost every fibre](hyp:hbound), and whose [complete-design
weight array is measurable](hyp:w,hw), [the weighted centered mark sum is sub-Gaussian on
almost every complete-design fibre with one quarter of its realized weight energy as variance
proxy](goal). -/
theorem product_weighted_centered_attachKernel_hasSubgaussianMGF
    {N : Nat} {D : Type*} [MeasurableSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Real) [IsMarkovKernel K]
    (mD : D -> Real) (hmD : Measurable mD)
    (hmean : ∀ᵐ d ∂Q, ∫ y, y ∂K d = mD d)
    (hbound : ∀ᵐ d ∂Q, ∀ᵐ y ∂K d, y ∈ Set.Icc (0 : Real) 1)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
      HasSubgaussianMGF (weightedCenteredMarkSum mD w d)
        (Real.toNNReal (realizedWeightEnergy w d / 4))
        (Causalean.Stat.finProductKernel N K d) := by
  have hmeans :
      ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
        ∀ i, ∫ y, y ∂K (d i) = mD (d i) := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin N => Q) (i := i) |>.eventually hmean
  have hbounds :
      ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
        ∀ i, ∀ᵐ y ∂K (d i), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin N => Q) (i := i) |>.eventually hbound
  filter_upwards [hmeans, hbounds] with d hdmean hdbound
  rw [Causalean.Stat.finProductKernel_apply]
  let mu : Measure (Fin N -> ℝ) := Measure.pi (fun i : Fin N => K (d i))
  let X : Fin N -> (Fin N -> ℝ) -> ℝ :=
    fun i y => w d i * (y i - mD (d i))
  let c : Fin N -> NNReal := fun i =>
    ⟨(w d i) ^ 2, sq_nonneg _⟩ * ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2)
  have hindep_eval : iIndepFun (fun i (y : Fin N -> ℝ) => y i) mu :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hindep : iIndepFun X mu :=
    hindep_eval.comp (fun i y => w d i * (y - mD (d i)))
      (fun i => measurable_const.mul (measurable_id.sub measurable_const))
  have hsub : ∀ i, HasSubgaussianMGF (X i) (c i) mu := by
    intro i
    have hbase := hasSubgaussianMGF_of_mem_Icc
      (μ := K (d i)) (X := id) measurable_id.aemeasurable (hdbound i)
    have hcentered : HasSubgaussianMGF (fun y : ℝ => y - mD (d i))
        ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (K (d i)) := by
      simpa [hdmean i] using hbase
    have hmap : Measure.map (fun y : Fin N -> ℝ => y i) mu = K (d i) := by
      simpa only [mu] using
        (measurePreserving_eval (fun j : Fin N => K (d j)) i).map_eq
    rw [← hmap] at hcentered
    have hbase' := HasSubgaussianMGF.of_map
      (μ := mu) (Y := fun y : Fin N -> ℝ => y i)
      (X := fun y : ℝ => y - mD (d i))
      (measurable_pi_apply i).aemeasurable hcentered
    change HasSubgaussianMGF (fun y : Fin N -> ℝ => y i - mD (d i))
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) mu at hbase'
    have hscaled := hbase'.const_mul (w d i)
    simpa only [X, c] using hscaled
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
    (s := Finset.univ) (fun i _ => hsub i)
  have hc_sum : (↑(∑ i, c i) : ℝ) = realizedWeightEnergy w d / 4 := by
    rw [NNReal.coe_sum]
    simp only [c]
    norm_num [Real.norm_eq_abs]
    change (∑ i, (w d i) ^ 2 * (1 / 4)) =
      (∑ i, (w d i) ^ 2) / 4
    rw [← Finset.sum_mul]
    ring
  have henergy_nonneg : 0 <= realizedWeightEnergy w d := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (w d i)
  have hc : (∑ i, c i) = Real.toNNReal (realizedWeightEnergy w d / 4) := by
    apply NNReal.eq
    rw [hc_sum, Real.coe_toNNReal _ (div_nonneg henergy_nonneg (by norm_num))]
  rw [hc] at hsum
  change HasSubgaussianMGF
    (fun y : Fin N -> Real => ∑ i, w d i * (y i - mD (d i)))
    (Real.toNNReal (realizedWeightEnergy w d / 4))
    (Measure.pi (fun i : Fin N => K (d i)))
  simpa only [mu, X] using hsum

/-- Under a [probability design law](hyp:Q) and [Markov marking kernel](hyp:K) whose [conditional
mean is the measurable regression](hyp:mD,hmD,hmean), whose [marks lie in the unit interval
almost surely on almost every fibre](hyp:hbound), and whose [complete-design weight array is
measurable](hyp:w,hw),
[the weighted centered sum has the conditional Hoeffding exponential-moment bound on almost
every complete-design fibre](goal). -/
theorem product_weighted_centered_attachKernel_conditional_mgf_le
    {N : Nat} {D : Type*} [MeasurableSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Real) [IsMarkovKernel K]
    (mD : D -> Real) (hmD : Measurable mD)
    (hmean : ∀ᵐ d ∂Q, ∫ y, y ∂K d = mD d)
    (hbound : ∀ᵐ d ∂Q, ∀ᵐ y ∂K d, y ∈ Set.Icc (0 : Real) 1)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q), ∀ s : Real,
      ∫ y, Real.exp (s * weightedCenteredMarkSum mD w d y)
          ∂Causalean.Stat.finProductKernel N K d <=
        Real.exp (s ^ 2 * realizedWeightEnergy w d / 8) := by
  filter_upwards [product_weighted_centered_attachKernel_hasSubgaussianMGF
    Q K mD hmD hmean hbound w hw] with d hd
  intro s
  have hmgf := hd.mgf_le s
  have henergy_nonneg : 0 <= realizedWeightEnergy w d := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (w d i)
  rw [Real.coe_toNNReal _ (div_nonneg henergy_nonneg (by norm_num))] at hmgf
  simp only [mgf] at hmgf
  convert hmgf using 1
  congr 1
  ring

/-- A probability law [P](hyp:P), [measurable design](hyp:design,hdesign), and [measurable
outcome](hyp:Y,hY) that is [almost surely in the unit interval](hyp:hY_nonneg,hY_le_one),
together with a [measurable regression equal almost surely to the conditional expectation given
the design](hyp:mD,hmD,hcond) and [measurable complete-design weights](hyp:w,hw), give [the
conditional Hoeffding exponential-moment bound on
almost every complete design vector](goal). -/
theorem product_weighted_centered_conditional_mgf_le
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : ∀ᵐ omega ∂P, 0 <= Y omega)
    (hY_le_one : ∀ᵐ omega ∂P, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin N => P.map design), ∀ s : Real,
      ∫ y, Real.exp (s * weightedCenteredMarkSum mD w d y)
          ∂Causalean.Stat.finProductKernel N (condDistrib Y design P) d <=
        Real.exp (s ^ 2 * realizedWeightEnergy w d / 8) := by
  -- Derive the conditional-distribution mean and range from `hcond` and the ambient
  -- bounds, then invoke the kernel-native product theorem.  No conditional-independence
  -- hypothesis is introduced here.
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
  letI : IsProbabilityMeasure (P.map design) :=
    Measure.isProbabilityMeasure_map hdesign.aemeasurable
  exact product_weighted_centered_attachKernel_conditional_mgf_le
    (P.map design) (condDistrib Y design P) mD hmD hmean hrange w hw


end Causalean.Stat.Concentration.RandomDesignWeightedHoeffding
