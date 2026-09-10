/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Kernel.Representation

/-!
# Parameterized quantile realization of real Markov kernels

This file constructs a jointly measurable realization of a real-valued Markov kernel supported
on the closed unit interval by one uniform variable.  The construction is the generalized inverse
of each fiber's distribution function, valued first in the unit interval and then extended to real
randomization inputs by clamping them to that interval.  It proves both the exact fiberwise
pushforward law and the pointwise range guarantee needed by parameterized coupling and conditional
law constructions.
-/

open MeasureTheory ProbabilityTheory Set Function Filter Topology ENNReal unitInterval
open scoped unitInterval

namespace Causalean.Mathlib.Probability.Kernel.ParameterizedKernelQuantileRealization

variable {S : Type*} [MeasurableSpace S]

/-- For [a real-valued Markov kernel](hyp:κ), [the unit-interval support property](goal)
[says that each parameter-specific probability distribution assigns total mass one to the closed
interval from zero to one](step:1).

It records the fiberwise support condition used by the realization theorems. -/
def SupportedOnUnitInterval (κ : ProbabilityTheory.Kernel S ℝ) : Prop :=
  ∀ s, κ s (Icc (0 : ℝ) 1) = 1

/-- For [a real-valued Markov kernel](hyp:κ), [a parameter value](hyp:s), and [a uniform level
in the closed unit interval](hyp:u), [the unit-interval-valued parameterized quantile](goal)
[is the supremum of the interval points whose fiber distribution mass below that point is strictly
smaller than the supplied level](step:1).

This is the generalized-inverse construction used for the kernel realization. -/
noncomputable def kernelUnitQuantile (κ : ProbabilityTheory.Kernel S ℝ) (s : S)
    (u : unitInterval) : unitInterval :=
  sSup {x : unitInterval | (κ s).real (Icc (0 : ℝ) x) < u}

/-- For [a real-valued Markov kernel](hyp:κ) and [a parameter--randomization pair](hyp:p),
[the real-valued quantile realization](goal) [evaluates the unit-interval quantile after clamping
the randomization coordinate to the closed unit interval](step:1).

The clamping makes the map defined on arbitrary real inputs while preserving its uniform-section
interpretation. -/
noncomputable def quantileRealization (κ : ProbabilityTheory.Kernel S ℝ) (p : S × ℝ) : ℝ :=
  kernelUnitQuantile κ p.1 (projIcc (0 : ℝ) 1 zero_le_one p.2)

/-- For [a real-valued Markov kernel](hyp:κ) and [a parameter--randomization pair](hyp:p),
[the corresponding realization value belongs to the closed unit interval](goal).

This pointwise range guarantee does not require a support assumption on the kernel. -/
theorem quantileRealization_mem_unitInterval (κ : ProbabilityTheory.Kernel S ℝ) (p : S × ℝ) :
    quantileRealization κ p ∈ Icc (0 : ℝ) 1 := by
  exact (kernelUnitQuantile κ p.1 (projIcc (0 : ℝ) 1 zero_le_one p.2)).property

/-- For [a real-valued Markov kernel](hyp:κ) that is Markov, [the unit-interval generalized
inverse is jointly measurable in the kernel parameter and uniform level](goal).

The proof expresses each strict superlevel set as a countable union over rational thresholds. -/
theorem measurable_kernelUnitQuantile (κ : ProbabilityTheory.Kernel S ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] :
    Measurable (uncurry (kernelUnitQuantile κ)) := by
  refine measurable_of_Ioi fun a ↦ ?_
  simp only [preimage, uncurry, mem_Ioi]
  have h_monotone s : Monotone (fun x : unitInterval ↦ (κ s).real (Icc (0 : ℝ) x)) :=
    fun x y hxy ↦ measureReal_mono (by gcongr)
  have sSup_eq_iUnion_rat :
      {x : S × unitInterval | a < kernelUnitQuantile κ x.1 x.2} =
        ⋃ (q : ℚ) (hqI : (↑q : ℝ) ∈ unitInterval) (_ : a < (q : ℝ)),
          {e | (κ e.1).real
            (Icc (0 : ℝ) ((⟨(q : ℝ), hqI⟩ : unitInterval) : ℝ)) < e.2} := by
    ext e
    simp_all only [lt_sSup_iff, mem_ofPred_eq, Subtype.exists, mem_Icc, Rat.cast_nonneg,
      mem_iUnion, exists_prop, exists_and_left, kernelUnitQuantile]
    constructor
    · rintro ⟨y, y_mem, hyI, (hy : a.1 < y)⟩
      obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
      have hq0 : 0 ≤ q := by
        exact (Rat.cast_nonneg (K := ℝ)).mp (a.2.1.trans hqa.le)
      have hqI : (q : ℝ) ∈ unitInterval :=
        ⟨a.2.1.trans hqa.le, hqy.le.trans hyI.2⟩
      refine ⟨q, ⟨hq0, hqI.2⟩, hqa, lt_of_lt_of_le' y_mem ?_⟩
      exact h_monotone e.1 (a := ⟨(q : ℝ), hqI⟩) (b := ⟨y, hyI⟩) hqy.le
    · intro he
      obtain ⟨q, hqI, hqa, h⟩ := he
      exact ⟨q, h, ⟨by simp [hqI.1], hqI.2⟩, hqa⟩
  rw [sSup_eq_iUnion_rat]
  refine MeasurableSet.iUnion (fun b ↦ MeasurableSet.iUnion
    (fun bI ↦ MeasurableSet.iUnion (fun _ ↦ ?_)))
  refine measurableSet_lt ?_ measurable_snd.subtype_val
  simp_rw [measureReal_def]
  have hκ := κ.measurable_coe
    (s := Icc (0 : ℝ) ((⟨(b : ℝ), bI⟩ : unitInterval) : ℝ)) measurableSet_Icc
  fun_prop

/-- For [a real-valued Markov kernel](hyp:κ), [the real-valued quantile realization is jointly
measurable in its parameter and real randomization input](goal).

It follows by composing the measurable unit-interval generalized inverse with the clamping map. -/
theorem measurable_quantileRealization (κ : ProbabilityTheory.Kernel S ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] :
    Measurable (quantileRealization κ) := by
  change Measurable (fun p : S × ℝ ↦
    ((kernelUnitQuantile κ p.1 (projIcc (0 : ℝ) 1 zero_le_one p.2) : unitInterval) : ℝ))
  exact measurable_subtype_coe.comp <| (measurable_kernelUnitQuantile κ).comp <|
    measurable_fst.prodMk
      ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp
        measurable_snd)

/-- For [a real-valued Markov kernel](hyp:κ) and [a fixed parameter value](hyp:s), [the
resulting real-valued function of the randomization input is measurable](goal).

This is the section form of joint measurability used in pushforward statements. -/
@[fun_prop]
theorem measurable_quantileRealization_section (κ : ProbabilityTheory.Kernel S ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] (s : S) :
    Measurable (fun u : ℝ => quantileRealization κ (s, u)) := by
  exact (measurable_quantileRealization κ).comp (measurable_const.prodMk measurable_id)

/-- Given [a real-valued Markov kernel](hyp:κ), [the condition that each fiber is supported on
the closed unit interval](hyp:hκ), and [a parameter value](hyp:s), [pushing canonical uniform
unit-interval volume through the fiber's quantile map exactly recovers that kernel fiber](goal).

The proof identifies the two measures on every left ray using the generalized-inverse relation. -/
theorem map_kernelUnitQuantile (κ : ProbabilityTheory.Kernel S ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] (hκ : SupportedOnUnitInterval κ) (s : S) :
    Measure.map (fun u : unitInterval => (kernelUnitQuantile κ s u : ℝ)) volume = κ s := by
  let f := fun u : unitInterval => (kernelUnitQuantile κ s u : ℝ)
  have hf : Measurable f :=
    measurable_subtype_coe.comp (measurable_kernelUnitQuantile κ).of_uncurry_left
  have hκ_compl : κ s (Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top (κ s) _), hκ s, measure_univ]
    simp
  have hκ_ae : ∀ᵐ y ∂κ s, y ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hκ_compl
  have hκ_Iic (z : unitInterval) : κ s (Iic (z : ℝ)) = κ s (Icc 0 (z : ℝ)) := by
    apply measure_congr
    refine hκ_ae.mono ?_
    intro y hy
    apply propext
    exact ⟨fun h ↦ ⟨hy.1, h⟩, And.right⟩
  refine (Measure.map f volume).ext_of_Iic (κ s) fun x ↦ ?_
  rw [Measure.map_apply hf measurableSet_Iic]
  change volume {u : unitInterval | (kernelUnitQuantile κ s u : ℝ) ≤ x} = κ s (Iic x)
  by_cases hx0 : x < 0
  · have hpre : {u : unitInterval | (kernelUnitQuantile κ s u : ℝ) ≤ x} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le.mpr (hx0.trans_le (kernelUnitQuantile κ s u).property.1)
    have hnull : κ s (Iic x) = 0 := by
      refine measure_mono_null ?_ hκ_compl
      intro y hy
      simp only [mem_Iic] at hy
      simp only [mem_compl_iff, mem_Icc, not_and_or]
      exact Or.inl (not_le.mpr (hy.trans_lt hx0))
    rw [hpre, measure_empty, hnull]
  · have hx0' : 0 ≤ x := le_of_not_gt hx0
    by_cases hx1 : x ≤ 1
    · let xI : unitInterval := ⟨x, hx0', hx1⟩
      have hIic : κ s (Iic x) = κ s (Icc 0 x) := hκ_Iic xI
      have κ_in_I : ((κ s).real (Icc (0 : ℝ) x)) ∈ unitInterval :=
        ⟨measureReal_nonneg, measureReal_le_one⟩
      rw [hIic, ← ofReal_measureReal (measure_ne_top (κ s) _),
        ← unitInterval.volume_Iic ⟨_, κ_in_I⟩]
      congr with ξ
      constructor
      · intro (hξ : kernelUnitQuantile κ s ξ ≤ xI)
        change ξ ≤ (κ s).real (Icc (0 : ℝ) x)
        by_cases hx : xI = 1
        · have hx' : x = 1 := congrArg Subtype.val hx
          rw [hx', measureReal_def, hκ s]
          simpa using ξ.2.2
        let g := fun y : unitInterval ↦ (κ s).real (Icc (0 : ℝ) y)
        let nebot : NeBot (𝓝[>] xI) := by
          refine nhdsGT_neBot_of_exists_gt ?_
          use 1
          exact lt_of_le_of_ne xI.2.2 hx
        refine le_of_tendsto_of_tendsto (b := 𝓝[>] xI) (g := g)
          continuousWithinAt_const ?_ ?_
        · let h := cdf (κ s)
          have h_continuousWithinAt :=
            continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous (xI : ℝ))
          have hreal (y : unitInterval) :
              (κ s).real (Icc (0 : ℝ) (y : ℝ)) = h (y : ℝ) := by
            change (κ s).real (Icc (0 : ℝ) (y : ℝ)) = cdf (κ s) (y : ℝ)
            rw [ProbabilityTheory.cdf_eq_real, measureReal_def, measureReal_def, hκ_Iic y]
          simp_rw [g, hreal]
          rw [hreal xI]
          exact h_continuousWithinAt.comp
            (Continuous.continuousWithinAt (by fun_prop)) (fun y hy ↦ hy)
        · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
          by_contra! h
          simp only [sSup_le_iff, kernelUnitQuantile] at hξ
          specialize hξ y h
          grind
      · intro (hξ : ξ ≤ (κ s).real (Icc (0 : ℝ) x))
        change kernelUnitQuantile κ s ξ ≤ xI
        simp only [sSup_le_iff, kernelUnitQuantile]
        intro c hc
        by_contra! h
        have h_lt : ¬(κ s).real (Icc (0 : ℝ) x) ≤ (κ s).real (Icc (0 : ℝ) c) :=
          not_le.mpr (lt_of_le_of_lt' hξ hc)
        refine h_lt ?_
        refine measureReal_mono ?_
        intro z hz
        exact ⟨hz.1, hz.2.trans (by exact_mod_cast h.le)⟩
    · have hx1' : 1 < x := lt_of_not_ge hx1
      have hpre : {u : unitInterval | (kernelUnitQuantile κ s u : ℝ) ≤ x} = Set.univ := by
        ext u
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (kernelUnitQuantile κ s u).property.2.trans hx1'.le
      have hfull : κ s (Iic x) = 1 := by
        calc
          κ s (Iic x) = κ s Set.univ := by
            apply measure_congr
            refine hκ_ae.mono ?_
            intro y hy
            exact propext ⟨fun _ ↦ mem_univ y, fun _ ↦ hy.2.trans hx1'.le⟩
          _ = 1 := measure_univ
      rw [hpre, measure_univ, hfull]

/-- Given [a real-valued Markov kernel](hyp:κ), [the condition that each fiber is supported on
the closed unit interval](hyp:hκ), and [a parameter value](hyp:s), [pushing Lebesgue measure
restricted to the closed unit interval through the real quantile section exactly recovers that
kernel fiber](goal).

This is the real-line form of the uniform realization law. -/
theorem map_quantileRealization (κ : ProbabilityTheory.Kernel S ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] (hκ : SupportedOnUnitInterval κ) (s : S) :
    Measure.map (fun u : ℝ => quantileRealization κ (s, u))
      (volume.restrict (Icc (0 : ℝ) 1)) = κ s := by
  rw [← unitInterval.measurePreserving_coe.map_eq,
    Measure.map_map (measurable_quantileRealization_section κ s) measurable_subtype_coe]
  rw [show (fun u : ℝ => quantileRealization κ (s, u)) ∘ Subtype.val =
      fun u : unitInterval => (kernelUnitQuantile κ s u : ℝ) by
    funext u
    simp only [Function.comp_apply, quantileRealization]
    rw [Set.projIcc_of_mem zero_le_one u.property]]
  exact map_kernelUnitQuantile κ hκ s

/-- For [a real-valued Markov kernel](hyp:κ) and [a parameter value](hyp:s), [the realization
section lies in the closed unit interval almost everywhere under the uniform law](goal).

The underlying range statement is pointwise. -/
theorem ae_quantileRealization_mem_unitInterval (κ : ProbabilityTheory.Kernel S ℝ) (s : S) :
    ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)),
      quantileRealization κ (s, u) ∈ Icc (0 : ℝ) 1 := by
  exact Filter.Eventually.of_forall fun u => quantileRealization_mem_unitInterval κ (s, u)

end Causalean.Mathlib.Probability.Kernel.ParameterizedKernelQuantileRealization
