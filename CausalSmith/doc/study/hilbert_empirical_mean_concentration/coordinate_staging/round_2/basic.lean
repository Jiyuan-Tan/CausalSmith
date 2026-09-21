/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration

/-!
# Dimension-free Hilbert empirical-mean moments

This module defines the population and empirical means of a Hilbert-valued
feature map and proves their finite-product second-moment identities.  In
particular, it establishes the dimension-free variance-of-the-mean calculation
by expanding Hilbert inner products and cancelling independent centered cross
terms; no finite-dimensionality assumption is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.Concentration.HilbertEmpiricalMean

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The [population mean](goal) of [a Hilbert-valued feature map](hyp:f) under
[a probability law](hyp:P) is [given by its Bochner integral](step:1). -/
def populationMean (P : Measure X) (f : X → H) : H :=
  ∫ x, f x ∂P

/-- The [empirical mean](goal) of [a Hilbert-valued feature map](hyp:f) on
[a sample with the stated size and observations](hyp:m,z) is [given by the
inverse sample size times its finite coordinate sum](step:1). -/
def empiricalMean (f : X → H) (m : ℕ) (z : Fin m → X) : H :=
  (m : ℝ)⁻¹ • ∑ r, f (z r)

/-- The [centered empirical mean](goal) for [a probability law](hyp:P),
[a Hilbert-valued feature map](hyp:f), and [a sample with the stated size and
observations](hyp:m,z) is [given by its empirical mean minus its population
mean](step:1). -/
def centeredEmpiricalMean (P : Measure X) (f : X → H) (m : ℕ)
    (z : Fin m → X) : H :=
  empiricalMean f m z - populationMean P f

/-- The [norm statistic for a centered empirical mean](goal) under
[a probability law](hyp:P), [a Hilbert-valued feature map](hyp:f), and
[a sample with the stated size and observations](hyp:m,z) is [given by the
Hilbert norm of that centered mean](step:1). -/
def centeredEmpiricalMeanNorm (P : Measure X) (f : X → H) (m : ℕ)
    (z : Fin m → X) : ℝ :=
  ‖centeredEmpiricalMean P f m z‖

/-- A [strongly measurable Hilbert-valued feature map](hyp:f,hf) whose norm is
[at most one at every observation](hyp:hbound) under [a probability law](hyp:P)
is [Bochner integrable](goal). -/
theorem integrable_of_norm_le_one (P : Measure X) [IsProbabilityMeasure P]
    (f : X → H) (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f P := by
  exact Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all P hbound)

/-- A [strongly measurable Hilbert-valued feature map](hyp:f,hf) whose norm is
[at most one at every observation](hyp:hbound) under [a probability law](hyp:P)
belongs [to the square-integrable class](goal). -/
theorem memLp_two_of_norm_le_one (P : Measure X) [IsProbabilityMeasure P]
    (f : X → H) (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    MemLp f 2 P := by
  exact MemLp.of_bound hf.aestronglyMeasurable 1 (ae_of_all P hbound)

/-- For [a probability law](hyp:P), [a Hilbert-valued feature map](hyp:f),
[a positive sample size](hyp:hm), and [a sample](hyp:z), [the centered empirical
mean equals the inverse sample size times the sum of centered observations](goal). -/
theorem centeredEmpiricalMean_eq_inv_smul_sum_centered
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    {m : ℕ} (hm : 0 < m) (z : Fin m → X) :
    centeredEmpiricalMean P f m z =
      (m : ℝ)⁻¹ • ∑ r, (f (z r) - populationMean P f) := by
  unfold centeredEmpiricalMean empiricalMean
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  simp only [Finset.sum_const, Finset.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hm.ne']

variable [MeasurableSpace H] [BorelSpace H]

/-- For [a probability law](hyp:P), [a strongly measurable Hilbert-valued
feature map](hyp:f,hf), and [a sample size](hyp:m), [the norm of its centered
empirical mean is measurable on the finite product sample space](goal). -/
@[fun_prop]
theorem measurable_centeredEmpiricalMeanNorm (P : Measure X) (f : X → H)
    (hf : StronglyMeasurable f) (m : ℕ) :
    Measurable (centeredEmpiricalMeanNorm P f m) := by
  unfold centeredEmpiricalMeanNorm centeredEmpiricalMean empiricalMean populationMean
  have hsum : StronglyMeasurable (fun z : Fin m → X => ∑ r, f (z r)) := by
    rw [← Finset.sum_fn]
    apply Finset.stronglyMeasurable_sum
    intro r _
    change StronglyMeasurable (f ∘ fun z : Fin m → X => z r)
    exact hf.comp_measurable (measurable_pi_apply r)
  exact ((hsum.const_smul (m : ℝ)⁻¹).sub stronglyMeasurable_const).norm.measurable

/-- For [a probability law](hyp:P), [a Hilbert-valued feature map](hyp:f) with
[unit-norm bound at every observation](hyp:hbound), [a positive sample size](hyp:hm),
[a coordinate](hyp:i), [a sample](hyp:z), and [a replacement observation](hyp:x'),
[changing that coordinate changes the centered-mean norm by at most two divided
by the sample size](goal). -/
theorem centeredEmpiricalMeanNorm_boundedDifference
    (P : Measure X) (f : X → H) (hbound : ∀ x, ‖f x‖ ≤ 1)
    {m : ℕ} (hm : 0 < m) (i : Fin m) (z : Fin m → X) (x' : X) :
    |centeredEmpiricalMeanNorm P f m z -
        centeredEmpiricalMeanNorm P f m (Function.update z i x')| ≤
      2 / (m : ℝ) := by
  have hsum :
      (∑ r, f (z r)) - ∑ r, f (Function.update z i x' r) = f (z i) - f x' := by
    have hupdate : (fun r => f (Function.update z i x' r)) =
        Function.update (fun r => f (z r)) i (f x') := by
      funext r
      by_cases hri : r = i <;> simp [hri]
    rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sdiff_singleton_eq_erase]
    rw [← Finset.sum_erase_add Finset.univ (fun r => f (z r)) (Finset.mem_univ i)]
    abel
  calc
    |centeredEmpiricalMeanNorm P f m z -
        centeredEmpiricalMeanNorm P f m (Function.update z i x')|
        ≤ ‖centeredEmpiricalMean P f m z -
            centeredEmpiricalMean P f m (Function.update z i x')‖ :=
          abs_norm_sub_norm_le _ _
    _ = ‖(m : ℝ)⁻¹ • (f (z i) - f x')‖ := by
          unfold centeredEmpiricalMean empiricalMean
          rw [sub_sub_sub_cancel_right, ← smul_sub, hsum]
    _ = (m : ℝ)⁻¹ * ‖f (z i) - f x'‖ := by
          rw [norm_smul]
          simp
    _ ≤ (m : ℝ)⁻¹ * 2 := by
          gcongr
          calc
            ‖f (z i) - f x'‖ ≤ ‖f (z i)‖ + ‖f x'‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add (hbound _) (hbound _)
            _ = 2 := by norm_num
    _ = 2 / (m : ℝ) := by ring

/-- For [a finite family of Hilbert vectors](hyp:v), [the squared norm of its
sum is the double sum of its pairwise inner products](goal). -/
theorem norm_sum_sq_eq_sum_inner {ι : Type*} [Fintype ι]
    (v : ι → H) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ∑ j, inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]

/-- For [a probability law](hyp:P) and [an integrable Hilbert-valued feature
map](hyp:f,hf), [the integral of the map centered at its population mean is zero](goal). -/
theorem integral_sub_populationMean_eq_zero
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : Integrable f P) :
    ∫ x, (f x - populationMean P f) ∂P = 0 := by
  rw [integral_sub hf (integrable_const _)]
  simp [populationMean]

/-- For [a probability law](hyp:P), [a strongly measurable square-integrable
Hilbert-valued feature map](hyp:f,hf,hf_L2), and [a product coordinate](hyp:i),
[the coordinate's centered second moment equals the population centered second
moment](goal). -/
theorem integral_norm_centered_coordinate_sq_eq
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hf_L2 : MemLp f 2 P)
    {m : ℕ} (i : Fin m) :
    ∫ z : Fin m → X, ‖f (z i) - populationMean P f‖ ^ 2
        ∂(Measure.pi (fun _ : Fin m => P)) =
      ∫ x, ‖f x - populationMean P f‖ ^ 2 ∂P := by
  let g : X → H := fun x => f x - populationMean P f
  have hg_L2 : MemLp g 2 P := by
    exact hf_L2.sub (memLp_const (populationMean P f))
  have hg_sq : Integrable (fun x => ‖g x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hg_L2.aestronglyMeasurable).1 hg_L2
  exact integral_comp_eval (μ := fun _ : Fin m => P) (i := i)
    hg_sq.aestronglyMeasurable

/-- For [a probability law](hyp:P), [a strongly measurable square-integrable
Hilbert-valued feature map](hyp:f,hf,hf_L2), and [two distinct product
coordinates](hyp:i,j,hij), [the expected inner product of their centered
values is zero](goal). -/
theorem integral_inner_centered_coordinates_eq_zero
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hf_L2 : MemLp f 2 P)
    {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    ∫ z : Fin m → X,
        inner ℝ (f (z i) - populationMean P f)
          (f (z j) - populationMean P f)
        ∂(Measure.pi (fun _ : Fin m => P)) = 0 := by
  let g : X → H := fun x => f x - populationMean P f
  have hg_L2 : MemLp g 2 P := by
    exact hf_L2.sub (memLp_const (populationMean P f))
  have hg : Integrable g P := hg_L2.integrable (by norm_num)
  have hIndep :
      (fun z : Fin m → X => z i) ⟂ᵢ[Measure.pi (fun _ : Fin m => P)]
        (fun z : Fin m → X => z j) :=
    (iIndepFun_pi (X := fun _ : Fin m => id) (fun _ => aemeasurable_id)).indepFun hij
  have hgi : Integrable g
      ((Measure.pi (fun _ : Fin m => P)).map (fun z : Fin m → X => z i)) := by
    rw [(measurePreserving_eval (fun _ : Fin m => P) i).map_eq]
    exact hg
  have hgj : Integrable g
      ((Measure.pi (fun _ : Fin m => P)).map (fun z : Fin m → X => z j)) := by
    rw [(measurePreserving_eval (fun _ : Fin m => P) j).map_eq]
    exact hg
  rw [show (fun z : Fin m → X =>
      inner ℝ (f (z i) - populationMean P f) (f (z j) - populationMean P f)) =
      fun z => (innerSL ℝ) (g (z i)) (g (z j)) by rfl]
  rw [hIndep.integral_bilin_comp_comp
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    hgi hgj (innerSL ℝ)]
  rw [integral_comp_eval (μ := fun _ : Fin m => P) hg.aestronglyMeasurable,
    integral_comp_eval (μ := fun _ : Fin m => P) hg.aestronglyMeasurable]
  change inner ℝ (∫ x, f x - populationMean P f ∂P)
    (∫ x, f x - populationMean P f ∂P) = 0
  rw [integral_sub_populationMean_eq_zero P f (hf_L2.integrable (by norm_num))]
  simp

/-- For [a probability law](hyp:P) and [a strongly measurable square-integrable
Hilbert-valued feature map](hyp:f,hf,hf_L2), [centering does not increase its
population second moment](goal). -/
theorem population_centered_secondMoment_le
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hf_L2 : MemLp f 2 P) :
    ∫ x, ‖f x - populationMean P f‖ ^ 2 ∂P ≤
      ∫ x, ‖f x‖ ^ 2 ∂P := by
  have hfi : Integrable f P := hf_L2.integrable (by norm_num)
  have hsq : Integrable (fun x => ‖f x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hf_L2.aestronglyMeasurable).1 hf_L2
  have hinner : Integrable (fun x => inner ℝ (populationMean P f) (f x)) P :=
    hfi.const_inner (populationMean P f)
  have hcross : Integrable (fun x => 2 * inner ℝ (populationMean P f) (f x)) P :=
    hinner.const_mul 2
  have hconst : Integrable (fun _ : X => ‖populationMean P f‖ ^ 2) P :=
    integrable_const _
  have hpoint : ∀ x,
      ‖f x - populationMean P f‖ ^ 2 =
        ‖f x‖ ^ 2 - 2 * inner ℝ (populationMean P f) (f x) +
          ‖populationMean P f‖ ^ 2 := by
    intro x
    rw [norm_sub_sq_real, real_inner_comm]
  rw [integral_congr_ae (ae_of_all P hpoint)]
  change (∫ x, ((fun x => ‖f x‖ ^ 2) -
      (fun x => 2 * inner ℝ (populationMean P f) (f x)) +
      (fun _ : X => ‖populationMean P f‖ ^ 2)) x ∂P) ≤ _
  rw [integral_add' (hsq.sub hcross) hconst, integral_sub' hsq hcross,
    integral_const_mul, integral_inner hfi, integral_const, probReal_univ, one_smul]
  rw [show ∫ x, f x ∂P = populationMean P f by rfl, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖populationMean P f‖]

/-- For [a probability law](hyp:P), [a strongly measurable square-integrable
Hilbert-valued feature map](hyp:f,hf,hf_L2), and [a sample size](hyp:m), [the
second moment of the unscaled centered sum equals the sample size times the
population centered second moment](goal). -/
theorem centeredSum_secondMoment_eq
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hf_L2 : MemLp f 2 P) (m : ℕ) :
    ∫ z : Fin m → X,
        ‖∑ r, (f (z r) - populationMean P f)‖ ^ 2
        ∂(Measure.pi (fun _ : Fin m => P)) =
      (m : ℝ) * ∫ x, ‖f x - populationMean P f‖ ^ 2 ∂P := by
  let g : X → H := fun x => f x - populationMean P f
  have hg_L2 : MemLp g 2 P :=
    hf_L2.sub (memLp_const (populationMean P f))
  have hcoord (i : Fin m) :
      MemLp (fun z : Fin m → X => g (z i)) 2
        (Measure.pi (fun _ : Fin m => P)) := by
    change MemLp (g ∘ (Function.eval i : (Fin m → X) → X)) 2 _
    exact hg_L2.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => P) i)
  have hinner (i j : Fin m) :
      Integrable (fun z : Fin m → X => inner ℝ (g (z i)) (g (z j)))
        (Measure.pi (fun _ : Fin m => P)) := by
    let gi : (Fin m → X) →₂[Measure.pi (fun _ : Fin m => P)] H :=
      (hcoord i).toLp (fun z : Fin m → X => g (z i))
    let gj : (Fin m → X) →₂[Measure.pi (fun _ : Fin m => P)] H :=
      (hcoord j).toLp (fun z : Fin m → X => g (z j))
    apply (L2.integrable_inner gi gj).congr
    filter_upwards [(hcoord i).coeFn_toLp, (hcoord j).coeFn_toLp] with z hzi hzj
    change gi z = g (z i) at hzi
    change gj z = g (z j) at hzj
    rw [hzi, hzj]
  have hterm (i j : Fin m) :
      (∫ z : Fin m → X, inner ℝ (g (z i)) (g (z j))
          ∂(Measure.pi (fun _ : Fin m => P))) =
        if i = j then ∫ x, ‖g x‖ ^ 2 ∂P else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      simpa only [g, real_inner_self_eq_norm_sq] using
        integral_norm_centered_coordinate_sq_eq P f hf hf_L2 i
    · rw [if_neg hij]
      simpa only [g] using
        integral_inner_centered_coordinates_eq_zero P f hf hf_L2 hij
  rw [show (fun z : Fin m → X =>
      ‖∑ r, (f (z r) - populationMean P f)‖ ^ 2) =
      fun z => ∑ i, ∑ j, inner ℝ (g (z i)) (g (z j)) by
        funext z
        exact norm_sum_sq_eq_sum_inner
          (fun r => f (z r) - populationMean P f)]
  rw [integral_finsetSum Finset.univ (by
        intro i hi
        exact integrable_finsetSum Finset.univ (fun j _ => hinner i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hinner _ j), hterm]
  simp [g]

/-- For [a probability law](hyp:P), [a strongly measurable square-integrable
Hilbert-valued feature map](hyp:f,hf,hf_L2), and [a positive sample size](hyp:hm),
[the centered empirical mean has second moment equal to the inverse sample
size times the population centered second moment](goal). -/
theorem centeredEmpiricalMean_secondMoment_eq
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hf_L2 : MemLp f 2 P)
    {m : ℕ} (hm : 0 < m) :
    ∫ z : Fin m → X, ‖centeredEmpiricalMean P f m z‖ ^ 2
        ∂(Measure.pi (fun _ : Fin m => P)) =
      (m : ℝ)⁻¹ * ∫ x, ‖f x - populationMean P f‖ ^ 2 ∂P := by
  have hpoint (z : Fin m → X) :
      ‖centeredEmpiricalMean P f m z‖ ^ 2 =
        ((m : ℝ)⁻¹) ^ 2 *
          ‖∑ r, (f (z r) - populationMean P f)‖ ^ 2 := by
    rw [centeredEmpiricalMean_eq_inv_smul_sum_centered P f hm z, norm_smul]
    rw [mul_pow]
    congr 2
    simp
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul,
    centeredSum_secondMoment_eq P f hf hf_L2 m]
  field_simp

/-- For [a probability law](hyp:P), [a strongly measurable square-integrable
Hilbert-valued feature map](hyp:f,hf,hf_L2), and [a positive sample size](hyp:hm),
[the centered empirical mean has second moment at most the inverse sample size
times the raw population second moment](goal). -/
theorem centeredEmpiricalMean_secondMoment_le
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hf_L2 : MemLp f 2 P)
    {m : ℕ} (hm : 0 < m) :
    ∫ z : Fin m → X, ‖centeredEmpiricalMean P f m z‖ ^ 2
        ∂(Measure.pi (fun _ : Fin m => P)) ≤
      (m : ℝ)⁻¹ * ∫ x, ‖f x‖ ^ 2 ∂P := by
  rw [centeredEmpiricalMean_secondMoment_eq P f hf hf_L2 hm]
  exact mul_le_mul_of_nonneg_left
    (population_centered_secondMoment_le P f hf hf_L2) (by positivity)

end Causalean.Stat.Concentration.HilbertEmpiricalMean
