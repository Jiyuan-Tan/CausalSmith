module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Bochner disintegration of finite atomic kernels

This module evaluates Bochner integrals against finite mixtures of Dirac measures and
disintegrates set integrals along a measurable base coordinate. It applies to a continuous
base measure with finitely many, possibly distinct, atoms above each base point.
-/

public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.FiniteAtomic

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass Y] [Fintype I]

/-- A [finite atomic kernel](hyp:κ), described by [its atom locations and nonnegative
weights](hyp:atom,weight,hweight) through [a pointwise Dirac decomposition](hyp:hκ), has [the
finite weighted integral of an integrable real-valued outcome](hyp:f,hf) at [the specified base
point](hyp:x) as [its Bochner integral](goal). -/
theorem integral_finiteAtomicKernel
    (κ : Kernel X Y) (atom : X → I → Y) (weight : X → I → ℝ)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hκ : ∀ x, κ x = ∑ i : I,
      ENNReal.ofReal (weight x i) • Measure.dirac (atom x i))
    (f : Y → ℝ) (x : X) (hf : Integrable f (κ x)) :
    ∫ y, f y ∂κ x = ∑ i : I, weight x i * f (atom x i) := by
  rw [hκ x]
  have hi : ∀ i ∈ (Finset.univ : Finset I),
      Integrable f (ENNReal.ofReal (weight x i) • Measure.dirac (atom x i)) :=
    (integrable_finsetSum_measure.mp (by simpa using (hκ x ▸ hf)))
  rw [integral_finsetSum_measure hi]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hweight x _), smul_eq_mul]

/-- An [s-finite base measure](hyp:μ) and [s-finite finite atomic kernel with nonnegative,
normalized weights](hyp:κ,atom,weight,hweight,hnorm,hκ), together with [a measurable projection
that recovers the base point from every atom](hyp:base,hbase_meas,hbase), a [measurable base
set](hyp:B,hB), and an [integrable outcome](hyp:f,hf), turn [the outcome integral over atoms
above that set into the integral of their finite weighted mean](goal). -/
theorem setIntegral_finiteAtomicKernel
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    (atom : X → I → Y) (weight : X → I → ℝ)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hnorm : ∀ x, ∑ i : I, weight x i = 1)
    (hκ : ∀ x, κ x = ∑ i : I,
      ENNReal.ofReal (weight x i) • Measure.dirac (atom x i))
    (base : Y → X) (hbase_meas : Measurable base)
    (hbase : ∀ x i, base (atom x i) = x)
    (B : Set X) (hB : MeasurableSet B)
    (f : Y → ℝ) (hf : Integrable f (κ ∘ₘ μ)) :
    ∫ y in {y | base y ∈ B}, f y ∂(κ ∘ₘ μ) =
      ∫ x in B, (∑ i : I, weight x i * f (atom x i)) ∂μ := by
  let S : Set Y := base ⁻¹' B
  have hS : MeasurableSet S := hB.preimage hbase_meas
  let g : Y → ℝ := S.indicator f
  have hg : Integrable g (κ ∘ₘ μ) := hf.indicator hS
  have hpair : Integrable (fun p : X × Y => g p.2) (μ ⊗ₘ κ) :=
    (Measure.integrable_compProd_snd_iff hg.1).2 hg
  have hcomp : ∫ y, g y ∂(κ ∘ₘ μ) = ∫ x, ∫ y, g y ∂κ x ∂μ := by
    rw [← Measure.snd_compProd μ κ]
    rw [← Measure.integral_compProd hpair]
    rw [Measure.snd]
    exact integral_map measurable_snd.aemeasurable (by
      simpa [← Measure.snd_compProd μ κ, Measure.snd] using hg.1)
  have hfiber : ∀ᵐ x ∂μ, Integrable g (κ x) :=
    Measure.ae_integrable_of_integrable_comp hg
  have heval : ∀ᵐ x ∂μ,
      (∫ y, g y ∂κ x) = B.indicator
        (fun x => ∑ i : I, weight x i * f (atom x i)) x := by
    filter_upwards [hfiber] with x hx
    rw [integral_finiteAtomicKernel κ atom weight hweight hκ g x hx]
    by_cases hxB : x ∈ B
    · simp [g, S, Set.indicator, hbase, hxB]
    · simp [g, S, Set.indicator, hbase, hxB]
  change ∫ y in S, f y ∂(κ ∘ₘ μ) = _
  rw [← integral_indicator hS, hcomp]
  rw [integral_congr_ae heval]
  exact integral_indicator hB

/-- An [s-finite base measure](hyp:μ),
[normalized finite atomic kernel](hyp:κ,atom,weight,hweight,hnorm,hκ),
[measurable base-recovering projection](hyp:base,hbase_meas,hbase),
[measurable base set](hyp:B,hB), and [integrable outcome](hyp:f,hf), with an [integrable
pointwise-equal candidate mean](hyp:q,hq_int,hq), make [the selected outcome integral equal the
set integral of that mean](goal). -/
theorem setIntegral_finiteAtomicKernel_of_pointwise
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    (atom : X → I → Y) (weight : X → I → ℝ)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hnorm : ∀ x, ∑ i : I, weight x i = 1)
    (hκ : ∀ x, κ x = ∑ i : I,
      ENNReal.ofReal (weight x i) • Measure.dirac (atom x i))
    (base : Y → X) (hbase_meas : Measurable base)
    (hbase : ∀ x i, base (atom x i) = x)
    (B : Set X) (hB : MeasurableSet B)
    (f : Y → ℝ) (hf : Integrable f (κ ∘ₘ μ))
    (q : X → ℝ) (hq_int : Integrable q μ)
    (hq : ∀ x, (∑ i : I, weight x i * f (atom x i)) = q x) :
    ∫ y in {y | base y ∈ B}, f y ∂(κ ∘ₘ μ) = ∫ x in B, q x ∂μ := by
  rw [setIntegral_finiteAtomicKernel μ κ atom weight hweight hnorm hκ
    base hbase_meas hbase B hB f hf]
  simp_rw [hq]

/-- An [s-finite base measure](hyp:μ) and [two-atom s-finite kernel with nonnegative,
normalized weights](hyp:κ,weight,hweight,hnorm,hκ), a [measurable base set](hyp:B,hB), and an
[integrable paired outcome](hyp:f,hf) give [the selected integral as the weighted average of the
two atom values over that base set](goal). -/
theorem setIntegral_twoAtomicKernel
    (μ : Measure X) [SFinite μ]
    [MeasurableSingletonClass (X × Fin 2)]
    (κ : Kernel X (X × Fin 2)) [IsSFiniteKernel κ]
    (weight : X → Fin 2 → ℝ)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hnorm : ∀ x, ∑ i : Fin 2, weight x i = 1)
    (hκ : ∀ x, κ x = ∑ i : Fin 2,
      ENNReal.ofReal (weight x i) • Measure.dirac (x, i))
    (B : Set X) (hB : MeasurableSet B)
    (f : X × Fin 2 → ℝ) (hf : Integrable f (κ ∘ₘ μ)) :
    ∫ y in {y | y.1 ∈ B}, f y ∂(κ ∘ₘ μ) =
      ∫ x in B, (∑ i : Fin 2, weight x i * f (x, i)) ∂μ := by
  exact setIntegral_finiteAtomicKernel μ κ (fun x i => (x, i)) weight
    hweight hnorm hκ Prod.fst measurable_fst (by intros; rfl) B hB f hf

example (κ : Kernel ℝ (ℝ × Fin 2)) [IsSFiniteKernel κ]
    (hκ : ∀ x, κ x = ∑ i : Fin 2,
      ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (x, i))
    (B : Set ℝ) (hB : MeasurableSet B)
    (f : ℝ × Fin 2 → ℝ) (hf : Integrable f (κ ∘ₘ volume)) :
    ∫ y in {y | y.1 ∈ B}, f y ∂(κ ∘ₘ volume) =
      ∫ x in B, (∑ i : Fin 2, (1 / 2 : ℝ) * f (x, i)) ∂volume := by
  apply setIntegral_twoAtomicKernel volume κ (fun _ _ => (1 / 2 : ℝ))
    (by intro x i; norm_num) ?_ hκ B hB f hf
  intro x
  simp

end Causalean.Mathlib.Probability.Kernel.FiniteAtomic
