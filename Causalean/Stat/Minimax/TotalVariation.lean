/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Total variation distance between probability measures

The statistical total variation distance

  `tvDist μ ν = ⨆ A measurable, |μ.real A − ν.real A|`

between two measures on a common space.  Mathlib only carries
`SignedMeasure.totalVariation` (the Jordan-decomposition norm); this file
develops the elementary *testing* characterization that drives Le Cam's
two-point method (`Causalean/Stat/Minimax/LeCam.lean`).

Main results (all under `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]`):

* `tvDist_nonneg`, `tvDist_le_one` — range `[0,1]`;
* `tvDist_symm` — symmetry;
* `measureReal_sub_le_tvDist` — each signed gap `ν.real A − μ.real A` is `≤ tvDist`;
* `one_sub_tvDist_le_test` — **the testing bound** `1 − tvDist μ ν ≤ μ.real A + ν.real Aᶜ`,
  i.e. the total error of any test (rejection region `A`) is at least `1 − tvDist`.

These are deliberately project-agnostic and are candidates for upstream
contribution to Mathlib.
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Total Variation Distance

This file defines the statistical total variation distance between two probability
measures on a common measurable space. It develops elementary bounds and the
testing inequality that underlies Le Cam's two-point minimax method. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- [The statistical total variation distance](goal) between [two measures](hyp:μ,ν) on
[a sample space equipped with a σ-algebra](hyp:Ω,mΩ) is the largest absolute difference
between their real-valued masses over all measurable events.

Equivalently, it is the supremum of `|μ.real A − ν.real A|` over measurable sets `A`. -/
noncomputable def tvDist (μ ν : Measure Ω) : ℝ :=
  ⨆ A : {A : Set Ω // MeasurableSet A}, |μ.real A.1 - ν.real A.1|

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Every term of the supremum defining `tvDist` is bounded by `1`. -/
theorem abs_measureReal_sub_le_one (A : Set Ω) : |μ.real A - ν.real A| ≤ 1 := by
  have hμ : μ.real A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by
      have := measureReal_mono (μ := μ) (Set.subset_univ A) (measure_ne_top μ _)
      simpa [probReal_univ] using this⟩
  have hν : ν.real A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by
      have := measureReal_mono (μ := ν) (Set.subset_univ A) (measure_ne_top ν _)
      simpa [probReal_univ] using this⟩
  rw [abs_le]
  constructor <;> [nlinarith [hμ.1, hμ.2, hν.1, hν.2]; nlinarith [hμ.1, hμ.2, hν.1, hν.2]]

/-- The family defining `tvDist` is bounded above (by `1`). -/
theorem bddAbove_tvDist_range :
    BddAbove (Set.range fun A : {A : Set Ω // MeasurableSet A} => |μ.real A.1 - ν.real A.1|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact abs_measureReal_sub_le_one A.1

/-- For a measurable set `A`, the gap `|μ.real A − ν.real A|` is at most `tvDist μ ν`. -/
theorem abs_measureReal_sub_le_tvDist {A : Set Ω} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ tvDist μ ν :=
  le_ciSup bddAbove_tvDist_range (⟨A, hA⟩ : {A : Set Ω // MeasurableSet A})

/-- The signed gap `ν.real A − μ.real A` is at most `tvDist μ ν`. -/
theorem measureReal_sub_le_tvDist {A : Set Ω} (hA : MeasurableSet A) :
    ν.real A - μ.real A ≤ tvDist μ ν :=
  (le_abs_self _).trans <| by
    rw [abs_sub_comm]; exact abs_measureReal_sub_le_tvDist hA

/-- Total variation distance between probability measures is nonnegative. -/
theorem tvDist_nonneg : 0 ≤ tvDist μ ν := by
  have := abs_measureReal_sub_le_tvDist (μ := μ) (ν := ν) MeasurableSet.empty
  simpa using (abs_nonneg _).trans this

/-- Total variation distance between probability measures is at most one. -/
theorem tvDist_le_one : tvDist μ ν ≤ 1 :=
  ciSup_le fun A => abs_measureReal_sub_le_one A.1

/-- `tvDist` is symmetric. -/
theorem tvDist_symm (μ ν : Measure Ω) : tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  congr 1
  ext A
  rw [abs_sub_comm]

/-- **Le Cam testing bound.** For probability measures `μ` and `ν` on the same space,
[any measurable rejection region `A`](hyp:hA) yields [a total testing error — the
probability of `A` under `μ` plus the probability of the complement of `A` under `ν` —
that is at least `1 − tvDist(μ,ν)`](goal).

This is the single inequality on which the two-point method rests. -/
theorem one_sub_tvDist_le_test {A : Set Ω} (hA : MeasurableSet A) :
    1 - tvDist μ ν ≤ μ.real A + ν.real Aᶜ := by
  have hcompl : ν.real Aᶜ = 1 - ν.real A := by
    rw [measureReal_compl hA, probReal_univ]
  rw [hcompl]
  have h := measureReal_sub_le_tvDist (μ := μ) (ν := ν) hA
  linarith

/-- The expectation gap of a measurable statistic confined to an interval of width `c` is at most
that width times the total-variation distance between the two probability laws.

This is the bounded-function side of the dual characterization of total variation, normalized
using the supremum over measurable events. -/
theorem tvDist_integral_range (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (a c : ℝ) (hc : 0 ≤ c)
    (hrange : ∀ x, f x ∈ Set.Icc a (a + c)) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν * c := by
  let g : Ω → ℝ := fun x => f x - a
  have hg : Measurable g := hf.sub_const a
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    dsimp [g]
    linarith [(hrange x).1]
  have hgc : ∀ x, g x ≤ c := fun x => by
    dsimp [g]
    linarith [(hrange x).2]
  have hgint (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable g ρ :=
    Integrable.of_bound hg.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
        exact hgc x)
  have htail_meas (ρ : Measure Ω) :
      Measurable (fun t : ℝ => ρ.real {x | t ≤ g x}) := by
    change Measurable fun t : ℝ => (ρ {x | t ≤ g x}).toReal
    exact Measurable.ennreal_toReal
      (Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => hst.trans hx)))
  have htail_int (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      IntegrableOn (fun t : ℝ => ρ.real {x | t ≤ g x}) (Set.Ioc 0 c) := by
    exact Integrable.of_bound
      ((htail_meas ρ).aestronglyMeasurable.mono_measure Measure.restrict_le_self) 1
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  have hlayer (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      ∫ x, g x ∂ρ = ∫ t in Set.Ioc 0 c, ρ.real {x | t ≤ g x} := by
    exact (hgint ρ).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hgc)
  have hfint (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable f ρ :=
    Integrable.of_bound hf.aestronglyMeasurable (|a| + c)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        calc
          |f x| = |a + g x| := by simp [g]
          _ ≤ |a| + |g x| := abs_add_le _ _
          _ ≤ |a| + c := by
            gcongr
            rw [abs_of_nonneg (hg0 x)]
            exact hgc x)
  have hshift (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      ∫ x, g x ∂ρ = (∫ x, f x ∂ρ) - a := by
    rw [show g = fun x => f x - a from rfl,
      integral_sub (hfint ρ) (integrable_const a)]
    simp
  have heq :
      (∫ x, f x ∂μ) - ∫ x, f x ∂ν =
        (∫ x, g x ∂μ) - ∫ x, g x ∂ν := by
    rw [hshift μ, hshift ν]
    ring
  rw [heq, hlayer μ, hlayer ν, ← integral_sub (htail_int μ) (htail_int ν)]
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 c),
      ‖μ.real {x | t ≤ g x} - ν.real {x | t ≤ g x}‖ ≤ tvDist μ ν := by
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact abs_measureReal_sub_le_tvDist (hg measurableSet_Ici)
  calc
    |∫ t in Set.Ioc 0 c, (μ.real {x | t ≤ g x} - ν.real {x | t ≤ g x})|
        = ‖∫ t in Set.Ioc 0 c,
            (μ.real {x | t ≤ g x} - ν.real {x | t ≤ g x})‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ tvDist μ ν * volume.real (Set.Ioc 0 c) :=
      norm_setIntegral_le_of_norm_le_const_ae (by simp) hbound
    _ = tvDist μ ν * c := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ c - 0)]
      ring

/-- A measurable statistic that lies almost surely in an interval of width `c` under both laws has
an expectation gap no larger than `c` times their total-variation distance.

The statistic may violate the range restriction on different null sets for the two probability
measures. -/
theorem tvDist_integral_le_of_range_ae (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (a c : ℝ) (hc : 0 ≤ c)
    (hμ : ∀ᵐ x ∂μ, f x ∈ Set.Icc a (a + c))
    (hν : ∀ᵐ x ∂ν, f x ∈ Set.Icc a (a + c)) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν * c := by
  let f' : Ω → ℝ := fun x => max a (min (a + c) (f x))
  have hf' : Measurable f' := measurable_const.max (measurable_const.min hf)
  have hac : a ≤ a + c := by linarith
  have hrange : ∀ x, f' x ∈ Set.Icc a (a + c) := fun x => by
    constructor
    · exact le_max_left _ _
    · exact max_le hac (min_le_left _ _)
  have hμ_eq : f' =ᵐ[μ] f := by
    filter_upwards [hμ] with x hx
    simp only [f', min_eq_right hx.2, max_eq_right hx.1]
  have hν_eq : f' =ᵐ[ν] f := by
    filter_upwards [hν] with x hx
    simp only [f', min_eq_right hx.2, max_eq_right hx.1]
  rw [← integral_congr_ae hμ_eq, ← integral_congr_ae hν_eq]
  exact tvDist_integral_range μ ν f' hf' a c hc hrange

/-- A measurable statistic bounded in absolute value by `M` almost surely under both laws has an
expectation gap no larger than `2M` times their total-variation distance.

The factor two is the width of the symmetric interval from `-M` to `M`. -/
theorem tvDist_integral_le_of_abs_le_ae (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hμ : ∀ᵐ x ∂μ, |f x| ≤ M) (hν : ∀ᵐ x ∂ν, |f x| ≤ M) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 2 * M * tvDist μ ν := by
  have hμ_range : ∀ᵐ x ∂μ, f x ∈ Set.Icc (-M) (-M + 2 * M) := by
    filter_upwards [hμ] with x hx
    have hx' := abs_le.mp hx
    constructor <;> linarith
  have hν_range : ∀ᵐ x ∂ν, f x ∈ Set.Icc (-M) (-M + 2 * M) := by
    filter_upwards [hν] with x hx
    have hx' := abs_le.mp hx
    constructor <;> linarith
  calc
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν * (2 * M) :=
      tvDist_integral_le_of_range_ae μ ν f hf (-M) (2 * M) (by positivity)
        hμ_range hν_range
    _ = 2 * M * tvDist μ ν := by ring

end Causalean.Stat


namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Given [two probability laws](hyp:mu,nu) and [a common Markov reconstruction
channel](hyp:K), applying that channel to both laws [cannot increase their total
variation distance](goal). -/
theorem tvDist_bind_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K] :
    tvDist (K ∘ₘ mu) (K ∘ₘ nu) ≤ tvDist mu nu := by
  let _ : IsProbabilityMeasure (K ∘ₘ mu) := by infer_instance
  let _ : IsProbabilityMeasure (K ∘ₘ nu) := by infer_instance
  unfold tvDist
  apply ciSup_le
  rintro ⟨S, hS⟩
  have hreal (rho : Measure A) [IsProbabilityMeasure rho] :
      (K ∘ₘ rho).real S = ∫ x, (K x S).toReal ∂rho := by
    rw [measureReal_def, Measure.bind_apply hS (Kernel.aemeasurable K), ←
      integral_toReal (K.measurable_coe hS).aemeasurable]
    filter_upwards with x
    exact measure_lt_top (K x) S
  rw [hreal mu, hreal nu]
  have hrange : ∀ x, (K x S).toReal ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle := ENNReal.toReal_mono (measure_ne_top (K x) _)
        (measure_mono (Set.subset_univ S))
      simpa using hle
  simpa only [zero_add, mul_one, tvDist] using
    tvDist_integral_range mu nu
      (fun x => (K x S).toReal) (K.measurable_coe hS).ennreal_toReal
      0 1 (by norm_num) (by simpa using hrange)

/-- For [two probability laws](hyp:mu,nu) and [a common Markov kernel](hyp:K),
the joint input-output laws obtained from that kernel have [exactly the same total
variation distance as the input laws](goal). -/
theorem tvDist_compProd_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K] :
    tvDist (mu ⊗ₘ K) (nu ⊗ₘ K) = tvDist mu nu := by
  have hjoint_le : tvDist (mu ⊗ₘ K) (nu ⊗ₘ K) ≤ tvDist mu nu := by
    unfold tvDist
    apply ciSup_le
    rintro ⟨T, hT⟩
    have hreal (rho : Measure A) [IsProbabilityMeasure rho] :
        (rho ⊗ₘ K).real T = ∫ x, (K x).real (Prod.mk x ⁻¹' T) ∂rho := by
      rw [measureReal_def, Measure.compProd_apply hT, ← integral_toReal]
      · rfl
      · exact (Kernel.measurable_kernel_prodMk_left hT).aemeasurable
      · filter_upwards with x
        exact measure_lt_top (K x) _
    rw [hreal mu, hreal nu]
    have hf : Measurable (fun x => (K x).real (Prod.mk x ⁻¹' T)) :=
      (Kernel.measurable_kernel_prodMk_left hT).ennreal_toReal
    have hrange : ∀ x, (K x).real (Prod.mk x ⁻¹' T) ∈ Set.Icc (0 : ℝ) (0 + 1) := by
      intro x
      exact ⟨measureReal_nonneg, by
        simpa using (measureReal_le_one (μ := K x) (s := Prod.mk x ⁻¹' T))⟩
    simpa only [mul_one, tvDist] using
      tvDist_integral_range mu nu _ hf 0 1 (by norm_num) hrange
  have hjoint_ge : tvDist mu nu ≤ tvDist (mu ⊗ₘ K) (nu ⊗ₘ K) := by
    unfold tvDist
    apply ciSup_le
    rintro ⟨S, hS⟩
    have hreal (rho : Measure A) [IsProbabilityMeasure rho] :
        (rho ⊗ₘ K).real (S ×ˢ (Set.univ : Set B)) = rho.real S := by
      simp [measureReal_def, Measure.compProd_apply_prod hS MeasurableSet.univ]
    rw [← hreal mu, ← hreal nu]
    exact abs_measureReal_sub_le_tvDist (hS.prod MeasurableSet.univ)
  exact le_antisymm hjoint_le hjoint_ge

/-- For [two probability laws](hyp:mu,nu) and [a common Markov kernel](hyp:K),
the output marginal distance is [at most the distance between their joint
input-output laws](goal). -/
theorem tvDist_bind_le_compProd
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K] :
    tvDist (K ∘ₘ mu) (K ∘ₘ nu) ≤ tvDist (mu ⊗ₘ K) (nu ⊗ₘ K) :=
  (tvDist_bind_le mu nu K).trans_eq (tvDist_compProd_eq mu nu K).symm

/-- For [two probability laws](hyp:mu,nu), [a common Markov kernel](hyp:K),
and [a measurable joint test](hyp:T,hT), the test's total error is [at least one
minus the input total variation distance](goal). -/
theorem one_sub_tvDist_le_compProd_test
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K]
    (T : Set (A × B)) (hT : MeasurableSet T) :
    1 - tvDist mu nu ≤ (mu ⊗ₘ K).real T + (nu ⊗ₘ K).real Tᶜ := by
  rw [← tvDist_compProd_eq mu nu K]
  exact one_sub_tvDist_le_test hT

/-- For [two probability laws](hyp:mu,nu), [a common Markov kernel](hyp:K),
and [a measurable output test](hyp:T,hT), the test's total error is [at least one
minus the input total variation distance](goal). -/
theorem one_sub_tvDist_le_bind_test
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K]
    (T : Set B) (hT : MeasurableSet T) :
    1 - tvDist mu nu ≤ (K ∘ₘ mu).real T + (K ∘ₘ nu).real Tᶜ := by
  exact (sub_le_sub_left (tvDist_bind_le mu nu K) 1).trans
    (one_sub_tvDist_le_test hT)

end Causalean.Stat


namespace Causalean.Stat

open MeasureTheory

/-- For a [probability measure on a countable measurable space with measurable
singletons](hyp:α,μ), the real masses of all singleton events sum to one. The result is [the unit-sum identity for real singleton masses](goal). -/
lemma probability_real_singleton_tsum {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    (∑' x : α, μ.real {x}) = 1 := by
  have h := MeasureTheory.Measure.tsum_indicator_apply_singleton μ
    (Set.univ : Set α) MeasurableSet.univ
  have htop : ∀ x : α, μ {x} ≠ ⊤ := fun x => measure_ne_top μ _
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.tsum_toReal_eq (fun x => by simp [htop x])] at hr
  simpa [Measure.real_def, probReal_univ] using hr


/-- For a [probability measure on a countable measurable space with measurable
singletons](hyp:α,μ) and a [measurable event](hyp:s,hs), the event's real mass
equals the sum of the real singleton masses it contains. The result is [the singleton-sum formula for the measurable event’s real mass](goal). -/
lemma probability_measureReal_eq_tsum_singletons {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Set α)
    (hs : MeasurableSet s) :
    μ.real s = ∑' x : α, s.indicator (fun x => μ.real {x}) x := by
  have h := MeasureTheory.Measure.tsum_indicator_apply_singleton μ s hs
  have htop : ∀ x : α,
      s.indicator (fun x => μ {x}) x ≠ ⊤ := by
    intro x
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx, measure_ne_top μ {x}]
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.tsum_toReal_eq htop] at hr
  rw [Measure.real_def, ← hr]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx, Measure.real_def]


/-- For [two probability measures on a countable measurable space with measurable
singletons](hyp:α,μ,ν), total variation is at most one half of the `ℓ¹`
distance between their real singleton masses. The result is [the half-`ℓ¹` upper bound on total variation](goal). -/
lemma tvDist_le_half_tsum_singleton_abs {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Causalean.Stat.tvDist μ ν ≤
      (1 / 2 : ℝ) * ∑' x : α, |μ.real {x} - ν.real {x}| := by
  let m : α → ℝ := fun x => μ.real {x}
  let v : α → ℝ := fun x => ν.real {x}
  let delta : α → ℝ := fun x => m x - v x
  have hm : Summable m := by
    apply ENNReal.summable_toReal
    have h := MeasureTheory.Measure.tsum_indicator_apply_singleton μ
      (Set.univ : Set α) MeasurableSet.univ
    simpa [m] using h.trans_ne (measure_ne_top μ Set.univ)
  have hv : Summable v := by
    apply ENNReal.summable_toReal
    have h := MeasureTheory.Measure.tsum_indicator_apply_singleton ν
      (Set.univ : Set α) MeasurableSet.univ
    simpa [v] using h.trans_ne (measure_ne_top ν Set.univ)
  have hdelta : Summable delta := by
    exact (hm.sub hv).congr fun x => by rfl
  have habs : Summable (fun x => |delta x|) := by
    simpa [Real.norm_eq_abs] using hdelta.norm
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨s, hs⟩
  have hmS := hm.indicator s
  have hvS := hv.indicator s
  have hmC := hm.indicator sᶜ
  have hvC := hv.indicator sᶜ
  have hdS : Summable (s.indicator delta) := hdelta.indicator s
  have hdC : Summable (sᶜ.indicator delta) := hdelta.indicator sᶜ
  have haS : Summable (s.indicator fun x => |delta x|) := habs.indicator s
  have haC : Summable (sᶜ.indicator fun x => |delta x|) := habs.indicator sᶜ
  have hgapS : μ.real s - ν.real s = ∑' x, s.indicator delta x := by
    rw [probability_measureReal_eq_tsum_singletons μ s hs,
      probability_measureReal_eq_tsum_singletons ν s hs,
      ← hmS.tsum_sub hvS]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ s <;> simp [m, v, delta, Set.indicator, hx]
  have hgapC : μ.real sᶜ - ν.real sᶜ =
      ∑' x, sᶜ.indicator delta x := by
    rw [probability_measureReal_eq_tsum_singletons μ sᶜ hs.compl,
      probability_measureReal_eq_tsum_singletons ν sᶜ hs.compl,
      ← hmC.tsum_sub hvC]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ sᶜ <;> simp [m, v, delta, Set.indicator, hx]
  have hcomp : μ.real sᶜ - ν.real sᶜ = -(μ.real s - ν.real s) := by
    rw [measureReal_compl hs, measureReal_compl hs, probReal_univ, probReal_univ]
    ring
  have hboundS : |μ.real s - ν.real s| ≤
      ∑' x, s.indicator (fun x => |delta x|) x := by
    rw [hgapS, ← Real.norm_eq_abs]
    have hnormS : Summable fun x => ‖s.indicator delta x‖ := by
      apply haS.congr
      intro x
      by_cases hx : x ∈ s <;> simp [Set.indicator, hx, Real.norm_eq_abs]
    calc
      ‖∑' x, s.indicator delta x‖ ≤
          ∑' x, ‖s.indicator delta x‖ :=
        norm_tsum_le_tsum_norm hnormS
      _ = ∑' x, s.indicator (fun x => |delta x|) x := by
        apply tsum_congr
        intro x
        by_cases hx : x ∈ s <;> simp [Set.indicator, hx, Real.norm_eq_abs]
  have hboundC : |μ.real s - ν.real s| ≤
      ∑' x, sᶜ.indicator (fun x => |delta x|) x := by
    rw [← abs_neg (μ.real s - ν.real s), ← hcomp, hgapC,
      ← Real.norm_eq_abs]
    have hnormC : Summable fun x => ‖sᶜ.indicator delta x‖ := by
      apply haC.congr
      intro x
      by_cases hx : x ∈ sᶜ <;> simp [Set.indicator, hx, Real.norm_eq_abs]
    calc
      ‖∑' x, sᶜ.indicator delta x‖ ≤
          ∑' x, ‖sᶜ.indicator delta x‖ :=
        norm_tsum_le_tsum_norm hnormC
      _ = ∑' x, sᶜ.indicator (fun x => |delta x|) x := by
        apply tsum_congr
        intro x
        by_cases hx : x ∈ sᶜ <;> simp [Set.indicator, hx, Real.norm_eq_abs]
  have hsplit :
      (∑' x, s.indicator (fun x => |delta x|) x) +
          (∑' x, sᶜ.indicator (fun x => |delta x|) x) =
        ∑' x, |delta x| := by
    rw [← haS.tsum_add haC]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  rw [show (1 / 2 : ℝ) * ∑' x, |μ.real {x} - ν.real {x}| =
      (1 / 2 : ℝ) * ∑' x, |delta x| by rfl]
  calc
    |μ.real s - ν.real s| ≤
        (1 / 2 : ℝ) *
          ((∑' x, s.indicator (fun x => |delta x|) x) +
            ∑' x, sᶜ.indicator (fun x => |delta x|) x) := by
      linarith
    _ = (1 / 2 : ℝ) * ∑' x, |delta x| := by rw [hsplit]

end Causalean.Stat
