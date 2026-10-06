module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# Integrability and integration on a Poisson count fibre

These lemmas isolate the fixed-count step in capped-prefix mixtures. A
positive Poisson count mass transports integrability to the corresponding
finite iid prefix. The weighted identity also covers zero-mass fibres.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- For [an iid observation law](hyp:ν), [a Poisson mean](hyp:lam),
[a sample size](hyp:n), [a count that fits in the sample](hyp:m,h), [an integrable finite-sample
statistic](hyp:g,hg), and [positive mass at that count](hyp:hmass),
[the statistic of the fixed-count iid prefix is integrable](goal). -/
theorem integrable_prefix_of_nonzero_poisson_count
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0)
    (n m : ℕ) (h : m ≤ n) (g : FiniteSample Y → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw ν lam))
    (hmass : poissonMeasure lam {m} ≠ 0) :
    Integrable (fun y : Fin n → Y => g (prefixOfLE y m h))
      (Measure.pi (fun _ : Fin n => ν)) := by
  /- Restrict `hg` to the count-m fibre, rewrite with
  `finitePoissonSampleLaw_restrict_count_eq`, cancel the nonzero finite
  Poisson scalar using `integrable_smul_measure`, then transport the
  map-integrability across `fixedSizeEmbed` and `map_prefixCoordinates_pi`. -/
  classical
  have hfixed : Integrable g
      (Measure.map (fixedSizeEmbed m) (Measure.pi (fun _ : Fin m => ν))) := by
    have hr := hg.restrict (s := FiniteSample.count ⁻¹' ({m} : Set ℕ))
    rw [finitePoissonSampleLaw_restrict_count_eq ν lam m] at hr
    exact (integrable_smul_measure hmass (measure_ne_top _ _)).mp hr
  have hsmall : Integrable (g ∘ fixedSizeEmbed m)
      (Measure.pi (fun _ : Fin m => ν)) :=
    (integrable_map_measure hfixed.aestronglyMeasurable
      (measurable_fixedSizeEmbed m).aemeasurable).mp hfixed
  let f : (Fin n → Y) → (Fin m → Y) :=
    fun x i => x ⟨i, lt_of_lt_of_le i.isLt h⟩
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hmap : Measure.map f (Measure.pi (fun _ : Fin n => ν)) =
      Measure.pi (fun _ : Fin m => ν) := by
    symm
    refine Measure.pi_eq (μ := fun _ : Fin m => ν) (fun s hs => ?_)
    rw [Measure.map_apply hf (.univ_pi hs)]
    have hpre : f ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun j : Fin n =>
          if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hx j
        split
        · exact hx ⟨j.val, ‹j.val < m›⟩
        · trivial
      · intro hx i
        simpa [f] using hx ⟨i.val, lt_of_lt_of_le i.isLt h⟩
    rw [hpre, Measure.pi_pi]
    let t : Finset (Fin n) := Finset.univ.filter fun j => j.val < m
    have ht (j : t) : j.val.val < m := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
    let e : Fin m ≃ t :=
      { toFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt h⟩, by simp [t, i.isLt]⟩
        invFun := fun j => ⟨j.val.val, ht j⟩
        left_inv := fun i => by rfl
        right_inv := fun j => by ext; rfl }
    calc
      (∏ j : Fin n, ν (if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ)) =
          ∏ j : Fin n, if hj : j.val < m then ν (s ⟨j.val, hj⟩) else 1 := by
            apply Fintype.prod_congr
            intro j
            split <;> simp
      _ = ∏ j : t, ν (s ⟨j.val.val, ht j⟩) := by
        rw [Finset.prod_dite]
        simp only [Finset.prod_const_one, mul_one]
        apply Fintype.prod_congr
        intro j
        congr 2
      _ = ∏ i : Fin m, ν (s i) := by
        symm
        apply Fintype.prod_equiv e
        intro i
        rfl
  have hlarge : Integrable ((g ∘ fixedSizeEmbed m) ∘ f)
      (Measure.pi (fun _ : Fin n => ν)) := by
    apply (integrable_map_measure (by rw [hmap]; exact hsmall.aestronglyMeasurable)
      hf.aemeasurable).mp
    rwa [hmap]
  simpa [Function.comp_def, f, prefixOfLE, fixedSizeEmbed] using hlarge

/-- For [an iid observation law](hyp:ν), [a Poisson mean](hyp:lam), [a count](hyp:m),
[a finite-sample statistic](hyp:g), and [zero mass at that count](hyp:hmass),
[integrating the statistic over that count fibre gives zero](goal). -/
theorem poisson_prefix_count_fibre_integral_of_zero
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0)
    (m : ℕ) (g : FiniteSample Y → ℝ)
    (hmass : poissonMeasure lam {m} = 0) :
    ∫ z : FiniteSample Y in FiniteSample.count ⁻¹' ({m} : Set ℕ),
      g z ∂finitePoissonSampleLaw ν lam = 0 := by
  /- The count restriction is a zero scalar multiple of its iid fibre law. -/
  rw [finitePoissonSampleLaw_restrict_count_eq ν lam m, hmass]
  simp

/-- For [an iid observation law](hyp:ν), [a Poisson mean](hyp:lam), [a sample size](hyp:n),
[a count that fits in the sample](hyp:m,h), [an integrable finite-sample statistic](hyp:g,hg),
and [positive mass at that count](hyp:hmass), [the restricted integral is that mass times
the iid fixed-prefix integral](goal). -/
theorem poisson_prefix_count_fibre_integral_of_nonzero
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0)
    (n m : ℕ) (h : m ≤ n) (g : FiniteSample Y → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw ν lam))
    (hmass : poissonMeasure lam {m} ≠ 0) :
    ∫ z : FiniteSample Y in FiniteSample.count ⁻¹' ({m} : Set ℕ),
      g z ∂finitePoissonSampleLaw ν lam =
    (poissonMeasure lam {m}).toReal *
      ∫ y : Fin n → Y, g (prefixOfLE y m h)
        ∂Measure.pi (fun _ : Fin n => ν) := by
  /- Rewrite the count restriction as a scalar times `map fixedSizeEmbed`.
  `integrable_prefix_of_nonzero_poisson_count` supplies fixed-prefix
  integrability. Transport the integral through `fixedSizeEmbed`, then show
  the first `m` coordinates of the `Fin n` iid law have the `Fin m` iid law.
  The latter calculation already appears as `hmap` in that theorem's proof. -/
  classical
  have hfixed : Integrable g
      (Measure.map (fixedSizeEmbed m) (Measure.pi (fun _ : Fin m => ν))) := by
    have hr := hg.restrict (s := FiniteSample.count ⁻¹' ({m} : Set ℕ))
    rw [finitePoissonSampleLaw_restrict_count_eq ν lam m] at hr
    exact (integrable_smul_measure hmass (measure_ne_top _ _)).mp hr
  have hsmall : Integrable (g ∘ fixedSizeEmbed m)
      (Measure.pi (fun _ : Fin m => ν)) :=
    (integrable_map_measure hfixed.aestronglyMeasurable
      (measurable_fixedSizeEmbed m).aemeasurable).mp hfixed
  let f : (Fin n → Y) → (Fin m → Y) :=
    fun x i => x ⟨i, lt_of_lt_of_le i.isLt h⟩
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hmap : Measure.map f (Measure.pi (fun _ : Fin n => ν)) =
      Measure.pi (fun _ : Fin m => ν) := by
    symm
    refine Measure.pi_eq (μ := fun _ : Fin m => ν) (fun s hs => ?_)
    rw [Measure.map_apply hf (.univ_pi hs)]
    have hpre : f ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun j : Fin n =>
          if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hx j
        split
        · exact hx ⟨j.val, ‹j.val < m›⟩
        · trivial
      · intro hx i
        simpa [f] using hx ⟨i.val, lt_of_lt_of_le i.isLt h⟩
    rw [hpre, Measure.pi_pi]
    let t : Finset (Fin n) := Finset.univ.filter fun j => j.val < m
    have ht (j : t) : j.val.val < m := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
    let e : Fin m ≃ t :=
      { toFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt h⟩, by simp [t, i.isLt]⟩
        invFun := fun j => ⟨j.val.val, ht j⟩
        left_inv := fun i => by rfl
        right_inv := fun j => by ext; rfl }
    calc
      (∏ j : Fin n, ν (if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ)) =
          ∏ j : Fin n, if hj : j.val < m then ν (s ⟨j.val, hj⟩) else 1 := by
            apply Fintype.prod_congr
            intro j
            split <;> simp
      _ = ∏ j : t, ν (s ⟨j.val.val, ht j⟩) := by
        rw [Finset.prod_dite]
        simp only [Finset.prod_const_one, mul_one]
        apply Fintype.prod_congr
        intro j
        congr 2
      _ = ∏ i : Fin m, ν (s i) := by
        symm
        apply Fintype.prod_equiv e
        intro i
        rfl
  have htransport :
      ∫ z : FiniteSample Y, g z
        ∂Measure.map (fixedSizeEmbed m) (Measure.pi (fun _ : Fin m => ν)) =
      ∫ y : Fin n → Y, g (prefixOfLE y m h)
        ∂Measure.pi (fun _ : Fin n => ν) := by
    rw [integral_map (measurable_fixedSizeEmbed m).aemeasurable
      hfixed.aestronglyMeasurable]
    have hcoordinate := integral_map (μ := Measure.pi (fun _ : Fin n => ν))
      hf.aemeasurable (by rw [hmap]; exact hsmall.aestronglyMeasurable)
      (f := g ∘ fixedSizeEmbed m)
    rw [hmap] at hcoordinate
    simpa [Function.comp_def, f, prefixOfLE, fixedSizeEmbed] using hcoordinate
  rw [finitePoissonSampleLaw_restrict_count_eq ν lam m,
    integral_smul_measure, smul_eq_mul, htransport]

/-- For [an iid observation law](hyp:ν), [a Poisson mean](hyp:lam), [a sample size](hyp:n),
[a count that fits in the sample](hyp:m,h), and [an integrable finite-sample
statistic](hyp:g,hg), [the count-fibre integral equals the Poisson atom
times the iid prefix integral](goal), including a zero-mass atom. -/
theorem poisson_prefix_count_fibre_integral
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0)
    (n m : ℕ) (h : m ≤ n) (g : FiniteSample Y → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw ν lam)) :
    ∫ z : FiniteSample Y in FiniteSample.count ⁻¹' ({m} : Set ℕ),
      g z ∂finitePoissonSampleLaw ν lam =
    (poissonMeasure lam {m}).toReal *
      ∫ y : Fin n → Y, g (prefixOfLE y m h)
        ∂Measure.pi (fun _ : Fin n => ν) := by
  /- If the Poisson atom is zero, both sides vanish. Otherwise apply
  `poisson_prefix_count_fibre_integral_of_nonzero`. -/
  by_cases hmass : poissonMeasure lam {m} = 0
  · rw [poisson_prefix_count_fibre_integral_of_zero ν lam m g hmass, hmass]
    simp
  · exact poisson_prefix_count_fibre_integral_of_nonzero ν lam n m h g hg hmass

end Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
