/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Concentration.TailBounds.Bernstein
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Basic

/-!
# Concentration of kernel-weighted design moments in dimension one

For independent design points with a density at most `f_max` near the evaluation point and a
nonnegative kernel bounded by `K_max` and supported on `[−1, 1]`, each normalized empirical
moment `(N h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, `u_i = (X_i − x₀)/h`, is close to its expectation.

Each summand is bounded by `K_max` and has second moment at most `2 h f_max K_max²`, so
Bernstein's inequality gives `localPoly_moment_entrywise_bernstein`: a deviation larger than `t`
has probability at most `2 exp(−N h t² / (4 (2 f_max K_max² + K_max t)))`. A union bound over
the `(p+1)²` entries gives `localPoly_moment_simultaneous_probability`. Only upper bounds on the
density and the kernel are used.
-/

public section

namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration
open scoped BigOperators

/-- For [a measurable kernel `K` and an evaluation point `x₀`, as carried by a design](hyp:D),
[the map `x ↦ K(u) u^j u^k`, `u = (x − x₀)/h`, is measurable for every bandwidth `h` and
exponents `j`, `k`](goal). -/
@[fun_prop] theorem momentSummand_measurable (D : KernelDesign) (h : ℝ) (j k : ℕ) :
    Measurable (momentSummand D h j k) := by
  unfold momentSummand
  exact (D.kernel_measurable.comp ((measurable_id.sub_const D.center).div_const h)).mul
    ((((measurable_id.sub_const D.center).div_const h).pow_const j).mul
      (((measurable_id.sub_const D.center).div_const h).pow_const k))

/-- For [a nonnegative kernel `K` that is at most `K_max` and vanishes outside `[−1, 1]`, with
an evaluation point `x₀`](hyp:D), [`|K(u) u^j u^k| ≤ K_max` for every bandwidth, pair of
exponents and point `x`, where `u = (x − x₀)/h`](goal). -/
theorem momentSummand_abs_le (D : KernelDesign) (h : ℝ) (j k : ℕ) (x : ℝ) :
    |momentSummand D h j k x| ≤ D.kernelMax := by
  unfold momentSummand
  let u := (x - D.center) / h
  change |D.kernel u * (u ^ j * u ^ k)| ≤ D.kernelMax
  by_cases hu : |u| ≤ 1
  · rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (D.kernel_nonneg u)]
    have hj : |u| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
    have hk : |u| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
    calc
      D.kernel u * (|u| ^ j * |u| ^ k) ≤ D.kernel u * (1 * 1) := by
        gcongr
        exact D.kernel_nonneg u
      _ ≤ D.kernelMax := by simpa using D.kernel_upper u
  · rw [D.kernel_support u (lt_of_not_ge hu)]
    simpa using D.kernelMax_nonneg

/-- For [a design law with a measurable nonnegative kernel `K ≤ K_max` vanishing outside `[−1,
1]`](hyp:D), [the kernel-weighted monomial `K(u) u^j u^k`, `u = (X − x₀)/h`, has a finite
expectation under the design law for every bandwidth and pair of exponents](goal). -/
theorem momentSummand_integrable (D : KernelDesign) (h : ℝ) (j k : ℕ) :
    Integrable (momentSummand D h j k) D.law := by
  let _ := D.probability
  exact (integrable_const D.kernelMax).mono'
    (momentSummand_measurable D h j k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using momentSummand_abs_le D h j k x)

/-- Let [the design density be at most `f_max` on `[x₀ − r, x₀ + r]` and the kernel `K` be
measurable, nonnegative, at most `K_max` and zero outside `[−1, 1]`](hyp:D). For [a positive
bandwidth `h`](hyp:hh) [not exceeding `r`](hyp:hwindow), [the second moment `E[(K(u) u^j
u^k)²]`, `u = (X − x₀)/h`, is at most `2 h f_max K_max²` for all exponents `j`, `k`](goal). -/
theorem momentSummand_secondMoment (D : KernelDesign) {h : ℝ}
    (hh : 0 < h) (hwindow : h ≤ D.radius) (j k : ℕ) :
    (∫ x, momentSummand D h j k x ^ 2 ∂D.law)
      ≤ 2 * h * D.upper * D.kernelMax ^ 2 := by
  classical
  have hu : 0 ≤ D.upper := D.upper_nonneg
  let W := Set.Icc (D.center - h) (D.center + h)
  have hW : MeasurableSet W := measurableSet_Icc
  have hsq : ∀ x, momentSummand D h j k x ^ 2 ≤ D.kernelMax ^ 2 := by
    intro x
    have hb := momentSummand_abs_le D h j k x
    nlinarith [sq_abs (momentSummand D h j k x), abs_nonneg (momentSummand D h j k x)]
  have hout : ∀ x, x ∉ W → momentSummand D h j k x = 0 := by
    intro x hx
    have hx' : h < |x - D.center| := by
      by_contra hn
      have ha := abs_le.mp (le_of_not_gt hn)
      apply hx
      constructor <;> linarith [ha.1, ha.2]
    unfold momentSummand
    rw [D.kernel_support _ (by
      rw [abs_div, abs_of_pos hh]
      exact (lt_div_iff₀ hh).mpr (by simpa using hx'))]
    simp
  rw [D.law_density, integral_withDensity_eq_integral_toReal_smul
    D.density_measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (D.density_nonneg _), smul_eq_mul]
  calc
    (∫ x, D.density x * momentSummand D h j k x ^ 2) ≤
        ∫ x, W.indicator (fun _ => D.upper * D.kernelMax ^ 2) x := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x =>
          mul_nonneg (D.density_nonneg x) (sq_nonneg _)
      · exact (integrableOn_const
          (isCompact_Icc.measure_ne_top (μ := volume))).integrable_indicator hW
      · apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ W
        · rw [Set.indicator_of_mem hx]
          have hxrad : |x - D.center| ≤ D.radius := by
            apply le_trans _ hwindow
            apply abs_le.mpr
            have hx' : D.center - h ≤ x ∧ x ≤ D.center + h := hx
            constructor <;> linarith [hx'.1, hx'.2]
          exact mul_le_mul (D.density_upper x hxrad) (hsq x) (sq_nonneg _) hu
        · simp [Set.indicator_of_notMem hx, hout x hx]
    _ = 2 * h * D.upper * D.kernelMax ^ 2 := by
      rw [integral_indicator hW, setIntegral_const]
      simp [W, hh.le]
      ring

/-- For [a design law with a measurable nonnegative kernel `K ≤ K_max` vanishing outside `[−1,
1]`](hyp:D), [the kernel-weighted monomial `K(u) u^j u^k`, `u = (x − x₀)/h`, differs from
its expectation under the design law by at most `2 K_max` at every point `x`](goal). -/
theorem momentSummand_centered_bound (D : KernelDesign) (h : ℝ) (j k : ℕ) :
    ∀ x, |momentSummand D h j k x - ∫ y, momentSummand D h j k y ∂D.law|
      ≤ 2 * D.kernelMax := by
  let _ := D.probability
  have hm : |∫ y, momentSummand D h j k y ∂D.law| ≤ D.kernelMax := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := D.law)
        (f := momentSummand D h j k) (C := D.kernelMax)
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using momentSummand_abs_le D h j k y))
  intro x
  calc
    |momentSummand D h j k x - ∫ y, momentSummand D h j k y ∂D.law| ≤
        |momentSummand D h j k x| + |∫ y, momentSummand D h j k y ∂D.law| :=
      abs_sub _ _
    _ ≤ D.kernelMax + D.kernelMax := add_le_add (momentSummand_abs_le D h j k x) hm
    _ = 2 * D.kernelMax := by ring

/-- Let [the design density be at most `f_max` on `[x₀ − r, x₀ + r]` and the kernel `K` be
measurable, nonnegative, at most `K_max` and zero outside `[−1, 1]`](hyp:D). For [a positive
bandwidth `h`](hyp:hh) [not exceeding `r`](hyp:hwindow), [the variance of `K(u) u^j u^k`, `u
= (X − x₀)/h`, under the design law is at most `2 h f_max K_max²` for all exponents `j`,
`k`](goal). -/
theorem momentSummand_variance (D : KernelDesign) {h : ℝ}
    (hh : 0 < h) (hwindow : h ≤ D.radius) (j k : ℕ) :
    (∫ x, (momentSummand D h j k x - ∫ y, momentSummand D h j k y ∂D.law) ^ 2
      ∂D.law) ≤ 2 * h * D.upper * D.kernelMax ^ 2 := by
  let _ := D.probability
  rw [← ProbabilityTheory.variance_eq_integral
    (momentSummand_measurable D h j k).aemeasurable]
  exact (ProbabilityTheory.variance_le_expectation_sq
    (momentSummand_measurable D h j k).aestronglyMeasurable).trans
    (momentSummand_secondMoment D hh hwindow j k)

/-- **Bernstein bound for one kernel-weighted design moment, dimension one.** Let [the design
points `X_1, …, X_N` be independent draws from a density that is at most `f_max` on an
interval `[x₀ − r, x₀ + r]`, and let the kernel `K` be measurable, nonnegative, at most
`K_max`, and zero outside `[−1, 1]`](hyp:D). For [a polynomial degree `p`](hyp:p), [a
positive sample size `N`](hyp:hN), [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow), [a positive tolerance `t`](hyp:ht) and [any two exponents `j, k` between
`0` and `p`](hyp:j,k), write `u_i = (X_i − x₀)/h` and compare the empirical moment `(N h)⁻¹
∑_i K(u_i) u_i^(j+k)` with its expectation. Then [the probability that the two differ by
more than `t` is at most `2 exp(−N h t² / (4 (2 f_max K_max² + K_max t)))`](goal).

No lower bound on the density or on the kernel is used. -/
theorem localPoly_moment_entrywise_bernstein (D : KernelDesign) (p N : ℕ)
    {h t : ℝ} (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius) (ht : 0 < t)
    (j k : Fin (p + 1)) :
    (Measure.pi (fun _ : Fin N => D.law)).real
      {x | t < |empiricalMoment D p h x j k - populationMoment D p h j k|}
      ≤ 2 * Real.exp (-(N : ℝ) * h * tailExponent D t) := by
  let _ := D.probability
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hK0 := D.kernelMax_nonneg
  by_cases hKz : D.kernelMax = 0
  · have hz : ∀ x, momentSummand D h j k x = 0 := fun x =>
      abs_eq_zero.mp (le_antisymm (hKz ▸ momentSummand_abs_le D h j k x) (abs_nonneg _))
    have hempty : {x : Fin N → ℝ |
        t < |empiricalMoment D p h x j k - populationMoment D p h j k|} = ∅ := by
      ext x
      simp [empiricalMoment, populationMoment, hz, ht.le]
    rw [hempty, measureReal_empty]
    positivity
  have hK : 0 < D.kernelMax := lt_of_le_of_ne hK0 (Ne.symm hKz)
  have hu : 0 ≤ D.upper := D.upper_nonneg
  have htail := iid_sum_bernstein_union_bound (N := N) D.law
    (fun _ : Unit => momentSummand D h j k)
    (fun _ => momentSummand_measurable D h j k)
    (fun _ => momentSummand_integrable D h j k)
    (fun _ => 2 * D.kernelMax)
    (fun _ => 2 * h * D.upper * D.kernelMax ^ 2)
    (fun _ => (N : ℝ) * h * t)
    (fun _ => by positivity) (fun _ => by positivity) (fun _ => by positivity) hN
    (fun _ => Filter.Eventually.of_forall (momentSummand_centered_bound D h j k))
    (fun _ => momentSummand_variance D hh hwindow j k)
  simp only [Finset.univ_unique, Finset.sum_singleton] at htail
  have hsub : {x : Fin N → ℝ |
      t < |empiricalMoment D p h x j k - populationMoment D p h j k|} ⊆
      {x : Fin N → ℝ | ∃ _ : Unit, (N : ℝ) * h * t ≤
        |(∑ i, momentSummand D h j k (x i)) -
          (N : ℝ) * ∫ y, momentSummand D h j k y ∂D.law|} := by
    intro x hx
    refine ⟨(), ?_⟩
    have heq : empiricalMoment D p h x j k - populationMoment D p h j k =
        ((∑ i, momentSummand D h j k (x i)) -
          (N : ℝ) * ∫ y, momentSummand D h j k y ∂D.law) / ((N : ℝ) * h) := by
      unfold empiricalMoment populationMoment
      field_simp
    change t < |empiricalMoment D p h x j k - populationMoment D p h j k| at hx
    rw [heq, abs_div, abs_of_pos (mul_pos hn hh)] at hx
    have := (lt_div_iff₀ (mul_pos hn hh)).mp hx
    exact le_of_lt (by simpa [mul_comm, mul_left_comm, mul_assoc] using this)
  refine (measureReal_mono hsub).trans (htail.trans (le_of_eq ?_))
  congr 2
  unfold tailExponent
  field_simp
  ring

/-- For [a design law with a measurable kernel](hyp:D), [the set of design vectors `(x_1, …,
x_N)` on which every empirical kernel moment of order up to `2p` is within `t` of its
expectation is measurable, for every degree `p`, sample size `N`, bandwidth `h` and
tolerance `t`](goal). -/
theorem momentEvent_measurable (D : KernelDesign) (p N : ℕ) (h t : ℝ) :
    MeasurableSet (momentEvent D p h N t) := by
  classical
  unfold momentEvent
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le _ measurable_const
  apply Measurable.abs
  apply Measurable.sub_const
  unfold empiricalMoment
  exact (Finset.measurable_sum _ (fun i _ =>
    (momentSummand_measurable D h j k).comp (measurable_pi_apply i))).div_const _

/-- **All kernel-weighted design moments are close at once, dimension one.** Let [the design
points `X_1, …, X_N` be independent draws from a density that is at most `f_max` on an
interval `[x₀ − r, x₀ + r]`, and let the kernel `K` be measurable, nonnegative, at most
`K_max`, and zero outside `[−1, 1]`](hyp:D). For [a polynomial degree `p`](hyp:p), [a
positive sample size `N`](hyp:hN), [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow) and [a positive tolerance `t`](hyp:ht), consider the `(p+1) × (p+1)`
matrix of empirical moments `(N h)⁻¹ ∑_i K(u_i) u_i^(j+k)`, `u_i = (X_i − x₀)/h`. Then [the
probability that some entry differs from its expectation by more than `t` is at most `2
(p+1)² exp(−N h t² / (4 (2 f_max K_max² + K_max t)))`](goal).

This is the union bound over the `(p+1)²` entries of the entrywise Bernstein bound. No lower
bound on the density or on the kernel is used. -/
theorem localPoly_moment_simultaneous_probability (D : KernelDesign) (p N : ℕ)
    {h t : ℝ} (hN : 0 < N) (hh : 0 < h) (hwindow : h ≤ D.radius) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin N => D.law)).real (momentEvent D p h N t)ᶜ
      ≤ failureBound D p N h t := by
  classical
  let _ := D.probability
  let E : Fin (p + 1) × Fin (p + 1) → Set (Fin N → ℝ) := fun a =>
    {x | t < |empiricalMoment D p h x a.1 a.2 - populationMoment D p h a.1 a.2|}
  have heq : (momentEvent D p h N t)ᶜ = ⋃ a, E a := by
    ext x
    simp [momentEvent, E, not_forall, not_le, Prod.exists]
  rw [heq]
  calc
    (Measure.pi (fun _ : Fin N => D.law)).real (⋃ a, E a) ≤
        ∑ a, (Measure.pi (fun _ : Fin N => D.law)).real (E a) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _a : Fin (p + 1) × Fin (p + 1),
        2 * Real.exp (-(N : ℝ) * h * tailExponent D t) := by
      apply Finset.sum_le_sum
      intro a _
      exact localPoly_moment_entrywise_bernstein D p N hN hh hwindow ht a.1 a.2
    _ = failureBound D p N h t := by
      simp [failureBound, Fintype.card_prod, pow_two]
      ring

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate
