/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Factorization
public import Causalean.Stat.Nonparametric.LocalPoly.GramCoercivity
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Basic

/-!
# Population moment matrices of one-dimensional local-polynomial regression

The population counterpart of the normalized empirical moment matrix is, after the change of
variables `x = x₀ + h u`, the matrix `T` with entries `∫ K(u) f(x₀ + h u) u^(j+k) du`
(`populationMoment_eq_shape`). Under density bounds `f_min ≤ f ≤ f_max` on the window and a
kernel bounded below by `K_min` on `[−Δ, Δ]`, the quadratic form of `T` dominates `f_min K_min`
times that of the monomial moment matrix on `[−Δ, Δ]`, which is positive definite because a
nonzero polynomial cannot vanish on an interval. Hence `T` and the kernel moment matrix are
positive definite (`shapeMoment_posDef`, `kernelMoment_posDef`), and every row of `T⁻¹` has
absolute sum at most an explicit constant that does not depend on the bandwidth
(`shape_inverse_rows`).

`designTolerance_spec` records that the explicit tolerance is small enough for the deterministic
inverse-perturbation bounds. Continuity of the kernel is not assumed.
-/

public section

namespace Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate

open Matrix MeasureTheory Causalean.Stat.Nonparametric
open scoped BigOperators

/-- **Change of variables for the population moments.** Let [the design law have a density `f`,
and let `K` be the kernel and `x₀` the evaluation point](hyp:D). For [a positive bandwidth
`h`](hyp:hh), [`E[K(u) u^(j+k)] / h = ∫ K(v) f(x₀ + h v) v^(j+k) dv` for all `0 ≤ j, k ≤ p`,
where `u = (X − x₀)/h`](goal). -/
theorem populationMoment_eq_shape (D : KernelDesign) (p : ℕ) {h : ℝ}
    (hh : 0 < h) :
    populationMoment D p h =
      weightMomentMatrix p (fun u => D.kernel u * D.density (D.center + h * u)) := by
  ext j k
  change (∫ x, momentSummand D h j k x ∂D.law) / h =
    ∫ u, (D.kernel u * D.density (D.center + h * u)) *
      (u ^ (j : ℕ) * u ^ (k : ℕ))
  have hdensity : (∫ x, momentSummand D h j k x ∂D.law) =
      ∫ x, D.density x * momentSummand D h j k x := by
    rw [D.law_density]
    simpa only [ENNReal.toReal_ofReal (D.density_nonneg _),
      smul_eq_mul] using
      integral_withDensity_eq_integral_toReal_smul (μ := volume)
        D.density_measurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))
        (momentSummand D h j k)
  have hcv : (∫ x, D.density x * momentSummand D h j k x) =
      h * ∫ u, (D.kernel u * D.density (D.center + h * u)) *
        (u ^ (j : ℕ) * u ^ (k : ℕ)) := by
    calc
      (∫ x, D.density x * momentSummand D h j k x) =
          ∫ x, (fun u => D.kernel u * (u ^ (j : ℕ) * u ^ (k : ℕ)))
            ((x - D.center) / h) * (x - D.center) ^ 0 * D.density x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by simp only [momentSummand, pow_zero]; ring)
      _ = h ^ (0 + 1) * ∫ u,
          (D.kernel u * (u ^ (j : ℕ) * u ^ (k : ℕ))) * u ^ 0 *
            D.density (D.center + h * u) :=
        popMomentEntry_changeOfVar
          (fun u => D.kernel u * (u ^ (j : ℕ) * u ^ (k : ℕ)))
          D.density D.center h hh 0
      _ = h * ∫ u, (D.kernel u * D.density (D.center + h * u)) *
          (u ^ (j : ℕ) * u ^ (k : ℕ)) := by
        simp only [Nat.zero_add, pow_one, pow_zero, mul_one]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by ring)
  rw [hdensity, hcv]
  field_simp

/-- Monomial products are integrable over the compact interval on which the kernel is bounded
below. -/
private lemma reference_moments_integrable (D : InteriorDesign) (p : ℕ) :
    ∀ j k : Fin (p + 1), Integrable (fun u =>
      (Set.Icc (-D.subradius) D.subradius).indicator (fun _ => (1 : ℝ)) u *
        (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
  intro j k
  have hc : Continuous (fun u : ℝ => u ^ (j : ℕ) * u ^ (k : ℕ)) := by fun_prop
  have hi := (integrable_indicator_iff measurableSet_Icc).2
    (hc.integrableOn_Icc (a := -D.subradius) (b := D.subradius) (μ := volume))
  have he : (fun u => (Set.Icc (-D.subradius) D.subradius).indicator
      (fun _ => (1 : ℝ)) u * (u ^ (j : ℕ) * u ^ (k : ℕ))) =
      (Set.Icc (-D.subradius) D.subradius).indicator
        (fun u => u ^ (j : ℕ) * u ^ (k : ℕ)) := by
    funext u
    by_cases hu : u ∈ Set.Icc (-D.subradius) D.subradius <;> simp [hu]
  rw [he]
  exact hi

/-- A measurable weight function that is bounded on `[−1, 1]` and vanishes outside it has finite
monomial moments of every order. -/
private lemma unit_moments_integrable {W : ℝ → ℝ} {C : ℝ}
    (hW : Measurable W) (hbound : ∀ u, |u| ≤ 1 → ‖W u‖ ≤ C)
    (hsupport : ∀ u, 1 < |u| → W u = 0) (p : ℕ) :
    ∀ j k : Fin (p + 1), Integrable (fun u => W u * (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
  intro j k
  let f : ℝ → ℝ := fun u => W u * (u ^ (j : ℕ) * u ^ (k : ℕ))
  have hm : Measurable f := hW.mul ((measurable_id.pow_const _).mul (measurable_id.pow_const _))
  have hi : IntegrableOn f (Set.Icc (-1 : ℝ) 1) := by
    apply Measure.integrableOn_of_bounded (M := C)
      isCompact_Icc.measure_ne_top hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have huabs : |u| ≤ 1 := abs_le.mpr hu
    have hj : ‖u ^ (j : ℕ)‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using pow_le_one₀ (n := (j : ℕ)) (abs_nonneg u) huabs
    have hk : ‖u ^ (k : ℕ)‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using pow_le_one₀ (n := (k : ℕ)) (abs_nonneg u) huabs
    calc
      ‖f u‖ = ‖W u‖ * (‖u ^ (j : ℕ)‖ * ‖u ^ (k : ℕ)‖) := by simp [f, norm_mul]
      _ ≤ C * (1 * 1) := mul_le_mul (hbound u huabs)
        (mul_le_mul hj hk (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        ((norm_nonneg (W u)).trans (hbound u huabs))
      _ = C := by ring
  have he : (Set.Icc (-1 : ℝ) 1).indicator f = f := by
    funext u
    by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1
    · simp [hu]
    · have hzero := hsupport u (lt_of_not_ge (by simpa [abs_le] using hu))
      simp [hu, f, hzero]
  change Integrable f
  rw [← he]
  exact (integrable_indicator_iff measurableSet_Icc).2 hi

/-- For [a kernel bounded below on an interval `[−Δ, Δ]` with `Δ > 0`, as carried by a
design](hyp:D), [the matrix with `(j,k)` entry `∫_{−Δ}^{Δ} u^(j+k) du`, `0 ≤ j, k ≤ p`, is
positive definite for every degree `p`](goal).

A nonzero polynomial cannot vanish on an interval of positive length. -/
theorem referenceMoment_posDef (D : InteriorDesign) (p : ℕ) :
    (referenceMoment D p).PosDef := by
  classical
  change (weightMomentMatrix p ((Set.Icc (-D.subradius) D.subradius).indicator
    (fun _ => (1 : ℝ)))).PosDef
  apply Matrix.PosDef.of_dotProduct_mulVec_pos weightMomentMatrix_isHermitian
  intro v hv
  simp only [star_trivial]
  rw [weightMomentMatrix_quadForm (reference_moments_integrable D p) v]
  let f : ℝ → ℝ := fun u => (∑ i, v i * u ^ (i : ℕ)) ^ 2
  have hc : Continuous f := by fun_prop
  have he : (fun u => (Set.Icc (-D.subradius) D.subradius).indicator
      (fun _ => (1 : ℝ)) u * (∑ i, v i * u ^ (i : ℕ)) ^ 2) =
      (Set.Icc (-D.subradius) D.subradius).indicator f := by
    funext u
    by_cases hu : u ∈ Set.Icc (-D.subradius) D.subradius <;> simp [hu, f]
  rw [he, integral_indicator measurableSet_Icc]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hc.integrableOn_Icc).2
  have hpoly : LocalPolynomial.localPolynomial p v ≠ 0 := by
    simpa [LocalPolynomial.localPolynomial_eq_zero_iff] using hv
  have hroots : Set.Finite {u : ℝ | Polynomial.IsRoot
      (LocalPolynomial.localPolynomial p v) u} :=
    (Polynomial.roots (LocalPolynomial.localPolynomial p v)).toFinset.finite_toSet.subset (by
      intro u hu
      simpa [Polynomial.mem_roots hpoly] using hu)
  have hinterval : Set.Infinite (Set.Ioo (-D.subradius) D.subradius) :=
    Set.Ioo_infinite (by linarith [D.subradius_pos])
  obtain ⟨u, hu, hroot⟩ := (hinterval.sdiff hroots).nonempty
  have hne : (∑ i, v i * u ^ (i : ℕ)) ≠ 0 := by
    rw [← LocalPolynomial.localPolynomial_eval]
    intro hz
    exact hroot (by simpa [Polynomial.IsRoot] using hz)
  have hopen : IsOpen (Function.support f ∩ Set.Ioo (-D.subradius) D.subradius) :=
    hc.isOpen_support.inter isOpen_Ioo
  have hnonempty : (Function.support f ∩ Set.Ioo (-D.subradius) D.subradius).Nonempty :=
    ⟨u, pow_ne_zero 2 hne, hu⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume hnonempty) (measure_mono (by
    intro x hx
    exact ⟨hx.1, hx.2.1.le, hx.2.2.le⟩))

/-- For [a measurable nonnegative kernel `K` that is at most `K_max` and vanishes outside `[−1,
1]`, as carried by a design](hyp:D), [`u ↦ K(u) u^j u^k` is integrable for all `0 ≤ j, k ≤
p`](goal). -/
theorem kernel_moments_integrable (D : KernelDesign) (p : ℕ) :
    ∀ j k : Fin (p + 1),
      Integrable (fun u => D.kernel u * (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
  apply unit_moments_integrable (C := D.kernelMax) D.kernel_measurable _ D.kernel_support p
  intro u hu
  simpa [Real.norm_eq_abs, abs_of_nonneg (D.kernel_nonneg u)] using D.kernel_upper u

/-- Let [the design density `f` be measurable and at most `f_max` on `[x₀ − r, x₀ + r]`, and the
kernel `K` be measurable, nonnegative, at most `K_max` and zero outside `[−1, 1]`](hyp:D).
For [a positive bandwidth `h`](hyp:hh) [not exceeding `r`](hyp:hwindow), [`v ↦ K(v) f(x₀ + h
v) v^j v^k` is integrable for all `0 ≤ j, k ≤ p`](goal). -/
theorem shape_moments_integrable (D : KernelDesign) (p : ℕ) {h : ℝ}
    (hh : 0 < h) (hwindow : h ≤ D.radius) :
    ∀ j k : Fin (p + 1), Integrable (fun u =>
      (D.kernel u * D.density (D.center + h * u)) * (u ^ (j : ℕ) * u ^ (k : ℕ))) := by
  apply unit_moments_integrable (C := D.kernelMax * D.upper)
    (D.kernel_measurable.mul (D.density_measurable.comp
      (measurable_const.add (measurable_const.mul measurable_id)))) _ _ p
  · intro u hu
    change ‖D.kernel u * D.density (D.center + h * u)‖ ≤ D.kernelMax * D.upper
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (D.kernel_nonneg u)
      (D.density_nonneg _))]
    exact (kernelDensity_upper_dom hh D.kernel_nonneg D.kernel_support
      (fun a ha => D.density_upper a (ha.trans hwindow)) u).trans
      ((mul_comm _ _).le.trans (mul_le_mul_of_nonneg_right (D.kernel_upper u)
        D.upper_nonneg))
  · intro u hu
    simp [D.kernel_support u hu]

/-- For [a measurable nonnegative bounded kernel `K` that vanishes outside `[−1, 1]` and is at
least `K_min > 0` on `[−Δ, Δ]`, as carried by a design](hyp:D), [the kernel moment matrix
with `(j,k)` entry `∫ K(u) u^(j+k) du`, `0 ≤ j, k ≤ p`, is positive definite for every
degree `p`](goal). -/
theorem kernelMoment_posDef (D : InteriorDesign) (p : ℕ) :
    (weightMomentMatrix p D.kernel).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos weightMomentMatrix_isHermitian
  intro v hv
  simp only [star_trivial]
  have href : 0 < v ⬝ᵥ (referenceMoment D p *ᵥ v) := by
    simpa only [star_trivial] using (referenceMoment_posDef D p).dotProduct_mulVec_pos hv
  apply lt_of_lt_of_le (mul_pos D.kernelMin_pos href)
  apply weightMomentMatrix_quadForm_sandwich D.kernelMin_pos.le
    (kernel_moments_integrable D p) (reference_moments_integrable D p)
  intro u
  by_cases hu : u ∈ Set.Icc (-D.subradius) D.subradius
  · simpa [hu] using D.kernel_lower u (abs_le.mpr hu)
  · simpa [hu] using D.kernel_nonneg u

/-- Let [the design density `f` lie between `f_min > 0` and `f_max` on `[x₀ − r, x₀ + r]`, and
the kernel `K` be measurable, nonnegative, bounded, zero outside `[−1, 1]` and at least
`K_min > 0` on `[−Δ, Δ]`](hyp:D). For [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow), [every vector `v` satisfies `f_min K_min · vᵀ R v ≤ vᵀ T v`, where `T`
has `(j,k)` entry `∫ K(u) f(x₀ + h u) u^(j+k) du` and `R` has `(j,k)` entry `∫_{−Δ}^{Δ}
u^(j+k) du`](goal). -/
theorem shape_dominates_reference (D : InteriorDesign) (p : ℕ) {h : ℝ}
    (hh : 0 < h) (hwindow : h ≤ D.radius) :
    ∀ v : Fin (p + 1) → ℝ,
      (D.lower * D.kernelMin) * (v ⬝ᵥ (referenceMoment D p *ᵥ v)) ≤
        v ⬝ᵥ (weightMomentMatrix p
          (fun u => D.kernel u * D.density (D.center + h * u)) *ᵥ v) := by
  apply weightMomentMatrix_quadForm_sandwich
    (mul_pos D.lower_pos D.kernelMin_pos).le
    (shape_moments_integrable D p hh hwindow) (reference_moments_integrable D p)
  intro u
  have hdom := kernelDensity_lower_dom hh D.kernel_nonneg D.kernel_support
    (fun a ha => D.density_lower a (ha.trans hwindow)) u
  refine le_trans ?_ hdom
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ D.lower_pos.le
  by_cases hu : u ∈ Set.Icc (-D.subradius) D.subradius
  · simpa [hu] using D.kernel_lower u (abs_le.mpr hu)
  · simpa [hu] using D.kernel_nonneg u

/-- Let [the design density `f` lie between `f_min > 0` and `f_max` on `[x₀ − r, x₀ + r]`, and
the kernel `K` be measurable, nonnegative, bounded, zero outside `[−1, 1]` and at least
`K_min > 0` on `[−Δ, Δ]`](hyp:D). For [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow), [the population moment matrix with `(j,k)` entry `∫ K(u) f(x₀ + h u)
u^(j+k) du`, `0 ≤ j, k ≤ p`, is positive definite](goal). -/
theorem shapeMoment_posDef (D : InteriorDesign) (p : ℕ) {h : ℝ}
    (hh : 0 < h) (hwindow : h ≤ D.radius) :
    (weightMomentMatrix p
      (fun u => D.kernel u * D.density (D.center + h * u))).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos weightMomentMatrix_isHermitian
  intro v hv
  simp only [star_trivial]
  have href : 0 < v ⬝ᵥ (referenceMoment D p *ᵥ v) := by
    simpa only [star_trivial] using (referenceMoment_posDef D p).dotProduct_mulVec_pos hv
  exact lt_of_lt_of_le (mul_pos (mul_pos D.lower_pos D.kernelMin_pos) href)
    (shape_dominates_reference D p hh hwindow v)

/-- If [a real square matrix `A` is positive semidefinite](hyp:hA), then [every entry satisfies
`|A_{ij}| ≤ tr A`](goal). -/
theorem posSemidef_abs_entry_le_trace {p : ℕ}
    {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hA : A.PosSemidef)
    (i j : Fin (p + 1)) : |A i j| ≤ ∑ k, A k k := by
  have hdiag : ∀ k, 0 ≤ A k k := fun _ => hA.diag_nonneg
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hdiag i)]
    exact Finset.single_le_sum (fun k _ => hdiag k) (Finset.mem_univ i)
  have hsym : A j i = A i j := by
    have h := congr_fun₂ hA.isHermitian.eq i j
    simpa [conjTranspose] using h
  have hplus := hA.dotProduct_mulVec_nonneg
    (Pi.single i 1 + Pi.single j 1)
  have hminus := hA.dotProduct_mulVec_nonneg
    (Pi.single i 1 - Pi.single j 1)
  have hp : 0 ≤ A i i + A i j + A j i + A j j := by
    simpa [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_assoc, hsym] using hplus
  have hm : 0 ≤ A i i - A i j - (A j i - A j j) := by
    simpa [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, hsym] using hminus
  have hpair : A i i + A j j ≤ ∑ k, A k k := by
    have h := Finset.sum_le_univ_sum_of_nonneg (s := {i, j}) hdiag
    simpa [hij] using h
  have habs : |A i j| ≤ (A i i + A j j) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hsym]
  linarith [hdiag i, hdiag j]

/-- Let [the design density lie between `f_min > 0` and `f_max` near the evaluation point, and
the kernel `K` be measurable, nonnegative, bounded, zero outside `[−1, 1]` and at least
`K_min > 0` on `[−Δ, Δ]`](hyp:D). Then for every polynomial degree `p`, [the constants
`c_row = (p+1) tr(R⁻¹)/(f_min K_min)` and `c_inv = (G⁻¹)₀₀/f_min` are positive and `c_top =
f_max ∫ K(u) du` is nonnegative, where `R` is the monomial moment matrix on `[−Δ, Δ]` and
`G` the kernel moment matrix](goal). -/
theorem designConstants_positive (D : InteriorDesign) (p : ℕ) :
    0 < inverseRowConstant D p ∧ 0 < inverseConstant D p ∧ 0 ≤ topConstant D := by
  have htrace : 0 < ∑ j, (referenceMoment D p)⁻¹ j j :=
    (referenceMoment_posDef D p).inv.trace_pos
  have hdim : 0 < (p + 1 : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact div_pos (mul_pos hdim htrace) (mul_pos D.lower_pos D.kernelMin_pos)
  · exact div_pos (kernelMoment_posDef D p).inv.diag_pos D.lower_pos
  · rw [topConstant]
    exact mul_nonneg (D.lower_pos.le.trans D.lower_le_upper)
      (integral_nonneg fun u => D.kernel_nonneg u)

/-- Let [the design density `f` lie between `f_min > 0` and `f_max` on `[x₀ − r, x₀ + r]`, and
the kernel `K` be measurable, nonnegative, bounded, zero outside `[−1, 1]` and at least
`K_min > 0` on `[−Δ, Δ]`](hyp:D). For [a positive bandwidth `h`](hyp:hh) [not exceeding
`r`](hyp:hwindow), let `T` be the population moment matrix with `(j,k)` entry `∫ K(u) f(x₀ +
h u) u^(j+k) du`. Then [every row of `T⁻¹` has absolute sum at most `c_row = (p+1)
tr(R⁻¹)/(f_min K_min)`, where `R` is the monomial moment matrix on `[−Δ, Δ]`](goal).

The bound does not depend on the bandwidth. -/
theorem shape_inverse_rows (D : InteriorDesign) (p : ℕ) {h : ℝ}
    (hh : 0 < h) (hwindow : h ≤ D.radius) :
    ∀ i, (∑ j, |(weightMomentMatrix p
      (fun u => D.kernel u * D.density (D.center + h * u)))⁻¹ i j|)
        ≤ inverseRowConstant D p := by
  have hc : 0 < D.lower * D.kernelMin := mul_pos D.lower_pos D.kernelMin_pos
  have hshape := shapeMoment_posDef D p hh hwindow
  have hdiag := inv_diag_le_of_quadForm_sandwich hshape
    (referenceMoment_posDef D p) hc (shape_dominates_reference D p hh hwindow)
  have htrace :
      (∑ j, (weightMomentMatrix p
        (fun u => D.kernel u * D.density (D.center + h * u)))⁻¹ j j) ≤
      (∑ j, (referenceMoment D p)⁻¹ j j) / (D.lower * D.kernelMin) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun j _ => hdiag j)
  intro i
  calc
    _ ≤ ∑ _j : Fin (p + 1),
        (∑ k, (referenceMoment D p)⁻¹ k k) / (D.lower * D.kernelMin) :=
      Finset.sum_le_sum (fun j _ =>
        (posSemidef_abs_entry_le_trace hshape.inv.posSemidef i j).trans htrace)
    _ = inverseRowConstant D p := by
      simp [inverseRowConstant, mul_div_assoc]

/-- Let [the design density lie between `f_min > 0` and `f_max` near the evaluation point, and
the kernel be measurable, nonnegative, bounded, zero outside `[−1, 1]` and bounded below on
`[−Δ, Δ]`](hyp:D). Then for every polynomial degree `p`, [the tolerance `t₀ = min(1, 1/(2
(p+1) c_row), c_inv/(2 (p+1) c_row²))` satisfies `0 < t₀ ≤ 1`, `c_row (p+1) t₀ ≤ 1/2` and `2
c_row² (p+1) t₀ ≤ c_inv`](goal). -/
theorem designTolerance_spec (D : InteriorDesign) (p : ℕ) :
    0 < designTolerance D p ∧ designTolerance D p ≤ 1 ∧
    inverseRowConstant D p * ((p + 1 : ℝ) * designTolerance D p) ≤ 1 / 2 ∧
    2 * inverseRowConstant D p ^ 2 * ((p + 1 : ℝ) * designTolerance D p)
      ≤ inverseConstant D p := by
  obtain ⟨hrow, hinv, _⟩ := designConstants_positive D p
  have hdim : 0 < (p + 1 : ℝ) := by positivity
  have hden₁ : 0 < 2 * (p + 1 : ℝ) * inverseRowConstant D p := by positivity
  have hden₂ : 0 < 2 * (p + 1 : ℝ) * inverseRowConstant D p ^ 2 := by positivity
  have hfirst : designTolerance D p ≤
      1 / (2 * (p + 1 : ℝ) * inverseRowConstant D p) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hsecond : designTolerance D p ≤
      inverseConstant D p / (2 * (p + 1 : ℝ) * inverseRowConstant D p ^ 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min (div_pos (by norm_num) hden₁)
      (div_pos hinv hden₂))
  · have h := (le_div_iff₀ hden₁).mp hfirst
    nlinarith
  · have h := (le_div_iff₀ hden₂).mp hsecond
    nlinarith

/-- Let [the design density lie between `f_min > 0` and `f_max` near the evaluation point and
the kernel be bounded by `K_max` and bounded below by `K_min > 0` on `[−Δ, Δ]`](hyp:D). For
[a positive tolerance `t`](hyp:ht), [`t² / (4 (2 f_max K_max² + K_max t)) > 0`](goal). -/
theorem tailExponent_pos (D : InteriorDesign) {t : ℝ} (ht : 0 < t) :
    0 < tailExponent D t := by
  unfold tailExponent
  have hu : 0 < D.upper := lt_of_lt_of_le D.lower_pos D.lower_le_upper
  have hw : 0 < D.kernelMax := D.kernelMax_pos
  positivity

end Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate
