module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Estimator
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularUStat

/-! # Rectangular variance bounds
The Hoeffding identity bounds a rectangular average using uncentered slice and
kernel second moments. The prescribed role counts then yield the paper's two
sample-size denominators. No independence between a first-order moment and its
rectangular correction is required.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Centering a square-integrable real statistic cannot increase its second moment.  Given [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the rectangular centered energy le conclusion](goal) holds. -/
lemma rectangular_centered_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, (f x - ∫ y, f y ∂μ)^2 ∂μ) ≤ ∫ x, (f x)^2 ∂μ := by
  have hv := variance_eq_sub hf
  rw [variance_eq_integral hf.aestronglyMeasurable.aemeasurable] at hv
  simp only [Pi.pow_apply] at hv
  linarith [sq_nonneg (∫ y, f y ∂μ)]

/-- The orthogonal degenerate remainder has no more energy than the original kernel.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular degenerate energy le conclusion](goal) holds. -/
lemma rectangular_degenerate_energy_le {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    let mean := ∫ p, H p ∂μ.prod ν
    (∫ p, (H p - mean - ((∫ z, H (p.1,z) ∂ν)-mean) -
      ((∫ w, H (w,p.2) ∂μ)-mean))^2 ∂μ.prod ν) ≤
        ∫ p, (H p)^2 ∂μ.prod ν := by
  dsimp only
  let mean := ∫ p, H p ∂μ.prod ν
  let H0 := fun p => H p - mean
  have hH0 : MemLp H0 2 (μ.prod ν) := hH.sub (memLp_const mean)
  have hzero : ∫ p, H0 p ∂μ.prod ν = 0 := by
    rw [integral_sub (hH.integrable (by norm_num)) (integrable_const mean)]
    simp [mean]
  have hr : (fun w => ∫ z, H0 (w,z) ∂ν) =ᵐ[μ]
      (fun w => (∫ z, H (w,z) ∂ν)-mean) := by
    filter_upwards [hH.integrable (by norm_num) |>.prod_right_ae] with w hw
    dsimp only [H0]
    rw [integral_sub hw (integrable_const mean)]
    simp
  have hc : (fun z => ∫ w, H0 (w,z) ∂μ) =ᵐ[ν]
      (fun z => (∫ w, H (w,z) ∂μ)-mean) := by
    filter_upwards [hH.integrable (by norm_num) |>.prod_left_ae] with z hz
    dsimp only [H0]
    rw [integral_sub hz (integrable_const mean)]
    simp
  have he := rectangular_anova_energy μ ν H0 hH0 hzero
  dsimp only at he
  have hres :
      (∫ p, (H0 p - (∫ z, H0 (p.1,z) ∂ν) - (∫ w, H0 (w,p.2) ∂μ))^2 ∂μ.prod ν) =
      (∫ p, (H p-mean-((∫ z, H (p.1,z) ∂ν)-mean)-
        ((∫ w, H (w,p.2) ∂μ)-mean))^2 ∂μ.prod ν) := by
    apply integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hr,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hc] with p hp hq
    rw [hp, hq]
  rw [hres] at he
  have hbound := rectangular_centered_energy_le (μ.prod ν) H hH
  have hrow : 0 ≤ ∫ w, (∫ z, H0 (w,z) ∂ν)^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hcol : 0 ≤ ∫ z, (∫ w, H0 (w,z) ∂μ)^2 ∂ν :=
    integral_nonneg (fun _ => sq_nonneg _)
  change (∫ p, (H p-mean-((∫ z, H (p.1,z) ∂ν)-mean)-
    ((∫ w, H (w,p.2) ∂μ)-mean))^2 ∂μ.prod ν) ≤ _
  change (∫ p, (H0 p)^2 ∂μ.prod ν) ≤ _ at hbound
  linarith

/-- The rectangular variance is bounded by the uncentered row, column, and kernel energies.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input ell](hyp:ell), [the specified input ht](hyp:ht), [the specified input hl](hyp:hl), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular variance le slice energies conclusion](goal) holds. -/
lemma rectangular_variance_le_slice_energies {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t ell : ℕ) (ht : 0 < t) (hl : 0 < ell) (H : W × Z → ℝ)
    (hH : MemLp H 2 (μ.prod ν)) :
    (∫ D, (((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell,
      H (D.1 i,D.2 j)-(∫ p, H p ∂μ.prod ν))^2
      ∂(Measure.pi (fun _ : Fin t => μ)).prod (Measure.pi (fun _ : Fin ell => ν))) ≤
      (∫ w, (∫ z, H (w,z) ∂ν)^2 ∂μ)/(t:ℝ) +
      (∫ z, (∫ w, H (w,z) ∂μ)^2 ∂ν)/(ell:ℝ) +
      (∫ p, (H p)^2 ∂μ.prod ν)/((t:ℝ)*(ell:ℝ)) := by
  rw [rectangular_ustat_variance μ ν t ell ht hl H hH]
  have hr := rectangular_centered_energy_le μ _ (rectangular_memLp_mean μ ν H hH)
  have hc := rectangular_centered_energy_le ν _ (rectangular_memLp_mean ν μ
    (fun p => H (p.2,p.1)) (hH.comp_measurePreserving Measure.measurePreserving_swap))
  rw [← integral_prod _ (hH.integrable (by norm_num))] at hr
  rw [← integral_prod_symm _ (hH.integrable (by norm_num))] at hc
  exact add_le_add
    (add_le_add (div_le_div_of_nonneg_right hr (Nat.cast_nonneg _))
      (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)))
    (div_le_div_of_nonneg_right (rectangular_degenerate_energy_le μ ν H hH)
      (by positivity))

/-- The floor split reserves at least one third of the labeled records and half of all treatment records.  Given [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the rectangular role count bounds conclusion](goal) holds. -/
lemma rectangular_role_count_bounds (n m : ℕ) (hn : 2 ≤ n) :
    (n:ℝ)/3 ≤ outcomeCount n ∧ ((n:ℝ)+m)/2 ≤ treatmentCount n m := by
  have hfloor : n ≤ 3*(n/2) := by omega
  have hhalf : 2*(n/2) ≤ n := by omega
  constructor
  · unfold outcomeCount
    have h := (show (n:ℝ) ≤ 3*(n/2:ℕ) by exact_mod_cast hfloor)
    linarith
  · unfold treatmentCount
    rw [Nat.cast_sub (by omega : n/2 ≤ n+m), Nat.cast_add]
    have h := (show (2:ℝ)*(n/2:ℕ) ≤ (n:ℝ) by exact_mod_cast hhalf)
    linarith [show (0:ℝ) ≤ m by positivity]

/-- Role reciprocals have the labeled and total-record orders required by the variance bound.  Given [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the rectangular role inverse bounds conclusion](goal) holds. -/
lemma rectangular_role_inverse_bounds (n m : ℕ) (hn : 2 ≤ n) :
    (outcomeCount n : ℝ)⁻¹ ≤ 3/(n:ℝ) ∧
    (treatmentCount n m : ℝ)⁻¹ ≤ 2/((n:ℝ)+m) ∧
    ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ ≤
      6/((n:ℝ)*((n:ℝ)+m)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (0:ℝ) < (n:ℝ)+m := by positivity
  obtain ⟨hl, ht⟩ := rectangular_role_count_bounds n m hn
  have hl0 : (0:ℝ) < outcomeCount n := (div_pos hn0 (by norm_num)).trans_le hl
  have ht0 : (0:ℝ) < treatmentCount n m := (div_pos hN (by norm_num)).trans_le ht
  have hil : (outcomeCount n : ℝ)⁻¹ ≤ 3/(n:ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    apply (inv_mul_le_iff₀ hl0).mpr
    linarith
  have hit : (treatmentCount n m : ℝ)⁻¹ ≤ 2/((n:ℝ)+m) := by
    apply (le_div_iff₀ hN).mpr
    apply (inv_mul_le_iff₀ ht0).mpr
    linarith
  refine ⟨hil, hit, ?_⟩
  rw [mul_inv_rev]
  calc
    _ ≤ (3/(n:ℝ))*(2/((n:ℝ)+m)) :=
      mul_le_mul hil hit (inv_nonneg.mpr ht0.le) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Uniform slice and kernel energies give the rectangular sampling order after the floor split.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input B](hyp:B), [the specified input E](hyp:E), [the specified input hB](hyp:hB), [the specified input hE](hyp:hE), [the specified input hrow](hyp:hrow), [the specified input hcol](hyp:hcol), [the specified input hkernel](hyp:hkernel), [the rectangular role variance bound conclusion](goal) holds. -/
lemma rectangular_role_variance_bound {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n m : ℕ) (hn : 2 ≤ n) (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν))
    (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hrow : (∫ w, (∫ z, H (w,z) ∂ν)^2 ∂μ) ≤ B)
    (hcol : (∫ z, (∫ w, H (w,z) ∂μ)^2 ∂ν) ≤ B)
    (hkernel : (∫ p, (H p)^2 ∂μ.prod ν) ≤ E) :
    (∫ D, (((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
      ∑ i : Fin (treatmentCount n m), ∑ j : Fin (outcomeCount n),
      H (D.1 i,D.2 j)-(∫ p, H p ∂μ.prod ν))^2
      ∂(Measure.pi (fun _ : Fin (treatmentCount n m) => μ)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => ν))) ≤
      5*B/(n:ℝ) + 6*E/((n:ℝ)*((n:ℝ)+m)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (0:ℝ) < (n:ℝ)+m := by positivity
  have hcounts : 0 < treatmentCount n m ∧ 0 < outcomeCount n := by
    unfold treatmentCount outcomeCount
    omega
  have hv := rectangular_variance_le_slice_energies μ ν
    (treatmentCount n m) (outcomeCount n) hcounts.1 hcounts.2 H hH
  obtain ⟨hil, hit, hip⟩ := rectangular_role_inverse_bounds n m hn
  have htotal : (2:ℝ)/((n:ℝ)+m) ≤ 2/(n:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hn0 (le_add_of_nonneg_right (Nat.cast_nonneg m))
  have hr : (∫ w, (∫ z, H (w,z) ∂ν)^2 ∂μ)/(treatmentCount n m:ℝ) ≤ B*(2/(n:ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hrow (hit.trans htotal) (by positivity) hB
  have hc : (∫ z, (∫ w, H (w,z) ∂μ)^2 ∂ν)/(outcomeCount n:ℝ) ≤ B*(3/(n:ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hcol hil (by positivity) hB
  have hp : (∫ p, (H p)^2 ∂μ.prod ν)/
      ((treatmentCount n m:ℝ)*(outcomeCount n:ℝ)) ≤ E*(6/((n:ℝ)*((n:ℝ)+m))) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hkernel hip (by positivity) hE
  calc
    _ ≤ _ := hv
    _ ≤ B*(2/(n:ℝ)) + B*(3/(n:ℝ)) + E*(6/((n:ℝ)*((n:ℝ)+m))) :=
      add_le_add (add_le_add hr hc) hp
    _ = _ := by ring

/-- A first-order moment and its rectangular correction need no independence for this energy bound.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the rectangular difference energy le conclusion](goal) holds. -/
lemma rectangular_difference_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x-g x)^2 ∂μ) ≤
      2*(∫ x, (f x)^2 ∂μ) + 2*(∫ x, (g x)^2 ∂μ) := by
  calc
    _ ≤ ∫ x, 2*(f x)^2 + 2*(g x)^2 ∂μ := by
      apply integral_mono (hf.sub hg).integrable_sq
        ((hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
      intro x
      change (f x-g x)^2 ≤ 2*(f x)^2 + 2*(g x)^2
      nlinarith [sq_nonneg (f x+g x)]
    _ = _ := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]

/-- Symmetrization is a contraction for the squared Frobenius norm.  Given [the specified input B](hyp:B), [the rectangular symmetrization energy le conclusion](goal) holds. -/
lemma rectangular_symmetrization_energy_le {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) :
    (∑ u, ∑ v, ((B u v+B v u)/2)^2) ≤ ∑ u, ∑ v, (B u v)^2 := by
  change ι → ι → ℝ at B
  have hp : (∑ u, ∑ v, ((B u v+B v u)/2)^2) ≤
      ∑ u, ∑ v, ((B u v)^2+(B v u)^2)/2 := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    nlinarith [sq_nonneg (B u v-B v u)]
  calc
    _ ≤ _ := hp
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun u v => (B v u)^2)]
      ring

/-- Symmetrization about a symmetric population matrix contracts the squared deviation.  Given [the specified input B](hyp:B), [the specified input Q](hyp:Q), [the specified input hQ](hyp:hQ), [the rectangular symmetrized deviation le conclusion](goal) holds. -/
lemma rectangular_symmetrized_deviation_le {ι : Type*} [Fintype ι]
    (B Q : Matrix ι ι ℝ) (hQ : ∀ u v, Q u v = Q v u) :
    (∑ u, ∑ v, ((B u v+B v u)/2-Q u v)^2) ≤
      ∑ u, ∑ v, (B u v-Q u v)^2 := by
  have h := rectangular_symmetrization_energy_le (B-Q)
  simp only [Matrix.sub_apply] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [← hQ u v]
  congr 1
  ring

/-- The roadmap's kernel and conditional-mean bounds give precisely the two-term sampling envelope.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input d](hyp:d), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input C](hyp:C), [the specified input k](hyp:k), [the specified input hh](hyp:hh), [the specified input hC](hyp:hC), [the specified input hk](hyp:hk), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input hrow](hyp:hrow), [the specified input hcol](hyp:hcol), [the specified input hkernel](hyp:hkernel), [the rectangular sampling from kernel energies conclusion](goal) holds. -/
lemma rectangular_sampling_from_kernel_energies {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n m d : ℕ) (hn : 2 ≤ n) (h C k : ℝ) (hh : 0 < h) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν))
    (hrow : (∫ w, (∫ z, H (w,z) ∂ν)^2 ∂μ) ≤ C/h^d)
    (hcol : (∫ z, (∫ w, H (w,z) ∂μ)^2 ∂ν) ≤ C/h^d)
    (hkernel : (∫ p, (H p)^2 ∂μ.prod ν) ≤ C*k/h^(2*d)) :
    (∫ D, (((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
      ∑ i : Fin (treatmentCount n m), ∑ j : Fin (outcomeCount n),
      H (D.1 i,D.2 j)-(∫ p, H p ∂μ.prod ν))^2
      ∂(Measure.pi (fun _ : Fin (treatmentCount n m) => μ)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => ν))) ≤
      6*C*(1/((n:ℝ)*h^d)+k/((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
  have hv := rectangular_role_variance_bound μ ν n m hn H hH
    (C/h^d) (C*k/h^(2*d)) (by positivity) (by positivity) hrow hcol hkernel
  have heq : 5*(C/h^d)/(n:ℝ) + 6*(C*k/h^(2*d))/((n:ℝ)*((n:ℝ)+m)) =
      5*C*(1/((n:ℝ)*h^d)) + 6*C*(k/((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at hv
  have ha : 0 ≤ C*(1/((n:ℝ)*h^d)) := by positivity
  calc
    _ ≤ _ := hv
    _ ≤ _ := by nlinarith only [ha]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
