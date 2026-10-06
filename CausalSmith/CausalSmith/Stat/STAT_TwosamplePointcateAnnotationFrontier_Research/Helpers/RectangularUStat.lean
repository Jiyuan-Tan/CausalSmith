module
public import Causalean.Mathlib.Probability.IidMeanVariance
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Helpers/RectangularUStat

Exact second moments and the Hoeffding variance identity for two independent finite
iid blocks. Slice means preserve square integrability; the centered kernel splits into
orthogonal row, column, and degenerate energies.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Square-integrability on a product gives square-integrable slices almost everywhere.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular mem lp slices conclusion](goal) holds. -/
lemma rectangular_memLp_slices {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    ∀ᵐ w ∂μ, MemLp (fun z => H (w,z)) 2 ν := by
  filter_upwards [hH.aestronglyMeasurable.prodMk_left, hH.integrable_sq.prod_right_ae]
    with w hm hi
  exact (memLp_two_iff_integrable_sq hm).2 hi

/-- The squared expectation is no greater than the second moment.  Given [the specified input W](hyp:W), [the specified input F](hyp:F), [the specified input hF](hyp:hF), [the rectangular sq integral le conclusion](goal) holds. -/
lemma rectangular_sq_integral_le {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] (F : W → ℝ) (hF : MemLp F 2 μ) :
    (∫ w, F w ∂μ)^2 ≤ ∫ w, (F w)^2 ∂μ := by
  have hv := variance_nonneg F μ
  rw [variance_eq_sub hF] at hv
  exact sub_nonneg.mp hv

/-- Integrating one coordinate of a square-integrable product function preserves L².  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular mem lp mean conclusion](goal) holds. -/
lemma rectangular_memLp_mean {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    MemLp (fun w => ∫ z, H (w,z) ∂ν) 2 μ := by
  have hm := hH.aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).2
  apply hH.integrable_sq.integral_prod_left.mono'
  · exact hm.pow 2
  · filter_upwards [rectangular_memLp_slices μ ν H hH] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact rectangular_sq_integral_le ν _ hw

/-- An iid average has second moment equal to its squared mean plus scaled variance.  Given [the specified input W](hyp:W), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the specified input F](hyp:F), [the specified input hF](hyp:hF), [the rectangular iid second moment conclusion](goal) holds. -/
lemma rectangular_iid_second_moment {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] (t : ℕ) (ht : 0 < t)
    (F : W → ℝ) (hF : MemLp F 2 μ) :
    (∫ s, ((t:ℝ)⁻¹ * ∑ i : Fin t, F (s i))^2 ∂Measure.pi (fun _ : Fin t => μ)) =
      (t:ℝ)⁻¹ * (∫ w, (F w)^2 ∂μ) +
      (1-(t:ℝ)⁻¹) * (∫ w, F w ∂μ)^2 := by
  have hs : MemLp (fun s => (t:ℝ)⁻¹ * ∑ i : Fin t, F (s i)) 2
      (Measure.pi (fun _ : Fin t => μ)) :=
    (memLp_finsetSum _ (fun i _ => hF.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin t => μ) i))).const_mul _
  have hv := Causalean.Mathlib.Probability.iid_average_variance μ t F hF
  rw [variance_eq_sub hs, Causalean.Mathlib.Probability.iid_average_integral μ t ht F
    (hF.integrable (by norm_num)), variance_eq_sub hF] at hv
  simp only [Pi.pow_apply] at hv
  linarith

/-- Averaging the first coordinate preserves square integrability on the remaining product.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular average mem lp conclusion](goal) holds. -/
lemma rectangular_average_memLp {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℕ) (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    MemLp (fun p : (Fin t → W) × Z => (t:ℝ)⁻¹ * ∑ i : Fin t, H (p.1 i,p.2)) 2
      ((Measure.pi (fun _ : Fin t => μ)).prod ν) := by
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro i _
  exact hH.comp_measurePreserving
    ((measurePreserving_eval (fun _ : Fin t => μ) i).prod (MeasurePreserving.id ν))

/-- The second moment after averaging one coordinate follows from iid variance and Fubini.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular average square conclusion](goal) holds. -/
lemma rectangular_average_square {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℕ) (ht : 0 < t) (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    (∫ p : (Fin t → W) × Z, ((t:ℝ)⁻¹ * ∑ i : Fin t, H (p.1 i,p.2))^2
      ∂(Measure.pi (fun _ : Fin t => μ)).prod ν) =
      (t:ℝ)⁻¹ * (∫ p, (H p)^2 ∂μ.prod ν) +
      (1-(t:ℝ)⁻¹) * (∫ z, (∫ w, H (w,z) ∂μ)^2 ∂ν) := by
  rw [integral_prod_symm _ (rectangular_average_memLp μ ν t H hH).integrable_sq]
  have hs : ∀ᵐ z ∂ν, MemLp (fun w => H (w,z)) 2 μ :=
    rectangular_memLp_slices ν μ (fun p => H (p.2,p.1))
      (hH.comp_measurePreserving Measure.measurePreserving_swap)
  rw [integral_congr_ae (by
    filter_upwards [hs] with z hz
    exact rectangular_iid_second_moment μ t ht _ hz)]
  have hm := rectangular_memLp_mean ν μ (fun p => H (p.2,p.1))
    (hH.comp_measurePreserving Measure.measurePreserving_swap)
  rw [integral_add (hH.integrable_sq.integral_prod_right.const_mul _)
    (hm.integrable_sq.const_mul _), integral_const_mul, integral_const_mul,
    ← integral_prod_symm _ hH.integrable_sq]

/-- Almost every slice mean of a first-coordinate average is the corresponding original mean.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular average mean conclusion](goal) holds. -/
lemma rectangular_average_mean {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℕ) (ht : 0 < t) (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    ∀ᵐ z ∂ν, (∫ s : Fin t → W, (t:ℝ)⁻¹ * ∑ i : Fin t, H (s i,z)
      ∂Measure.pi (fun _ : Fin t => μ)) = ∫ w, H (w,z) ∂μ := by
  filter_upwards [hH.integrable (by norm_num) |>.prod_left_ae] with z hz
  exact Causalean.Mathlib.Probability.iid_average_integral μ t ht _ hz

/-- Slice integration commutes with a finite first-coordinate average.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular average other mean conclusion](goal) holds. -/
lemma rectangular_average_other_mean {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℕ) (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    ∀ᵐ s ∂Measure.pi (fun _ : Fin t => μ),
      (∫ z, (t:ℝ)⁻¹ * ∑ i : Fin t, H (s i,z) ∂ν) =
        (t:ℝ)⁻¹ * ∑ i : Fin t, ∫ z, H (s i,z) ∂ν := by
  have hs : ∀ i : Fin t, ∀ᵐ s ∂Measure.pi (fun _ : Fin t => μ),
      Integrable (fun z => H (s i,z)) ν := fun i =>
    (measurePreserving_eval (fun _ : Fin t => μ) i).quasiMeasurePreserving.ae
      (hH.integrable (by norm_num) |>.prod_right_ae)
  filter_upwards [ae_all_iff.mpr hs] with s hs
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hs i)]

/-- Iterated iid averaging gives the exact uncentered rectangular second moment.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input ell](hyp:ell), [the specified input ht](hyp:ht), [the specified input hl](hyp:hl), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular second moment conclusion](goal) holds. -/
lemma rectangular_second_moment {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t ell : ℕ) (ht : 0 < t) (hl : 0 < ell) (H : W × Z → ℝ)
    (hH : MemLp H 2 (μ.prod ν)) :
    (∫ D, (((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell, H (D.1 i,D.2 j))^2
      ∂(Measure.pi (fun _ : Fin t => μ)).prod (Measure.pi (fun _ : Fin ell => ν))) =
      (t:ℝ)⁻¹*(ell:ℝ)⁻¹ * (∫ p, (H p)^2 ∂μ.prod ν) +
      (t:ℝ)⁻¹*(1-(ell:ℝ)⁻¹) * (∫ w, (∫ z, H (w,z) ∂ν)^2 ∂μ) +
      (1-(t:ℝ)⁻¹)*(ell:ℝ)⁻¹ * (∫ z, (∫ w, H (w,z) ∂μ)^2 ∂ν) +
      (1-(t:ℝ)⁻¹)*(1-(ell:ℝ)⁻¹) * (∫ p, H p ∂μ.prod ν)^2 := by
  let μt := Measure.pi (fun _ : Fin t => μ)
  let νl := Measure.pi (fun _ : Fin ell => ν)
  let A : (Fin t → W) × Z → ℝ := fun p => (t:ℝ)⁻¹ * ∑ i : Fin t, H (p.1 i,p.2)
  have hA : MemLp A 2 (μt.prod ν) := rectangular_average_memLp μ ν t H hH
  have hsecond := rectangular_average_square ν μt ell hl (fun p => A (p.2,p.1))
    (hA.comp_measurePreserving Measure.measurePreserving_swap)
  dsimp only at hsecond
  change (∫ p : (Fin ell → Z) × (Fin t → W),
    ((ell:ℝ)⁻¹ * ∑ j : Fin ell, A (p.2,p.1 j))^2 ∂νl.prod μt) = _ at hsecond
  have hswap : (∫ p : (Fin ell → Z) × (Fin t → W),
      ((ell:ℝ)⁻¹ * ∑ j : Fin ell, A (p.2,p.1 j))^2 ∂νl.prod μt) =
      (∫ p : (Fin t → W) × (Fin ell → Z),
      ((ell:ℝ)⁻¹ * ∑ j : Fin ell, A (p.1,p.2 j))^2 ∂μt.prod νl) := by
    simpa only [Prod.swap] using integral_prod_swap (μ := μt) (ν := νl)
      (fun p => ((ell:ℝ)⁻¹ * ∑ j : Fin ell, A (p.1,p.2 j))^2)
  rw [hswap] at hsecond
  have havg : (fun p : (Fin t → W) × (Fin ell → Z) =>
      (ell:ℝ)⁻¹ * ∑ j : Fin ell, A (p.1,p.2 j)) =
      (fun p => ((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell, H (p.1 i,p.2 j)) := by
    funext p
    simp only [A, ← Finset.mul_sum, mul_inv_rev]
    rw [Finset.sum_comm]
    ring
  change (∫ p, ((ell:ℝ)⁻¹ * ∑ j : Fin ell, A (p.1,p.2 j))^2 ∂μt.prod νl) = _ at hsecond
  simp_rw [congrFun havg] at hsecond
  have hswapA : (∫ p : Z × (Fin t → W), (A (p.2,p.1))^2 ∂ν.prod μt) =
      ∫ p, (A p)^2 ∂μt.prod ν := by
    simpa only [Prod.swap] using integral_prod_swap (μ := μt) (ν := ν) (fun p => (A p)^2)
  rw [hswapA] at hsecond
  change _ = (ell:ℝ)⁻¹ * (∫ p, (A p)^2 ∂μt.prod ν) +
    (1-(ell:ℝ)⁻¹) * (∫ s, (∫ z, A (s,z) ∂ν)^2 ∂μt) at hsecond
  have hmeansq : (∫ s, (∫ z, A (s,z) ∂ν)^2 ∂μt) =
      (∫ s, ((t:ℝ)⁻¹ * ∑ i : Fin t, ∫ z, H (s i,z) ∂ν)^2 ∂μt) := by
    apply integral_congr_ae
    filter_upwards [rectangular_average_other_mean μ ν t H hH] with s hs
    exact congrArg (fun x : ℝ => x^2) hs
  rw [hmeansq] at hsecond
  rw [rectangular_average_square μ ν t ht H hH,
    rectangular_iid_second_moment μ t ht _ (rectangular_memLp_mean μ ν H hH),
    ← integral_prod _ (hH.integrable (by norm_num))] at hsecond
  rw [hsecond]
  ring

/-- A product function has the same inner product with a first-coordinate function as its slice mean.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input H](hyp:H), [the specified input g](hyp:g), [the specified input hH](hyp:hH), [the specified input hg](hyp:hg), [the rectangular mean inner conclusion](goal) holds. -/
lemma rectangular_mean_inner {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : W × Z → ℝ) (g : W → ℝ) (hH : MemLp H 2 (μ.prod ν))
    (hg : MemLp g 2 μ) :
    (∫ p, H p * g p.1 ∂μ.prod ν) = ∫ w, (∫ z, H (w,z) ∂ν) * g w ∂μ := by
  have hi : Integrable (fun p : W × Z => H p*g p.1) (μ.prod ν) := by
    simpa only [Pi.mul_def] using hH.integrable_mul (hg.comp_fst ν)
  rw [integral_prod (fun p => H p*g p.1) hi]
  simp_rw [integral_mul_const]

/-- The centered rectangular kernel splits into orthogonal row, column, and degenerate energies.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the specified input hzero](hyp:hzero), [the rectangular anova energy conclusion](goal) holds. -/
lemma rectangular_anova_energy {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : W × Z → ℝ) (hH : MemLp H 2 (μ.prod ν)) (hzero : ∫ p, H p ∂μ.prod ν = 0) :
    let R := fun w => ∫ z, H (w,z) ∂ν
    let C := fun z => ∫ w, H (w,z) ∂μ
    (∫ p, (H p-R p.1-C p.2)^2 ∂μ.prod ν) =
      (∫ p, (H p)^2 ∂μ.prod ν) - (∫ w, (R w)^2 ∂μ) - (∫ z, (C z)^2 ∂ν) := by
  dsimp only
  let R := fun w => ∫ z, H (w,z) ∂ν
  let C := fun z => ∫ w, H (w,z) ∂μ
  have hR : MemLp R 2 μ := rectangular_memLp_mean μ ν H hH
  have hC : MemLp C 2 ν := rectangular_memLp_mean ν μ (fun p => H (p.2,p.1))
    (hH.comp_measurePreserving Measure.measurePreserving_swap)
  have hRf := hR.comp_fst ν
  have hCs := hC.comp_snd μ
  have hHR := rectangular_mean_inner μ ν H R hH hR
  have hHC : (∫ p, H p * C p.2 ∂μ.prod ν) = ∫ z, (C z)^2 ∂ν := by
    have h := rectangular_mean_inner ν μ (fun p => H (p.2,p.1)) C
      (hH.comp_measurePreserving Measure.measurePreserving_swap) hC
    have hs : (∫ p : Z × W, H (p.2,p.1)*C p.1 ∂ν.prod μ) =
        ∫ p, H p*C p.2 ∂μ.prod ν := by
      simpa only [Prod.swap] using integral_prod_swap (μ := μ) (ν := ν)
        (fun p => H p*C p.2)
    rw [hs] at h
    simpa only [C, pow_two] using h
  have hRC : (∫ p : W × Z, R p.1*C p.2 ∂μ.prod ν) = 0 := by
    rw [integral_prod_mul]
    have hr : ∫ w, R w ∂μ = 0 := by
      rw [← integral_prod _ (hH.integrable (by norm_num))]
      exact hzero
    rw [hr, zero_mul]
  have hRsq : (∫ p : W × Z, (R p.1)^2 ∂μ.prod ν) = ∫ w, (R w)^2 ∂μ := by
    simpa using integral_fun_fst (μ := μ) (ν := ν) (fun w => (R w)^2)
  have hCsq : (∫ p : W × Z, (C p.2)^2 ∂μ.prod ν) = ∫ z, (C z)^2 ∂ν := by
    simpa using integral_fun_snd (μ := μ) (ν := ν) (fun z => (C z)^2)
  have hiH := hH.integrable_sq
  have hiR := hRf.integrable_sq
  have hiC := hCs.integrable_sq
  have hiHR : Integrable (fun p : W × Z => H p*R p.1) (μ.prod ν) := by
    simpa only [Pi.mul_def] using hH.integrable_mul hRf
  have hiHC : Integrable (fun p : W × Z => H p*C p.2) (μ.prod ν) := by
    simpa only [Pi.mul_def] using hH.integrable_mul hCs
  have hiRC : Integrable (fun p : W × Z => R p.1*C p.2) (μ.prod ν) := by
    simpa only [Pi.mul_def] using hRf.integrable_mul hCs
  have hiHR2 := hiHR.const_mul (2:ℝ)
  have hiHC2 := hiHC.const_mul (2:ℝ)
  have hiRC2 := hiRC.const_mul (2:ℝ)
  have hiSum := ((hiH.add hiR).add hiC).sub hiHR2 |>.sub hiHC2
  have hexpand : (fun p : W × Z => (H p-R p.1-C p.2)^2) =
      (fun p => (H p)^2 + (R p.1)^2 + (C p.2)^2 -
        2*(H p*R p.1) - 2*(H p*C p.2) + 2*(R p.1*C p.2)) := by
    funext p
    ring
  change (∫ p, (H p-R p.1-C p.2)^2 ∂μ.prod ν) = _
  rw [hexpand]
  integral_linearity
  simp only [hRsq, hCsq, hHC, hRC]
  have hHR' : (∫ p, H p*R p.1 ∂μ.prod ν) = ∫ w, (R w)^2 ∂μ := by
    simpa only [R, pow_two] using hHR
  rw [hHR']
  ring

/-- Two independent finite iid blocks give the rectangular Hoeffding variance identity.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input t](hyp:t), [the specified input ell](hyp:ell), [the specified input ht](hyp:ht), [the specified input hl](hyp:hl), [the specified input H](hyp:H), [the specified input hH](hyp:hH), [the rectangular ustat variance conclusion](goal) holds. -/
lemma rectangular_ustat_variance {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t ell : ℕ) (ht : 0 < t) (hl : 0 < ell) (H : W × Z → ℝ)
    (hH : MemLp H 2 (μ.prod ν)) :
    let mean := ∫ wz, H wz ∂μ.prod ν
    let H1 := fun w => (∫ z, H (w,z) ∂ν)-mean
    let H2 := fun z => (∫ w, H (w,z) ∂μ)-mean
    let H12 := fun wz => H wz-mean-H1 wz.1-H2 wz.2
    (∫ D, (((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell, H (D.1 i,D.2 j)-mean)^2
      ∂(Measure.pi (fun _ : Fin t => μ)).prod (Measure.pi (fun _ : Fin ell => ν))) =
      (∫ w, (H1 w)^2 ∂μ)/(t:ℝ) + (∫ z, (H2 z)^2 ∂ν)/(ell:ℝ) +
      (∫ wz, (H12 wz)^2 ∂μ.prod ν)/((t:ℝ)*(ell:ℝ)) := by
  dsimp only
  let mean := ∫ p, H p ∂μ.prod ν
  let H0 := fun p => H p-mean
  let H1 := fun w => (∫ z, H (w,z) ∂ν)-mean
  let H2 := fun z => (∫ w, H (w,z) ∂μ)-mean
  let R := fun w => ∫ z, H0 (w,z) ∂ν
  let C := fun z => ∫ w, H0 (w,z) ∂μ
  have hH0 : MemLp H0 2 (μ.prod ν) := hH.sub (memLp_const mean)
  have hzero : (∫ p, H0 p ∂μ.prod ν) = 0 := by
    rw [integral_sub (hH.integrable (by norm_num)) (integrable_const mean)]
    simp [mean]
  have hrow : R =ᵐ[μ] H1 := by
    filter_upwards [hH.integrable (by norm_num) |>.prod_right_ae] with w hw
    dsimp only [R, H0, H1]
    rw [integral_sub hw (integrable_const mean)]
    simp
  have hcol : C =ᵐ[ν] H2 := by
    filter_upwards [hH.integrable (by norm_num) |>.prod_left_ae] with z hz
    dsimp only [C, H0, H2]
    rw [integral_sub hz (integrable_const mean)]
    simp
  have hrowSq : (∫ w, (R w)^2 ∂μ) = ∫ w, (H1 w)^2 ∂μ :=
    integral_congr_ae (hrow.fun_comp (fun x : ℝ => x^2))
  have hcolSq : (∫ z, (C z)^2 ∂ν) = ∫ z, (H2 z)^2 ∂ν :=
    integral_congr_ae (hcol.fun_comp (fun x : ℝ => x^2))
  have hresSq : (∫ p, (H0 p-R p.1-C p.2)^2 ∂μ.prod ν) =
      ∫ p, (H p-mean-H1 p.1-H2 p.2)^2 ∂μ.prod ν := by
    apply integral_congr_ae
    have hr := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hrow
    have hc := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hcol
    filter_upwards [hr, hc] with p hp hq
    rw [hp, hq]
  have henergy := rectangular_anova_energy μ ν H0 hH0 hzero
  change (∫ p, (H0 p-R p.1-C p.2)^2 ∂μ.prod ν) =
    (∫ p, (H0 p)^2 ∂μ.prod ν) - (∫ w, (R w)^2 ∂μ) - (∫ z, (C z)^2 ∂ν) at henergy
  rw [hresSq, hrowSq, hcolSq] at henergy
  have hsecond := rectangular_second_moment μ ν t ell ht hl H0 hH0
  change _ = (t:ℝ)⁻¹*(ell:ℝ)⁻¹ * (∫ p, (H0 p)^2 ∂μ.prod ν) +
      (t:ℝ)⁻¹*(1-(ell:ℝ)⁻¹) * (∫ w, (R w)^2 ∂μ) +
      (1-(t:ℝ)⁻¹)*(ell:ℝ)⁻¹ * (∫ z, (C z)^2 ∂ν) +
      (1-(t:ℝ)⁻¹)*(1-(ell:ℝ)⁻¹) * (∫ p, H0 p ∂μ.prod ν)^2 at hsecond
  rw [hrowSq, hcolSq, hzero] at hsecond
  have htR : (t:ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hlR : (ell:ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have havg (D : (Fin t → W) × (Fin ell → Z)) :
      ((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell, H0 (D.1 i,D.2 j) =
      ((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell, H (D.1 i,D.2 j)-mean := by
    simp only [H0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [havg] at hsecond
  change (∫ D, (((t:ℝ)*(ell:ℝ))⁻¹ * ∑ i : Fin t, ∑ j : Fin ell,
      H (D.1 i,D.2 j)-mean)^2
      ∂(Measure.pi (fun _ : Fin t => μ)).prod (Measure.pi (fun _ : Fin ell => ν))) =
      (∫ w, (H1 w)^2 ∂μ)/(t:ℝ) + (∫ z, (H2 z)^2 ∂ν)/(ell:ℝ) +
      (∫ p, (H p-mean-H1 p.1-H2 p.2)^2 ∂μ.prod ν)/((t:ℝ)*(ell:ℝ))
  rw [hsecond]
  have hE : (∫ p, (H0 p)^2 ∂μ.prod ν) =
      (∫ p, (H p-mean-H1 p.1-H2 p.2)^2 ∂μ.prod ν) +
      (∫ w, (H1 w)^2 ∂μ) + (∫ z, (H2 z)^2 ∂ν) := by linarith [henergy]
  rw [hE]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
