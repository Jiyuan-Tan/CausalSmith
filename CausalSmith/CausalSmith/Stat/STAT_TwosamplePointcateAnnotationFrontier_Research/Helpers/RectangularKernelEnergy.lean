module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.ResidualControl
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationMoments
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularVarianceBounds

/-! # Rectangular kernel second moments
Uniform design converts the squared, doubly localized projection kernel into
its rank times the inverse squared localization volume. Bounded record marks
and coarse features preserve this order. These are the kernel-energy steps of
the rectangular sampling roadmap.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The fine projection kernel is globally bounded at every fixed resolution.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input x](hyp:x), [the specified input y](hyp:y), [the rectangular fine kernel abs bound conclusion](goal) holds. -/
lemma rectangular_fineKernel_abs_bound (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 1 ≤ J) (x y : Cov d) :
    |fineKernel d h J x y| ≤ (Fintype.card (FineIdx d J):ℝ) *
      (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)^2 := by
  unfold fineKernel
  calc
    _ ≤ ∑ z : FineIdx d J, |fineBasis h J x z * fineBasis h J y z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : FineIdx d J, (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)^2 := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul, pow_two]
      exact mul_le_mul (fineBasis_abs_bound d h J hh hJ x z)
        (fineBasis_abs_bound d h J hh hJ y z) (abs_nonneg _) (by positivity)
    _ = _ := by simp

/-- The localization weight is nonnegative and at most its fixed height.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the rectangular loc weight bounds conclusion](goal) holds. -/
lemma rectangular_locWeight_bounds (d : ℕ) (h : ℝ) (hh : 0 < h) (x : Cov d) :
    0 ≤ locWeight h x ∧ locWeight h x ≤ h^(-(d:ℝ)) := by
  unfold locWeight
  split_ifs <;> constructor <;> first | exact le_refl _ | positivity

/-- A bounded fine kernel remains square integrable with either one or two localization weights.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input X](hyp:X), [the specified input Y](hyp:Y), [the specified input hX](hyp:hX), [the specified input hY](hyp:hY), [the specified input a](hyp:a), [the specified input b](hyp:b), [the rectangular weighted kernel mem lp conclusion](goal) holds. -/
lemma rectangular_weighted_kernel_memLp {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J)
    (X : W → Cov d) (Y : Z → Cov d) (hX : Measurable X) (hY : Measurable Y)
    (a b : ℕ) :
    MemLp (fun p : W × Z => (locWeight h (X p.1))^a *
      (locWeight h (Y p.2))^b * fineKernel d h J (X p.1) (Y p.2)) 2 (μ.prod ν) := by
  apply (memLp_top_of_bound (by fun_prop)
    ((h^(-(d:ℝ)))^a * (h^(-(d:ℝ)))^b * (Fintype.card (FineIdx d J):ℝ) *
      (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)^2) ?_).mono_exponent (by simp)
  filter_upwards [] with p
  simp only [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (rectangular_locWeight_bounds d h hh _).1]
  calc
    _ ≤ (h^(-(d:ℝ)))^a * (h^(-(d:ℝ)))^b *
        ((Fintype.card (FineIdx d J):ℝ) * (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)^2) := by
      obtain ⟨hx0, hx⟩ := rectangular_locWeight_bounds d h hh (X p.1)
      obtain ⟨hy0, hy⟩ := rectangular_locWeight_bounds d h hh (Y p.2)
      gcongr <;> first | positivity | assumption | exact rectangular_fineKernel_abs_bound d h J hh hJ _ _
    _ = _ := by ring

/-- Product localization is obtained by applying the one-variable identity twice.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input F](hyp:F), [the specified input hfull](hyp:hfull), [the specified input hloc](hyp:hloc), [the rectangular product localization integral conclusion](goal) holds. -/
lemma rectangular_product_localization_integral (d : ℕ) (h : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (F : Cov d × Cov d → ℝ)
    (hfull : Integrable (fun p => locWeight h p.1 * locWeight h p.2 * F p)
      ((uniformLaw d).prod (uniformLaw d)))
    (hloc : Integrable F ((locLaw d h).prod (locLaw d h))) :
    (∫ p, locWeight h p.1 * locWeight h p.2 * F p
      ∂(uniformLaw d).prod (uniformLaw d)) =
      ∫ p, F p ∂(locLaw d h).prod (locLaw d h) := by
  letI : SFinite (uniformLaw d) := by unfold uniformLaw; infer_instance
  letI : SFinite (locLaw d h) := by unfold locLaw; infer_instance
  rw [integral_prod _ hfull]
  simp_rw [mul_assoc, integral_const_mul,
    uniformLaw_localization_integral d h hh hh']
  rw [integral_prod _ hloc]

/-- Under uniform design, the squared weighted kernel has exactly rank divided by squared volume.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the rectangular uniform kernel square integral conclusion](goal) holds. -/
lemma rectangular_uniform_kernel_square_integral (d : ℕ)
    [IsProbabilityMeasure (uniformLaw d)] (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) :
    (∫ p, (locWeight h p.1 * locWeight h p.2 * fineKernel d h J p.1 p.2)^2
      ∂(uniformLaw d).prod (uniformLaw d)) =
      (Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d) := by
  letI := localization_probability d h hh hh'
  have hsq (x : Cov d) : (locWeight h x)^2 = h^(-(d:ℝ))*locWeight h x := by
    unfold locWeight
    split_ifs <;> ring
  have heq (p : Cov d × Cov d) :
      (locWeight h p.1 * locWeight h p.2 * fineKernel d h J p.1 p.2)^2 =
        (h^(-(d:ℝ)))^2 *
          (locWeight h p.1 * locWeight h p.2 * (fineKernel d h J p.1 p.2)^2) := by
    rw [mul_pow, mul_pow, hsq, hsq]
    ring
  have hfull := (rectangular_weighted_kernel_memLp (uniformLaw d) (uniformLaw d)
    d h J hh hJ id id measurable_id measurable_id 1 1).integrable_sq
  have hi : Integrable (fun p : Cov d × Cov d => locWeight h p.1 * locWeight h p.2 *
      (fineKernel d h J p.1 p.2)^2) ((uniformLaw d).prod (uniformLaw d)) := by
    have hrewrite : (fun p : Cov d × Cov d => locWeight h p.1 * locWeight h p.2 *
        (fineKernel d h J p.1 p.2)^2) =
        (fun p => ((h^(-(d:ℝ)))^2)⁻¹ *
          (locWeight h p.1 * locWeight h p.2 * fineKernel d h J p.1 p.2)^2) := by
      funext p
      rw [heq]
      field_simp
    rw [hrewrite]
    simpa only [pow_one, id_eq] using hfull.const_mul (((h^(-(d:ℝ)))^2)⁻¹)
  have hlocal := (rectangular_weighted_kernel_memLp (locLaw d h) (locLaw d h)
    d h J hh hJ id id measurable_id measurable_id 0 0).integrable_sq
  simp only [pow_one, pow_zero, one_mul, id_eq] at hfull hlocal
  simp_rw [heq]
  rw [integral_const_mul, rectangular_product_localization_integral d h hh hh' _ hi hlocal,
    fineKernel_square_integral d h J hh hh' hJ]
  rw [Real.rpow_neg hh.le, Real.rpow_natCast, ← inv_pow, ← pow_mul]
  rw [Nat.mul_comm d 2]
  ring

/-- Independent uniform covariates retain the exact weighted-kernel energy under record maps.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input X](hyp:X), [the specified input Y](hyp:Y), [the specified input hX](hyp:hX), [the specified input hY](hyp:hY), [the uniform pushforward identities](hyp:hμ,hν), [the rectangular record kernel square integral conclusion](goal) holds. -/
lemma rectangular_record_kernel_square_integral {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (X : W → Cov d) (Y : Z → Cov d) (hX : Measurable X) (hY : Measurable Y)
    (hμ : μ.map X = uniformLaw d) (hν : ν.map Y = uniformLaw d) :
    (∫ p, (locWeight h (X p.1) * locWeight h (Y p.2) *
      fineKernel d h J (X p.1) (Y p.2))^2 ∂μ.prod ν) =
      (Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d) := by
  letI : IsProbabilityMeasure (uniformLaw d) := hμ ▸ Measure.isProbabilityMeasure_map hX.aemeasurable
  have hmap : (μ.prod ν).map (fun p : W × Z => (X p.1, Y p.2)) =
      (uniformLaw d).prod (uniformLaw d) := by
    change (μ.prod ν).map (Prod.map X Y) = _
    rw [← Measure.map_prod_map μ ν hX hY, hμ, hν]
  have hi := integral_map (show AEMeasurable (fun p : W × Z => (X p.1, Y p.2))
    (μ.prod ν) from (by fun_prop))
    (f := fun p : Cov d × Cov d =>
      (locWeight h p.1 * locWeight h p.2 * fineKernel d h J p.1 p.2)^2)
    (by fun_prop)
  rw [hmap] at hi
  rw [← hi]
  exact rectangular_uniform_kernel_square_integral d h J hh hh' hJ

/-- Locally bounded record features multiply kernel energy by their squared bounds.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input X](hyp:X), [the specified input Y](hyp:Y), [the specified input hX](hyp:hX), [the specified input hY](hyp:hY), [the uniform pushforward identities](hyp:hμ,hν), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input hfA](hyp:hfA), [the specified input hgB](hyp:hgB), [the rectangular marked kernel energy le conclusion](goal) holds. -/
lemma rectangular_marked_kernel_energy_le {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (X : W → Cov d) (Y : Z → Cov d) (hX : Measurable X) (hY : Measurable Y)
    (hμ : μ.map X = uniformLaw d) (hν : ν.map Y = uniformLaw d)
    (f : W → ℝ) (g : Z → ℝ) (hf : Measurable f) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∀ w, X w ∈ locCube d h → |f w| ≤ A)
    (hgB : ∀ z, Y z ∈ locCube d h → |g z| ≤ B) :
    MemLp (fun p : W × Z => locWeight h (X p.1) * locWeight h (Y p.2) *
      fineKernel d h J (X p.1) (Y p.2) * f p.1 * g p.2) 2 (μ.prod ν) ∧
    (∫ p, (locWeight h (X p.1) * locWeight h (Y p.2) *
      fineKernel d h J (X p.1) (Y p.2) * f p.1 * g p.2)^2 ∂μ.prod ν) ≤
      A^2 * B^2 * ((Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d)) := by
  let K := fun p : W × Z => locWeight h (X p.1) * locWeight h (Y p.2) *
    fineKernel d h J (X p.1) (Y p.2)
  let H := fun p : W × Z => K p * f p.1 * g p.2
  have hK : MemLp K 2 (μ.prod ν) := by
    simpa only [K, pow_one] using
      rectangular_weighted_kernel_memLp μ ν d h J hh hJ X Y hX hY 1 1
  have hbound (p : W × Z) : ‖H p‖ ≤ (A*B)*‖K p‖ := by
    by_cases hx : X p.1 ∈ locCube d h
    · by_cases hy : Y p.2 ∈ locCube d h
      · simp only [H, Real.norm_eq_abs, abs_mul]
        calc
          _ ≤ |K p| * A * B := mul_le_mul
            (mul_le_mul_of_nonneg_left (hfA p.1 hx) (abs_nonneg _)) (hgB p.2 hy)
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) hA)
          _ = _ := by ring
      · simp [H, K, locWeight, hy]
    · simp [H, K, locWeight, hx]
  have hH : MemLp H 2 (μ.prod ν) :=
    hK.of_le_mul (by dsimp [H, K]; fun_prop) (Filter.Eventually.of_forall hbound)
  refine ⟨hH, ?_⟩
  have he := rectangular_record_kernel_square_integral μ ν d h J hh hh' hJ X Y hX hY hμ hν
  change (∫ p, (H p)^2 ∂μ.prod ν) ≤ _
  calc
    _ ≤ ∫ p, (A*B)^2 * (K p)^2 ∂μ.prod ν := by
      apply integral_mono hH.integrable_sq (hK.integrable_sq.const_mul _)
      intro p
      have hb := hbound p
      simp only [Real.norm_eq_abs] at hb
      have hs := mul_self_le_mul_self (abs_nonneg (H p)) hb
      simpa only [← pow_two, mul_pow, sq_abs] using hs
    _ = _ := by rw [integral_const_mul, he]; ring

/-- Primitive-class membership fixes the actual covariate marginal, regardless of raw versions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the rectangular primitive uniform design conclusion](goal) holds. -/
lemma rectangular_primitive_uniform_design {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) : UniformDesign P := by
  have hs := canonicalLaw_spec P hP
  change P.law.map Prod.fst = uniformLaw d
  rw [← hs.1]
  exact hs.2.1

/-- A treatment-role record has uniform covariates.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the rectangular xa law covariates conclusion](goal) holds. -/
lemma rectangular_xaLaw_covariates {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    (xaLaw P).map Prod.fst = uniformLaw d := by
  unfold xaLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact rectangular_primitive_uniform_design P hP

/-- An outcome-role record has uniform covariates.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the rectangular obs law covariates conclusion](goal) holds. -/
lemma rectangular_obsLaw_covariates {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    (obsLaw P).map Prod.fst = uniformLaw d := by
  unfold obsLaw
  rw [Measure.map_map (by fun_prop) population_measurable_observed]
  exact rectangular_primitive_uniform_design P hP

/-- Binary record marks have absolute value at most one.  Given [the specified input a](hyp:a), [the rectangular bit abs le one conclusion](goal) holds. -/
lemma rectangular_bit_abs_le_one (a : Bool) : |bit a| ≤ 1 := by
  cases a <;> norm_num [bit]

/-- The vector correction kernel has second moment at most a dimension constant times rank over squared volume.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the rectangular r kernel energy conclusion](goal) holds. -/
lemma rectangular_r_kernel_energy {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (u : PolyIdx d) :
    (∫ p : (Cov d × Bool) × (Cov d × Bool × Bool),
      (locWeight h p.1.1 * locWeight h p.2.1 * coarseBasis h p.1.1 u *
        bit p.1.2 * fineKernel d h J p.1.1 p.2.1 * bit p.2.2.2)^2
      ∂(xaLaw P).prod (obsLaw P)) ≤
      ((4:ℝ)^d)^2 * ((Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d)) := by
  letI := xaLaw_probability P
  letI := obsLaw_probability P
  have he := rectangular_marked_kernel_energy_le (xaLaw P) (obsLaw P) d h J hh hh' hJ
    Prod.fst Prod.fst measurable_fst measurable_fst
    (rectangular_xaLaw_covariates P hP) (rectangular_obsLaw_covariates P hP)
    (fun w => coarseBasis h w.1 u * bit w.2) (fun z => bit z.2.2)
    (by fun_prop) (by fun_prop) ((4:ℝ)^d) 1 (by positivity) zero_le_one
    (fun w hw => by
      rw [abs_mul]
      simpa using mul_le_mul (coarseBasis_abs_bound d h hh w.1 hw u)
        (rectangular_bit_abs_le_one w.2) (abs_nonneg _) (by positivity))
    (fun z _ => rectangular_bit_abs_le_one z.2.2)
  convert he.2 using 1
  · congr 1
    funext p
    congr 1
    ring
  · ring

/-- The raw Gram correction kernel has the same rank-over-squared-volume order.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the rectangular q kernel energy conclusion](goal) holds. -/
lemma rectangular_q_kernel_energy {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (u v : PolyIdx d) :
    (∫ p : (Cov d × Bool) × (Cov d × Bool × Bool),
      (locWeight h p.1.1 * locWeight h p.2.1 * coarseBasis h p.1.1 u *
        coarseBasis h p.2.1 v * bit p.1.2 * bit p.2.2.1 *
        fineKernel d h J p.1.1 p.2.1)^2 ∂(xaLaw P).prod (obsLaw P)) ≤
      ((4:ℝ)^d)^4 * ((Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d / h^(2*d)) := by
  letI := xaLaw_probability P
  letI := obsLaw_probability P
  have hb (a : PolyIdx d) (x : Cov d) (hx : x ∈ locCube d h) (b : Bool) :
      |coarseBasis h x a * bit b| ≤ (4:ℝ)^d := by
    rw [abs_mul]
    simpa using mul_le_mul (coarseBasis_abs_bound d h hh x hx a)
      (rectangular_bit_abs_le_one b) (abs_nonneg _) (by positivity)
  have he := rectangular_marked_kernel_energy_le (xaLaw P) (obsLaw P) d h J hh hh' hJ
    Prod.fst Prod.fst measurable_fst measurable_fst
    (rectangular_xaLaw_covariates P hP) (rectangular_obsLaw_covariates P hP)
    (fun w => coarseBasis h w.1 u * bit w.2) (fun z => coarseBasis h z.1 v * bit z.2.1)
    (by fun_prop) (by fun_prop) ((4:ℝ)^d) ((4:ℝ)^d) (by positivity) (by positivity)
    (fun w hw => hb u w.1 hw w.2) (fun z hz => hb v z.1 hz z.2.1)
  convert he.2 using 1
  · congr 1
    funext p
    congr 1
    ring
  · ring

/-- A locally bounded record feature has a globally bounded weighted extension.  Given [the specified input W](hyp:W), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the rectangular localized mark mem lp top conclusion](goal) holds. -/
lemma rectangular_localized_mark_memLp_top {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsFiniteMeasure μ] (d : ℕ) (h : ℝ) (hh : 0 < h)
    (X : W → Cov d) (hX : Measurable X) (f : W → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hfB : ∀ w, X w ∈ locCube d h → |f w| ≤ B) :
    MemLp (fun w => locWeight h (X w) * f w) ∞ μ := by
  apply memLp_top_of_bound (by fun_prop) (h^(-(d:ℝ))*B)
  filter_upwards [] with w
  change |locWeight h (X w) * f w| ≤ _
  rw [abs_mul, abs_of_nonneg (rectangular_locWeight_bounds d h hh _).1]
  by_cases hx : X w ∈ locCube d h
  · exact mul_le_mul (rectangular_locWeight_bounds d h hh _).2 (hfB w hx)
      (abs_nonneg _) (Real.rpow_nonneg hh.le _)
  · simp only [locWeight, if_neg hx, zero_mul]
    positivity

/-- Bounded record marks and uniform design give a resolution-independent conditional kernel bound.  Given [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input Y](hyp:Y), [the specified input hY](hyp:hY), [its uniform pushforward identity](hyp:hν), [the specified input g](hyp:g), [the specified input hg](hyp:hg), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hgB](hyp:hgB), [the specified input x](hyp:x), [the rectangular kernel slice abs le conclusion](goal) holds. -/
lemma rectangular_kernel_slice_abs_le {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsProbabilityMeasure ν] (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (Y : Z → Cov d) (hY : Measurable Y) (hν : ν.map Y = uniformLaw d)
    (g : Z → ℝ) (hg : Measurable g) (B : ℝ) (hB : 0 ≤ B)
    (hgB : ∀ z, Y z ∈ locCube d h → |g z| ≤ B) (x : Cov d) :
    |∫ z, locWeight h (Y z) * fineKernel d h J x (Y z) * g z ∂ν| ≤
      B * ((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2) := by
  let M := (Fintype.card (FineIdx d J):ℝ) * (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hkernel : ∀ y, |fineKernel d h J x y| ≤ M :=
    rectangular_fineKernel_abs_bound d h J hh hJ x
  have hi : Integrable (fun z => locWeight h (Y z) *
      fineKernel d h J x (Y z) * g z) ν := by
    have hm := rectangular_localized_mark_memLp_top ν d h hh Y hY
      (fun z => fineKernel d h J x (Y z) * g z) (by fun_prop) (M*B)
      (mul_nonneg hM hB) (fun z hz => by
        rw [abs_mul]
        exact mul_le_mul (hkernel _) (hgB z hz) (abs_nonneg _) hM)
    simpa only [mul_assoc] using hm.integrable (by simp)
  have hj : Integrable (fun z => B * (locWeight h (Y z) * |fineKernel d h J x (Y z)|)) ν := by
    exact (rectangular_localized_mark_memLp_top ν d h hh Y hY
      (fun z => |fineKernel d h J x (Y z)|) (by fun_prop) M hM
      (fun z _ => by simpa only [abs_abs] using hkernel (Y z))).integrable (by simp) |>.const_mul B
  have hpoint (z : Z) : |locWeight h (Y z) * fineKernel d h J x (Y z) * g z| ≤
      B * (locWeight h (Y z) * |fineKernel d h J x (Y z)|) := by
    by_cases hz : Y z ∈ locCube d h
    · rw [abs_mul, abs_mul, abs_of_nonneg (rectangular_locWeight_bounds d h hh _).1]
      calc
        _ ≤ (locWeight h (Y z) * |fineKernel d h J x (Y z)|) * B :=
          mul_le_mul_of_nonneg_left (hgB z hz) (by
            exact mul_nonneg (rectangular_locWeight_bounds d h hh _).1 (abs_nonneg _))
        _ = _ := by ring
    · simp [locWeight, hz]
  have he : (∫ z, locWeight h (Y z) * |fineKernel d h J x (Y z)| ∂ν) =
      ∫ y, |fineKernel d h J x y| ∂locLaw d h := by
    have hm := integral_map (μ := ν) hY.aemeasurable
      (f := fun y => locWeight h y * |fineKernel d h J x y|) (by fun_prop)
    rw [hν, uniformLaw_localization_integral d h hh hh'] at hm
    exact hm.symm
  calc
    _ ≤ ∫ z, |locWeight h (Y z) * fineKernel d h J x (Y z) * g z| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, B * (locWeight h (Y z) * |fineKernel d h J x (Y z)|) ∂ν :=
      integral_mono hi.abs hj hpoint
    _ = B * (∫ y, |fineKernel d h J x y| ∂locLaw d h) := by rw [integral_const_mul, he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (fineKernel_abs_row_bound d h J hh hh' hJ x) hB

/-- The squared localization weight integrates to inverse localization volume under uniform design.  Given [the specified input W](hyp:W), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [its uniform pushforward identity](hyp:hμ), [the rectangular record loc weight square integral conclusion](goal) holds. -/
lemma rectangular_record_locWeight_square_integral {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] (d : ℕ) (h : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (X : W → Cov d) (hX : Measurable X)
    (hμ : μ.map X = uniformLaw d) :
    (∫ w, (locWeight h (X w))^2 ∂μ) = 1/h^d := by
  letI := localization_probability d h hh hh'
  have he (x : Cov d) : (locWeight h x)^2 = h^(-(d:ℝ))*locWeight h x := by
    unfold locWeight
    split_ifs <;> ring
  have hm := integral_map (μ := μ) hX.aemeasurable (f := fun x : Cov d => (locWeight h x)^2) (by fun_prop)
  rw [hμ] at hm
  rw [← hm]
  simp_rw [he]
  rw [integral_const_mul]
  have hw := uniformLaw_localization_integral d h hh hh' (fun _ => (1:ℝ))
  simp only [mul_one] at hw
  simp at hw
  rw [hw, mul_one, Real.rpow_neg hh.le, Real.rpow_natCast, one_div]

/-- First conditional integration has second moment of inverse-volume order, with no rank factor.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input X](hyp:X), [the specified input Y](hyp:Y), [the specified input hX](hyp:hX), [the specified input hY](hyp:hY), [the uniform pushforward identities](hyp:hμ,hν), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input hfA](hyp:hfA), [the specified input hgB](hyp:hgB), [the rectangular marked kernel row energy conclusion](goal) holds. -/
lemma rectangular_marked_kernel_row_energy {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (X : W → Cov d) (Y : Z → Cov d) (hX : Measurable X) (hY : Measurable Y)
    (hμ : μ.map X = uniformLaw d) (hν : ν.map Y = uniformLaw d)
    (f : W → ℝ) (g : Z → ℝ) (hf : Measurable f) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∀ w, X w ∈ locCube d h → |f w| ≤ A)
    (hgB : ∀ z, Y z ∈ locCube d h → |g z| ≤ B) :
    (∫ w, (∫ z, locWeight h (X w) * locWeight h (Y z) *
      fineKernel d h J (X w) (Y z) * f w * g z ∂ν)^2 ∂μ) ≤
      (A * B * ((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2))^2 / h^d := by
  let D := (Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2
  let F := fun w => ∫ z, locWeight h (X w) * locWeight h (Y z) *
    fineKernel d h J (X w) (Y z) * f w * g z ∂ν
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hF : MemLp F 2 μ := rectangular_memLp_mean μ ν _
    (rectangular_marked_kernel_energy_le μ ν d h J hh hh' hJ X Y hX hY hμ hν
      f g hf hg A B hA hB hfA hgB).1
  have hw : MemLp (fun w => locWeight h (X w)) ∞ μ := by
    simpa only [mul_one] using rectangular_localized_mark_memLp_top μ d h hh X hX
      (fun _ => 1) measurable_const 1 zero_le_one (fun _ _ => by norm_num)
  have hbound (w : W) : |F w| ≤ (A*B*D)*locWeight h (X w) := by
    have he : F w = (locWeight h (X w)*f w) *
        (∫ z, locWeight h (Y z) * fineKernel d h J (X w) (Y z) * g z ∂ν) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    rw [he, abs_mul, abs_mul, abs_of_nonneg (rectangular_locWeight_bounds d h hh _).1]
    by_cases hx : X w ∈ locCube d h
    · calc
        _ ≤ (locWeight h (X w)*A)*(B*D) := mul_le_mul
          (mul_le_mul_of_nonneg_left (hfA w hx) (rectangular_locWeight_bounds d h hh _).1)
          (rectangular_kernel_slice_abs_le ν d h J hh hh' hJ Y hY hν g hg B hB hgB (X w))
          (abs_nonneg _) (mul_nonneg (rectangular_locWeight_bounds d h hh _).1 hA)
        _ = _ := by ring
    · simp [locWeight, hx]
  calc
    _ ≤ ∫ w, (A*B*D)^2*(locWeight h (X w))^2 ∂μ := by
      apply integral_mono hF.integrable_sq
        ((hw.mono_exponent (by simp : (2:ℝ≥0∞) ≤ ∞)).integrable_sq.const_mul _)
      intro w
      have hb := mul_self_le_mul_self (abs_nonneg (F w)) (hbound w)
      simpa only [← pow_two, mul_pow, sq_abs] using hb
    _ = _ := by
      rw [integral_const_mul, rectangular_record_locWeight_square_integral μ d h hh hh' X hX hμ]
      dsimp [D]
      ring

/-- The finite projection kernel is symmetric in its covariate arguments.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input x](hyp:x), [the specified input y](hyp:y), [the rectangular fine kernel symmetric conclusion](goal) holds. -/
lemma rectangular_fineKernel_symmetric (d : ℕ) (h : ℝ) (J : ℕ) (x y : Cov d) :
    fineKernel d h J x y = fineKernel d h J y x := by
  unfold fineKernel
  apply Finset.sum_congr rfl
  intro z _
  exact mul_comm _ _

/-- Reversing the independent roles gives the same inverse-volume bound for the second conditional integration.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input X](hyp:X), [the specified input Y](hyp:Y), [the specified input hX](hyp:hX), [the specified input hY](hyp:hY), [the uniform pushforward identities](hyp:hμ,hν), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input hfA](hyp:hfA), [the specified input hgB](hyp:hgB), [the rectangular marked kernel column energy conclusion](goal) holds. -/
lemma rectangular_marked_kernel_column_energy {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (X : W → Cov d) (Y : Z → Cov d) (hX : Measurable X) (hY : Measurable Y)
    (hμ : μ.map X = uniformLaw d) (hν : ν.map Y = uniformLaw d)
    (f : W → ℝ) (g : Z → ℝ) (hf : Measurable f) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∀ w, X w ∈ locCube d h → |f w| ≤ A)
    (hgB : ∀ z, Y z ∈ locCube d h → |g z| ≤ B) :
    (∫ z, (∫ w, locWeight h (X w) * locWeight h (Y z) *
      fineKernel d h J (X w) (Y z) * f w * g z ∂μ)^2 ∂ν) ≤
      (A * B * ((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2))^2 / h^d := by
  have he := rectangular_marked_kernel_row_energy ν μ d h J hh hh' hJ Y X hY hX hν hμ
    g f hg hf B A hB hA hgB hfA
  convert he using 1
  · congr 1
    funext z
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    rw [rectangular_fineKernel_symmetric d h J (X w) (Y z)]
    ring
  · ring

/-- The roadmap's two conditional energies and kernel rank give the full variance order for each rectangular correction.  Given [the specified input W](hyp:W), [the specified input Z](hyp:Z), [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input X](hyp:X), [the specified input Y](hyp:Y), [the specified input hX](hyp:hX), [the specified input hY](hyp:hY), [the uniform pushforward identities](hyp:hμ,hν), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input hfA](hyp:hfA), [the specified input hgB](hyp:hgB), [the rectangular marked kernel variance bound conclusion](goal) holds. -/
lemma rectangular_marked_kernel_variance_bound {W Z : Type*}
    [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure W) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (X : W → Cov d) (Y : Z → Cov d) (hX : Measurable X) (hY : Measurable Y)
    (hμ : μ.map X = uniformLaw d) (hν : ν.map Y = uniformLaw d)
    (f : W → ℝ) (g : Z → ℝ) (hf : Measurable f) (hg : Measurable g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∀ w, X w ∈ locCube d h → |f w| ≤ A)
    (hgB : ∀ z, Y z ∈ locCube d h → |g z| ≤ B) :
    let H := fun p : W × Z => locWeight h (X p.1) * locWeight h (Y p.2) *
      fineKernel d h J (X p.1) (Y p.2) * f p.1 * g p.2
    let C := (A*B)^2 * (((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2)^2+1)
    (∫ D, (((treatmentCount n m:ℝ)*(outcomeCount n:ℝ))⁻¹ *
      ∑ i : Fin (treatmentCount n m), ∑ j : Fin (outcomeCount n),
      H (D.1 i,D.2 j)-(∫ p, H p ∂μ.prod ν))^2
      ∂(Measure.pi (fun _ : Fin (treatmentCount n m) => μ)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => ν))) ≤
      6*C*(1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
        ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
  dsimp only
  let D := (Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2
  let C := (A*B)^2*(D^2+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsmall : (A*B*D)^2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (A*B)]
  have hbase : A^2*B^2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (A*B*D)]
  have hk : 0 ≤ (Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d := by positivity
  have hr := rectangular_marked_kernel_row_energy μ ν d h J hh hh' hJ X Y hX hY hμ hν
    f g hf hg A B hA hB hfA hgB
  have hc := rectangular_marked_kernel_column_energy μ ν d h J hh hh' hJ X Y hX hY hμ hν
    f g hf hg A B hA hB hfA hgB
  obtain ⟨hH, he⟩ := rectangular_marked_kernel_energy_le μ ν d h J hh hh' hJ X Y hX hY hμ hν
    f g hf hg A B hA hB hfA hgB
  apply rectangular_sampling_from_kernel_energies μ ν n m d hn h C _ hh hC hk _ hH
  · exact hr.trans (div_le_div_of_nonneg_right hsmall (by positivity))
  · exact hc.trans (div_le_div_of_nonneg_right hsmall (by positivity))
  · calc
      _ ≤ _ := he
      _ = (A^2*B^2) * ((Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d) / h^(2*d) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbase hk) (by positivity)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
