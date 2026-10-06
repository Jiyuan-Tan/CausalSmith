module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationEntries

/-!
# Helpers/PopulationGram

Two-channel point-CATE annotation frontier: Helpers/PopulationGram
constructions and obligations.
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


/-- The squared norm of a finite orthonormal expansion is the squared coefficient norm.  Given [the specified input b](hyp:b), [the specified input hb](hyp:hb), [the specified input hortho](hyp:hortho), [the specified input v](hyp:v), [the finite orthonormal square norm conclusion](goal) holds. -/
lemma finite_orthonormal_square_norm {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (b : ι → Ω → ℝ) (hb : ∀ i, MemLp (b i) 2 μ)
    (hortho : ∀ i j, (∫ x, b i x * b j x ∂μ) = if i = j then 1 else 0)
    (v : ι → ℝ) :
    (∫ x, (∑ i, b i x * v i)^2 ∂μ) = ∑ i, (v i)^2 := by
  classical
  have hexpand (x : Ω) : (∑ i, b i x * v i)^2 =
      ∑ i, ∑ j, (b i x * b j x) * (v i * v j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum (f := fun i x => ∑ j, (b i x * b j x) * (v i * v j))
    Finset.univ (fun i _ => integrable_finsetSum _
      (fun j _ => ((hb i).integrable_mul (hb j)).mul_const (v i * v j)))]
  congr 1
  funext i
  rw [integral_finsetSum (f := fun j x => (b i x * b j x) * (v i * v j))
    Finset.univ (fun j _ => ((hb i).integrable_mul (hb j)).mul_const (v i * v j))]
  simp_rw [integral_mul_const, hortho]
  simp [pow_two]

/-- Coarse orthonormality supplies square integrability of each polynomial basis entry.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input u](hyp:u), [the coarse basis mem lp conclusion](goal) holds. -/
lemma coarseBasis_memLp (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (u : PolyIdx d) : MemLp (fun x => coarseBasis h x u) 2 (locLaw d h) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  by_contra hi
  have hz := integral_undef hi
  have ho := coarse_orthonormal d h hh hh' u u
  simp only [ite_true, ← pow_two] at ho
  rw [hz] at ho
  norm_num at ho

/-- Polynomial coefficient vectors define square-integrable localization polynomials.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input v](hyp:v), [the pv mem lp conclusion](goal) holds. -/
lemma pv_memLp (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (v : PolyIdx d → ℝ) : MemLp (pv h v) 2 (locLaw d h) := by
  exact memLp_finsetSum _ (fun u _ => (coarseBasis_memLp d h hh hh' u).mul_const (v u))

/-- Coarse orthonormality identifies polynomial and coefficient squared norms.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input v](hyp:v), [the pv square norm conclusion](goal) holds. -/
lemma pv_square_norm (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (v : PolyIdx d → ℝ) : (∫ x, (pv h v x)^2 ∂locLaw d h) = ∑ u, (v u)^2 := by
  exact finite_orthonormal_square_norm (locLaw d h) (fun u x => coarseBasis h x u)
    (coarseBasis_memLp d h hh hh') (fun i j => by
      have ho := coarse_orthonormal d h hh hh' i j
      by_cases hij : i = j
      · simp only [if_pos hij] at ho ⊢; exact ho
      · simp only [if_neg hij] at ho ⊢; exact ho) v

/-- Overlap at level eps bounds the weighted squared integral below by eps·(1 − eps) times its norm.  Given [the specified input μ](hyp:μ), [the specified input e](hyp:e), [the specified input f](hyp:f), [the overlap level eps](hyp:eps), [its nonnegativity](hyp:heps), [the specified input he](hyp:he), [the specified input hf](hyp:hf), [the specified input hoverlap](hyp:hoverlap), [the overlap weighted square lower conclusion](goal) holds. -/
lemma overlap_weighted_square_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (e f : Ω → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (he : AEMeasurable e μ) (hf : MemLp f 2 μ)
    (hoverlap : ∀ᵐ x ∂μ, eps ≤ e x ∧ e x ≤ 1 - eps) :
    eps * (1 - eps) * (∫ x, (f x)^2 ∂μ) ≤
      ∫ x, e x * (1-e x) * (f x)^2 ∂μ := by
  have hweight : ∀ᵐ x ∂μ, eps * (1 - eps) ≤ e x * (1-e x) ∧
      e x * (1-e x) ≤ 1 ∧ 0 ≤ e x * (1-e x) := by
    filter_upwards [hoverlap] with x hx
    have hprod := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
    have h0 : 0 ≤ e x := le_trans heps hx.1
    have h1 : 0 ≤ 1 - e x := by linarith [hx.2]
    refine ⟨by nlinarith, by nlinarith [sq_nonneg (e x - 1/2)], mul_nonneg h0 h1⟩
  have hi : Integrable (fun x => e x * (1-e x) * (f x)^2) μ := by
    apply hf.integrable_sq.mono'
    · exact (he.aestronglyMeasurable.mul
        (aestronglyMeasurable_const.sub he.aestronglyMeasurable)).mul
        (hf.aestronglyMeasurable.pow 2)
    · filter_upwards [hweight] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.2.2 (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) hx.2.1
  have hm := integral_mono_ae (hf.integrable_sq.const_mul (eps * (1 - eps))) hi
    (by
      filter_upwards [hweight] with x hx
      exact mul_le_mul_of_nonneg_right hx.1 (sq_nonneg _))
  rwa [integral_const_mul] at hm

/-- The overlap contribution and the projection residual give the deterministic positivity bound.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input e](hyp:e), [the specified input f](hyp:f), [the specified input he](hyp:he), [the specified input hf](hyp:hf), [the specified input hef](hyp:hef), [the specified input hoverlap](hyp:hoverlap), [the overlap level eps](hyp:eps), [the projection overlap lower conclusion](goal) holds. -/
lemma projection_overlap_lower (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (e f : Cov d → ℝ) (eps : ℝ) (heps : 0 ≤ eps) (he : AEMeasurable e (locLaw d h))
    (hf : MemLp f 2 (locLaw d h))
    (hef : MemLp (fun x => e x * f x) 2 (locLaw d h))
    (hoverlap : ∀ᵐ x ∂locLaw d h, eps ≤ e x ∧ e x ≤ 1 - eps) :
    (∫ x, (e x * f x)^2 ∂locLaw d h) =
      (∫ x, (projOp d h J (fun y => e y * f y) x)^2 ∂locLaw d h) +
      (∫ x, (e x * f x - projOp d h J (fun y => e y * f y) x)^2 ∂locLaw d h) ∧
    eps * (1 - eps) * (∫ x, (f x)^2 ∂locLaw d h) ≤
      (∫ x, e x * (1-e x) * (f x)^2 ∂locLaw d h) +
      (∫ x, (e x * f x - projOp d h J (fun y => e y * f y) x)^2 ∂locLaw d h) := by
  refine ⟨projection_pythagoras d h J hh hh' hJ _ hef, ?_⟩
  exact (overlap_weighted_square_lower (locLaw d h) e f eps heps he hf hoverlap).trans
    (le_add_of_nonneg_right (integral_nonneg (fun x => sq_nonneg _)))

/-- Every admissible localization box lies inside the design cube.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh'](hyp:hh'), [the loc cube subset cube conclusion](goal) holds. -/
lemma locCube_subset_cube (d : ℕ) (h : ℝ) (hh' : h ≤ 1/2) :
    locCube d h ⊆ cube d := by
  intro x hx i
  have hxi := hx i
  constructor <;> linarith [hxi.1, hxi.2]

/-- For [a primitive law P](hyp:P) [in the model class](hyp:hP) at [overlap level eps](hyp:eps), [the designated propensity is Borel on the whole covariate space](goal). -/
@[fun_prop] lemma measurable_designatedPropensity {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    Measurable (designatedPropensity P hP) := by
  unfold designatedPropensity
  have hc : MeasurableSet (cube d) := by
    unfold cube
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_Icc.preimage (by fun_prop)
  exact Measurable.ite hc (canonicalLaw P hP).measurable_e measurable_const

/-- Localization inherits the overlap interval from primitive-class membership.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh'](hyp:hh'), [the designated propensity overlap loc law conclusion](goal) holds. -/
lemma designatedPropensity_overlap_locLaw {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh' : h ≤ 1/2) :
    ∀ᵐ x ∂locLaw d h, eps ≤ designatedPropensity P hP x ∧
      designatedPropensity P hP x ≤ 1 - eps := by
  unfold locLaw
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (isClosed_locCube d h).measurableSet] with x hx
  have hc := locCube_subset_cube d h hh' hx
  simpa only [designatedPropensity, if_pos hc] using
    (canonicalLaw_spec P hP).2.2.2.1.2 x hc

/-- The deterministic population expression has the claimed coefficient lower bound.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input v](hyp:v), [the population expression positivity conclusion](goal) holds. -/
lemma population_expression_positivity {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) (J : ℕ) (v : PolyIdx d → ℝ) :
    eps * (1 - eps) * (∑ u, (v u)^2) ≤
      (∫ x, designatedPropensity P hP x * (1-designatedPropensity P hP x) *
        (pv h v x)^2 ∂locLaw d h) +
      (∫ x, (designatedPropensity P hP x * pv h v x -
        projOp d h J (fun y => designatedPropensity P hP y * pv h v y) x)^2 ∂locLaw d h) := by
  rw [← pv_square_norm d h hh hh' v]
  exact (overlap_weighted_square_lower (locLaw d h) _ _ eps hP.eps_pos.le
    (measurable_designatedPropensity P hP).aemeasurable (pv_memLp d h hh hh' v)
    (designatedPropensity_overlap_locLaw P hP h hh')).trans
      (le_add_of_nonneg_right (integral_nonneg (fun x => sq_nonneg _)))

/-- A bounded propensity preserves square integrability under localization.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh'](hyp:hh'), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the designated propensity mul mem lp conclusion](goal) holds. -/
lemma designatedPropensity_mul_memLp {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh' : h ≤ 1/2) (f : Cov d → ℝ)
    (hf : MemLp f 2 (locLaw d h)) :
    MemLp (fun x => designatedPropensity P hP x * f x) 2 (locLaw d h) := by
  apply hf.of_le_mul ((measurable_designatedPropensity P hP).aestronglyMeasurable.mul
    hf.aestronglyMeasurable) (c := 1)
  filter_upwards [designatedPropensity_overlap_locLaw P hP h hh'] with x hx
  change ‖designatedPropensity P hP x * f x‖ ≤ 1 * ‖f x‖
  rw [norm_mul, Real.norm_eq_abs (designatedPropensity P hP x),
    abs_of_nonneg (by linarith [hx.1, hP.eps_pos]), one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hx.2, hP.eps_pos])

/-- The first population energy is integrable because overlap bounds its multiplier.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh'](hyp:hh'), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the designated propensity square integrable conclusion](goal) holds. -/
lemma designatedPropensity_square_integrable {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh' : h ≤ 1/2) (f : Cov d → ℝ)
    (hf : MemLp f 2 (locLaw d h)) :
    Integrable (fun x => designatedPropensity P hP x * (f x)^2) (locLaw d h) := by
  apply hf.integrable_sq.mono'
  · exact (measurable_designatedPropensity P hP).aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.pow 2)
  · filter_upwards [designatedPropensity_overlap_locLaw P hP h hh'] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hx.1, hP.eps_pos]) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (by linarith [hx.2, hP.eps_pos])

/-- Pythagoras turns the population first energy minus the projected energy into
an overlap energy plus the nonnegative projection residual.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the population projection energy identity conclusion](goal) holds. -/
lemma population_projection_energy_identity {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) (J : ℕ) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) :
    (∫ x, designatedPropensity P hP x * (f x)^2 ∂locLaw d h) -
      (∫ x, (projOp d h J (fun y => designatedPropensity P hP y * f y) x)^2 ∂locLaw d h) =
    (∫ x, designatedPropensity P hP x * (1-designatedPropensity P hP x) *
      (f x)^2 ∂locLaw d h) +
      (∫ x, (designatedPropensity P hP x * f x -
        projOp d h J (fun y => designatedPropensity P hP y * f y) x)^2 ∂locLaw d h) := by
  have hef := designatedPropensity_mul_memLp P hP h hh' f hf
  have hi := designatedPropensity_square_integrable P hP h hh' f hf
  have hpyth := projection_pythagoras d h J hh hh' hJ _ hef
  have hsplit : (∫ x, designatedPropensity P hP x * (1-designatedPropensity P hP x) *
      (f x)^2 ∂locLaw d h) =
      (∫ x, designatedPropensity P hP x * (f x)^2 ∂locLaw d h) -
      (∫ x, (designatedPropensity P hP x * f x)^2 ∂locLaw d h) := by
    simp_rw [show ∀ x, designatedPropensity P hP x * (1-designatedPropensity P hP x) *
      (f x)^2 = designatedPropensity P hP x * (f x)^2 -
        (designatedPropensity P hP x * f x)^2 by intro x; ring]
    exact integral_sub hi hef.integrable_sq
  rw [hsplit, hpyth]
  ring

/-- A finite bilinear integral matrix acts on coefficients by integrating the
product of their two finite expansions.  Given [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hab](hyp:hab), [the specified input v](hyp:v), [the finite bilinear integral quadratic conclusion](goal) holds. -/
lemma finite_bilinear_integral_quadratic {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (a b : ι → Ω → ℝ)
    (hab : ∀ i j, Integrable (fun x => a i x * b j x) μ) (v : ι → ℝ) :
    (∑ i, v i * (∑ j, (∫ x, a i x * b j x ∂μ) * v j)) =
      ∫ x, (∑ i, a i x * v i) * (∑ j, b j x * v j) ∂μ := by
  classical
  have hexpand (x : Ω) : (∑ i, a i x * v i) * (∑ j, b j x * v j) =
      ∑ i, ∑ j, (a i x * b j x) * (v i * v j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum (f := fun i x => ∑ j, (a i x * b j x) * (v i * v j))
    Finset.univ (fun i _ => integrable_finsetSum _
      (fun j _ => (hab i j).mul_const (v i * v j)))]
  simp_rw [integral_finsetSum Finset.univ
    (fun j _ => (hab _ j).mul_const (v _ * v j)), integral_mul_const, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The quadratic form of a finite coefficient Gram matrix is the sum of the
squared coefficient expansions.  Given [the specified input c](hyp:c), [the specified input v](hyp:v), [the finite coefficient gram quadratic conclusion](goal) holds. -/
lemma finite_coefficient_gram_quadratic {ι ζ : Type*} [Fintype ι] [Fintype ζ]
    (c : ζ → ι → ℝ) (v : ι → ℝ) :
    (∑ i, v i * (∑ j, (∑ z, c z i * c z j) * v j)) =
      ∑ z, (∑ i, c z i * v i)^2 := by
  classical
  simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Finite kernel integration expands the projection in its orthonormal basis.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input x](hyp:x), [the projection finite expansion conclusion](goal) holds. -/
lemma projection_finite_expansion (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) (x : Cov d) :
    projOp d h J f x = ∑ z : FineIdx d J, fineBasis h J x z *
      (∫ y, fineBasis h J y z * f y ∂locLaw d h) := by
  unfold projOp fineKernel
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum (f := fun z y => fineBasis h J x z * (fineBasis h J y z * f y))
    Finset.univ (fun z _ => ((fineBasis_memLp d h J hh hh' hJ z).integrable_mul hf).const_mul
      (fineBasis h J x z))]
  simp_rw [integral_const_mul]

/-- Projection energy is exactly the sum of squared orthonormal coefficients.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the projection square coefficients conclusion](goal) holds. -/
lemma projection_square_coefficients (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) :
    (∫ x, (projOp d h J f x)^2 ∂locLaw d h) =
      ∑ z : FineIdx d J, (∫ y, fineBasis h J y z * f y ∂locLaw d h)^2 := by
  simp_rw [projection_finite_expansion d h J hh hh' hJ f hf]
  exact finite_orthonormal_square_norm (locLaw d h) (fun z x => fineBasis h J x z)
    (fineBasis_memLp d h J hh hh' hJ) (fun i j => by
      have ho := fine_orthonormal d h J hh hh' hJ i j
      by_cases hij : i = j
      · simp only [if_pos hij] at ho ⊢; exact ho
      · simp only [if_neg hij] at ho ⊢; exact ho) _

/-- The weighted polynomial's fine coefficients are linear combinations of the
weighted coarse-basis coefficients.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input v](hyp:v), [the specified input z](hyp:z), [the weighted pv projection coefficient conclusion](goal) holds. -/
lemma weighted_pv_projection_coefficient {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) (J : ℕ) (hJ : 1 ≤ J)
    (v : PolyIdx d → ℝ) (z : FineIdx d J) :
    (∫ x, fineBasis h J x z * (designatedPropensity P hP x * pv h v x) ∂locLaw d h) =
      ∑ u, (∫ x, fineBasis h J x z *
        (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) * v u := by
  have hexpand (x : Cov d) : fineBasis h J x z * (designatedPropensity P hP x * pv h v x) =
      ∑ u, (fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u)) * v u := by
    simp only [pv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum (f := fun u x =>
    (fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u)) * v u)
    Finset.univ (fun u _ => ((fineBasis_memLp d h J hh hh' hJ z).integrable_mul
      (designatedPropensity_mul_memLp P hP h hh' _ (coarseBasis_memLp d h hh hh' u))).mul_const (v u))]
  simp_rw [integral_mul_const]

/-- The population coordinate formula implies the full quadratic projection
identity by finite expansion, without an empirical invertibility assumption.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input Q](hyp:Q), [the specified input hQ](hyp:hQ), [the specified input v](hyp:v), [the population gram quadratic of entries conclusion](goal) holds. -/
lemma population_gram_quadratic_of_entries {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) (J : ℕ) (hJ : 1 ≤ J)
    (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (hQ : ∀ u w, Q u w =
      (∫ x, coarseBasis h x u * (designatedPropensity P hP x * coarseBasis h x w) ∂locLaw d h) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x w) ∂locLaw d h))
    (v : PolyIdx d → ℝ) :
    (∑ u, v u * (Q.mulVec v) u) =
      (∫ x, designatedPropensity P hP x * (pv h v x)^2 ∂locLaw d h) -
      (∫ x, (projOp d h J (fun y => designatedPropensity P hP y * pv h v y) x)^2 ∂locLaw d h) := by
  classical
  simp only [Matrix.mulVec, dotProduct, hQ, sub_mul, Finset.sum_sub_distrib,
    mul_sub]
  rw [finite_bilinear_integral_quadratic]
  · rw [finite_coefficient_gram_quadratic, projection_square_coefficients d h J hh hh' hJ _
      (designatedPropensity_mul_memLp P hP h hh' _ (pv_memLp d h hh hh' v))]
    simp_rw [weighted_pv_projection_coefficient P hP h hh hh' J hJ v]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [pv, mul_assoc, ← Finset.mul_sum, pow_two]
    ring
  · intro u w
    exact (coarseBasis_memLp d h hh hh' u).integrable_mul
      (designatedPropensity_mul_memLp P hP h hh' _ (coarseBasis_memLp d h hh hh' w))

-- @node: lem:population-positivity
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input v](hyp:v), [the population positivity conclusion](goal) holds. -/
lemma population_positivity (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) (n m : ℕ) (hn : 2 ≤ n)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) (J : ℕ) (hJ : 1 ≤ J)
    (v : PolyIdx d → ℝ) :
    (∑ u, v u*((qPop P n m h J).mulVec v) u) =
      (∫ x, (designatedPropensity P hP) x*(1-(designatedPropensity P hP) x)*(pv h v x)^2 ∂locLaw d h) +
      (∫ x, ((designatedPropensity P hP) x*pv h v x-projOp d h J (fun y => (designatedPropensity P hP) y*pv h v y) x)^2 ∂locLaw d h) ∧
    eps*(1-eps)*(∑ u, v u^2) ≤ ∑ u, v u*((qPop P n m h J).mulVec v) u := by
  have hentries : ∀ u w, qPop P n m h J u w =
      (∫ x, coarseBasis h x u * (designatedPropensity P hP x * coarseBasis h x w) ∂locLaw d h) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x w) ∂locLaw d h) := by
    exact population_gram_entries P hP n m hn h hh hh' J hJ
  have hmoment := population_gram_quadratic_of_entries P hP h hh hh' J hJ _ hentries v
  have hidentity := hmoment.trans (population_projection_energy_identity P hP h hh hh' J hJ
    (pv h v) (pv_memLp d h hh hh' v))
  refine ⟨hidentity, ?_⟩
  rw [hidentity]
  exact population_expression_positivity P hP h hh hh' J v

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
