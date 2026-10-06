module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationGram
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularMomentBounds

/-! # Population outcome entries
Finite expansion of the response correction and independence of the two roles
identify the population vector using observed outcome moments. The terminal
response is the observed outcome, without an additional treatment mark.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 800000
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Localization makes any locally bounded Borel record statistic essentially bounded.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the population localized record mem lp conclusion](goal) holds. -/
lemma population_localized_record_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (h : ℝ) (hh : 0 < h)
    (X : Ω → Cov d) (hX : Measurable X) (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hfB : ∀ w, X w ∈ locCube d h → |f w| ≤ B) :
    MemLp (fun w => locWeight h (X w) * f w) ∞ μ := by
  apply memLp_top_of_bound (by fun_prop) (h^(-(d:ℝ))*B)
  filter_upwards [] with w
  change |locWeight h (X w) * f w| ≤ _
  by_cases hx : X w ∈ locCube d h
  · rw [locWeight, if_pos hx, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hh _)]
    exact mul_le_mul_of_nonneg_left (hfB w hx) (by positivity)
  · simp only [locWeight, if_neg hx, zero_mul, abs_zero]
    positivity

/-- Independent role averages of separated bounded features factor into their means.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hf2](hyp:hf2), [the specified input hg2](hyp:hg2), [the population rectangular observed product mean conclusion](goal) holds. -/
lemma population_rectangular_observed_product_mean {d n m : ℕ}
    (P : PrimitiveLaw d) (hn : 2 ≤ n)
    (f : Cov d × Bool → ℝ) (g : Cov d × Bool × Bool → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f ∞ (xaLaw P)) (hg2 : MemLp g ∞ (obsLaw P)) :
    Integrable (rectangularAverage (n := n) (m := m) (fun p => f p.1*g p.2))
      (experiment P n m) ∧
    (∫ w, rectangularAverage (n := n) (m := m) (fun p => f p.1*g p.2) w
      ∂experiment P n m) = (∫ z, f z ∂xaLaw P)*(∫ z, g z ∂obsLaw P) := by
  letI := xaLaw_probability P
  letI := obsLaw_probability P
  letI := population_experiment_probability P n m
  have hp2 : MemLp (fun p : (Cov d × Bool) × (Cov d × Bool × Bool) => f p.1*g p.2)
      2 ((xaLaw P).prod (obsLaw P)) := by
    convert
      ((hf2.comp_measurePreserving measurePreserving_fst).mul (r := ∞)
        (hg2.comp_measurePreserving measurePreserving_snd)).mono_exponent (show (2:ℝ≥0∞) ≤ ∞ from le_top) using 1
    ext p
    simp only [Function.comp_def, Pi.mul_apply]
    ring
  refine ⟨(rectangular_original_average_memLp P _ hp2).integrable
    (by norm_num), ?_⟩
  rw [rectangular_original_average_mean P hn _ (by fun_prop) hp2]
  exact integral_prod_mul f g

/-- The response correction is a sum of products of treatment and observed-outcome features.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [the r hat finite role expansion conclusion](goal) holds. -/
lemma rHat_finite_role_expansion {d n m : ℕ} (D : Dataset d n m)
    (h : ℝ) (J : ℕ) (u : PolyIdx d) :
    rHat D h J u =
      rectangularOutcomeAverage (fun z => locWeight h z.1 *
        (coarseBasis h z.1 u * bit z.2.1 * bit z.2.2)) (D,0) -
      ∑ z : FineIdx d J, rectangularAverage (fun p =>
        weightedTreatmentFeature h (fun x => coarseBasis h x u * fineBasis h J x z) p.1 *
        (locWeight h p.2.1 * (fineBasis h J p.2.1 z * bit p.2.2.2))) (D,0) := by
  classical
  rw [rHat_rectangular]
  unfold rectangularOutcomeAverage rectangularAverage weightedTreatmentFeature fineKernel
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring

/-- The population response vector has the finite projection-coefficient formula under the original-record experiment.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the population response observed entries conclusion](goal) holds. -/
lemma population_response_observed_entries {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (u : PolyIdx d) :
    rBar P n m h J u =
      (∫ w, locWeight h w.1 * (coarseBasis h w.1 u * bit w.2.1 * bit w.2.2) ∂obsLaw P) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ w, locWeight h w.1 * (fineBasis h J w.1 z * bit w.2.2) ∂obsLaw P) := by
  classical
  letI := xaLaw_probability P
  letI := obsLaw_probability P
  letI := population_experiment_probability P n m
  let F := fun w : Cov d × Bool × Bool =>
    locWeight h w.1 * (coarseBasis h w.1 u * bit w.2.1 * bit w.2.2)
  let f := fun z : FineIdx d J => weightedTreatmentFeature h
    (fun x => coarseBasis h x u * fineBasis h J x z)
  let g := fun z : FineIdx d J => fun w : Cov d × Bool × Bool =>
    locWeight h w.1 * (fineBasis h J w.1 z * bit w.2.2)
  have hF : MemLp F ∞ (obsLaw P) := by
    apply population_localized_record_memLp (obsLaw P) d h hh Prod.fst (by fun_prop)
      _ (by fun_prop) ((4:ℝ)^d) (by positivity)
    intro w hw
    rcases w with ⟨x,a,y⟩
    cases a <;> cases y <;> simp only [bit, if_true, Bool.false_eq_true, if_false,
      mul_one, mul_zero, abs_zero] <;> first | positivity | exact coarseBasis_abs_bound d h hh x hw u
  have hf (z) : MemLp (f z) ∞ (xaLaw P) := by
    unfold f weightedTreatmentFeature
    simp only [mul_assoc]
    apply population_localized_record_memLp (xaLaw P) d h hh Prod.fst (by fun_prop)
      _ (by fun_prop) ((4:ℝ)^d * (Real.sqrt ((J:ℝ)^d)*(4:ℝ)^d)) (by positivity)
    intro w hw
    rcases w with ⟨x,a⟩
    cases a
    · simp [bit]
    · simpa only [bit, if_true, mul_one, Real.norm_eq_abs, mul_assoc] using
        (population_basis_product_bounds d h J hh hJ u u z).2 x hw
  have hg (z) : MemLp (g z) ∞ (obsLaw P) := by
    apply population_localized_record_memLp (obsLaw P) d h hh Prod.fst (by fun_prop)
      _ (by fun_prop) (Real.sqrt ((J:ℝ)^d)*(4:ℝ)^d) (by positivity)
    intro w hw
    rcases w with ⟨x,a,y⟩
    cases y
    · simp [bit]
    · simpa only [bit, if_true, mul_one] using fineBasis_abs_bound d h J hh hJ x z
  have hm := rectangular_outcome_average_moments (n := n) (m := m) P hn F (by fun_prop) (hF.mono_exponent (by simp))
  have hp (z) := population_rectangular_observed_product_mean (n := n) (m := m)
    P hn (f z) (g z) (by unfold f; fun_prop) (by unfold g; fun_prop) (hf z) (hg z)
  unfold rBar
  simp_rw [rHat_finite_role_expansion]
  change (∫ w, rectangularOutcomeAverage F w -
    ∑ z, rectangularAverage (fun p => f z p.1*g z p.2) w ∂experiment P n m) = _
  rw [integral_sub (hm.1.integrable (by norm_num))
    (integrable_finsetSum _ (fun z _ => (hp z).1)),
    integral_finsetSum _ (fun z _ => (hp z).1), hm.2]
  simp_rw [(hp _).2]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  have ht := designated_local_treatment_moment P hP h hh hh'
    (fun x => coarseBasis h x u * fineBasis h J x z) (by fun_prop)
    ((4:ℝ)^d * (Real.sqrt ((J:ℝ)^d)*(4:ℝ)^d)) (by positivity)
    (population_basis_product_bounds d h J hh hJ u u z).2
  change (∫ w, locWeight h w.1 * (coarseBasis h w.1 u * fineBasis h J w.1 z) * bit w.2 ∂xaLaw P) = _
  rw [ht]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
