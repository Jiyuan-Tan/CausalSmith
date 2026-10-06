module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEquationContinuity
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Smoothness of the fair Taylor equation through its axes

Compactness of the integration interval supplies uniform derivative bounds for
parameter differentiation. Iterating this argument preserves every finite order
of smoothness in the two Taylor integrations.
-/
public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The scalar integration coordinate is fixed when taking the parameter derivative.](goal) Under [the stated assumptions](hyp:F,f,x). Under [the stated assumptions](hyp:hf). -/
-- @node: calibration_parameter_fderiv_contDiffAt
lemma calibration_parameter_fderiv_contDiffAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ → F) (x : E) (y : ℝ)
    (hf : ContDiffAt ℝ ∞ f.uncurry (x, y)) :
    ContDiffAt ℝ ∞ (fun z : E × ℝ => fderiv ℝ (fun w => f w z.2) z.1) (x, y) := by
  have h := hf.comp ((x, y),x)
    (show ContDiffAt ℝ ∞ (fun z : (E × ℝ) × E => (z.2,z.1.2)) ((x, y),x) by fun_prop)
  exact h.fderiv (by fun_prop) (by simp)

/-- [Local joint differentiability on a compact interval justifies differentiation
under the parameter integral, with a bound uniform in the integration coordinate. [the documented result](goal) Under [the stated assumptions](hyp:F,f,x,hf). -/
-- @node: calibration_intervalIntegral_hasFDerivAt
lemma calibration_intervalIntegral_hasFDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → ℝ → F) (x : E)
    (hf : ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f.uncurry (x, y)) :
    HasFDerivAt (fun z => ∫ y in (0 : ℝ)..1, f z y)
      (∫ y in (0 : ℝ)..1, fderiv ℝ (fun z => f z y) x) x := by
  let f' : E → ℝ → E →L[ℝ] F := fun z y => fderiv ℝ (fun w => f w y) z
  have hpartial (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      ContinuousAt f'.uncurry (x, y) := by
    have h := (hf y hy).comp ((x, y),x)
      (show ContDiffAt ℝ 1 (fun z : (E × ℝ) × E => (z.2,z.1.2)) ((x, y),x) by fun_prop)
    exact (show ContDiffAt ℝ 0 f'.uncurry (x, y) from
      h.fderiv (by fun_prop) (by norm_num)).continuousAt
  have hbase : ContinuousOn (f' x) (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    exact ((hpartial y hy).comp (by fun_prop)).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hbase.norm
  have hevent : ∀ᶠ z in 𝓝 x, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 f.uncurry (z,y) ∧ ‖f' z y‖ < B+1 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro y hy
    exact ((hf y hy).eventually (by norm_num)).and
      ((hpartial y hy).norm.eventually (gt_mem_nhds
        (lt_of_le_of_lt (hB ⟨y,hy,rfl⟩) (lt_add_one B))))
  let S := {z | ∀ y ∈ Set.Icc (0 : ℝ) 1,
    ContDiffAt ℝ 1 f.uncurry (z,y) ∧ ‖f' z y‖ < B+1}
  have hS : S ∈ 𝓝 x := hevent
  have hslice (z : E) (hz : z ∈ S) : ContinuousOn (f z) (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    exact (((hz y hy).1.continuousAt).comp (by fun_prop)).continuousWithinAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' hS
  · filter_upwards [hS] with z hz
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hslice z hz).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · have hx : x ∈ S := mem_of_mem_nhds hS
    exact (hslice x hx).intervalIntegrable_of_Icc (by norm_num)
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hbase.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact fun z hz => (hz y ⟨hy.1.le,hy.2⟩).2.le
  · exact intervalIntegrable_const
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    intro z hz
    exact (((hz y ⟨hy.1.le,hy.2⟩).1.differentiableAt (by norm_num)).comp z
      (show DifferentiableAt ℝ (fun w : E => (w,y)) z by fun_prop)).hasFDerivAt

/-- [Every finite derivative order passes through integration on the fixed
compact interval. The induction differentiates the actual parameter family. [the documented result](goal) Under [the stated assumptions](hyp:F,f,x,hf). -/
-- @node: calibration_intervalIntegral_contDiffAt_nat
lemma calibration_intervalIntegral_contDiffAt_nat
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : E → ℝ → F) (x : E)
    (hf : ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ f.uncurry (x, y)) :
    ContDiffAt ℝ n (fun z => ∫ y in (0 : ℝ)..1, f z y) x := by
  induction n generalizing F f x with
  | zero =>
    have hevent : ∀ᶠ z in 𝓝 x, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ContDiffAt ℝ 1 f.uncurry (z,y) := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro y hy
      exact ((hf y hy).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
    apply contDiffAt_zero.mpr
    exact ⟨{z | ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f.uncurry (z,y)},
      hevent, fun z hz =>
        (calibration_intervalIntegral_hasFDerivAt f z hz).continuousAt.continuousWithinAt⟩
  | succ n ih =>
    let f' : E → ℝ → E →L[ℝ] F := fun z y => fderiv ℝ (fun w => f w y) z
    have hevent : ∀ᶠ z in 𝓝 x, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ContDiffAt ℝ 1 f.uncurry (z,y) := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro y hy
      exact ((hf y hy).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun z => ∫ y in (0 : ℝ)..1, f' z y, ?_, ?_⟩
    · exact ⟨{z | ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f.uncurry (z,y)},
        hevent, fun z hz => calibration_intervalIntegral_hasFDerivAt f z hz⟩
    · exact ih f' x (fun y hy => calibration_parameter_fderiv_contDiffAt f x y (hf y hy))

/-- [Smoothness at all points above a compact integration interval gives smoothness
of the parameter integral on a full neighborhood of the base parameter. [the documented result](goal) Under [the stated assumptions](hyp:F,f,x,hf). -/
-- @node: calibration_intervalIntegral_contDiffAt
lemma calibration_intervalIntegral_contDiffAt
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → ℝ → F) (x : E)
    (hf : ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ f.uncurry (x, y)) :
    ContDiffAt ℝ ∞ (fun z => ∫ y in (0 : ℝ)..1, f z y) x := by
  apply contDiffAt_infty.mpr
  intro n
  exact calibration_intervalIntegral_contDiffAt_nat n f x hf

/-- [Both Taylor integrations preserve joint smoothness of the actual fair
normalized equation, including both axes and every boundary of the closed box. [the documented result](goal) Under [the stated assumptions](hyp:hx). -/
-- @node: fairEquation_contDiffAt
lemma fairEquation_contDiffAt (x : Fin 4 → ℝ) (hx : x ∈ fairTaylorParameterRegion) :
    ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ =>
      fairEquation (w 0) (w 1) (w 2) (w 3)) x := by
  let F : ((Fin 4 → ℝ) × ℝ) → ℝ → ℝ := fun z v =>
    (1-v)*deriv (fun T => deriv (deriv (fun D =>
      fairNumerator T D (z.1 2) (z.1 3))) (v*z.1 1)) (z.2*z.1 0)
  apply calibration_intervalIntegral_contDiffAt
  intro s hs
  exact calibration_intervalIntegral_contDiffAt F (x,s)
    (fun v hv => (fairTaylorIntegrand_contDiffAt ((x,s),v) hx hs hv).of_le le_top)

/-- [The center partial derivative is jointly smooth also on the removable axes.](goal) Under [the stated assumptions](hyp:x,hx). -/
-- @node: fairEquation_center_deriv_contDiffAt
lemma fairEquation_center_deriv_contDiffAt (x : Fin 4 → ℝ)
    (hx : x ∈ fairTaylorParameterRegion) :
    ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ =>
      deriv (fun ξ => fairEquation (w 0) (w 1) ξ (w 3)) (w 2)) x := by
  have hvec : ![x 0,x 1,x 2,x 3] = x := by
    funext i
    fin_cases i <;> rfl
  have h' := (fairEquation_contDiffAt x hx)
  rw [← hvec] at h'
  have hlift := h'.comp (x,x 2)
    (show ContDiffAt ℝ ∞ (fun z : (Fin 4 → ℝ) × ℝ =>
      ![z.1 0,z.1 1,z.2,z.1 3]) (x,x 2) by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop)
  exact (hlift.fderiv (by fun_prop) (by simp)).clm_apply contDiffAt_const

/-- Every fixed derivative order of the actual normalized equation is uniformly
bounded on the same closed parameter box, with no excluded amplitude axis. [the documented result](goal) -/
-- @node: fairEquation_uniform_derivative_bounds
lemma fairEquation_uniform_derivative_bounds (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ fairTaylorParameterRegion,
      ‖iteratedFDeriv ℝ m (fun w : Fin 4 → ℝ =>
        fairEquation (w 0) (w 1) (w 2) (w 3)) x‖ ≤ B := by
  have hc : ContinuousOn (iteratedFDeriv ℝ m (fun w : Fin 4 → ℝ =>
      fairEquation (w 0) (w 1) (w 2) (w 3))) fairTaylorParameterRegion := by
    intro x hx
    exact ((fairEquation_contDiffAt x hx).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨C,hC⟩ := fairTaylorParameterRegion_isCompact.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
