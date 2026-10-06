module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCellSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairTaylorDerivatives

/-! # Quadratic fair-root bounds

The integral Taylor estimate derives the quadratic amplitude bound for the
actual root and its spatial derivative from smoothness and the axis value.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [An even scalar function has zero totalized derivative at the origin.](goal) Under [the stated assumptions](hyp:f). Under [the stated assumptions](hyp:he). -/
-- @node: calibration_even_deriv_zero
lemma calibration_even_deriv_zero (f : ℝ → ℝ) (he : ∀ x, f (-x) = f x) :
    deriv f 0 = 0 := by
  have h := deriv_comp_neg f 0
  rw [show (fun x => f (-x)) = f from funext he] at h
  simp only [neg_zero] at h
  linarith

/-- [The second integral Taylor formula bounds a smooth even function for signed increments.](goal) Under [the stated assumptions](hyp:f,hf). Under [the stated assumptions](hyp:he,hb). -/
-- @node: calibration_even_quadratic_bound
lemma calibration_even_quadratic_bound (f : ℝ → ℝ) (a B : ℝ)
    (hf : ∀ x ∈ Set.uIcc 0 a, ContDiffAt ℝ ∞ f x)
    (he : ∀ x, f (-x) = f x)
    (hb : ∀ x ∈ Set.uIcc 0 a, |deriv (deriv f) x| ≤ B) :
    |f a - f 0| ≤ B*a^2 := by
  have hTaylor := calibration_scaled_second_taylor (fun x => f x - f 0) a
    (fun x hx => (hf x hx).sub contDiffAt_const) (by simp)
    (by rw [deriv_sub_const]; exact calibration_even_deriv_zero f he)
  simp only [deriv_sub_const_fun] at hTaylor
  have hi : |∫ v in (0 : ℝ)..1, (1-v)*deriv (deriv f) (v*a)| ≤ B := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
      (f := fun v => (1-v)*deriv (deriv f) (v*a)) (a := 0) (b := 1) (by
        intro v hv
        have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (by norm_num)] at hv
          exact ⟨hv.1.le,hv.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hv'.2] : 0 ≤ 1-v)]
        have hd := hb _ (calibration_unit_mul_mem_segment a v hv')
        have hm : 0 ≤ v*|deriv (deriv f) (v*a)| :=
          mul_nonneg hv'.1 (abs_nonneg _)
        nlinarith)
    simpa using h
  rw [← hTaylor, abs_mul, abs_of_nonneg (sq_nonneg a)]
  nlinarith [sq_nonneg a]

/-- [Scalar coordinate partial derivative of a joint parameter function. -/
-- @node: calibrationCoordinateDeriv
def calibrationCoordinateDeriv (f : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (w : Fin 3 → ℝ) : ℝ := deriv (fun D => f (Function.update w i D)) (w i)

/-- Coordinate differentiation preserves joint smoothness at the actual parameter point. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hf) hold, and [the stated conclusion follows](goal). -/
-- @node: calibrationCoordinateDeriv_contDiffAt
lemma calibrationCoordinateDeriv_contDiffAt (f : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (v : Fin 3 → ℝ) (hf : ContDiffAt ℝ ∞ f v) :
    ContDiffAt ℝ ∞ (calibrationCoordinateDeriv f i) v := by
  classical
  unfold calibrationCoordinateDeriv
  have hLift : ContDiffAt ℝ ∞ (fun z : (Fin 3 → ℝ) × ℝ =>
      f (Function.update z.1 i z.2)) (v,v i) := by
    have hp : ContDiffAt ℝ ∞
        (fun z : (Fin 3 → ℝ) × ℝ => Function.update z.1 i z.2) (v,v i) := by
      apply contDiffAt_pi.mpr
      intro j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hj]
        fun_prop
    have hf' : ContDiffAt ℝ ∞ f (Function.update v i (v i)) := by simpa using hf
    exact hf'.comp (v,v i) hp
  exact (hLift.fderiv (by fun_prop) (by simp)).clm_apply contDiffAt_const

/-- [Smoothness on the closed calibration region uniformly bounds the actual
second amplitude derivatives of the root and its spatial derivative. [the documented result](goal) Under [the stated assumptions](hyp:hf). -/
-- @node: fairRoot_second_partial_bounds
lemma fairRoot_second_partial_bounds (ε : ℝ)
    (hf : ∀ v ∈ fairParameterRegion ε,
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v) :
    ∃ B : ℝ, 0 < B ∧ ∀ t δ u : ℝ,
      t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      |deriv (deriv (fun D => fairRoot t D u)) δ| ≤ B ∧
      |deriv (deriv (fun D => deriv (fairRoot t D) u)) δ| ≤ B := by
  let f : (Fin 3 → ℝ) → ℝ := fun w => fairRoot (w 0) (w 1) (w 2)
  let A := calibrationCoordinateDeriv (calibrationCoordinateDeriv f 1) 1
  let U := calibrationCoordinateDeriv
    (calibrationCoordinateDeriv (calibrationCoordinateDeriv f 2) 1) 1
  have ha : ∀ v ∈ fairParameterRegion ε, ContDiffAt ℝ ∞ A v := by
    intro v hv
    exact calibrationCoordinateDeriv_contDiffAt _ _ _
      (calibrationCoordinateDeriv_contDiffAt _ _ _ (hf v hv))
  have hu : ∀ v ∈ fairParameterRegion ε, ContDiffAt ℝ ∞ U v := by
    intro v hv
    exact calibrationCoordinateDeriv_contDiffAt _ _ _
      (calibrationCoordinateDeriv_contDiffAt _ _ _
        (calibrationCoordinateDeriv_contDiffAt _ _ _ (hf v hv)))
  obtain ⟨Ca,hCa⟩ := (fairParameterRegion_isCompact ε).exists_bound_of_continuousOn
    (fun v hv => (ha v hv).continuousAt.continuousWithinAt)
  obtain ⟨Cu,hCu⟩ := (fairParameterRegion_isCompact ε).exists_bound_of_continuousOn
    (fun v hv => (hu v hv).continuousAt.continuousWithinAt)
  refine ⟨max 1 (max Ca Cu), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro t δ u ht hδ hu'
  have hv : ![t,δ,u] ∈ fairParameterRegion ε := ⟨ht,hδ,hu'⟩
  have h1 := (hCa _ hv).trans ((le_max_left Ca Cu).trans (le_max_right 1 (max Ca Cu)))
  have h2 := (hCu _ hv).trans ((le_max_right Ca Cu).trans (le_max_right 1 (max Ca Cu)))
  simpa [A,U,f,calibrationCoordinateDeriv,Real.norm_eq_abs,Function.update] using And.intro h1 h2

/-- Constancy on the closed spatial interval forces the actual derivative to
vanish even at the endpoints, where two-sided smoothness is available. [the documented result](goal) Under [the stated assumptions](hyp:hu,hf,hc). -/
-- @node: calibration_deriv_zero_on_unit_interval
lemma calibration_deriv_zero_on_unit_interval (f : ℝ → ℝ) (c u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hf : DifferentiableAt ℝ f u)
    (hc : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = c) : deriv f u = 0 := by
  have huniq := uniqueDiffOn_Icc_zero_one u hu
  rw [← hf.derivWithin huniq]
  rw [derivWithin_congr (fun x hx => hc x hx) (hc u hu)]
  exact congrFun (derivWithin_const _ _) u

/-- [Smoothness and the zero-amplitude center derive one uniform quadratic
bound for the actual fair root and its spatial derivative. [the documented result](goal) Under [the stated assumptions](hyp:hf,haxis). Under [the stated assumptions](hyp:hε). -/
-- @node: fairRoot_quadratic_bound_of_smooth
lemma fairRoot_quadratic_bound_of_smooth (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ v ∈ fairParameterRegion ε,
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v)
    (haxis : ∀ t u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) →
      u ∈ Set.Icc (0 : ℝ) 1 → fairRoot t 0 u = 2/5) :
    ∃ M : ℝ, 0 < M ∧ ∀ t δ u : ℝ,
      t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      |fairRoot t δ u-2/5|+|deriv (fairRoot t δ) u| ≤ M*δ^2 := by
  obtain ⟨B,hB,hbound⟩ := fairRoot_second_partial_bounds ε hf
  refine ⟨2*B, by positivity, ?_⟩
  intro t δ u ht hδ hu
  have hmem (D : ℝ) (hD : D ∈ Set.uIcc 0 δ) : |D| ≤ ε :=
    (calibration_segment_abs_le δ D hD).trans hδ
  have hp (D : ℝ) (hD : |D| ≤ ε) :
      ContDiffAt ℝ ∞ (fun A => fairRoot t A u) D := by
    exact (hf ![t,D,u] ⟨ht,hD,hu⟩).comp D (show ContDiffAt ℝ ∞ (fun A : ℝ => ![t,A,u]) D by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop)
  have hs (D : ℝ) (hD : |D| ≤ ε) :
      ContDiffAt ℝ ∞ (fun A => deriv (fairRoot t A) u) D := by
    have h := calibrationCoordinateDeriv_contDiffAt _ 2 _ (hf ![t,D,u] ⟨ht,hD,hu⟩)
    have h' := h.comp D (show ContDiffAt ℝ ∞ (fun A : ℝ => ![t,A,u]) D by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop)
    simpa [Function.comp_def,calibrationCoordinateDeriv,Function.update] using h'
  have hzero : deriv (fairRoot t 0) u = 0 := by
    apply calibration_deriv_zero_on_unit_interval _ (2/5) u hu
    · exact ((hf ![t,0,u] ⟨ht,by simpa using hε,hu⟩).comp u
        (show ContDiffAt ℝ ∞ (fun U : ℝ => ![t,0,U]) u by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)).differentiableAt (by simp)
    · exact fun x hx => haxis t x ht hx
  have hroot := calibration_even_quadratic_bound (fun D => fairRoot t D u) δ B
    (fun D hD => hp D (hmem D hD)) (fun D => fairRoot_even t D u)
    (fun D hD => (hbound t D u ht (hmem D hD) hu).1)
  have hspatial := calibration_even_quadratic_bound (fun D => deriv (fairRoot t D) u) δ B
    (fun D hD => hs D (hmem D hD)) (fun D => by
      rw [show fairRoot t (-D) = fairRoot t D from funext (fun U => fairRoot_even t D U)])
    (fun D hD => (hbound t D u ht (hmem D hD) hu).2)
  rw [haxis t u ht hu] at hroot
  rw [hzero,sub_zero] at hspatial
  linarith

end CausalSmith.Stat.LogoddsLowsmoothFrontier
