module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedProductDerivatives

/-! # Scalar mixed partials from full derivative bounds

Coordinate lines have unit tangent vectors. The chain rule transfers the full
first and second Fréchet derivative envelopes to the scalar amplitude partials.
-/
public section
noncomputable section
open Filter Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The first amplitude derivative is the full derivative on a unit coordinate direction.](goal) Under [the stated assumptions](hyp:x,hf). Under [the stated assumptions](hyp:f). -/
-- @node: mixed_coordinate_deriv_left
lemma mixed_coordinate_deriv_left (f : (Fin 2 → ℝ) → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ f ![x,y]) :
    deriv (fun r => f ![r,y]) x = fderiv ℝ f ![x,y] (Pi.single 0 1) := by
  have hline : HasDerivAt (fun r : ℝ => ![r,y]) (Pi.single 0 1) x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp
    · exact hasDerivAt_id x
    · exact hasDerivAt_const x y
  exact (hf.hasFDerivAt.comp_hasDerivAt x hline).deriv

/-- [The second amplitude derivative uses the other unit coordinate direction.](goal) Under [the stated assumptions](hyp:x,hf). Under [the stated assumptions](hyp:f). -/
-- @node: mixed_coordinate_deriv_right
lemma mixed_coordinate_deriv_right (f : (Fin 2 → ℝ) → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ f ![x,y]) :
    deriv (fun z => f ![x,z]) y = fderiv ℝ f ![x,y] (Pi.single 1 1) := by
  have hline : HasDerivAt (fun z : ℝ => ![x,z]) (Pi.single 1 1) y := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp
    · exact hasDerivAt_const y x
    · exact hasDerivAt_id y
  exact (hf.hasFDerivAt.comp_hasDerivAt y hline).deriv

/-- [Two-variable smoothness supplies the scalar mixed derivative and its
literal second-order operator-norm bound. [the documented result](goal) Under [the stated assumptions](hyp:hf,h1,h2). -/
-- @node: mixed_coordinate_derivative_bounds
lemma mixed_coordinate_derivative_bounds (f : (Fin 2 → ℝ) → ℝ) (x y M : ℝ)
    (hf : ContDiffAt ℝ 2 f ![x,y])
    (h1 : ‖iteratedFDeriv ℝ 1 f ![x,y]‖ ≤ M)
    (h2 : ‖iteratedFDeriv ℝ 2 f ![x,y]‖ ≤ M) :
    (∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun r => f ![r,z]) x) ∧
    DifferentiableAt ℝ (fun z => f ![x,z]) y ∧
    DifferentiableAt ℝ (fun z => deriv (fun r => f ![r,z]) x) y ∧
    |deriv (fun r => f ![r,y]) x| ≤ M ∧
    |deriv (fun z => f ![x,z]) y| ≤ M ∧
    |deriv (fun z => deriv (fun r => f ![r,z]) x) y| ≤ M := by
  have hd := hf.differentiableAt (by norm_num)
  have hevent : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 f ![x,z] :=
    (by fun_prop : ContinuousAt (fun z : ℝ => ![x,z]) y)
      (hf.eventually (by norm_num))
  have hline : HasDerivAt (fun z : ℝ => ![x,z]) (Pi.single 1 1) y := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp
    · exact hasDerivAt_const y x
    · exact hasDerivAt_id y
  have hfd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hclm := hfd.hasFDerivAt.comp_hasDerivAt y hline
  have happ := hclm.clm_apply (hasDerivAt_const y (Pi.single 0 (1 : ℝ)))
  have heq : (fun z => deriv (fun r => f ![r,z]) x) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ f ![x,z] (Pi.single 0 1)) := by
    filter_upwards [hevent] with z hz
    exact mixed_coordinate_deriv_left f x z (hz.differentiableAt (by norm_num))
  have hcross := happ.congr_of_eventuallyEq heq
  have hn0 : ‖(Pi.single 0 (1 : ℝ) : Fin 2 → ℝ)‖ = 1 := by rw [Pi.norm_single]; norm_num
  have hn1 : ‖(Pi.single 1 (1 : ℝ) : Fin 2 → ℝ)‖ = 1 := by rw [Pi.norm_single]; norm_num
  refine ⟨?_, hd.comp y hline.differentiableAt, hcross.differentiableAt, ?_, ?_, ?_⟩
  · filter_upwards [hevent] with z hz
    apply (hz.differentiableAt (by norm_num)).comp x
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · rw [mixed_coordinate_deriv_left f x y hd, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ f ![x,y]‖ * ‖(Pi.single 0 (1 : ℝ) : Fin 2 → ℝ)‖ :=
        (fderiv ℝ f ![x,y]).le_opNorm _
      _ ≤ M := by simpa only [hn0, mul_one, norm_iteratedFDeriv_one] using h1
  · rw [mixed_coordinate_deriv_right f x y hd, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ f ![x,y]‖ * ‖(Pi.single 1 (1 : ℝ) : Fin 2 → ℝ)‖ :=
        (fderiv ℝ f ![x,y]).le_opNorm _
      _ ≤ M := by simpa only [hn1, mul_one, norm_iteratedFDeriv_one] using h1
  · rw [hcross.deriv]
    simp only [ContinuousLinearMap.map_zero, add_zero]
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) ![x,y] (Pi.single 1 1)‖ * ‖(Pi.single 0 (1 : ℝ) : Fin 2 → ℝ)‖ :=
        (fderiv ℝ (fderiv ℝ f) ![x,y] (Pi.single 1 1)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) ![x,y]‖ * ‖(Pi.single 1 (1 : ℝ) : Fin 2 → ℝ)‖) *
          ‖(Pi.single 0 (1 : ℝ) : Fin 2 → ℝ)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (fderiv ℝ (fderiv ℝ f) ![x,y]).le_opNorm _
      _ ≤ M := by
        simpa only [hn0, hn1, mul_one, ← norm_iteratedFDeriv_one,
          norm_iteratedFDeriv_fderiv] using h2

end CausalSmith.Stat.LogoddsLowsmoothFrontier
