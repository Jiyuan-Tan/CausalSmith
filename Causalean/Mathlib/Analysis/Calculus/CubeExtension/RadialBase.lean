module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetBounds
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Plateau
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Exact radial plateau on projected Euclidean norms

Local constancy near the projection kernel removes the norm singularity.
Uniform first and second jet bounds are obtained from the compactly supported
codomain profile, with one and two factors of the projection operator norm.
This module is independent of coordinate product profiles and bandwidth scaling.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- For [a continuous linear map P into an inner product space](hyp:P), [the
radial plateau](goal) at [a point x](hyp:x) is [the scalar plateau evaluated at
the norm of P x](step:1). -/
noncomputable def radialPlateau (P : E →L[ℝ] F) (x : E) : ℝ := plateau ‖P x‖

omit [FiniteDimensional ℝ F] in
/-- For [a coordinate map](hyp:P) at [a point](hyp:x),
[the radial plateau lies between zero and one](goal). -/
theorem radialPlateau_bounds (P : E →L[ℝ] F) (x : E) :
    0 ≤ radialPlateau P x ∧ radialPlateau P x ≤ 1 := by
  exact plateau_bounds ‖P x‖

/-- [The radial plateau is locally constant one](goal) near [a point](hyp:x)
whose [projected norm is less than one](hyp:hx) for [the projection](hyp:P).

Use continuity of P and the norm to obtain eventual projected norm ≤ 1.
This lemma is the required treatment of P x = 0; do not differentiate norm there. -/
theorem radialPlateau_eventually_one (P : E →L[ℝ] F) (x : E) (hx : ‖P x‖ < 1) :
    ∀ᶠ y in nhds x, radialPlateau P y = 1 := by
  have h := (P.continuous.norm.continuousAt).eventually (Iio_mem_nhds hx)
  filter_upwards [h] with y hy
  exact plateau_eq_one _ hy.le

/-- For [a continuous linear map P into a finite-dimensional inner product
space](hyp:P), [the radial plateau is twice continuously differentiable on the
whole space](goal), including at points that P sends to zero. -/
-- Use `contDiff_iff_contDiffAt`. If P x = 0, `radialPlateau_eventually_one`
-- identifies the germ with a constant. Otherwise `contDiffAt_norm ℝ` composed
-- with P and `plateau_contDiff.contDiffAt` handles the ordinary chain rule.
-- Primary reference: Mathlib/Analysis/InnerProductSpace/Calculus.lean,
-- pinned commit db584cd6d46c92f209a44c0f1c829460d327499d, contDiffAt_norm.
theorem radialPlateau_contDiff (P : E →L[ℝ] F) : ContDiff ℝ 2 (radialPlateau P) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : P x = 0
  · have h : radialPlateau P =ᶠ[nhds x] (fun _ => (1 : ℝ)) :=
      radialPlateau_eventually_one P x (by simp [hx])
    exact contDiffAt_const.congr_of_eventuallyEq h
  · exact plateau_contDiff.contDiffAt.comp x
      ((contDiffAt_norm ℝ hx).comp x P.contDiff.contDiffAt)

/-- [The norm plateau on the finite-dimensional codomain has compact support](goal)
in [the fixed inner-product space](hyp:F).

This is a bound for the codomain profile itself, not for a projection with a
nontrivial kernel. Its support lies in the compact closed radius-two ball. -/
theorem radialPlateau_base_hasCompactSupport : HasCompactSupport (fun x : F => plateau ‖x‖) := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : F) 2) (isCompact_closedBall _ _)
  intro x hx
  apply plateau_eq_zero
  have hr : ¬ ‖x‖ ≤ 2 := by simpa using hx
  exact (lt_of_not_ge hr).le

/-- At [a point](hyp:x) whose [projected radius is at least two](hyp:hx)
under [the projection](hyp:P), [the value and both ambient jets vanish](goal).

Strict exterior points use local constancy; equality points use continuity of
the first and second jets and approximation by dilating x. -/
theorem radialPlateau_jets_zero (P : E →L[ℝ] F) (x : E) (hx : 2 ≤ ‖P x‖) :
    radialPlateau P x = 0 ∧ fderiv ℝ (radialPlateau P) x = 0 ∧
      fderiv ℝ (fderiv ℝ (radialPlateau P)) x = 0 := by
  have hext (y : E) (hy : 2 < ‖P y‖) :
      radialPlateau P y = 0 ∧ fderiv ℝ (radialPlateau P) y = 0 ∧
        fderiv ℝ (fderiv ℝ (radialPlateau P)) y = 0 := by
    apply jets_zero_of_eventually_zero
    have h := P.continuous.norm.continuousAt.eventually (Ioi_mem_nhds hy)
    filter_upwards [h] with z hz
    exact plateau_eq_zero _ hz.le
  have hd : ContDiff ℝ 1 (fderiv ℝ (radialPlateau P)) :=
    (contDiff_succ_iff_fderiv.mp (radialPlateau_contDiff P)).2.2
  have hc : Continuous (fun t : ℝ => t • x) := by fun_prop
  have hs : IsClosed {t : ℝ |
      fderiv ℝ (radialPlateau P) (t • x) = 0 ∧
      fderiv ℝ (fderiv ℝ (radialPlateau P)) (t • x) = 0} :=
    (isClosed_eq (hd.continuous.comp hc) continuous_const).inter
      (isClosed_eq ((hd.continuous_fderiv (by norm_num)).comp hc) continuous_const)
  have hsub : Set.Ioi (1 : ℝ) ⊆ {t : ℝ |
      fderiv ℝ (radialPlateau P) (t • x) = 0 ∧
      fderiv ℝ (fderiv ℝ (radialPlateau P)) (t • x) = 0} := by
    intro t ht
    change 1 < t at ht
    apply (hext (t • x) ?_).2
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < t)]
    nlinarith
  have hmem : (1 : ℝ) ∈ closure (Set.Ioi (1 : ℝ)) := by
    rw [closure_Ioi]
    change (1 : ℝ) ≤ 1
    exact le_rfl
  have hj := (closure_minimal hsub hs) hmem
  change fderiv ℝ (radialPlateau P) ((1 : ℝ) • x) = 0 ∧
    fderiv ℝ (fderiv ℝ (radialPlateau P)) ((1 : ℝ) • x) = 0 at hj
  refine ⟨plateau_eq_zero ‖P x‖ hx, ?_⟩
  simpa only [one_smul] using hj

/-- [A finite constant bounds the radial first and second jets by the first and
second powers of the projection norm](goal), and values by one, uniformly over
[all coordinate maps between the fixed spaces](hyp:E,F).

First bound the C² codomain profile `y ↦ plateau ‖y‖` using
`radialPlateau_base_hasCompactSupport` and `exists_jetBounds_of_compactSupport`.
Precomposition with P contributes one operator norm for the first jet and two
for the second jet. This avoids computing the Hessian of the norm explicitly.
Compact support of the composed function is not available for a map with kernel. -/
-- `ContinuousLinearMap.iteratedFDeriv_comp_right` and the norm bound for
-- `ContinuousMultilinearMap.compContinuousLinearMap` give the codomain jet
-- bound multiplied by ‖P‖^j. Relate j=1,2 to nested ambient fderiv via
-- `norm_iteratedFDeriv_fderiv` and the order-one norm identity.
theorem radialPlateau_uniform_jetBounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : E →L[ℝ] F) (x : E),
      |radialPlateau P x| ≤ 1 ∧
      ‖fderiv ℝ (radialPlateau P) x‖ ≤ C * ‖P‖ ∧
      ‖fderiv ℝ (fderiv ℝ (radialPlateau P)) x‖ ≤ C * ‖P‖ ^ 2 := by
  let b : F → ℝ := fun y => plateau ‖y‖
  have hb : ContDiff ℝ 2 b := by
    exact radialPlateau_contDiff (ContinuousLinearMap.id ℝ F)
  obtain ⟨C, hC, hB⟩ := exists_jetBounds_of_compactSupport hb
    radialPlateau_base_hasCompactSupport
  refine ⟨C, hC, ?_⟩
  intro P x
  have hbound (j : ℕ) (hj : j ≤ 2) (hjet : ‖iteratedFDeriv ℝ j b (P x)‖ ≤ C) :
      ‖iteratedFDeriv ℝ j (radialPlateau P) x‖ ≤ C * ‖P‖ ^ j := by
    change ‖iteratedFDeriv ℝ j (b ∘ P) x‖ ≤ _
    rw [P.iteratedFDeriv_comp_right hb x (by exact_mod_cast hj)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j b (P x)‖ * ∏ _ : Fin j, ‖P‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ j b (P x)‖ * ‖P‖ ^ j := by simp
      _ ≤ C * ‖P‖ ^ j := mul_le_mul_of_nonneg_right hjet (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg (radialPlateau_bounds P x).1]
    exact (radialPlateau_bounds P x).2
  · simpa only [norm_iteratedFDeriv_one, pow_one] using
      hbound 1 (by norm_num) (by simpa only [norm_iteratedFDeriv_one] using hB.first (P x))
  · have hn (f : E → ℝ) :
        ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    have hnF : ‖iteratedFDeriv ℝ 2 b (P x)‖ ≤ C := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
      exact hB.second (P x)
    simpa only [hn] using hbound 2 le_rfl hnF

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
