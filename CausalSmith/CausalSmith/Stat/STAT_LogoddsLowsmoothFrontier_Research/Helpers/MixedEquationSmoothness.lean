module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedRootExistence
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Smooth mixed calibration equation

The exponential divided difference is smooth through zero by its analytic
slope extension. The positive - radicand table formula is consequently smooth
jointly in the signed amplitudes, spatial coordinate, and root variable.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Filter
open scoped BigOperators Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The integral divided difference recovers the exponential increment, also at zero. [the stated conclusion](goal) holds. -/
-- @node: dividedExp_mul
lemma dividedExp_mul (t : ℝ) : t * dividedExp t = Real.exp t - 1 := by
  unfold dividedExp
  rw [intervalIntegral.mul_integral_comp_mul_right, integral_exp]
  simp

/-- The integral divided difference is the derivative - completed exponential slope. [the stated conclusion](goal) holds. -/
-- @node: dividedExp_eq_dslope
lemma dividedExp_eq_dslope : dividedExp = dslope Real.exp 0 := by
  funext t
  by_cases ht : t = 0
  · subst t
    simp [dividedExp, Real.deriv_exp]
  · rw [dslope_of_ne _ ht]
    simp only [slope, vsub_eq_sub, sub_zero, Real.exp_zero, smul_eq_mul]
    have h := dividedExp_mul t
    field_simp
    nlinarith [h]

/-- The actual integral formula is smooth to every order, including at zero. [The stated conclusion follows](goal). -/
-- @node: dividedExp_contDiff
@[fun_prop] lemma dividedExp_contDiff : ContDiff ℝ ⊤ dividedExp := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    obtain ⟨p, hp⟩ := (analyticAt_rexp : AnalyticAt ℝ Real.exp 0)
    have ha : AnalyticAt ℝ (dslope Real.exp 0) 0 :=
      ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    rw [dividedExp_eq_dslope]
    exact ha.contDiffAt
  · have he : dividedExp =ᶠ[𝓝 t] fun x => (Real.exp x - 1)/x := by
      filter_upwards [eventually_ne_nhds ht] with x hx
      apply (eq_div_iff hx).mpr
      simpa [mul_comm] using dividedExp_mul x
    exact ((Real.contDiff_exp.contDiffAt.sub contDiffAt_const).div contDiffAt_id ht).congr_of_eventuallyEq he

/-- The normalized table is jointly smooth at every positive radicand and nonzero denominator. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hrad,hden). -/
-- @node: normalizedBranch_contDiffAt
lemma normalizedBranch_contDiffAt (v : Fin 3 → ℝ)
    (hrad : 0 < (1 + (Real.exp (v 0) - 1) * (v 1 * (1 - v 2) + (1 - v 1) * v 2)) ^ 2-
      4 * (Real.exp (v 0) - 1) ^ 2 * (v 1 * (1 - v 1) * v 2 * (1 - v 2)))
    (hden : 1 + (Real.exp (v 0) - 1) * (v 1 * (1 - v 2) + (1 - v 1) * v 2) +
      Real.sqrt ((1 + (Real.exp (v 0) - 1) * (v 1 * (1 - v 2) + (1 - v 1) * v 2)) ^ 2-
        4 * (Real.exp (v 0) - 1) ^ 2 * (v 1 * (1 - v 1) * v 2 * (1 - v 2))) ≠ 0) :
    ContDiffAt ℝ ⊤ (fun w : Fin 3 → ℝ => normalizedBranch (w 0) (w 1) (w 2)) v := by
  unfold normalizedBranch
  dsimp only
  apply ContDiffAt.div
  · fun_prop
  · apply ContDiffAt.add
    · fun_prop
    · apply ContDiffAt.sqrt
      · fun_prop
      · exact ne_of_gt hrad
  · exact hden

/-- Radicand of a mixed normalized table, with all signed parameters substituted. -/
-- @node: mixedTableRadicand
def mixedTableRadicand (η ζ u q : ℝ) (s : Bool × Bool) : ℝ :=
  let t := 32 * η * ζ
  let ξ := 1/2 - η * q * localSignField u s
  let υ := 1/2 + ζ * localSignField u s
  let d := Real.exp t - 1
  (1 + d * (ξ * (1-υ) + (1-ξ) * υ))^2 -
    4 * d^2 * (ξ * (1-ξ) * υ * (1-υ))

/-- Smoothness of the actual mixed equation follows from its finitely many positive radicands. Under the stated assumptions. [The stated hypotheses](hyp:hrad,hden) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedEquation_contDiffAt
lemma mixedEquation_contDiffAt (v : (ℝ × ℝ) × (ℝ × ℝ))
    (hrad : ∀ s, 0 < mixedTableRadicand v.1.1 v.1.2 v.2.1 v.2.2 s)
    (hden : ∀ s, mixedTableDenominator v.1.1 v.1.2 v.2.1 v.2.2 s ≠ 0) :
    ContDiffAt ℝ ⊤ (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      mixedEquation w.1.1 w.1.2 w.2.1 w.2.2) v := by
  unfold mixedEquation signAverage
  apply ContDiffAt.sub
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro s hs
    let f : ((ℝ × ℝ) × (ℝ × ℝ)) → (Fin 3 → ℝ) := fun w =>
      ![32 * w.1.1 * w.1.2, 1/2 - w.1.1 * w.2.2 * localSignField w.2.1 s,
        1/2 + w.1.2 * localSignField w.2.1 s]
    have hf : ContDiffAt ℝ ⊤ f v := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp [f, localSignField] <;> fun_prop
    exact (normalizedBranch_contDiffAt (f v) (hrad s) (hden s)).comp v hf
  · fun_prop

/-- [At every point of the zero-amplitude rectangle, the full mixed equation is smooth. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_contDiffAt_zero
lemma mixedEquation_contDiffAt_zero (u q : ℝ) :
    ContDiffAt ℝ ⊤ (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      mixedEquation w.1.1 w.1.2 w.2.1 w.2.2) ((0,0),(u,q)) := by
  apply mixedEquation_contDiffAt
  · intro s
    norm_num [mixedTableRadicand]
  · intro s
    norm_num [mixedTableDenominator]

/-- The root-variable derivative at zero amplitudes is exactly minus one. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_deriv_zero
lemma mixedEquation_deriv_zero (u q : ℝ) : deriv (mixedEquation 0 0 u) q = -1 := by
  have he : mixedEquation 0 0 u = fun q => 1-q := funext (mixedEquation_zero_amplitudes u)
  rw [he]
  simpa using ((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).deriv

/-- The root-variable derivative varies continuously jointly near each zero-amplitude point. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_partial_continuousAt_zero
lemma mixedEquation_partial_continuousAt_zero (u q : ℝ) :
    ContinuousAt (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      deriv (mixedEquation w.1.1 w.1.2 w.2.1) w.2.2) ((0,0),(u,q)) := by
  let f : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ → ℝ := fun w χ =>
    mixedEquation w.1.1 w.1.2 w.2.1 χ
  have hf : ContDiffAt ℝ ⊤ (Function.uncurry f) (((0,0),(u,q)),q) := by
    exact (mixedEquation_contDiffAt_zero u q).comp (((0,0),(u,q)),q)
      (show ContDiffAt ℝ ⊤
        (fun z : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) => (z.1.1, (z.1.2.1, z.2)))
        (((0,0),(u,q)),q) by fun_prop)
  have hpartial := hf.fderiv (show ContDiffAt ℝ (0 : WithTop ℕ∞)
    (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.2.2) ((0,0),(u,q)) by fun_prop) (by simp)
  exact hpartial.continuousAt.clm_apply continuousAt_const

/-- Compactness supplies one signed amplitude square with a uniform negative derivative floor. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_uniform_deriv_neg
lemma mixedEquation_uniform_deriv_neg : ∃ ε : ℝ, 0 < ε ∧
    ∀ η ζ u q : ℝ, |η| ≤ ε → |ζ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (3/4 : ℝ) (5/4) →
      deriv (mixedEquation η ζ u) q < -1/2 := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (3/4 : ℝ) (5/4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hevent : ∀ᶠ a : ℝ × ℝ in 𝓝 (0,0), ∀ z ∈ K,
      deriv (mixedEquation a.1 a.2 z.1) z.2 < -1/2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    exact (mixedEquation_partial_continuousAt_zero z.1 z.2).eventually
      (gt_mem_nhds (by dsimp only; rw [mixedEquation_deriv_zero]; norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ/2, by linarith, ?_⟩
  intro η ζ u q hη hζ hu hq
  have hmem : (η,ζ) ∈ Metric.ball (0,0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  exact hball hmem (u,q) ⟨hu,hq⟩

/-- A negative derivative floor gives uniqueness throughout the entire prescribed root bracket. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hderiv,hp,hq,hep,heq) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedEquation_bracket_unique
lemma mixedEquation_bracket_unique (η ζ u : ℝ)
    (hderiv : ∀ q ∈ Set.Icc (3/4 : ℝ) (5/4), deriv (mixedEquation η ζ u) q < -1/2)
    (p q : ℝ) (hp : p ∈ Set.Ioo (3/4 : ℝ) (5/4))
    (hq : q ∈ Set.Ioo (3/4 : ℝ) (5/4))
    (hep : mixedEquation η ζ u p = 0) (heq : mixedEquation η ζ u q = 0) : p = q := by
  have hc : ContinuousOn (mixedEquation η ζ u) (Set.Icc (3/4 : ℝ) (5/4)) := by
    intro x hx
    exact (differentiableAt_of_deriv_ne_zero (by linarith [hderiv x hx])).continuousAt.continuousWithinAt
  have ha : StrictAntiOn (mixedEquation η ζ u) (Set.Icc (3/4 : ℝ) (5/4)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hc (fun x hx =>
      lt_trans (hderiv x (interior_subset hx)) (by norm_num))
  exact ha.injOn ⟨hp.1.le, hp.2.le⟩ ⟨hq.1.le, hq.2.le⟩ (hep.trans heq.symm)

/-- Existence and the uniform derivative floor give a unique mixed root on one absolute signed square. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_uniform_existsUnique
lemma mixedEquation_uniform_existsUnique : ∃ ε : ℝ, 0 < ε ∧
    ∀ η ζ u : ℝ, |η| ≤ ε → |ζ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      ∃! q : ℝ, q ∈ Set.Ioo (3/4 : ℝ) (5/4) ∧ mixedEquation η ζ u q = 0 := by
  obtain ⟨εr, hr, hroot⟩ := mixedEquation_uniform_exists
  obtain ⟨εd, hd, hderiv⟩ := mixedEquation_uniform_deriv_neg
  refine ⟨min εr εd, lt_min hr hd, ?_⟩
  intro η ζ u hη hζ hu
  obtain ⟨q, hq, heq⟩ := hroot η ζ u
    (hη.trans (min_le_left _ _)) (hζ.trans (min_le_left _ _)) hu
  refine ⟨q, ⟨hq, heq⟩, ?_⟩
  intro p hp
  exact mixedEquation_bracket_unique η ζ u
    (fun χ hχ => hderiv η ζ u χ (hη.trans (min_le_right _ _))
      (hζ.trans (min_le_right _ _)) hu hχ)
    p q hp.1 hq hp.2 heq

end CausalSmith.Stat.LogoddsLowsmoothFrontier
