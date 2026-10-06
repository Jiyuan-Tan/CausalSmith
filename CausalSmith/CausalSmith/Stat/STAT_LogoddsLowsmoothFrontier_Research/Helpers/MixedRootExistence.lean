module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Uniform existence of the mixed calibration root

Positive table denominators and uniform sign separation follow from continuity
on the compact zero-amplitude parameter rectangle. The intermediate value theorem
then supplies a root in the prescribed open bracket for small signed amplitudes.
-/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- The exponential divided difference is continuous also at zero. [The stated conclusion follows](goal). -/
-- @node: dividedExp_continuous
@[fun_prop] lemma dividedExp_continuous : Continuous dividedExp := by
  unfold dividedExp
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t s : ℝ => Real.exp (s*t)) (by fun_prop) 0 1

/-- Denominator of one normalized mixed table, before selecting a root. -/
-- @node: mixedTableDenominator
def mixedTableDenominator (η ζ u q : ℝ) (s : Bool × Bool) : ℝ :=
  let t := 32*η*ζ
  let ξ := 1/2-η*q*localSignField u s
  let υ := 1/2+ζ*localSignField u s
  let d := Real.exp t-1
  let v := ξ*(1-ξ)*υ*(1-υ)
  let L := 1+d*(ξ*(1-υ)+(1-ξ)*υ)
  L+Real.sqrt (L^2-4*d^2*v)

/-- Each mixed-table denominator varies continuously with all parameters. [The stated conclusion follows](goal). -/
-- @node: mixedTableDenominator_continuous
@[fun_prop] lemma mixedTableDenominator_continuous (s : Bool × Bool) :
    Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ) =>
      mixedTableDenominator v.1.1 v.1.2 v.2.1 v.2.2 s) := by
  unfold mixedTableDenominator localSignField
  fun_prop

/-- The mixed equation is continuous wherever its finitely many denominators are nonzero. Under the stated assumptions. [The stated hypotheses](hyp:hv) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedEquation_continuousAt
lemma mixedEquation_continuousAt (v : (ℝ × ℝ) × (ℝ × ℝ))
    (hv : ∀ s, mixedTableDenominator v.1.1 v.1.2 v.2.1 v.2.2 s ≠ 0) :
    ContinuousAt (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      mixedEquation w.1.1 w.1.2 w.2.1 w.2.2) v := by
  unfold mixedEquation signAverage
  apply ContinuousAt.sub
  · apply ContinuousAt.const_mul
    apply ContinuousAt.const_mul
    apply tendsto_finsetSum
    intro s hs
    unfold normalizedBranch
    dsimp only
    apply ContinuousAt.div
    · unfold localSignField
      fun_prop
    · exact (mixedTableDenominator_continuous s).continuousAt
    · exact hv s
  · fun_prop

/-- At zero amplitudes the equation is the affine function with root one. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_zero_amplitudes
lemma mixedEquation_zero_amplitudes (u q : ℝ) : mixedEquation 0 0 u q = 1-q := by
  norm_num [mixedEquation, signAverage, normalizedBranch, dividedExp]

/-- Compactness gives one signed amplitude square with positive denominators and separated signs. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_uniform_neighbourhood
lemma mixedEquation_uniform_neighbourhood : ∃ ε : ℝ, 0 < ε ∧
    ∀ η ζ u q : ℝ, |η| ≤ ε → |ζ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (7/8 : ℝ) (9/8) →
      (∀ s, 0 < mixedTableDenominator η ζ u q s) ∧
      |mixedEquation η ζ u q - (1-q)| < 1/16 := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (7/8 : ℝ) (9/8)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hevent : ∀ᶠ a : ℝ × ℝ in 𝓝 (0,0), ∀ z ∈ K,
      (∀ s, 0 < mixedTableDenominator a.1 a.2 z.1 z.2 s) ∧
      |mixedEquation a.1 a.2 z.1 z.2 - (1-z.2)| < 1/16 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hden : ∀ s, ∀ᶠ w : (ℝ × ℝ) × (ℝ × ℝ) in 𝓝 ((0,0),z),
        0 < mixedTableDenominator w.1.1 w.1.2 w.2.1 w.2.2 s := by
      intro s
      exact (mixedTableDenominator_continuous s).continuousAt.eventually
        (lt_mem_nhds (show 0 < mixedTableDenominator 0 0 z.1 z.2 s by norm_num [mixedTableDenominator]))
    have hF := mixedEquation_continuousAt ((0,0),z)
      (by intro s; norm_num [mixedTableDenominator])
    have hE : ContinuousAt (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        |mixedEquation w.1.1 w.1.2 w.2.1 w.2.2 - (1-w.2.2)|) ((0,0),z) := by
      exact (hF.sub (by fun_prop)).abs
    have hsmall := hE.eventually (gt_mem_nhds
      (by simp [mixedEquation_zero_amplitudes] :
        |mixedEquation 0 0 z.1 z.2 - (1-z.2)| < (1/16 : ℝ)))
    exact ((eventually_all.mpr hden).and hsmall)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ/2, by linarith, ?_⟩
  intro η ζ u q hη hζ hu hq
  have hmem : (η,ζ) ∈ Metric.ball (0,0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  exact hball hmem (u,q) ⟨hu,hq⟩

/-- Uniform sign separation and continuity provide a genuine interior mixed root. [the stated conclusion](goal) holds. -/
-- @node: mixedEquation_uniform_exists
lemma mixedEquation_uniform_exists : ∃ ε : ℝ, 0 < ε ∧
    ∀ η ζ u : ℝ, |η| ≤ ε → |ζ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      ∃ q : ℝ, q ∈ Set.Ioo (3/4) (5/4) ∧ mixedEquation η ζ u q = 0 := by
  obtain ⟨ε, hε, hlocal⟩ := mixedEquation_uniform_neighbourhood
  refine ⟨ε,hε,?_⟩
  intro η ζ u hη hζ hu
  have hcont : ContinuousOn (mixedEquation η ζ u) (Set.Icc (7/8 : ℝ) (9/8)) := by
    intro q hq
    have h := mixedEquation_continuousAt ((η,ζ),(u,q))
      (fun s => ne_of_gt ((hlocal η ζ u q hη hζ hu hq).1 s))
    exact (h.comp (f := fun q : ℝ => ((η,ζ),(u,q))) (by fun_prop)).continuousWithinAt
  have hlo := (hlocal η ζ u (7/8) hη hζ hu (by constructor <;> norm_num)).2
  have hhi := (hlocal η ζ u (9/8) hη hζ hu (by constructor <;> norm_num)).2
  obtain ⟨q,hq,heq⟩ := intermediate_value_Icc' (by norm_num : (7/8 : ℝ) ≤ 9/8) hcont
    (show (0 : ℝ) ∈ Set.Icc (mixedEquation η ζ u (9/8)) (mixedEquation η ζ u (7/8)) from
      ⟨by linarith [(abs_lt.mp hhi).2], by linarith [(abs_lt.mp hlo).1]⟩)
  exact ⟨q, ⟨by linarith [hq.1], by linarith [hq.2]⟩, heq⟩
end CausalSmith.Stat.LogoddsLowsmoothFrontier
