module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairTaylorDerivatives

/-! # Regularity and endpoint roots of the fair equation

The Taylor identity gives joint smoothness away from the removable axes,
including relative smoothness on the closed parameter box. At the cell endpoints
it supplies actual bracket roots off the axes. Matching itself follows from the
undivided Taylor identity, including both axes.
-/
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The closed effect, signed amplitude, and centering box; position is unrestricted. -/
-- @node: fairEquationParameterRegion
def fairEquationParameterRegion : Set (Fin 4 → ℝ) :=
  {v | v 0 ∈ Set.Icc (0 : ℝ) (1/4) ∧ |v 1| ≤ 1/100 ∧
    v 2 ∈ Set.Icc (3/10 : ℝ) (1/2)}

/-- Off the axes the Taylor extension has the joint smoothness of its quotient,
relative to the full closed calibration box. [the documented result](goal) Under [the stated assumptions](hyp:hv,hne). -/
-- @node: fairEquation_contDiffWithinAt_off_axes
lemma fairEquation_contDiffWithinAt_off_axes (v : Fin 4 → ℝ)
    (hv : v ∈ fairEquationParameterRegion) (hne : v 0 * v 1 ≠ 0) :
    ContDiffWithinAt ℝ ⊤
      (fun w : Fin 4 → ℝ => fairEquation (w 0) (w 1) (w 2) (w 3))
      fairEquationParameterRegion v := by
  have hden : v 0 * (v 1)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero_iff.mp hne).1 (pow_ne_zero 2 (mul_ne_zero_iff.mp hne).2)
  have hquot : ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ =>
      fairNumerator (w 0) (w 1) (w 2) (w 3) / (w 0 * (w 1)^2)) v :=
    (fairNumerator_contDiffAt v hv.1 hv.2.1 hv.2.2).div (by fun_prop) hden
  have hevent : ∀ᶠ w : Fin 4 → ℝ in 𝓝 v, w 0 * w 1 ≠ 0 :=
    (show ContinuousAt (fun w : Fin 4 → ℝ => w 0 * w 1) v by fun_prop).eventually_ne hne
  apply hquot.contDiffWithinAt.congr_of_eventuallyEq _
    (fairEquation_eq_div _ _ _ _ hv.1 hv.2.1 hv.2.2 hne)
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hbox
  exact fairEquation_eq_div _ _ _ _ hbox.1 hbox.2.1 hbox.2.2 hw

/-- [At interior box points, off-axis smoothness holds on a full neighborhood.](goal) Under [the stated assumptions](hyp:hδ,hne). Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairEquation_contDiffAt_off_axes
lemma fairEquation_contDiffAt_off_axes (v : Fin 4 → ℝ)
    (ht : v 0 ∈ Set.Ioo (0 : ℝ) (1/4)) (hδ : |v 1| < 1/100)
    (hξ : v 2 ∈ Set.Ioo (3/10 : ℝ) (1/2)) (hne : v 0 * v 1 ≠ 0) :
    ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ =>
      fairEquation (w 0) (w 1) (w 2) (w 3)) v := by
  have hv : v ∈ fairEquationParameterRegion :=
    ⟨⟨ht.1.le,ht.2.le⟩,hδ.le,⟨hξ.1.le,hξ.2.le⟩⟩
  apply (fairEquation_contDiffWithinAt_off_axes v hv hne).contDiffAt
  have ht' : ∀ᶠ w : Fin 4 → ℝ in 𝓝 v, w 0 ∈ Set.Ioo (0 : ℝ) (1/4) :=
    (continuous_apply (0 : Fin 4)).continuousAt.eventually
      (isOpen_Ioo.mem_nhds ht)
  have hδ' : ∀ᶠ w : Fin 4 → ℝ in 𝓝 v, |w 1| < 1/100 :=
    ((continuous_apply (1 : Fin 4)).continuousAt.abs).eventually
      (gt_mem_nhds hδ)
  have hξ' : ∀ᶠ w : Fin 4 → ℝ in 𝓝 v, w 2 ∈ Set.Ioo (3/10 : ℝ) (1/2) :=
    (continuous_apply (2 : Fin 4)).continuousAt.eventually
      (isOpen_Ioo.mem_nhds hξ)
  filter_upwards [ht',hδ',hξ'] with w hw hd hx
  exact ⟨⟨hw.1.le,hw.2.le⟩,hd.le,⟨hx.1.le,hx.2.le⟩⟩

/-- [Endpoint matching supplies a root of the actual normalized equation off the axes.](goal) Under [the stated assumptions](hyp:hδ,hu,hne). Under [the stated assumptions](hyp:ht). -/
-- @node: fairEquation_endpoint_zero_off_axes
lemma fairEquation_endpoint_zero_off_axes (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hu : u = 0 ∨ u = 1) (hne : t*δ ≠ 0) :
    fairEquation t δ (2/5) u = 0 := by
  rw [fairEquation_eq_div t δ (2/5) u ht hδ (by constructor <;> norm_num) hne,
    fairNumerator_endpoints t δ u ht hδ hu, zero_div]

/-- [The endpoint root belongs to the prescribed open centering bracket.](goal) Under [the stated assumptions](hyp:hδ,hu,hne). Under [the stated assumptions](hyp:ht). -/
-- @node: fairEquation_endpoint_exists_off_axes
lemma fairEquation_endpoint_exists_off_axes (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hu : u = 0 ∨ u = 1) (hne : t*δ ≠ 0) :
    ∃ p ∈ Set.Ioo (3/10 : ℝ) (1/2), fairEquation t δ p u = 0 := by
  exact ⟨2/5, by constructor <;> norm_num,
    fairEquation_endpoint_zero_off_axes t δ u ht hδ hu hne⟩

/-- [Multiplying the normalized root equation gives matching without any division
or exception for the effect and amplitude axes. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hξ,he). -/
-- @node: fair_matching_of_equation
lemma fair_matching_of_equation (t δ ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hξ : ξ ∈ Set.Icc (3/10 : ℝ) (1/2)) (he : fairEquation t δ ξ u = 0) :
    signAverage (fun s => riskShift t (ξ+δ*localSignField u s)) =
      riskShift (comparatorEffect t δ) ξ := by
  apply sub_eq_zero.mp
  change fairNumerator t δ ξ u = 0
  rw [← fairEquation_mul_parameters t δ ξ u ht hδ hξ, he, mul_zero]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
