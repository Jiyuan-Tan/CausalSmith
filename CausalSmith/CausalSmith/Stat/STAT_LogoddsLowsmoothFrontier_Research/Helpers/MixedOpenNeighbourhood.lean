module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedCellSmoothness

/-! # Common open mixed-calibration neighborhood

The implicit branch supplies actual bracket zeros near each zero-amplitude
spatial point. The derivative floor identifies the selector uniquely there.
Compactness of the spatial interval then gives a closed amplitude square inside
one open set on which both the selector and every substituted cell are smooth.
-/
public section
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Bracket existence and uniqueness persist on ambient neighborhoods, including
beyond the endpoints of the spatial interval. [the documented result](goal) -/
-- @node: mixedCalibrationZero_eventually_zero
lemma mixedCalibrationZero_eventually_zero (u : ℝ) :
    ∀ᶠ v : Fin 3 → ℝ in 𝓝 ![0,0,u], MixedCalibrationZero v := by
  let F : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    mixedEquation (z.1 0) (z.1 1) (z.1 2) z.2
  have hF : ContDiffAt ℝ ⊤ F (![0,0,u],1) := by
    change ContDiffAt ℝ ⊤ (fun z : (Fin 3 → ℝ) × ℝ =>
      mixedEquation (z.1 0) (z.1 1) (z.1 2) z.2) (![0,0,u],1)
    exact (mixedEquation_contDiffAt_zero u 1).comp (![0,0,u],1)
      (by fun_prop : ContDiffAt ℝ ⊤ (fun z : (Fin 3 → ℝ) × ℝ =>
        ((z.1 0,z.1 1),(z.1 2,z.2))) (![0,0,u],1))
  obtain ⟨S,hS,hSmooth⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨D,hDsub,hDopen,hDbase⟩ := mem_nhds_iff.mp hS
  obtain ⟨U,V,g,hU,hbU,hV,hbV,hUV,hg,hgBase,hgRange,hgGraph⟩ :=
    scalar_smooth_implicit_function 3 F D ![0,0,u] 1 hDopen hDbase
      (hSmooth.mono hDsub)
      (by simp [F,mixedEquation_zero_amplitudes])
      (by change deriv (mixedEquation 0 0 u) 1 ≠ 0
          rw [mixedEquation_deriv_zero]; norm_num)
  have hRange : ∀ᶠ v in 𝓝 ![0,0,u], g v ∈ Set.Ioo (3/4 : ℝ) (5/4) :=
    (hg.contDiffAt (hU.mem_nhds hbU)).continuousAt
      (by rw [hgBase]; exact isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
  filter_upwards [hU.mem_nhds hbU,hRange,
    mixedEquation_eventually_bracket_deriv_neg u] with v hv hgv hneg
  have hz : mixedEquation (v 0) (v 1) (v 2) (g v) = 0 :=
    (hgGraph v hv (g v) (hgRange v hv)).mpr rfl
  have hs := mixedRoot_bracket_spec (v 0) (v 1) (v 2) ⟨g v,hgv,hz⟩
  refine ⟨hs.1,hs.2,?_⟩
  intro q hq he
  exact mixedEquation_bracket_unique (v 0) (v 1) (v 2) hneg
    q (mixedRoot (v 0) (v 1) (v 2)) hq hs.1 he hs.2

/-- One common open set contains a positive closed signed amplitude square and
preserves the genuine mixed branch and all fully substituted cell formulas. [the documented result](goal) -/
-- @node: mixed_calibration_open_neighbourhood
lemma mixed_calibration_open_neighbourhood :
    ∃ ε : ℝ, ∃ U : Set (Fin 3 → ℝ), 0 < ε ∧ IsOpen U ∧
      mixedParameterRegion ε ⊆ U ∧
      (∀ v ∈ U, MixedCalibrationZero v) ∧
      ContDiffOn ℝ ∞ (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) U ∧
      (∀ b s a y, ContDiffOn ℝ ∞ (localMixedCell b s a y) U) := by
  let S : Set (Fin 3 → ℝ) := {v | MixedCalibrationZero v ∧
    ContDiffAt ℝ ⊤ (fun w : Fin 3 → ℝ => mixedRoot (w 0) (w 1) (w 2)) v ∧
    ∀ b s a y, ContDiffAt ℝ ⊤ (localMixedCell b s a y) v}
  let U := interior S
  have hbase (u : ℝ) : ![0,0,u] ∈ U := by
    apply mem_interior_iff_mem_nhds.mpr
    have hcells : ∀ᶠ v in 𝓝 ![0,0,u],
        ∀ b s a y, ContDiffAt ℝ ⊤ (localMixedCell b s a y) v := by
      simp only [Filter.eventually_all]
      intro b s a y
      exact (localMixedCell_contDiffAt_zero b s a y u).eventually (by simp)
    filter_upwards [mixedCalibrationZero_eventually_zero u,
      (mixedRoot_contDiffAt_zero u).eventually (by simp),hcells] with v hz hr hc
    exact ⟨hz,hr,hc⟩
  have hevent : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0),
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ![z.1,z.2,u] ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    exact (by fun_prop : ContinuousAt
      (fun z : (ℝ × ℝ) × ℝ => ![z.1.1,z.1.2,z.2]) ((0,0),u))
      (isOpen_interior.mem_nhds (hbase u))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ/2,U,by linarith,isOpen_interior,?_,?_,?_,?_⟩
  · intro v hv
    have hmem : (v 0,v 1) ∈ Metric.ball (0,0) δ := by
      rw [Metric.mem_ball,Prod.dist_eq]
      simp only [Real.dist_eq,sub_zero]
      exact max_lt (by linarith [hv.1]) (by linarith [hv.2.1])
    have he : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
    simpa only [he] using hball hmem (v 2) hv.2.2
  · intro v hv
    exact (interior_subset hv).1
  · intro v hv
    exact ((interior_subset hv).2.1.of_le le_top).contDiffWithinAt
  · intro b s a y v hv
    exact ((interior_subset hv).2.2 b s a y).of_le le_top |>.contDiffWithinAt

end CausalSmith.Stat.LogoddsLowsmoothFrontier
