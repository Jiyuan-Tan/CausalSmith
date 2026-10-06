module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairAmbientSmoothness

/-! # Common open fair-calibration neighborhood

The implicit equation supplies genuine roots on ambient neighborhoods of the
zero-amplitude effect and spatial rectangle. Persistent bracket uniqueness
identifies the actual selector there. Compactness then puts a closed signed
amplitude box inside one open set for the root and every substituted cell.
-/
public section
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- At zero amplitude the fair selector remains a genuine, unique narrow-bracket
root on a full ambient parameter neighborhood. [the documented result](goal) Under [the stated assumptions](hyp:ht,hu). -/
-- @node: fairCalibrationZero_eventually_zero_smooth
lemma fairCalibrationZero_eventually_zero_smooth (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ v : Fin 3 → ℝ in 𝓝 ![t,0,u], FairCalibrationZero (1/20) v ∧
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v := by
  obtain ⟨r,hr,hrsmall,hpos⟩ := fairEquation_uniform_center_slope_pos
  obtain ⟨a,ha,hasmall,hconf⟩ := fairEquation_uniform_root_confined r hr
  have hUnique := fairEquation_eventually_unique_of_center_control t 0 u r
    ht (by norm_num) hu hr hrsmall
    (fun x hx => hpos t 0 x u ht (by simpa using hr.le)
      (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩) hu)
    (fun x hx he => hconf t 0 u x ht (by simpa using ha.le) hu hx he)
  let F : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    fairEquation (z.1 0) (z.1 1) z.2 (z.1 2)
  have hx : ![t,0,2/5,u] ∈ fairTaylorParameterRegion :=
    (fairTaylorParameterRegion_mem _).mpr
      ⟨ht,by norm_num,by
        change (2/5 : ℝ) ∈ Set.Icc (3/10) (1/2)
        constructor <;> norm_num,hu⟩
  have hFevent : ∀ᶠ z : (Fin 3 → ℝ) × ℝ in 𝓝 (![t,0,u],2/5),
      ContDiffAt ℝ ∞ F z := by
    have he := (by fun_prop : ContinuousAt (fun z : (Fin 3 → ℝ) × ℝ =>
      ![z.1 0,z.1 1,z.2,z.1 2]) (![t,0,u],2/5))
      (fairEquation_eventually_contDiffAt _ hx)
    filter_upwards [he] with z hz
    change ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ =>
      fairEquation (w 0) (w 1) (w 2) (w 3)) ![z.1 0,z.1 1,z.2,z.1 2] at hz
    exact hz.comp (f := fun z : (Fin 3 → ℝ) × ℝ => ![z.1 0,z.1 1,z.2,z.1 2]) z
      (by apply contDiffAt_pi.mpr; intro i; fin_cases i <;> dsimp <;> fun_prop)
  obtain ⟨D,hDsub,hDopen,hDbase⟩ := mem_nhds_iff.mp hFevent
  have hSmooth : ContDiffOn ℝ ∞ F D := by
    intro z hz
    have hh : ContDiffAt ℝ ∞ F z := hDsub hz
    exact hh.contDiffWithinAt
  obtain ⟨U,V,g,hU,hbU,hV,hbV,hUV,hg,hgBase,hgRange,hgGraph⟩ :=
    scalar_infty_implicit_function 3 F D ![t,0,u] (2/5) hDopen hDbase
      hSmooth
      (fairEquation_zero_amplitude_center t u ht)
      (ne_of_gt (fairEquation_center_slope_pos t u ht hu))
  have hRange : ∀ᶠ v in 𝓝 ![t,0,u],
      g v ∈ Set.Ioo ((2/5 : ℝ)-1/20) (2/5+1/20) :=
    (hg.contDiffAt (hU.mem_nhds hbU)).continuousAt
      (by rw [hgBase]; exact isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
  have hevent : (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) =ᶠ[𝓝 ![t,0,u]] g := by
    filter_upwards [hU.mem_nhds hbU,hRange,hUnique] with v hv hgv huniq
    have hwide : g v ∈ Set.Ioo (3/10 : ℝ) (1/2) := by
      constructor <;> linarith [hgv.1,hgv.2]
    have hz : fairEquation (v 0) (v 1) (g v) (v 2) = 0 :=
      (hgGraph v hv (g v) (hgRange v hv)).mpr rfl
    have hs := fairRoot_spec (v 0) (v 1) (v 2) ⟨g v,hwide,hz⟩
    exact huniq _ hs.1 _ hwide hs.2 hz
  filter_upwards [hU.mem_nhds hbU,hRange,hUnique,hevent,hevent.eventually_nhds]
    with v hv hgv huniq he heNear
  have hwide : g v ∈ Set.Ioo (3/10 : ℝ) (1/2) := by
    constructor <;> linarith [hgv.1,hgv.2]
  have hz : fairEquation (v 0) (v 1) (g v) (v 2) = 0 :=
    (hgGraph v hv (g v) (hgRange v hv)).mpr rfl
  have hs := fairRoot_spec (v 0) (v 1) (v 2) ⟨g v,hwide,hz⟩
  refine ⟨⟨he.symm ▸ hgv,hs.1,hs.2,?_⟩,?_⟩
  · intro p hp hep
    have hpwide : p ∈ Set.Ioo (3/10 : ℝ) (1/2) := by
      constructor <;> linarith [hp.1,hp.2]
    exact huniq _ hpwide _ hs.1 hep hs.2
  · exact (hg.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq heNear

/-- One open set contains a positive closed signed amplitude box over the
entire fair effect and spatial ranges, with unique roots and smooth actual cells. [the documented result](goal) -/
-- @node: fair_calibration_open_neighbourhood
lemma fair_calibration_open_neighbourhood :
    ∃ ε : ℝ, ∃ V : Set (Fin 3 → ℝ), 0 < ε ∧ IsOpen V ∧
      fairParameterRegion ε ⊆ V ∧
      (∀ v ∈ V, FairCalibrationZero (1/20) v) ∧
      ContDiffOn ℝ ∞ (fun v : Fin 3 → ℝ => fairRoot (v 0) (v 1) (v 2)) V ∧
      (∀ b s a y, ContDiffOn ℝ ∞ (localFairCell b s a y) V) := by
  let S : Set (Fin 3 → ℝ) := {v | FairCalibrationZero (1/20) v ∧
    ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v ∧
    ∀ b s a y, ContDiffAt ℝ ∞ (localFairCell b s a y) v}
  let V := interior S
  have hbase (t u : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4))
      (hu : u ∈ Set.Icc (0 : ℝ) 1) : ![t,0,u] ∈ V := by
    have hzero := fairCalibrationZero_eventually_zero_smooth t u ht hu
    have hroot := hzero.mono (fun v hv => hv.2)
    have hq := hroot.self_of_nhds
    have hcells : ∀ᶠ v in 𝓝 ![t,0,u],
        ∀ b s a y, ContDiffAt ℝ ∞ (localFairCell b s a y) v := by
      simp only [Filter.eventually_all]
      intro b s a y
      exact localFairCell_eventually_contDiffAt_of_root t u ht hq.continuousAt hroot b s a y
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hzero,hcells] with v hv hc
    exact ⟨hv.1,hv.2,hc⟩
  let K := Set.Icc (0 : ℝ) (1/4) ×ˢ Set.Icc (0 : ℝ) 1
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0, ∀ z ∈ K, ![z.1,δ,z.2] ∈ V := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro z hz
    exact (by fun_prop : ContinuousAt (fun w : ℝ × (ℝ × ℝ) =>
      ![w.2.1,w.1,w.2.2]) (0,z))
      (isOpen_interior.mem_nhds (hbase z.1 z.2 hz.1 hz.2))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ/2,V,by linarith,isOpen_interior,?_,?_,?_,?_⟩
  · intro v hv
    have hmem : v 1 ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero]
      linarith [hv.2.1]
    have he : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
    simpa only [he] using hball hmem (v 0,v 2) ⟨hv.1,hv.2.2⟩
  · intro v hv
    exact (interior_subset hv).1
  · intro v hv
    exact (interior_subset hv).2.1.contDiffWithinAt
  · intro b s a y v hv
    exact ((interior_subset hv).2.2 b s a y).contDiffWithinAt

end CausalSmith.Stat.LogoddsLowsmoothFrontier
