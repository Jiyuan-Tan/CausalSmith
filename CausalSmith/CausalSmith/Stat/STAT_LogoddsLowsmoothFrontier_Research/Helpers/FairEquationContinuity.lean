module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEquationRegularity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! # Continuity of the normalized fair equation through its axes

Compact domination justifies continuity of both Taylor integrations. The exact
endpoint numerator identity then extends to the actual normalized equation on
both zero axes, providing genuine bracket roots for the literal selector.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A continuous family on a compact parameter set has a continuous unit-interval integral.](goal) Under [the stated assumptions](hyp:hS,F). Under [the stated assumptions](hyp:hF). -/
-- @node: calibration_compact_intervalIntegral_continuousOn
lemma calibration_compact_intervalIntegral_continuousOn {X : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] (S : Set X) (hS : IsCompact S)
    (F : X → ℝ → ℝ) (hF : ContinuousOn F.uncurry (S ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x => ∫ y in (0 : ℝ)..1, F x y) S := by
  obtain ⟨B, hB⟩ := (hS.prod isCompact_Icc).bddAbove_image hF.norm
  have hslice (x : X) (hx : x ∈ S) : ContinuousOn (F x) (Set.Icc (0 : ℝ) 1) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hx,hy⟩)
  intro x hx
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => B)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hslice z hz).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with z hz
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    exact hB ⟨(z,y), ⟨hz,hy.1.le,hy.2⟩, rfl⟩
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    exact (hF.comp (continuousOn_id.prodMk continuousOn_const)
        (fun z hz => ⟨hz,hy.1.le,hy.2⟩)) x hx

/-- [The compact box on which the fair Taylor equation is used. -/
-- @node: fairTaylorParameterRegion
def fairTaylorParameterRegion : Set (Fin 4 → ℝ) :=
  Set.pi Set.univ (fun i => if i = 0 then Set.Icc (0 : ℝ) (1 / 4)
    else if i = 1 then Set.Icc (-(1 / 100 : ℝ)) (1 / 100)
    else if i = 2 then Set.Icc (3 / 10 : ℝ) (1 / 2) else Set.Icc (0 : ℝ) 1)

/-- Coordinate characterization of the closed Taylor box. [the stated conclusion](goal) holds. -/
-- @node: fairTaylorParameterRegion_mem
lemma fairTaylorParameterRegion_mem (v : Fin 4 → ℝ) :
    v ∈ fairTaylorParameterRegion ↔ v 0 ∈ Set.Icc (0 : ℝ) (1 / 4) ∧
      |v 1| ≤ 1 / 100 ∧ v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2) ∧ v 3 ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [fairTaylorParameterRegion, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h
    exact ⟨by simpa using h 0, abs_le.mpr (by simpa using h 1),
      by simpa using h 2, by simpa using h 3⟩
  · rintro ⟨ht,hδ,hξ,hu⟩ i
    fin_cases i
    · simpa using ht
    · simpa using abs_le.mp hδ
    · simpa using hξ
    · simpa using hu

/-- Compactness includes both removable axes and all spatial endpoints. [the stated conclusion](goal) holds. -/
-- @node: fairTaylorParameterRegion_isCompact
lemma fairTaylorParameterRegion_isCompact : IsCompact fairTaylorParameterRegion :=
  isCompact_univ_pi (fun i => by
    split
    · exact isCompact_Icc
    · split
      · exact isCompact_Icc
      · split <;> exact isCompact_Icc)

/-- The actual weighted Taylor integrand is smooth jointly in the parameters
and its two integration coordinates on full neighborhoods of the closed box. [the documented result](goal) Under [the stated assumptions](hyp:hz,hs,hv). -/
-- @node: fairTaylorIntegrand_contDiffAt
lemma fairTaylorIntegrand_contDiffAt (z : ((Fin 4 → ℝ) × ℝ) × ℝ)
    (hz : z.1.1 ∈ fairTaylorParameterRegion)
    (hs : z.1.2 ∈ Set.Icc (0 : ℝ) 1) (hv : z.2 ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (fun w : ((Fin 4 → ℝ) × ℝ) × ℝ =>
      (1-w.2)*deriv (fun T => deriv (deriv (fun D =>
        fairNumerator T D (w.1.1 2) (w.1.1 3))) (w.2*w.1.1 1)) (w.1.2*w.1.1 0)) z := by
  obtain ⟨ht,hδ,hξ,hu⟩ := (fairTaylorParameterRegion_mem _).mp hz
  have ht' : z.1.2*z.1.1 0 ∈ Set.Icc (0 : ℝ) (1 / 4) :=
    ⟨mul_nonneg hs.1 ht.1, by nlinarith [hs.2,ht.1,ht.2]⟩
  have hδ' : |z.2*z.1.1 1| ≤ 1 / 100 :=
    (calibration_segment_abs_le _ _ (calibration_unit_mul_mem_segment _ _ hv)).trans hδ
  have hp : ContDiffAt ℝ ⊤ (fun w : ((Fin 4 → ℝ) × ℝ) × ℝ =>
      ![w.1.2*w.1.1 0,w.2*w.1.1 1,w.1.1 2,w.1.1 3]) z := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hderiv := (fairNumerator_taylor_deriv_contDiffAt
    ![z.1.2*z.1.1 0,z.2*z.1.1 1,z.1.1 2,z.1.1 3] ht' hδ' hξ).comp z hp
  apply (show ContDiffAt ℝ ⊤ (fun w : ((Fin 4 → ℝ) × ℝ) × ℝ => 1-w.2) z by fun_prop).mul
  simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] using hderiv

/-- The double Taylor integral is jointly continuous through both axes. Compact bounds on the actual integrand justify both integrations. [The stated conclusion follows](goal). -/
-- @node: fairEquation_continuousOn
@[fun_prop] lemma fairEquation_continuousOn : ContinuousOn (fun w : Fin 4 → ℝ =>
    fairEquation (w 0) (w 1) (w 2) (w 3)) fairTaylorParameterRegion := by
  let F : ((Fin 4 → ℝ) × ℝ) → ℝ → ℝ := fun z v =>
    (1-v)*deriv (fun T => deriv (deriv (fun D =>
      fairNumerator T D (z.1 2) (z.1 3))) (v*z.1 1)) (z.2*z.1 0)
  have hF : ContinuousOn F.uncurry
      ((fairTaylorParameterRegion ×ˢ Set.Icc (0 : ℝ) 1) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro z hz
    exact (fairTaylorIntegrand_contDiffAt z hz.1.1 hz.1.2 hz.2).continuousAt.continuousWithinAt
  have hInner := calibration_compact_intervalIntegral_continuousOn _
    (fairTaylorParameterRegion_isCompact.prod isCompact_Icc) F hF
  exact calibration_compact_intervalIntegral_continuousOn _
    fairTaylorParameterRegion_isCompact
    (fun w s => ∫ v in (0 : ℝ)..1, F (w,s) v) hInner

/-- Endpoint roots persist through zero effect for every nonzero signed amplitude. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:ht,hδ,hu,hδne) hold, and [the stated conclusion follows](goal). -/
-- @node: fairEquation_endpoint_zero_nonzero_amplitude
lemma fairEquation_endpoint_zero_nonzero_amplitude (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hu : u = 0 ∨ u = 1) (hδne : δ ≠ 0) :
    fairEquation t δ (2 / 5) u = 0 := by
  have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hu with rfl | rfl <;> constructor <;> norm_num
  have hc : ContinuousOn (fun T => fairEquation T δ (2 / 5) u) (Set.Icc (0 : ℝ) (1 / 4)) := by
    have hp : ContinuousOn (fun T : ℝ => ![T,δ,2 / 5,u]) (Set.Icc (0 : ℝ) (1 / 4)) := by
      apply Continuous.continuousOn
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have h := fairEquation_continuousOn.comp hp (fun T hT =>
      (fairTaylorParameterRegion_mem _).mpr ⟨hT,hδ,by
        change (2 / 5 : ℝ) ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)
        constructor <;> norm_num,hu'⟩)
    simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] using h
  have he : Set.EqOn (fun T => fairEquation T δ (2 / 5) u) (fun _ => 0)
      (Set.Ioo (0 : ℝ) (1 / 4)) := by
    intro T hT
    exact fairEquation_endpoint_zero_off_axes T δ u ⟨hT.1.le,hT.2.le⟩ hδ hu
      (mul_ne_zero (ne_of_gt hT.1) hδne)
  exact he.of_subset_closure hc continuousOn_const Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 4)]) ht

/-- [The endpoint center solves the actual Taylor-normalized equation also on
both removable axes, by joint continuity and the exact off-axis identity. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hu). -/
-- @node: fairEquation_endpoint_zero
lemma fairEquation_endpoint_zero (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hu : u = 0 ∨ u = 1) : fairEquation t δ (2 / 5) u = 0 := by
  by_cases hδne : δ ≠ 0
  · exact fairEquation_endpoint_zero_nonzero_amplitude t δ u ht hδ hu hδne
  · have hδzero : δ = 0 := not_ne_iff.mp hδne
    subst δ
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      rcases hu with rfl | rfl <;> constructor <;> norm_num
    have hc : ContinuousOn (fun D => fairEquation t D (2 / 5) u) (Set.Icc (0 : ℝ) (1 / 100)) := by
      have hp : ContinuousOn (fun D : ℝ => ![t,D,2 / 5,u]) (Set.Icc (0 : ℝ) (1 / 100)) := by
        apply Continuous.continuousOn
        apply continuous_pi
        intro i
        fin_cases i <;> dsimp <;> fun_prop
      have h := fairEquation_continuousOn.comp hp (fun D hD =>
        (fairTaylorParameterRegion_mem _).mpr
          ⟨ht,by change |D| ≤ 1 / 100; rw [abs_of_nonneg hD.1]; exact hD.2,
          by change (2 / 5 : ℝ) ∈ Set.Icc (3 / 10 : ℝ) (1 / 2); constructor <;> norm_num,hu'⟩)
      simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val] using h
    have he : Set.EqOn (fun D => fairEquation t D (2 / 5) u) (fun _ => 0)
        (Set.Ioo (0 : ℝ) (1 / 100)) := by
      intro D hD
      exact fairEquation_endpoint_zero_nonzero_amplitude t D u ht
        (by simpa only [abs_of_pos hD.1] using hD.2.le) hu (ne_of_gt hD.1)
    exact he.of_subset_closure hc continuousOn_const Set.Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 100)]) (by constructor <;> norm_num)

/-- [Every endpoint has an actual bracket root, with no off-axis restriction.](goal) Under [the stated assumptions](hyp:hδ,hu). Under [the stated assumptions](hyp:ht). -/
-- @node: fairEquation_endpoint_exists
lemma fairEquation_endpoint_exists (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hu : u = 0 ∨ u = 1) :
    ∃ p ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2), fairEquation t δ p u = 0 :=
  ⟨2 / 5, by constructor <;> norm_num, fairEquation_endpoint_zero t δ u ht hδ hu⟩

/-- [At either spatial endpoint the literal selected fair root is a genuine
bracket zero, including zero effect and zero amplitude. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hu). -/
-- @node: fairRoot_endpoint_spec
lemma fairRoot_endpoint_spec (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hu : u = 0 ∨ u = 1) :
    fairRoot t δ u ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2) ∧
      fairEquation t δ (fairRoot t δ u) u = 0 :=
  fairRoot_spec t δ u (fairEquation_endpoint_exists t δ u ht hδ hu)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
