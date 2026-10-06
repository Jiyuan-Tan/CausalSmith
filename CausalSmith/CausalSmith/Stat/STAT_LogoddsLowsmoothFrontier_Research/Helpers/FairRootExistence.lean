module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEndpointUniqueness

/-! # Uniform fair-root existence over the full effect range

The strictly separated zero-amplitude bracket signs persist on one signed
amplitude neighborhood by compactness in effect and spatial coordinate.
Continuity in the centering argument then supplies an interior root.
-/
public section
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- One absolute signed amplitude neighborhood preserves the fair bracket
signs for all effects and spatial coordinates in their closed prescribed ranges. [the documented result](goal) -/
-- @node: fairEquation_uniform_bracket_signs
lemma fairEquation_uniform_bracket_signs : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧
    ∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 →
      fairEquation t δ (3/10) u < 0 ∧ 0 < fairEquation t δ (1/2) u := by
  let K := Set.Icc (0 : ℝ) (1/4) ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0, ∀ z ∈ K,
      fairEquation z.1 δ (3/10) z.2 < 0 ∧
        0 < fairEquation z.1 δ (1/2) z.2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hcont (q : ℝ) (hq : q ∈ Set.Icc (3/10 : ℝ) (1/2)) :
        ContinuousAt (fun w : ℝ × (ℝ × ℝ) =>
          fairEquation w.2.1 w.1 q w.2.2) (0,z) := by
      have hbox : ![z.1,0,q,z.2] ∈ fairTaylorParameterRegion :=
        (fairTaylorParameterRegion_mem _).mpr ⟨hz.1,by norm_num,hq,hz.2⟩
      have hp : ContDiffAt ℝ ∞ (fun w : ℝ × (ℝ × ℝ) =>
          ![w.2.1,w.1,q,w.2.2]) (0,z) := by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop
      have hh := (fairEquation_contDiffAt ![z.1,0,q,z.2] hbox).comp (0,z) hp
      exact hh.continuousAt
    have hs := fairEquation_zero_amplitude_bracket_signs z.1 z.2 hz.1 hz.2
    exact ((hcont (3/10) (by constructor <;> norm_num)).eventually (gt_mem_nhds hs.1)).and
      ((hcont (1/2) (by constructor <;> norm_num)).eventually (lt_mem_nhds hs.2))
  obtain ⟨a,ha,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε := min (a/2) (1/100)
  refine ⟨ε,lt_min (by linarith) (by norm_num),min_le_right _ _,?_⟩
  intro t δ u ht hδ hu
  apply hball _ (t,u) ⟨ht,hu⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero]
  exact lt_of_le_of_lt (hδ.trans (min_le_left _ _)) (by linarith)

/-- The intermediate value theorem yields a genuine fair root in the full
selector bracket on one absolute signed amplitude neighborhood. [the documented result](goal) -/
-- @node: fairEquation_uniform_exists
lemma fairEquation_uniform_exists : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧
    ∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 →
      ∃ p ∈ Set.Ioo (3/10 : ℝ) (1/2), fairEquation t δ p u = 0 := by
  obtain ⟨ε,hε,hsmall,hsigns⟩ := fairEquation_uniform_bracket_signs
  refine ⟨ε,hε,hsmall,?_⟩
  intro t δ u ht hδ hu
  have hcont : ContinuousOn (fun p => fairEquation t δ p u)
      (Set.Icc (3/10 : ℝ) (1/2)) := by
    intro p hp
    have hbox : ![t,δ,p,u] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr ⟨ht,hδ.trans hsmall,hp,hu⟩
    have hmap : ContDiffAt ℝ ∞ (fun x : ℝ => ![t,δ,x,u]) p := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have hh := (fairEquation_contDiffAt ![t,δ,p,u] hbox).comp p hmap
    exact hh.continuousAt.continuousWithinAt
  obtain ⟨hlo,hhi⟩ := hsigns t δ u ht hδ hu
  obtain ⟨p,hp,he⟩ := intermediate_value_Icc (by norm_num : (3/10 : ℝ) ≤ 1/2)
    hcont (show (0 : ℝ) ∈ Set.Icc (fairEquation t δ (3/10) u)
      (fairEquation t δ (1/2) u) from ⟨hlo.le,hhi.le⟩)
  refine ⟨p,⟨?_,?_⟩,he⟩
  · have hn : p ≠ 3/10 := by intro h; subst p; linarith
    exact lt_of_le_of_ne hp.1 (Ne.symm hn)
  · have hn : p ≠ 1/2 := by intro h; subst p; linarith
    exact lt_of_le_of_ne hp.2 hn

end CausalSmith.Stat.LogoddsLowsmoothFrontier
