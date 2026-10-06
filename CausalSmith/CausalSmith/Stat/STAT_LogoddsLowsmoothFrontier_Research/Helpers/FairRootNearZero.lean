module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairZeroEffect
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ScalarImplicitFunction
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Local fair-root regularity at zero effect

The explicit zero-effect equation supplies a nonzero center slope. Compactness
preserves its signs and local monotonicity, identifying the literal selector
with a smooth implicit branch on full neighborhoods of the zero-effect axis.
-/
public section
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The normalized equation has the Bernoulli-variance slope on the zero-effect axis.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:hξ,hu). -/
-- @node: fairEquation_center_deriv_zero_effect
lemma fairEquation_center_deriv_zero_effect (δ ξ u : ℝ)
    (hδ : |δ| ≤ 1/100) (hξ : ξ ∈ Set.Ioo (3/10 : ℝ) (1/2))
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun x => fairEquation 0 δ x u) ξ = (1-2*ξ)/(6/25) := by
  have hd : HasDerivAt (fun x : ℝ => -1+x*(1-x)/(6/25))
      ((1-2*ξ)/(6/25)) ξ := by
    convert (hasDerivAt_const ξ (-1 : ℝ)).add
      (((hasDerivAt_id ξ).mul ((hasDerivAt_const ξ (1 : ℝ)).sub
        (hasDerivAt_id ξ))).div_const (6/25)) using 1 <;> first | rfl | (dsimp; ring)
  apply (hd.congr_of_eventuallyEq ?_).deriv
  filter_upwards [isOpen_Ioo.mem_nhds hξ] with x hx
  exact fairEquation_zero_effect δ x u hδ ⟨hx.1.le,hx.2.le⟩ hu

/-- [On a full parameter neighborhood, every bracket value remains close to
its explicit zero-effect value and remains jointly smooth. [the documented result](goal) Under [the stated assumptions](hyp:hu). -/
-- @node: fairEquation_eventually_zero_effect_control
lemma fairEquation_eventually_zero_effect_control (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![0,0,u], ∀ ξ ∈ Set.Icc (3/10 : ℝ) (1/2),
      ContDiffAt ℝ 1 (fun z : (Fin 3 → ℝ) × ℝ =>
        fairEquation (z.1 0) (z.1 1) z.2 (z.1 2)) (a,ξ) ∧
      |fairEquation (a 0) (a 1) ξ (a 2) - (-1+ξ*(1-ξ)/(6/25))| < 1/100 := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro ξ hξ
  have hx : ![0,0,ξ,u] ∈ fairTaylorParameterRegion :=
    (fairTaylorParameterRegion_mem _).mpr
      ⟨by constructor <;> norm_num, by norm_num, hξ, hu⟩
  have hs := (fairEquation_contDiffAt _ hx).comp (![0,0,u],ξ)
    (show ContDiffAt ℝ ∞ (fun z : (Fin 3 → ℝ) × ℝ =>
      ![z.1 0,z.1 1,z.2,z.1 2]) (![0,0,u],ξ) by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop)
  have hc : ContinuousAt (fun z : (Fin 3 → ℝ) × ℝ =>
      |fairEquation (z.1 0) (z.1 1) z.2 (z.1 2) -
        (-1+z.2*(1-z.2)/(6/25))|) (![0,0,u],ξ) := by
    exact (hs.continuousAt.sub (by fun_prop)).abs
  exact ((hs.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)).and (hc.eventually (gt_mem_nhds (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [fairEquation_zero_effect 0 ξ u (by norm_num) hξ hu]
    norm_num)))

/-- The center derivative stays uniformly positive on a smaller bracket in
full neighborhoods of zero effect and amplitude, including spatial endpoints. [the documented result](goal) Under [the stated assumptions](hyp:hu). -/
-- @node: fairEquation_eventually_center_deriv_pos
lemma fairEquation_eventually_center_deriv_pos (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![0,0,u], ∀ ξ ∈ Set.Icc (7/20 : ℝ) (9/20),
      1/4 < deriv (fun x => fairEquation (a 0) (a 1) x (a 2)) ξ := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro ξ hξ
  have hξ' : ξ ∈ Set.Icc (3/10 : ℝ) (1/2) := ⟨by linarith [hξ.1],by linarith [hξ.2]⟩
  have hx : ![0,0,ξ,u] ∈ fairTaylorParameterRegion :=
    (fairTaylorParameterRegion_mem _).mpr
      ⟨by constructor <;> norm_num, by norm_num, hξ', hu⟩
  have hc := (fairEquation_center_deriv_contDiffAt _ hx).continuousAt.comp
    (f := fun z : (Fin 3 → ℝ) × ℝ => ![z.1 0,z.1 1,z.2,z.1 2])
    (by fun_prop : ContinuousAt (fun z : (Fin 3 → ℝ) × ℝ =>
      ![z.1 0,z.1 1,z.2,z.1 2]) (![0,0,u],ξ))
  apply hc.eventually
  apply lt_mem_nhds
  change 1/4 < deriv (fun x => fairEquation 0 0 x u) ξ
  rw [fairEquation_center_deriv_zero_effect 0 ξ u (by norm_num)
    ⟨by linarith [hξ.1],by linarith [hξ.2]⟩ hu]
  linarith [hξ.2]

/-- Uniform approximation to the limiting variance equation excludes roots
outside a smaller bracket, rather than presupposing the selected root's value. [the documented result](goal) Under [the stated assumptions](hyp:hq,he,hc). -/
-- @node: fairEquation_root_confined_near_zero
lemma fairEquation_root_confined_near_zero (t δ u q : ℝ)
    (hq : q ∈ Set.Ioo (3/10 : ℝ) (1/2))
    (he : fairEquation t δ q u = 0)
    (hc : |fairEquation t δ q u - (-1+q*(1-q)/(6/25))| < 1/100) :
    q ∈ Set.Ioo (7/20 : ℝ) (9/20) := by
  rw [he] at hc
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hc
  constructor
  · by_contra hn
    have hqlo : q ≤ 7/20 := le_of_not_gt hn
    have hprod := mul_nonneg (show 0 ≤ 7/20-q by linarith)
      (show 0 ≤ 13/20-q by linarith)
    nlinarith
  · by_contra hn
    have hqhi : 9/20 ≤ q := le_of_not_gt hn
    have hprod := mul_nonneg (show 0 ≤ q-9/20 by linarith)
      (show 0 ≤ 11/20-q by linarith [hq.2])
    nlinarith

/-- [Opposite signs give an interior root, and the derivative floor makes it
unique throughout the original selector bracket on a full parameter neighborhood. [the documented result](goal) Under [the stated assumptions](hyp:hu). -/
-- @node: fairEquation_eventually_existsUnique_near_zero
lemma fairEquation_eventually_existsUnique_near_zero (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![0,0,u],
      ∃! q : ℝ, q ∈ Set.Ioo (3/10 : ℝ) (1/2) ∧
        fairEquation (a 0) (a 1) q (a 2) = 0 := by
  filter_upwards [fairEquation_eventually_zero_effect_control u hu,
    fairEquation_eventually_center_deriv_pos u hu] with a hcontrol hpos
  let f : ℝ → ℝ := fun q => fairEquation (a 0) (a 1) q (a 2)
  have hcont : ContinuousOn f (Set.Icc (7/20 : ℝ) (9/20)) := by
    intro q hq
    have hq' : q ∈ Set.Icc (3/10 : ℝ) (1/2) :=
      ⟨by linarith [hq.1],by linarith [hq.2]⟩
    exact (((hcontrol q hq').1.continuousAt).comp
      (f := fun q : ℝ => (a,q)) (by fun_prop)).continuousWithinAt
  have hlow := (hcontrol (7/20) (by constructor <;> norm_num)).2
  have hhigh := (hcontrol (9/20) (by constructor <;> norm_num)).2
  have hsignlo : f (7/20) < 0 := by
    dsimp [f]
    norm_num at hlow
    linarith [(abs_lt.mp hlow).2]
  have hsignhi : 0 < f (9/20) := by
    dsimp [f]
    norm_num at hhigh
    linarith [(abs_lt.mp hhigh).1]
  obtain ⟨q,hq,heq⟩ := intermediate_value_Icc (by norm_num : (7/20 : ℝ) ≤ 9/20)
    hcont (show (0 : ℝ) ∈ Set.Icc (f (7/20)) (f (9/20)) from ⟨hsignlo.le,hsignhi.le⟩)
  have hmono : StrictMonoOn f (Set.Icc (7/20 : ℝ) (9/20)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro x hx
    rw [interior_Icc] at hx
    exact lt_trans (by norm_num : (0 : ℝ) < 1/4) (hpos x ⟨hx.1.le,hx.2.le⟩)
  refine ⟨q, ⟨⟨by linarith [hq.1],by linarith [hq.2]⟩,heq⟩, ?_⟩
  intro p hp
  have hp' := fairEquation_root_confined_near_zero (a 0) (a 1) (a 2) p hp.1 hp.2
    (hcontrol p ⟨hp.1.1.le,hp.1.2.le⟩).2
  exact hmono.injOn ⟨hp'.1.le,hp'.2.le⟩ hq (hp.2.trans heq.symm)

/-- One absolute signed neighborhood supplies unique fair bracket roots for
all spatial coordinates, including both endpoints, when the effect is near zero. [the documented result](goal) -/
-- @node: fairEquation_uniform_existsUnique_near_zero
lemma fairEquation_uniform_existsUnique_near_zero : ∃ ε : ℝ, 0 < ε ∧
    ∀ t δ u : ℝ, |t| ≤ ε → |δ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      ∃! q : ℝ, q ∈ Set.Ioo (3/10 : ℝ) (1/2) ∧ fairEquation t δ q u = 0 := by
  have hevent : ∀ᶠ a : ℝ × ℝ in 𝓝 (0,0), ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∃! q : ℝ, q ∈ Set.Ioo (3/10 : ℝ) (1/2) ∧ fairEquation a.1 a.2 q u = 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    exact (by fun_prop : ContinuousAt (fun z : (ℝ × ℝ) × ℝ =>
      ![z.1.1,z.1.2,z.2]) ((0,0),u)) (fairEquation_eventually_existsUnique_near_zero u hu)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨d/2, by linarith, ?_⟩
  intro t δ u ht hδ hu
  have hmem : (t,δ) ∈ Metric.ball (0,0) d := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  exact hball hmem u hu

/-- A C∞ equation and nearby uniqueness give C∞ regularity of the actual
bracket selector. A C1 implicit branch first supplies continuity; the pointwise
implicit theorem then upgrades it without an analyticity assumption. [the documented result](goal) Under [the stated assumptions](hyp:F,l,hF,hb,hZero,hPartial,hSpec,hUnique). -/
-- @node: scalar_bracket_selector_contDiffAt_infty
lemma scalar_bracket_selector_contDiffAt_infty (d : ℕ)
    (F : ((Fin d → ℝ) × ℝ) → ℝ) (q : (Fin d → ℝ) → ℝ)
    (b : Fin d → ℝ) (l r : ℝ)
    (hF : ContDiffAt ℝ ∞ F (b,q b))
    (hb : q b ∈ Set.Ioo l r) (hZero : F (b,q b) = 0)
    (hPartial : deriv (fun x => F (b,x)) (q b) ≠ 0)
    (hSpec : ∀ a, (∃ x ∈ Set.Ioo l r, F (a,x) = 0) →
      q a ∈ Set.Ioo l r ∧ F (a,q a) = 0)
    (hUnique : ∀ᶠ a in 𝓝 b, ∀ x ∈ Set.Ioo l r, ∀ y ∈ Set.Ioo l r,
      F (a,x) = 0 → F (a,y) = 0 → x = y) :
    ContDiffAt ℝ ∞ q b := by
  have hC1 := hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  obtain ⟨S,hS,hSmooth⟩ := hC1.contDiffOn le_rfl (by simp)
  obtain ⟨D,hDsub,hDopen,hDbase⟩ := mem_nhds_iff.mp hS
  obtain ⟨U,V,g,hU,hbU,hV,hbV,hUV,hg,hgBase,hgRange,hgGraph⟩ :=
    scalar_implicit_function d F D b (q b) hDopen hDbase
      (hSmooth.mono hDsub) hZero hPartial
  have hgAt := hg.contDiffAt (hU.mem_nhds hbU)
  have hRange : ∀ᶠ a in 𝓝 b, g a ∈ Set.Ioo l r :=
    hgAt.continuousAt (by rw [hgBase]; exact isOpen_Ioo.mem_nhds hb)
  have he : q =ᶠ[𝓝 b] g := by
    filter_upwards [hU.mem_nhds hbU,hRange,hUnique] with a ha hga hunique
    have hz : F (a,g a) = 0 := (hgGraph a ha (g a) (hgRange a ha)).mpr rfl
    obtain ⟨hqa,hqz⟩ := hSpec a ⟨g a,hga,hz⟩
    exact hunique (q a) hqa (g a) hga hqz hz
  have hq : ContinuousAt q b := hgAt.continuousAt.congr_of_eventuallyEq he
  have hz : ∀ᶠ a in 𝓝 b, F (a,q a) = 0 := by
    filter_upwards [hU.mem_nhds hbU,he] with a ha hea
    rw [hea]
    exact (hgGraph a ha (g a) (hgRange a ha)).mpr rfl
  exact scalar_implicit_root_contDiffAt d ∞ (by simp) F q b hF hq hz hPartial

/-- The literal fair root is jointly C∞ at zero effect and zero amplitude,
on full neighborhoods of every spatial point in the closed interval. [the documented result](goal) Under [the stated assumptions](hyp:hu). -/
-- @node: fairRoot_contDiffAt_zero_effect_amplitude
lemma fairRoot_contDiffAt_zero_effect_amplitude (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun a : Fin 3 → ℝ => fairRoot (a 0) (a 1) (a 2)) ![0,0,u] := by
  let F : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    fairEquation (z.1 0) (z.1 1) z.2 (z.1 2)
  have hbase : fairRoot 0 0 u = 2/5 := fairRoot_zero_effect 0 u (by norm_num) hu
  apply scalar_bracket_selector_contDiffAt_infty 3 F
    (fun a => fairRoot (a 0) (a 1) (a 2)) ![0,0,u] (3/10) (1/2)
  · simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,hbase]
    have hx : ![0,0,2/5,u] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr
        ⟨by constructor <;> norm_num,by norm_num,by
          change (2/5 : ℝ) ∈ Set.Icc (3/10) (1/2)
          constructor <;> norm_num,hu⟩
    exact (fairEquation_contDiffAt _ hx).comp (![0,0,u],2/5)
      (show ContDiffAt ℝ ∞ (fun z : (Fin 3 → ℝ) × ℝ =>
        ![z.1 0,z.1 1,z.2,z.1 2]) (![0,0,u],2/5) by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
  · simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,hbase]
    constructor <;> norm_num
  · change fairEquation 0 0 (fairRoot 0 0 u) u = 0
    rw [hbase]
    exact fairEquation_zero_effect_center 0 u (by norm_num) hu
  · change deriv (fun x => fairEquation 0 0 x u) (fairRoot 0 0 u) ≠ 0
    rw [hbase,fairEquation_center_deriv_zero_effect 0 (2/5) u
      (by norm_num) (by constructor <;> norm_num) hu]
    norm_num
  · intro a ha
    exact fairRoot_spec (a 0) (a 1) (a 2) ha
  · filter_upwards [fairEquation_eventually_existsUnique_near_zero u hu] with a ha
    intro x hx y hy hex hey
    exact ha.unique ⟨hx,hex⟩ ⟨hy,hey⟩

/-- The actual selected fair root solves its normalized equation and is the
only root in the prescribed bracket on one absolute neighborhood of the origin. [the documented result](goal) -/
-- @node: fairRoot_uniform_spec_near_zero
lemma fairRoot_uniform_spec_near_zero : ∃ ε : ℝ, 0 < ε ∧
    ∀ t δ u : ℝ, |t| ≤ ε → |δ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      fairEquation t δ (fairRoot t δ u) u = 0 ∧
      ∀ q ∈ Set.Ioo (3/10 : ℝ) (1/2), fairEquation t δ q u = 0 →
        q = fairRoot t δ u := by
  obtain ⟨ε,hε,hroots⟩ := fairEquation_uniform_existsUnique_near_zero
  refine ⟨ε,hε,?_⟩
  intro t δ u ht hδ hu
  have hr := hroots t δ u ht hδ hu
  have hs := fairRoot_spec t δ u hr.exists
  exact ⟨hs.2,fun q hq he => hr.unique ⟨hq,he⟩ hs⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
