module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootExistence

/-! # Nonzero fair center slope over the full effect range

Differentiating the cleared endpoint identity at the asymmetric center proves
strict positivity of the actual normalized equation's center derivative.
The zero-effect extension handles the removable boundary without division.
-/
public section
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Differentiating the endpoint factorization at its center root gives a
cleared derivative identity throughout the full effect range. [the documented result](goal) Under [the stated assumptions](hyp:ht,hu). -/
-- @node: fairEquation_center_slope_cleared
lemma fairEquation_center_slope_cleared (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    t * deriv (fun x => fairEquation t 0 x u) (2/5) *
      (1+(Real.exp t-1)*(2/5))^3 * ((3/5)*(1+(2/5)*(Real.exp t-1))) =
      (Real.exp t-1)*Real.exp t*(8*(Real.exp t-1)+5)/10 := by
  let d := Real.exp t-1
  let H : ℝ → ℝ := fun x => fairEquation t 0 x u
  have hbox : ![t,0,2/5,u] ∈ fairTaylorParameterRegion :=
    (fairTaylorParameterRegion_mem _).mpr
      ⟨ht,by norm_num,by
        change (2/5 : ℝ) ∈ Set.Icc (3/10) (1/2)
        constructor <;> norm_num,hu⟩
  have hH : DifferentiableAt ℝ H (2/5) := by
    exact ((fairEquation_contDiffAt _ hbox).comp (2/5)
      (show ContDiffAt ℝ ∞ (fun x : ℝ => ![t,0,x,u]) (2/5) by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)).differentiableAt (by simp)
  have hz : H (2/5) = 0 := fairEquation_zero_amplitude_center t u ht
  have hB := (hasDerivAt_const (2/5 : ℝ) (1 : ℝ)).add
    ((hasDerivAt_id (2/5 : ℝ)).const_mul d)
  have hL : HasDerivAt (fun x => t*H x*(1+d*x)^3*((3/5)*(1+(2/5)*d)))
      (t*deriv H (2/5)*(1+d*(2/5))^3*((3/5)*(1+(2/5)*d))) (2/5) := by
    convert (((hH.hasDerivAt.const_mul t).mul (hB.pow 3)).mul_const
      ((3/5)*(1+(2/5)*d))) using 1 <;> first | rfl | (dsimp; rw [hz]; ring)
  have hQ := (((hasDerivAt_id (2/5 : ℝ)).pow 2).const_mul (25*d)).sub
    ((hasDerivAt_id (2/5 : ℝ)).const_mul (15*d))
  have hR : HasDerivAt (fun x => -d*Real.exp t*(5*x-2)*
      (25*d*x^2-15*d*x-6*d+25*x-15)/50)
      (d*Real.exp t*(8*d+5)/10) (2/5) := by
    convert ((((hasDerivAt_id (2/5 : ℝ)).const_mul 5).sub_const 2).const_mul
      (-d*Real.exp t)).mul
      (((hQ.sub_const (6*d)).add ((hasDerivAt_id (2/5 : ℝ)).const_mul 25)).sub_const 15)
      |>.div_const 50 using 1 <;> first | rfl | (dsimp; ring)
  have he : (fun x => t*H x*(1+d*x)^3*((3/5)*(1+(2/5)*d))) =ᶠ[𝓝 (2/5 : ℝ)]
      (fun x => -d*Real.exp t*(5*x-2)*(25*d*x^2-15*d*x-6*d+25*x-15)/50) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (2/5 : ℝ) ∈ Set.Ioo (3/10) (1/2) by constructor <;> norm_num)] with x hx
    have hx' : x ∈ Set.Icc (3/10 : ℝ) (1/2) := ⟨hx.1.le,hx.2.le⟩
    dsimp [H,d]
    rw [fairEquation_zero_amplitude_endpoint t x u ht hx']
    exact fairEquation_endpoint_factor_zero_amplitude t x ht hx'
  exact (hL.congr_of_eventuallyEq he.symm).unique hR

/-- The fair equation's center derivative is strictly positive, including
zero effect, at every point of the closed effect and position ranges. [the documented result](goal) Under [the stated assumptions](hyp:ht,hu). -/
-- @node: fairEquation_center_slope_pos
lemma fairEquation_center_slope_pos (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 < deriv (fun x => fairEquation t 0 x u) (2/5) := by
  by_cases hz : t = 0
  · subst t
    rw [fairEquation_center_deriv_zero_effect 0 (2/5) u (by norm_num)
      (by constructor <;> norm_num) hu]
    norm_num
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hd : 0 < Real.exp t-1 := by
    have h := Real.exp_lt_exp.mpr htpos
    simpa using sub_pos.mpr h
  have he := fairEquation_center_slope_cleared t u ht hu
  have hA : 0 < t*(1+(Real.exp t-1)*(2/5))^3*
      ((3/5)*(1+(2/5)*(Real.exp t-1))) := by positivity
  have hR : 0 < (Real.exp t-1)*Real.exp t*(8*(Real.exp t-1)+5)/10 := by positivity
  have hm : 0 < deriv (fun x => fairEquation t 0 x u) (2/5) *
      (t*(1+(Real.exp t-1)*(2/5))^3*((3/5)*(1+(2/5)*(Real.exp t-1)))) := by
    nlinarith only [he,hR]
  exact (mul_pos_iff.mp hm).resolve_right (by intro h; linarith [h.2]) |>.1

set_option maxHeartbeats 800000 in
/-- Compactness in effect and position preserves the positive center slope
on one absolute signed amplitude and center neighborhood. [the documented result](goal) -/
-- @node: fairEquation_uniform_center_slope_pos
lemma fairEquation_uniform_center_slope_pos : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧
    ∀ t δ ξ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε →
      |ξ-2/5| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      0 < deriv (fun x => fairEquation t δ x u) ξ := by
  let K := Set.Icc (0 : ℝ) (1/4) ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hevent : ∀ᶠ a : ℝ × ℝ in 𝓝 (0,2/5), ∀ z ∈ K,
      0 < deriv (fun x => fairEquation z.1 a.1 x z.2) a.2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hbox : ![z.1,0,2/5,z.2] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr ⟨hz.1,by norm_num,by
        change (2/5 : ℝ) ∈ Set.Icc (3/10) (1/2)
        constructor <;> norm_num,hz.2⟩
    have hp : ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        ![w.2.1,w.1.1,w.1.2,w.2.2]) ((0,2/5),z) := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have hh := (fairEquation_center_deriv_contDiffAt _ hbox).comp ((0,2/5),z) hp
    have hc := hh.continuousAt
    change ContinuousAt (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      deriv (fun x => fairEquation w.2.1 w.1.1 x w.2.2) w.1.2) ((0,2/5),z) at hc
    apply hc.eventually
    apply lt_mem_nhds
    change 0 < deriv (fun x => fairEquation z.1 0 x z.2) (2/5)
    exact fairEquation_center_slope_pos z.1 z.2 hz.1 hz.2
  obtain ⟨a,ha,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε := min (a/2) (1/100)
  refine ⟨ε,lt_min (by linarith) (by norm_num),min_le_right _ _,?_⟩
  intro t δ ξ u ht hδ hξ hu
  have hm : (δ,ξ) ∈ Metric.ball (0,2/5) a := by
    rw [Metric.mem_ball,Prod.dist_eq]
    simp only [Real.dist_eq,sub_zero]
    exact max_lt (lt_of_le_of_lt (hδ.trans (min_le_left _ _)) (by linarith))
      (lt_of_le_of_lt (hξ.trans (min_le_left _ _)) (by linarith))
  exact hball hm (t,u) ⟨ht,hu⟩

/-- The normalized fair equation is strictly increasing on a fixed center
bracket for every allowed effect and all sufficiently small signed amplitudes. [the documented result](goal) -/
-- @node: fairEquation_uniform_center_strictMono
lemma fairEquation_uniform_center_strictMono : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧
    ∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 →
      StrictMonoOn (fun x => fairEquation t δ x u)
        (Set.Icc (2/5-ε) (2/5+ε)) := by
  obtain ⟨ε,hε,hsmall,hpos⟩ := fairEquation_uniform_center_slope_pos
  refine ⟨ε,hε,hsmall,?_⟩
  intro t δ u ht hδ hu
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro x hx
    have hξ : x ∈ Set.Icc (3/10 : ℝ) (1/2) := by
      constructor <;> linarith [hx.1,hx.2]
    have hbox : ![t,δ,x,u] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr ⟨ht,hδ.trans hsmall,hξ,hu⟩
    have hp : ContDiffAt ℝ ∞ (fun y : ℝ => ![t,δ,y,u]) x := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    exact ((fairEquation_contDiffAt _ hbox).comp x hp).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hpos t δ x u ht hδ (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩) hu

/-- Uniform continuity excludes every zero-amplitude noncenter root, even
at the bracket endpoints, on a compact set away from the center. [the documented result](goal) Under [the stated assumptions](hyp:hr). -/
-- @node: fairEquation_uniform_root_confined
lemma fairEquation_uniform_root_confined (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧ ∀ t δ u q : ℝ,
      t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      q ∈ Set.Icc (3/10 : ℝ) (1/2) → fairEquation t δ q u = 0 → |q-2/5| < r := by
  let S := Set.Icc (3/10 : ℝ) (1/2) ∩ {q : ℝ | r ≤ |q-2/5|}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le continuous_const (by fun_prop))
  let K := (Set.Icc (0 : ℝ) (1/4) ×ˢ Set.Icc (0 : ℝ) 1) ×ˢ S
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).prod hS
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0, ∀ z ∈ K, fairEquation z.1.1 δ z.2 z.1.2 ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hbox : ![z.1.1,0,z.2,z.1.2] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr ⟨hz.1.1,by norm_num,hz.2.1,hz.1.2⟩
    have hp : ContDiffAt ℝ ∞ (fun w : ℝ × ((ℝ × ℝ) × ℝ) =>
        ![w.2.1.1,w.1,w.2.2,w.2.1.2]) (0,z) := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have hh := (fairEquation_contDiffAt _ hbox).comp (0,z) hp
    apply hh.continuousAt.eventually_ne
    change fairEquation z.1.1 0 z.2 z.1.2 ≠ 0
    intro he
    have hcenter : z.2 = 2/5 := by
      by_cases hlo : z.2 = 3/10
      · rw [hlo] at he
        have hs := (fairEquation_zero_amplitude_bracket_signs z.1.1 z.1.2 hz.1.1 hz.1.2).1
        linarith
      by_cases hhi : z.2 = 1/2
      · rw [hhi] at he
        have hs := (fairEquation_zero_amplitude_bracket_signs z.1.1 z.1.2 hz.1.1 hz.1.2).2
        linarith
      exact fairEquation_zero_amplitude_unique z.1.1 z.1.2 z.2 hz.1.1 hz.1.2
        ⟨lt_of_le_of_ne hz.2.1.1 (Ne.symm hlo),lt_of_le_of_ne hz.2.1.2 hhi⟩ he
    have haway : r ≤ |z.2-2/5| := hz.2.2
    rw [hcenter,sub_self,abs_zero] at haway
    linarith
  obtain ⟨a,ha,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε := min (a/2) (1/100)
  refine ⟨ε,lt_min (by linarith) (by norm_num),min_le_right _ _,?_⟩
  intro t δ u q ht hδ hu hq he
  by_contra hn
  have hδball : δ ∈ Metric.ball (0 : ℝ) a := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact lt_of_le_of_lt (hδ.trans (min_le_left _ _)) (by linarith)
  exact hball hδball ((t,u),q) ⟨⟨ht,hu⟩,hq,le_of_not_gt hn⟩ he

/-- [A fixed center derivative neighborhood and compact exclusion of all
other roots yield uniqueness on the original full selector bracket. [the documented result](goal) -/
-- @node: fairEquation_uniform_existsUnique
lemma fairEquation_uniform_existsUnique : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧
    ∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 →
      ∃! q : ℝ, q ∈ Set.Ioo (3/10 : ℝ) (1/2) ∧ fairEquation t δ q u = 0 := by
  obtain ⟨r,hr,hrsmall,hmono⟩ := fairEquation_uniform_center_strictMono
  obtain ⟨a,ha,hasmall,hconf⟩ := fairEquation_uniform_root_confined r hr
  obtain ⟨b,hb,hbsmall,hex⟩ := fairEquation_uniform_exists
  let ε := min r (min a b)
  have her : ε ≤ r := min_le_left _ _
  have hea : ε ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have heb : ε ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,lt_min hr (lt_min ha hb),her.trans hrsmall,?_⟩
  intro t δ u ht hδ hu
  obtain ⟨q,hq,he⟩ := hex t δ u ht (hδ.trans heb) hu
  have hcq := hconf t δ u q ht (hδ.trans hea) hu ⟨hq.1.le,hq.2.le⟩ he
  refine ⟨q,⟨hq,he⟩,?_⟩
  intro p hp
  have hcp := hconf t δ u p ht (hδ.trans hea) hu ⟨hp.1.1.le,hp.1.2.le⟩ hp.2
  apply (hmono t δ u ht (hδ.trans her) hu).injOn
  · exact ⟨by linarith [(abs_lt.mp hcp).1],by linarith [(abs_lt.mp hcp).2]⟩
  · exact ⟨by linarith [(abs_lt.mp hcq).1],by linarith [(abs_lt.mp hcq).2]⟩
  · exact hp.2.trans he.symm

/-- A positive center slope and exclusion of roots elsewhere remain valid
on full parameter neighborhoods, including effect and position endpoints. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hu,hr,hrsmall,hpos,hconf). -/
-- @node: fairEquation_eventually_unique_of_center_control
lemma fairEquation_eventually_unique_of_center_control (t δ u r : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hr : 0 < r) (hrsmall : r ≤ 1/100)
    (hpos : ∀ x ∈ Set.Icc (2/5-r) (2/5+r),
      0 < deriv (fun y => fairEquation t δ y u) x)
    (hconf : ∀ x ∈ Set.Icc (3/10 : ℝ) (1/2), fairEquation t δ x u = 0 → |x-2/5| < r) :
    ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![t,δ,u], ∀ x ∈ Set.Ioo (3/10 : ℝ) (1/2),
      ∀ y ∈ Set.Ioo (3/10 : ℝ) (1/2),
        fairEquation (a 0) (a 1) x (a 2) = 0 →
        fairEquation (a 0) (a 1) y (a 2) = 0 → x = y := by
  have hbox (x : ℝ) (hx : x ∈ Set.Icc (3/10 : ℝ) (1/2)) :
      ![t,δ,x,u] ∈ fairTaylorParameterRegion :=
    (fairTaylorParameterRegion_mem _).mpr ⟨ht,hδ,hx,hu⟩
  have hp (x : ℝ) : ContDiffAt ℝ ∞ (fun z : (Fin 3 → ℝ) × ℝ =>
      ![z.1 0,z.1 1,z.2,z.1 2]) (![t,δ,u],x) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hcontrol : ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![t,δ,u], ∀ x ∈ Set.Icc (3/10 : ℝ) (1/2),
      ContDiffAt ℝ 1 (fun z : (Fin 3 → ℝ) × ℝ =>
        fairEquation (z.1 0) (z.1 1) z.2 (z.1 2)) (a,x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x hx
    exact (((fairEquation_contDiffAt _ (hbox x hx)).comp (![t,δ,u],x) (hp x)).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
  have hpositive : ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![t,δ,u], ∀ x ∈ Set.Icc (2/5-r) (2/5+r),
      0 < deriv (fun y => fairEquation (a 0) (a 1) y (a 2)) x := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x hx
    have hx' : x ∈ Set.Icc (3/10 : ℝ) (1/2) := by
      constructor <;> linarith [hx.1,hx.2]
    have hh := (fairEquation_center_deriv_contDiffAt _ (hbox x hx')).comp (![t,δ,u],x) (hp x)
    exact hh.continuousAt.eventually (lt_mem_nhds (hpos x hx))
  let S := Set.Icc (3/10 : ℝ) (1/2) ∩ {x : ℝ | r ≤ |x-2/5|}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le continuous_const (by fun_prop))
  have hexclude : ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![t,δ,u], ∀ x ∈ S,
      fairEquation (a 0) (a 1) x (a 2) ≠ 0 := by
    apply hS.eventually_forall_of_forall_eventually
    intro x hx
    have hh := (fairEquation_contDiffAt _ (hbox x hx.1)).comp (![t,δ,u],x) (hp x)
    apply hh.continuousAt.eventually_ne
    change fairEquation t δ x u ≠ 0
    intro he
    exact (not_lt_of_ge hx.2) (hconf x hx.1 he)
  filter_upwards [hcontrol,hpositive,hexclude] with a hc hp' he'
  have hmono : StrictMonoOn (fun x => fairEquation (a 0) (a 1) x (a 2))
      (Set.Icc (2/5-r) (2/5+r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x hx
      have hx' : x ∈ Set.Icc (3/10 : ℝ) (1/2) := by
        constructor <;> linarith [hx.1,hx.2]
      exact (((hc x hx').continuousAt).comp
        (f := fun x : ℝ => (a,x)) (by fun_prop)).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hp' x ⟨hx.1.le,hx.2.le⟩
  have hnear (x : ℝ) (hx : x ∈ Set.Ioo (3/10 : ℝ) (1/2))
      (he : fairEquation (a 0) (a 1) x (a 2) = 0) : x ∈ Set.Icc (2/5-r) (2/5+r) := by
    have hn : |x-2/5| < r := by
      by_contra h
      exact he' x ⟨⟨hx.1.le,hx.2.le⟩,le_of_not_gt h⟩ he
    exact ⟨by linarith [(abs_lt.mp hn).1],by linarith [(abs_lt.mp hn).2]⟩
  intro x hx y hy hex hey
  exact hmono.injOn (hnear x hx hex) (hnear y hy hey) (hex.trans hey.symm)

/-- The actual fair selector is jointly smooth on full neighborhoods of the
closed parameter region, uniformly over the complete prescribed effect range. [the documented result](goal) -/
-- @node: fairRoot_uniform_contDiffAt
lemma fairRoot_uniform_contDiffAt : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/100 ∧
    ∀ v ∈ fairParameterRegion ε,
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v := by
  obtain ⟨r,hr,hrsmall,hpos⟩ := fairEquation_uniform_center_slope_pos
  obtain ⟨a,ha,hasmall,hconf⟩ := fairEquation_uniform_root_confined r hr
  obtain ⟨b,hb,hbsmall,hex⟩ := fairEquation_uniform_exists
  let ε := min r (min a b)
  have her : ε ≤ r := min_le_left _ _
  have hea : ε ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have heb : ε ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,lt_min hr (lt_min ha hb),her.trans hrsmall,?_⟩
  intro v hv
  have ht := hv.1
  have hδ : |v 1| ≤ 1/100 := hv.2.1.trans (her.trans hrsmall)
  have hu := hv.2.2
  have hs := fairRoot_spec (v 0) (v 1) (v 2)
    (hex (v 0) (v 1) (v 2) ht (hv.2.1.trans heb) hu)
  have hqnear := hconf (v 0) (v 1) (v 2) _ ht (hv.2.1.trans hea) hu
    ⟨hs.1.1.le,hs.1.2.le⟩ hs.2
  let F : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    fairEquation (z.1 0) (z.1 1) z.2 (z.1 2)
  apply scalar_bracket_selector_contDiffAt_infty 3 F
    (fun w => fairRoot (w 0) (w 1) (w 2)) v (3/10) (1/2)
  · have hbox : ![v 0,v 1,fairRoot (v 0) (v 1) (v 2),v 2] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr ⟨ht,hδ,⟨hs.1.1.le,hs.1.2.le⟩,hu⟩
    exact (fairEquation_contDiffAt _ hbox).comp (v,fairRoot (v 0) (v 1) (v 2))
      (show ContDiffAt ℝ ∞ (fun z : (Fin 3 → ℝ) × ℝ =>
        ![z.1 0,z.1 1,z.2,z.1 2]) (v,fairRoot (v 0) (v 1) (v 2)) by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
  · exact hs.1
  · exact hs.2
  · exact ne_of_gt (hpos (v 0) (v 1) _ (v 2) ht (hv.2.1.trans her) hqnear.le hu)
  · intro w hw
    exact fairRoot_spec (w 0) (w 1) (w 2) hw
  · have hvec : ![v 0,v 1,v 2] = v := by
      funext i
      fin_cases i <;> rfl
    rw [← hvec]
    exact fairEquation_eventually_unique_of_center_control (v 0) (v 1) (v 2) r
      ht hδ hu hr hrsmall
      (fun x hx => hpos (v 0) (v 1) x (v 2) ht (hv.2.1.trans her)
        (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩) hu)
      (fun x hx he => hconf (v 0) (v 1) (v 2) x ht (hv.2.1.trans hea) hu hx he)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
