module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCenterSlope

/-! # Ambient smoothness of the fair Taylor equation

Compactness of the two integration coordinates preserves joint smoothness on
one ambient neighborhood. The scalar implicit theorem then gives one smooth
branch on an open set, rather than order-dependent point neighborhoods.
-/
public section
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The analytic Taylor integrand remains smooth above a common ambient
neighborhood of every point of the closed parameter box. [the documented result](goal) Under [the stated assumptions](hyp:hx). -/
-- @node: fairEquation_eventually_contDiffAt
lemma fairEquation_eventually_contDiffAt (x : Fin 4 → ℝ)
    (hx : x ∈ fairTaylorParameterRegion) :
    ∀ᶠ w in 𝓝 x, ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ =>
      fairEquation (z 0) (z 1) (z 2) (z 3)) w := by
  let F : ((Fin 4 → ℝ) × ℝ) → ℝ → ℝ := fun z v =>
    (1-v)*deriv (fun T => deriv (deriv (fun D =>
      fairNumerator T D (z.1 2) (z.1 3))) (v*z.1 1)) (z.2*z.1 0)
  have hevent : ∀ᶠ w in 𝓝 x, ∀ sv ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ ⊤ F.uncurry ((w,sv.1),sv.2) := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro sv hsv
    exact (by fun_prop : ContinuousAt (fun z : (Fin 4 → ℝ) × (ℝ × ℝ) =>
      ((z.1,z.2.1),z.2.2)) (x,sv))
      ((fairTaylorIntegrand_contDiffAt ((x,sv.1),sv.2) hx hsv.1 hsv.2).eventually
        (by simp))
  filter_upwards [hevent] with w hw
  apply calibration_intervalIntegral_contDiffAt
  intro s hs
  exact calibration_intervalIntegral_contDiffAt F (w,s)
    (fun v hv => (hw (s,v) ⟨hs,hv⟩).of_le le_top)

/-- [A single open domain of smoothness gives a single smooth implicit branch
for every finite derivative order. [the documented result](goal) Under [the stated assumptions](hyp:F,hOpen,hMem,hSmooth,hZero,hPartial). -/
-- @node: scalar_infty_implicit_function
lemma scalar_infty_implicit_function (d : ℕ)
    (F : ((Fin d → ℝ) × ℝ) → ℝ) (D : Set ((Fin d → ℝ) × ℝ))
    (b₀ : Fin d → ℝ) (χ₀ : ℝ) (hOpen : IsOpen D) (hMem : (b₀, χ₀) ∈ D)
    (hSmooth : ContDiffOn ℝ ∞ F D) (hZero : F (b₀, χ₀) = 0)
    (hPartial : deriv (fun χ => F (b₀, χ)) χ₀ ≠ 0) :
    ∃ (U : Set (Fin d → ℝ)) (V : Set ℝ) (q : (Fin d → ℝ) → ℝ),
      IsOpen U ∧ b₀ ∈ U ∧ IsOpen V ∧ χ₀ ∈ V ∧ U ×ˢ V ⊆ D ∧
      ContDiffOn ℝ ∞ q U ∧ q b₀ = χ₀ ∧
      (∀ b ∈ U, q b ∈ V) ∧
      (∀ b ∈ U, ∀ χ ∈ V, F (b,χ) = 0 ↔ χ = q b) := by
  have hCoeff (z : (Fin d → ℝ) × ℝ) (hz : z ∈ D) :
      deriv (fun χ => F (z.1, χ)) z.2 = fderiv ℝ F z (0, 1) := by
    have hAt := (hSmooth.contDiffAt (hOpen.mem_nhds hz)).differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
    exact (hAt.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right z.1 z.2)).hasDerivAt.deriv
  have hc : ContinuousAt (fun z => fderiv ℝ F z (0, 1)) (b₀, χ₀) := by
    exact ((hSmooth.continuousOn_fderiv_of_isOpen hOpen (by simp)).continuousAt
      (hOpen.mem_nhds hMem)).clm_apply continuousAt_const
  have hne : ∀ᶠ z in 𝓝 (b₀, χ₀), fderiv ℝ F z (0, 1) ≠ 0 :=
    hc.eventually_ne (by rwa [← hCoeff (b₀, χ₀) hMem])
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hne
  obtain ⟨U, V, q, hU, hb, hV, hχ, hUV, hC1, hBase, hRange, hGraph⟩ :=
    scalar_implicit_function d F (D ∩ W) b₀ χ₀ (hOpen.inter hWopen)
      ⟨hMem, hWmem⟩ ((hSmooth.of_le (by simp)).mono Set.inter_subset_left)
      hZero hPartial
  refine ⟨U, V, q, hU, hb, hV, hχ, ?_, ?_, hBase, hRange, hGraph⟩
  · intro z hz
    exact (hUV hz).1
  · intro b hb
    have hz : (b, q b) ∈ D ∩ W := hUV ⟨hb, hRange b hb⟩
    have hq := (hC1.contDiffAt (hU.mem_nhds hb)).continuousAt
    have he : ∀ᶠ a in 𝓝 b, F (a, q a) = 0 := by
      filter_upwards [hU.mem_nhds hb] with a ha
      exact (hGraph a ha (q a) (hRange a ha)).mpr rfl
    apply (scalar_implicit_root_contDiffAt d ∞ (by simp) F q b
      (hSmooth.contDiffAt (hOpen.mem_nhds hz.1)) hq he ?_).contDiffWithinAt
    rw [hCoeff (b, q b) hz.1]
    exact hWsub hz.2

/-- Smooth selected roots near a zero-amplitude point yield smooth actual fair
cells nearby; the outer risk formulas have analytic ambient neighborhoods. [the documented result](goal) Under [the stated assumptions](hyp:ht,hq,hroot). -/
-- @node: localFairCell_eventually_contDiffAt_of_root
lemma localFairCell_eventually_contDiffAt_of_root (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4))
    (hq : ContinuousAt (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) ![t,0,u])
    (hroot : ∀ᶠ v in 𝓝 ![t,0,u],
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v)
    (b : Bool) (s : Bool × Bool) (a y : Bool) :
    ∀ᶠ v in 𝓝 ![t,0,u], ContDiffAt ℝ ∞ (localFairCell b s a y) v := by
  let q : (Fin 3 → ℝ) → ℝ := fun w => fairRoot (w 0) (w 1) (w 2)
  let μ : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    if b then z.2+z.1 1*localSignField (z.1 2) s else z.2
  let T : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    if b then z.1 0 else comparatorEffect (z.1 0) (z.1 1)
  let H : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    (1/2)*(if y then (if a then riskShift (T z) (μ z) else μ z)
      else 1-(if a then riskShift (T z) (μ z) else μ z))
  let z₀ := (![t,0,u],q ![t,0,u])
  have hμ : ContDiffAt ℝ ⊤ μ z₀ := by
    cases b <;> dsimp [μ] <;> first | fun_prop | (unfold localSignField; fun_prop)
  have hT : ContDiffAt ℝ ⊤ T z₀ := by
    cases b
    · have hp : ContDiffAt ℝ ⊤ (fun z : (Fin 3 → ℝ) × ℝ => ![z.1 0,z.1 1]) z₀ := by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop
      exact (comparatorEffect_contDiffAt ![t,0] ht (by norm_num)).comp z₀ hp
    · dsimp [T]; fun_prop
  have hμpos : 0 ≤ μ z₀ := by
    have hp := fairRoot_mem_bracket t 0 u
    cases b <;> simp [μ,z₀,q] <;> linarith [hp.1]
  have hTpos : 0 ≤ T z₀ := by
    have h := comparatorEffect_range_bounds t 0 ht (by norm_num)
    cases b <;> dsimp [T,z₀] <;> linarith [ht.1,h.1]
  have hshift : ContDiffAt ℝ ⊤ (fun z => riskShift (T z) (μ z)) z₀ := by
    unfold riskShift
    exact (hT.exp.mul hμ).div
      (contDiffAt_const.add ((hT.exp.sub contDiffAt_const).mul hμ))
      (ne_of_gt (riskShift_denominator_pos _ _ hTpos hμpos))
  have hH : ContDiffAt ℝ ⊤ H z₀ := by
    cases a <;> cases y <;> dsimp [H] <;> fun_prop
  have hevent := (continuousAt_id.prodMk hq) (hH.eventually (by simp))
  filter_upwards [hevent,hroot] with v hHv hqv
  change ContDiffAt ℝ ⊤ H (v,q v) at hHv
  have hc : ContDiffAt ℝ ∞ (fun w => H (w,q w)) v :=
    (hHv.of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top)).comp
      (f := fun w => (w,q w)) (g := H) v (contDiffAt_id.prodMk hqv)
  exact hc

end CausalSmith.Stat.LogoddsLowsmoothFrontier
