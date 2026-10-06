module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # T ScalarImplicitFunction

The scalar product-domain implicit-function theorem, with open coordinate neighborhoods
and local uniqueness of the zero graph. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @node: lem:scalar-implicit-function
/-- [A scalar zero set is locally the graph of a unique C1 function.](goal) Under [the stated assumptions](hyp:hOpen,hC1). Under [the stated assumptions](hyp:F,hMem,hC1,hZero,hPartial). -/
lemma scalar_implicit_function (d : ℕ)
    (F : ((Fin d → ℝ) × ℝ) → ℝ) (D : Set ((Fin d → ℝ) × ℝ))
    (b₀ : Fin d → ℝ) (χ₀ : ℝ) (hOpen : IsOpen D) (hMem : (b₀, χ₀) ∈ D)
    (hC1 : ContDiffOn ℝ 1 F D) (hZero : F (b₀, χ₀) = 0)
    (hPartial : deriv (fun χ => F (b₀, χ)) χ₀ ≠ 0) :
    ∃ (U : Set (Fin d → ℝ)) (V : Set ℝ) (q : (Fin d → ℝ) → ℝ),
      IsOpen U ∧ b₀ ∈ U ∧ IsOpen V ∧ χ₀ ∈ V ∧ U ×ˢ V ⊆ D ∧
      ContDiffOn ℝ 1 q U ∧ q b₀ = χ₀ ∧
      (∀ b ∈ U, q b ∈ V) ∧
      (∀ b ∈ U, ∀ χ ∈ V, F (b,χ) = 0 ↔ χ = q b) := by
  have hAt : ContDiffAt ℝ 1 F (b₀, χ₀) :=
    hC1.contDiffAt (hOpen.mem_nhds hMem)
  let L := fderiv ℝ F (b₀, χ₀) ∘L ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ
  have hDeriv : HasDerivAt (fun χ => F (b₀, χ)) (L 1) χ₀ :=
    ((hAt.differentiableAt one_ne_zero).hasFDerivAt.comp χ₀
      (hasFDerivAt_prodMk_right b₀ χ₀)).hasDerivAt
  have hL : L 1 ≠ 0 := by
    rw [← hDeriv.deriv]
    exact hPartial
  have hScale (x : ℝ) : L x = x * L 1 := by
    simpa using L.map_smul x (1 : ℝ)
  have hInv : L.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      rw [hScale]
      field_simp
    · ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      rw [hScale]
      field_simp
  let q := hAt.implicitFunction one_ne_zero hInv
  have hqBase : q b₀ = χ₀ := hAt.implicitFunction_apply_self one_ne_zero hInv
  have hqSmooth : ContDiffAt ℝ 1 q b₀ := hAt.contDiffAt_implicitFunction one_ne_zero hInv
  have hGraph : ∀ᶠ z in 𝓝 (b₀, χ₀), F z = 0 ↔ q z.1 = z.2 := by
    simpa [hZero] using hAt.eventually_apply_eq_iff_implicitFunction one_ne_zero hInv
  have hRect : {z | F z = 0 ↔ q z.1 = z.2} ∩ D ∈ 𝓝 (b₀, χ₀) :=
    inter_mem hGraph (hOpen.mem_nhds hMem)
  rw [nhds_prod_eq] at hRect
  obtain ⟨U₁, hU₁, V₁, hV₁, hUV⟩ := mem_prod_iff.mp hRect
  obtain ⟨U₂, hU₂sub, hU₂open, hU₂base⟩ := mem_nhds_iff.mp hU₁
  obtain ⟨V, hVsub, hVopen, hVbase⟩ := mem_nhds_iff.mp hV₁
  obtain ⟨S, hS, hSmooth⟩ := hqSmooth.contDiffOn le_rfl (by simp)
  have hPre : q ⁻¹' V ∈ 𝓝 b₀ :=
    hqSmooth.continuousAt (by simpa [hqBase] using hVopen.mem_nhds hVbase)
  obtain ⟨U, hUsub, hUopen, hUbase⟩ :=
    mem_nhds_iff.mp (inter_mem (inter_mem (hU₂open.mem_nhds hU₂base) hS) hPre)
  refine ⟨U, V, q, hUopen, hUbase, hVopen, hVbase, ?_, ?_, hqBase, ?_, ?_⟩
  · intro z hz
    exact (hUV ⟨hU₂sub (hUsub hz.1).1.1, hVsub hz.2⟩).2
  · exact hSmooth.mono (fun b hb => (hUsub hb).1.2)
  · intro b hb
    exact (hUsub hb).2
  · intro b hb χ hχ
    exact ((hUV ⟨hU₂sub (hUsub hb).1.1, hVsub hχ⟩).1).trans eq_comm

/-- [A continuous zero-graph inherits every smoothness order of its scalar
implicit equation. This identifies the actual selected root with Mathlib's
local branch, rather than proving regularity of an unrelated witness. [the documented result](goal) Under [the stated assumptions](hyp:F,hF,hq,hZero,hPartial). Under [the stated assumptions](hyp:hn). -/
-- @node: scalar_implicit_root_contDiffAt
lemma scalar_implicit_root_contDiffAt (d : ℕ) (n : ℕ∞ω) (hn : n ≠ 0)
    (F : ((Fin d → ℝ) × ℝ) → ℝ) (q : (Fin d → ℝ) → ℝ) (b : Fin d → ℝ)
    (hF : ContDiffAt ℝ n F (b, q b)) (hq : ContinuousAt q b)
    (hZero : ∀ᶠ a in 𝓝 b, F (a, q a) = 0)
    (hPartial : deriv (fun χ => F (b, χ)) (q b) ≠ 0) :
    ContDiffAt ℝ n q b := by
  let L := fderiv ℝ F (b, q b) ∘L ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ
  have hDeriv : HasDerivAt (fun χ => F (b, χ)) (L 1) (q b) :=
    ((hF.differentiableAt hn).hasFDerivAt.comp (q b)
      (hasFDerivAt_prodMk_right b (q b))).hasDerivAt
  have hL : L 1 ≠ 0 := by
    rw [← hDeriv.deriv]
    exact hPartial
  have hScale (x : ℝ) : L x = x * L 1 := by
    simpa using L.map_smul x (1 : ℝ)
  have hInv : L.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      rw [hScale]
      field_simp
    · ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      rw [hScale]
      field_simp
  have hBase : F (b, q b) = 0 := by
    exact hZero.self_of_nhds
  have hGraph := hF.eventually_apply_eq_iff_implicitFunction hn hInv
  have hPull := (continuousAt_id.prodMk hq) hGraph
  have he : q =ᶠ[𝓝 b] hF.implicitFunction hn hInv := by
    filter_upwards [hPull, hZero] with a ha hz
    exact ((ha).mp (hz.trans hBase.symm)).symm
  exact (hF.contDiffAt_implicitFunction hn hInv).congr_of_eventuallyEq he

/-- [Smooth scalar equations have a single smooth local zero-graph on open
coordinate neighborhoods. The C1 graph is upgraded pointwise by local
implicit uniqueness, so all finite derivative orders concern the same root. [the documented result](goal) Under [the stated assumptions](hyp:F,hOpen,hMem,hSmooth,hZero,hPartial). -/
-- @node: scalar_smooth_implicit_function
lemma scalar_smooth_implicit_function (d : ℕ)
    (F : ((Fin d → ℝ) × ℝ) → ℝ) (D : Set ((Fin d → ℝ) × ℝ))
    (b₀ : Fin d → ℝ) (χ₀ : ℝ) (hOpen : IsOpen D) (hMem : (b₀, χ₀) ∈ D)
    (hSmooth : ContDiffOn ℝ ⊤ F D) (hZero : F (b₀, χ₀) = 0)
    (hPartial : deriv (fun χ => F (b₀, χ)) χ₀ ≠ 0) :
    ∃ (U : Set (Fin d → ℝ)) (V : Set ℝ) (q : (Fin d → ℝ) → ℝ),
      IsOpen U ∧ b₀ ∈ U ∧ IsOpen V ∧ χ₀ ∈ V ∧ U ×ˢ V ⊆ D ∧
      ContDiffOn ℝ ⊤ q U ∧ q b₀ = χ₀ ∧
      (∀ b ∈ U, q b ∈ V) ∧
      (∀ b ∈ U, ∀ χ ∈ V, F (b,χ) = 0 ↔ χ = q b) := by
  have hCoeff (z : (Fin d → ℝ) × ℝ) (hz : z ∈ D) :
      deriv (fun χ => F (z.1, χ)) z.2 = fderiv ℝ F z (0, 1) := by
    have hAt := (hSmooth.contDiffAt (hOpen.mem_nhds hz)).differentiableAt
      (by simp : (⊤ : ℕ∞ω) ≠ 0)
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
    apply (scalar_implicit_root_contDiffAt d ⊤ (by simp) F q b
      (hSmooth.contDiffAt (hOpen.mem_nhds hz.1)) hq he ?_).contDiffWithinAt
    rw [hCoeff (b, q b) hz.1]
    exact hWsub hz.2

/-- [A bracket selector inherits smoothness from the local implicit branch when
nearby bracket roots are unique. No continuity assumption on the selector is
needed: uniqueness identifies it with the smooth branch on a neighborhood. [the documented result](goal) Under [the stated assumptions](hyp:F,l,hF,hb,hZero,hPartial,hSpec,hUnique). -/
-- @node: scalar_bracket_selector_contDiffAt
lemma scalar_bracket_selector_contDiffAt (d : ℕ)
    (F : ((Fin d → ℝ) × ℝ) → ℝ) (q : (Fin d → ℝ) → ℝ)
    (b : Fin d → ℝ) (l r : ℝ)
    (hF : ContDiffAt ℝ ⊤ F (b, q b))
    (hb : q b ∈ Set.Ioo l r) (hZero : F (b, q b) = 0)
    (hPartial : deriv (fun χ => F (b, χ)) (q b) ≠ 0)
    (hSpec : ∀ a, (∃ χ ∈ Set.Ioo l r, F (a, χ) = 0) →
      q a ∈ Set.Ioo l r ∧ F (a, q a) = 0)
    (hUnique : ∀ᶠ a in 𝓝 b, ∀ χ ∈ Set.Ioo l r, ∀ ψ ∈ Set.Ioo l r,
      F (a, χ) = 0 → F (a, ψ) = 0 → χ = ψ) :
    ContDiffAt ℝ ⊤ q b := by
  obtain ⟨S, hS, hSmooth⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨D, hDsub, hDopen, hDbase⟩ := mem_nhds_iff.mp hS
  obtain ⟨U, V, g, hU, hbU, hV, hbV, hUV, hg, hgBase, hgRange, hgGraph⟩ :=
    scalar_smooth_implicit_function d F D b (q b) hDopen hDbase
      (hSmooth.mono hDsub) hZero hPartial
  have hgAt := hg.contDiffAt (hU.mem_nhds hbU)
  have hRange : ∀ᶠ a in 𝓝 b, g a ∈ Set.Ioo l r :=
    hgAt.continuousAt (by rw [hgBase]; exact isOpen_Ioo.mem_nhds hb)
  have he : q =ᶠ[𝓝 b] g := by
    filter_upwards [hU.mem_nhds hbU, hRange, hUnique] with a ha hga hunique
    have hz : F (a, g a) = 0 := (hgGraph a ha (g a) (hgRange a ha)).mpr rfl
    obtain ⟨hqa, hqz⟩ := hSpec a ⟨g a, hga, hz⟩
    exact hunique (q a) hqa (g a) hga hqz hz
  exact hgAt.congr_of_eventuallyEq he

/-- [Compactness bounds each fixed derivative order of the actual smooth map.
Smoothness is required on neighborhoods of the compact set, so the derivatives
are unrestricted derivatives even at boundary points. [the documented result](goal) Under [the stated assumptions](hyp:hK,hf). -/
-- @node: compact_smooth_derivative_bounds
lemma compact_smooth_derivative_bounds (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (hf : ∀ b ∈ K, ContDiffAt ℝ ⊤ f b) :
    ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ b ∈ K, ‖iteratedFDeriv ℝ m f b‖ ≤ B := by
  intro m
  have hc : ContinuousOn (iteratedFDeriv ℝ m f) K := by
    intro b hb
    exact ((hf b hb).differentiableAt_iteratedFDeriv (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro b hb
  exact (hC b hb).trans (le_max_left _ _)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
