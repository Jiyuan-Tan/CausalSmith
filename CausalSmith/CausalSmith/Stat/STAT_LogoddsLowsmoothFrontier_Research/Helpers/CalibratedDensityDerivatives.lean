module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCellSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCenterSlope
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedCellSmoothness

/-! # Amplitude derivative envelopes for calibrated densities

Affine amplitude slices do not increase derivative norms. The compact local
cell envelopes therefore control the fully substituted density formulas.
-/
public section
noncomputable section
open Filter Topology
open scoped ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Restricting a smooth local cell to a contractive affine amplitude slice
cannot increase the norm of any fixed-order derivative. [the documented result](goal) Under [the stated assumptions](hyp:f,x,hf,hL). -/
-- @node: calibrated_affine_slice_derivative_bound
lemma calibrated_affine_slice_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 3 → ℝ) → ℝ) (L : E →L[ℝ] (Fin 3 → ℝ))
    (c : Fin 3 → ℝ) (x : E) (m : ℕ)
    (hf : ContDiffAt ℝ ∞ f (L x + c)) (hL : ‖L‖ ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun z => f (L z + c)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (L x + c)‖ := by
  let F : (Fin 3 → ℝ) → ℝ := fun z => f (z + c)
  have hF : ContDiffAt ℝ m F (L x) := by
    exact (hf.of_le (WithTop.coe_le_coe.mpr le_top)).comp (L x)
      (by fun_prop : ContDiffAt ℝ m (fun z : Fin 3 → ℝ => z+c) (L x))
  obtain ⟨S, hS, hFS⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨D, hDS, hD, hxD⟩ := mem_nhds_iff.mp hS
  have hpre : IsOpen (L ⁻¹' D) := hD.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right (hFS.mono hDS)
    hD.uniqueDiffOn hpre.uniqueDiffOn hxD (i := m) le_rfl
  rw [iteratedFDerivWithin_of_isOpen m hpre (show x ∈ L ⁻¹' D from hxD),
    iteratedFDerivWithin_of_isOpen m hD hxD] at heq
  change iteratedFDeriv ℝ m (fun z => f (L z + c)) x = _ at heq
  rw [heq]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m F (L x)‖ * ∏ _ : Fin m, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ m F (L x)‖ * ∏ _ : Fin m, (1 : ℝ) := by
      gcongr
    _ = ‖iteratedFDeriv ℝ m f (L x + c)‖ := by
      rw [show iteratedFDeriv ℝ m F (L x) = iteratedFDeriv ℝ m f (L x + c) from
        iteratedFDeriv_comp_add_right m c (L x)]
      simp

/-- [The mixed amplitude plane is a contractive slice of the full local
parameter space, with the spatial coordinate held fixed. [the documented result](goal) Under [the stated assumptions](hyp:f,hf). -/
-- @node: calibrated_mixed_slice_derivative_bound
lemma calibrated_mixed_slice_derivative_bound
    (f : (Fin 3 → ℝ) → ℝ) (v : Fin 2 → ℝ) (u : ℝ) (m : ℕ)
    (hf : ContDiffAt ℝ ∞ f ![v 0, v 1, u]) :
    ‖iteratedFDeriv ℝ m (fun w : Fin 2 → ℝ => f ![w 0, w 1, u]) v‖ ≤
      ‖iteratedFDeriv ℝ m f ![v 0, v 1, u]‖ := by
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]
  let c : Fin 3 → ℝ := ![0, 0, u]
  have heq (w : Fin 2 → ℝ) : L w + c = ![w 0, w 1, u] := by
    ext i
    simp only [L, c, Pi.add_apply, ContinuousLinearMap.pi_apply]
    fin_cases i <;> norm_num
  have hL : ‖L‖ ≤ 1 := by
    refine L.opNorm_le_bound (by norm_num) ?_
    intro w
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
    intro i
    simp only [L, ContinuousLinearMap.pi_apply]
    fin_cases i <;> simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply]
    · change ‖w 0‖ ≤ ‖w‖
      exact norm_le_pi_norm w 0
    · change ‖w 1‖ ≤ ‖w‖
      exact norm_le_pi_norm w 1
    · change ‖(0 : ℝ)‖ ≤ ‖w‖
      simpa using norm_nonneg w
  simpa only [heq] using
    calibrated_affine_slice_derivative_bound f L c v m (by simpa only [heq] using hf) hL

/-- [The fair amplitude line is a contractive slice, with effect and spatial
coordinate held fixed. [the documented result](goal) Under [the stated assumptions](hyp:f,hf). -/
-- @node: calibrated_fair_slice_derivative_bound
lemma calibrated_fair_slice_derivative_bound
    (f : (Fin 3 → ℝ) → ℝ) (t δ u : ℝ) (m : ℕ)
    (hf : ContDiffAt ℝ ∞ f ![t, δ, u]) :
    ‖iteratedFDeriv ℝ m (fun d : ℝ => f ![t, d, u]) δ‖ ≤
      ‖iteratedFDeriv ℝ m f ![t, δ, u]‖ := by
  let L : ℝ →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi ![0, ContinuousLinearMap.id ℝ ℝ, 0]
  let c : Fin 3 → ℝ := ![t, 0, u]
  have heq (d : ℝ) : L d + c = ![t, d, u] := by
    ext i
    simp only [L, c, Pi.add_apply, ContinuousLinearMap.pi_apply]
    fin_cases i <;> norm_num
  have hL : ‖L‖ ≤ 1 := by
    refine L.opNorm_le_bound (by norm_num) ?_
    intro d
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr
    intro i
    simp only [L, ContinuousLinearMap.pi_apply]
    fin_cases i <;> simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
    · change ‖(0 : ℝ)‖ ≤ ‖d‖
      simpa using norm_nonneg d
    · change ‖d‖ ≤ ‖d‖
      exact le_rfl
    · change ‖(0 : ℝ)‖ ≤ ‖d‖
      simpa using norm_nonneg d
  simpa only [heq] using
    calibrated_affine_slice_derivative_bound f L c δ m (by simpa only [heq] using hf) hL

/-- [Passing from a cell probability to its uniform-label relative density
multiplies every amplitude derivative envelope by four. [the documented result](goal) Under [the stated assumptions](hyp:f,x,hf,hB). -/
-- @node: calibrated_density_rescale_derivative_bound
lemma calibrated_density_rescale_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (m : ℕ) (B : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) (hB : ‖iteratedFDeriv ℝ m f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun z => 4 * f z) x‖ ≤ 4 * B := by
  change ‖iteratedFDeriv ℝ m (fun z => (4 : ℝ) • f z) x‖ ≤ 4 * B
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    norm_smul]
  norm_num
  linarith

/-- Compact local calibration boxes give a common finite envelope for the
first two derivatives of both relative-density amplitude slices. [the documented result](goal) -/
-- @node: calibrated_local_density_derivative_envelopes
lemma calibrated_local_density_derivative_envelopes : ∃ r M : ℝ,
    0 < r ∧ 1 ≤ M ∧
    (∀ η ζ u : ℝ, |η| ≤ r → |ζ| ≤ r → u ∈ Set.Icc (0 : ℝ) 1 →
      ∀ b s a y, ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
        ‖iteratedFDeriv ℝ m
          (fun w : Fin 2 → ℝ => 4 * localMixedCell b s a y ![w 0, w 1, u]) ![η, ζ]‖ ≤ M) ∧
    (∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ r → u ∈ Set.Icc (0 : ℝ) 1 →
      ∀ b s a y, ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
        ‖iteratedFDeriv ℝ m (fun d : ℝ => 4 * localFairCell b s a y ![t, d, u]) δ‖ ≤ M) := by
  obtain ⟨rm, hrm, hsm, hbm⟩ := localMixedCell_uniform_smooth_derivative_bounds
  obtain ⟨rf, hrf, hsmall, hsf⟩ := fairRoot_uniform_contDiffAt
  obtain ⟨_, hbf⟩ := localFairCell_smooth_derivative_bounds_of_root rf hsmall hsf
  obtain ⟨Bm1, hBm1, hm1⟩ := hbm 1
  obtain ⟨Bm2, hBm2, hm2⟩ := hbm 2
  obtain ⟨Bf1, hBf1, hf1⟩ := hbf 1
  obtain ⟨Bf2, hBf2, hf2⟩ := hbf 2
  let M := 4 * (Bm1 + Bm2 + Bf1 + Bf2) + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith
  refine ⟨min rm rf, M, lt_min hrm hrf, hM, ?_, ?_⟩
  · intro η ζ u hη hζ hu b s a y m hmlo hmhi
    have hv : ![η, ζ, u] ∈ mixedParameterRegion rm :=
      ⟨hη.trans (min_le_left _ _), hζ.trans (min_le_left _ _), hu⟩
    have hs : ContDiffAt ℝ ∞ (localMixedCell b s a y) ![η, ζ, u] :=
      (hsm _ hv b s a y).of_le le_top
    have hslice : ContDiffAt ℝ ∞
        (fun w : Fin 2 → ℝ => localMixedCell b s a y ![w 0, w 1, u]) ![η, ζ] := by
      exact hs.comp ![η, ζ] (show ContDiffAt ℝ ∞
        (fun w : Fin 2 → ℝ => ![w 0, w 1, u]) ![η, ζ] from by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
    have hfull : ‖iteratedFDeriv ℝ m (localMixedCell b s a y) ![η, ζ, u]‖ ≤ Bm1 + Bm2 := by
      have hm : m = 1 ∨ m = 2 := by omega
      rcases hm with rfl | rfl
      · exact (hm1 _ hv b s a y).trans (by linarith)
      · exact (hm2 _ hv b s a y).trans (by linarith)
    have hsliceBound := (calibrated_mixed_slice_derivative_bound _ ![η, ζ] u m hs).trans hfull
    exact (calibrated_density_rescale_derivative_bound _ _ m _ hslice hsliceBound).trans
      (by dsimp [M]; linarith)
  · intro t δ u ht hδ hu b s a y m hmlo hmhi
    have hv : ![t, δ, u] ∈ fairParameterRegion rf :=
      ⟨ht, hδ.trans (min_le_right _ _), hu⟩
    have hs := localFairCell_contDiffAt_of_root _ ht (hv.2.1.trans hsmall) (hsf _ hv) b s a y
    have hslice : ContDiffAt ℝ ∞
        (fun d : ℝ => localFairCell b s a y ![t, d, u]) δ := by
      have hmap : ContDiffAt ℝ ∞ (fun d : ℝ => ![t, d, u]) δ := by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop
      have hcomp := hs.comp δ hmap
      exact hcomp
    have hfull : ‖iteratedFDeriv ℝ m (localFairCell b s a y) ![t, δ, u]‖ ≤ Bf1 + Bf2 := by
      have hm : m = 1 ∨ m = 2 := by omega
      rcases hm with rfl | rfl
      · exact ((hf1 _ hv).2 b s a y).trans (by linarith)
      · exact ((hf2 _ hv).2 b s a y).trans (by linarith)
    have hsliceBound := (calibrated_fair_slice_derivative_bound _ t δ u m hs).trans hfull
    exact (calibrated_density_rescale_derivative_bound _ _ m _ hslice hsliceBound).trans
      (by dsimp [M]; linarith)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
