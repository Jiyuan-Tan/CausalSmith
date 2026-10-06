module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleOverlap

/-!
Two-role overlap specialization and treatment-arm variance subtraction for the multiband
covariance proof, together with the public second- and third-order overlap budgets.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Subtracting treatment arms costs at most twice their summed variances, without independence. -/
-- @node: arm_difference_variance_le
lemma arm_difference_variance_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (X Y : E → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun o => X o - Y o) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  have hnon := variance_nonneg (X + Y) μ
  rw [variance_add hX hY] at hnon
  rw [variance_fun_sub hX hY]
  linarith

/-- The same subtraction inequality applies to every Hilbert-space test vector. -/
-- @node: arm_difference_inner_variance_le
lemma arm_difference_inner_variance_le {E F : Type*} [MeasurableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (μ : Measure E) [IsFiniteMeasure μ] (X Y : E → F) (f : F)
    (hX : MemLp (fun o => inner ℝ (X o) f) 2 μ)
    (hY : MemLp (fun o => inner ℝ (Y o) f) 2 μ) :
    variance (fun o => inner ℝ (X o - Y o) f) μ ≤
      2 * variance (fun o => inner ℝ (X o) f) μ +
      2 * variance (fun o => inner ℝ (Y o) f) μ := by
  simp_rw [inner_sub_left]
  exact arm_difference_variance_le μ _ _ hX hY

/-- The two-role identity has exactly two singleton terms and one full-overlap term. -/
-- @node: exact_role_overlap_two
lemma exact_role_overlap_two {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (m : ℕ) (hm : 1 ≤ m)
    (h : (Fin 2 → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin 2 => P))) :
    variance (roleAverage 2 m h)
      (Measure.pi (fun _ : Fin 2 => Measure.pi (fun _ : Fin m => P))) =
    ((m - 1 : ℕ) : ℝ) / (m : ℝ) ^ 2 *
      (variance (partialRoleKernel P 2 {0} h) (Measure.pi (fun _ : Fin 2 => P)) +
       variance (partialRoleKernel P 2 {1} h) (Measure.pi (fun _ : Fin 2 => P))) +
    1 / (m : ℝ) ^ 2 *
      variance (partialRoleKernel P 2 {0, 1} h) (Measure.pi (fun _ : Fin 2 => P)) := by
  classical
  rw [exact_role_overlap_variance P 2 m (by omega) hm h hMeas hL2]
  have hs : (Finset.univ : Finset (Fin 2)).powerset.erase ∅ =
      {{0}, {1}, {0, 1}} := by decide
  rw [hs]
  rw [Finset.sum_insert
      (by decide : ({0} : Finset (Fin 2)) ∉ ({{1}, {0, 1}} : Finset (Finset (Fin 2)))),
    Finset.sum_insert (by decide : ({1} : Finset (Fin 2)) ∉ ({{0, 1}} : Finset (Finset (Fin 2)))),
    Finset.sum_singleton]
  norm_num
  ring

/-- The second-order overlap weights are absorbed with no constraint on correction ranks. -/
-- @node: second_order_overlap_budget_le
lemma second_order_overlap_budget_le (m : ℕ) (hm : 1 ≤ m) (F S : ℝ)
    (hF : 0 ≤ F) (hS : 0 ≤ S) :
    24484 * ((m - 1 : ℕ) : ℝ) / (m : ℝ) ^ 2 * F +
      36864 / (m : ℝ) ^ 2 * S ≤
    (2 : ℝ) ^ 16 * ((m : ℝ)⁻¹ * F + (m : ℝ) ^ (-2 : ℤ) * S) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpred : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  rw [zpow_neg, zpow_ofNat]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hmpos)).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hpred hF]

/-- The three projection second moments give the second-order variance budget of (8).
This leaves the multiband kernel estimates as explicit, separate proof obligations. -/
-- @node: two_role_variance_le_of_projection_moments
lemma two_role_variance_le_of_projection_moments {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (m : ℕ) (hm : 1 ≤ m)
    (h : (Fin 2 → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin 2 => P))) (F S : ℝ)
    (hF : 0 ≤ F) (hS : 0 ≤ S)
    (hfirst : (∫ o, (partialRoleKernel P 2 {0} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 2 => P)) ≤ 8100 * F)
    (hsecond : (∫ o, (partialRoleKernel P 2 {1} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 2 => P)) ≤ 16384 * F)
    (hfull : (∫ o, (partialRoleKernel P 2 {0, 1} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 2 => P)) ≤ 36864 * S) :
    variance (roleAverage 2 m h)
      (Measure.pi (fun _ : Fin 2 => Measure.pi (fun _ : Fin m => P))) ≤
      (2 : ℝ) ^ 16 * ((m : ℝ)⁻¹ * F + (m : ℝ) ^ (-2 : ℤ) * S) := by
  have h0 := (variance_le_expectation_sq
    (partial_role_kernel_memLp P 2 {0} h hL2).aestronglyMeasurable).trans hfirst
  have h1 := (variance_le_expectation_sq
    (partial_role_kernel_memLp P 2 {1} h hL2).aestronglyMeasurable).trans hsecond
  have h01 := (variance_le_expectation_sq
    (partial_role_kernel_memLp P 2 {0, 1} h hL2).aestronglyMeasurable).trans hfull
  rw [exact_role_overlap_two P m hm h hMeas hL2]
  calc
    _ ≤ ((m - 1 : ℕ) : ℝ) / (m : ℝ) ^ 2 * (24484 * F) +
        1 / (m : ℝ) ^ 2 * (36864 * S) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left (by linarith [h0, h1]) (by positivity)
      · exact mul_le_mul_of_nonneg_left h01 (by positivity)
    _ = 24484 * ((m - 1 : ℕ) : ℝ) / (m : ℝ) ^ 2 * F +
        36864 / (m : ℝ) ^ 2 * S := by ring
    _ ≤ _ := second_order_overlap_budget_le m hm F S hF hS

/-- All seven third-order overlaps are absorbed using only the restriction q ≤ m. -/
-- @node: third_order_overlap_budget_le
lemma third_order_overlap_budget_le (m q : ℕ) (hm : 1 ≤ m) (hq : q ≤ m) :
    130336 * ((m - 1 : ℕ) : ℝ) ^ 2 / (m : ℝ) ^ 3 +
      367812 * ((m - 1 : ℕ) : ℝ) * q / (m : ℝ) ^ 3 +
      331776 * (q : ℝ) ^ 2 / (m : ℝ) ^ 3 ≤ (2 : ℝ) ^ 20 * (m : ℝ)⁻¹ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpred : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hqr : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hp2 : ((m - 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) hmpos.le).2 hpred
  have hq2 : (q : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) hmpos.le).2 hqr
  have hpq : ((m - 1 : ℕ) : ℝ) * q ≤ (m : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hpred hqr (by positivity) hmpos.le
  apply (mul_le_mul_iff_left₀ (pow_pos hmpos 3)).mp
  field_simp
  nlinarith

/-- The three-role identity keeps each of the seven nonempty overlaps, including m = 1. -/
-- @node: exact_role_overlap_three
lemma exact_role_overlap_three {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (m : ℕ) (hm : 1 ≤ m)
    (h : (Fin 3 → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin 3 => P))) :
    variance (roleAverage 3 m h)
      (Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin m => P))) =
    ((m - 1 : ℕ) : ℝ) ^ 2 / (m : ℝ) ^ 3 *
      (variance (partialRoleKernel P 3 {0} h) (Measure.pi (fun _ : Fin 3 => P)) +
       variance (partialRoleKernel P 3 {1} h) (Measure.pi (fun _ : Fin 3 => P)) +
       variance (partialRoleKernel P 3 {2} h) (Measure.pi (fun _ : Fin 3 => P))) +
    ((m - 1 : ℕ) : ℝ) / (m : ℝ) ^ 3 *
      (variance (partialRoleKernel P 3 {0, 1} h) (Measure.pi (fun _ : Fin 3 => P)) +
       variance (partialRoleKernel P 3 {0, 2} h) (Measure.pi (fun _ : Fin 3 => P)) +
       variance (partialRoleKernel P 3 {1, 2} h) (Measure.pi (fun _ : Fin 3 => P))) +
    1 / (m : ℝ) ^ 3 *
      variance (partialRoleKernel P 3 {0, 1, 2} h) (Measure.pi (fun _ : Fin 3 => P)) := by
  classical
  rw [exact_role_overlap_variance P 3 m (by omega) hm h hMeas hL2]
  have hs : (Finset.univ : Finset (Fin 3)).powerset.erase ∅ =
      {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hs]
  rw [Finset.sum_insert (by decide : ({0} : Finset (Fin 3)) ∉ ({{1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3)))),
    Finset.sum_insert (by decide : ({1} : Finset (Fin 3)) ∉ ({{2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3)))),
    Finset.sum_insert (by decide : ({2} : Finset (Fin 3)) ∉ ({{0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3)))),
    Finset.sum_insert (by decide : ({0, 1} : Finset (Fin 3)) ∉ ({{0, 2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3)))),
    Finset.sum_insert (by decide : ({0, 2} : Finset (Fin 3)) ∉ ({{1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3)))),
    Finset.sum_insert (by decide : ({1, 2} : Finset (Fin 3)) ∉ ({{0, 1, 2}} : Finset (Finset (Fin 3)))),
    Finset.sum_singleton]
  rw [show ({0, 2} : Finset (Fin 3)).card = 2 by decide,
    show ({1, 2} : Finset (Fin 3)).card = 2 by decide,
    show ({0, 1, 2} : Finset (Fin 3)).card = 3 by decide]
  norm_num
  ring

/-- The seven second-moment estimates (11), (13), and (14) give the third-order
variance bound (15). The kernel estimates remain separate obligations. -/
-- @node: three_role_variance_le_of_projection_moments
lemma three_role_variance_le_of_projection_moments {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (m q : ℕ) (hm : 1 ≤ m) (hq : q ≤ m)
    (h : (Fin 3 → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin 3 => P))) (F : ℝ) (hF : 0 ≤ F)
    (h0 : (∫ o, (partialRoleKernel P 3 {0} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 32400 * F)
    (h1 : (∫ o, (partialRoleKernel P 3 {1} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 32400 * F)
    (h2 : (∫ o, (partialRoleKernel P 3 {2} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 65536 * F)
    (h01 : (∫ o, (partialRoleKernel P 3 {0, 1} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 72900 * q * F)
    (h02 : (∫ o, (partialRoleKernel P 3 {0, 2} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 147456 * q * F)
    (h12 : (∫ o, (partialRoleKernel P 3 {1, 2} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 147456 * q * F)
    (h012 : (∫ o, (partialRoleKernel P 3 {0, 1, 2} h o) ^ 2
      ∂Measure.pi (fun _ : Fin 3 => P)) ≤ 331776 * (q : ℝ) ^ 2 * F) :
    variance (roleAverage 3 m h)
      (Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin m => P))) ≤
    (2 : ℝ) ^ 20 * (m : ℝ)⁻¹ * F := by
  have hv (S : Finset (Fin 3)) := variance_le_expectation_sq
    (partial_role_kernel_memLp P 3 S h hL2).aestronglyMeasurable
  have v0 := (hv {0}).trans h0
  have v1 := (hv {1}).trans h1
  have v2 := (hv {2}).trans h2
  have v01 := (hv {0, 1}).trans h01
  have v02 := (hv {0, 2}).trans h02
  have v12 := (hv {1, 2}).trans h12
  have v012 := (hv {0, 1, 2}).trans h012
  rw [exact_role_overlap_three P m hm h hMeas hL2]
  calc
    _ ≤ ((m - 1 : ℕ) : ℝ) ^ 2 / (m : ℝ) ^ 3 * (130336 * F) +
        ((m - 1 : ℕ) : ℝ) / (m : ℝ) ^ 3 * (367812 * q * F) +
        1 / (m : ℝ) ^ 3 * (331776 * (q : ℝ) ^ 2 * F) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by linarith [v0, v1, v2]) (by positivity)
        · exact mul_le_mul_of_nonneg_left (by linarith [v01, v02, v12]) (by positivity)
      · exact mul_le_mul_of_nonneg_left v012 (by positivity)
    _ = (130336 * ((m - 1 : ℕ) : ℝ) ^ 2 / (m : ℝ) ^ 3 +
        367812 * ((m - 1 : ℕ) : ℝ) * q / (m : ℝ) ^ 3 +
        331776 * (q : ℝ) ^ 2 / (m : ℝ) ^ 3) * F := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (third_order_overlap_budget_le m q hm hq) hF

/-- Independent correction orders sum their variances; the public constant absorbs
both arm-subtraction factors and the three moment constants in (17). -/
-- @node: independent_correction_variance_le
lemma independent_correction_variance_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (X Y Z : E → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ)
    (hXY : IndepFun X Y μ) (hXYZ : IndepFun (X + Y) Z μ)
    (F S : ℝ) (hF : 0 ≤ F) (hS : 0 ≤ S)
    (hfirst : variance X μ ≤ 4 * 4096 * F)
    (hsecond : variance Y μ ≤ 4 * (2 : ℝ) ^ 16 * (F + S))
    (hthird : variance Z μ ≤ 4 * (2 : ℝ) ^ 20 * F) :
    variance (X + Y + Z) μ ≤ (2 : ℝ) ^ 24 * (F + S) := by
  rw [hXYZ.variance_add (hX.add hY) hZ, hXY.variance_add hX hY]
  calc
    _ ≤ 4 * 4096 * F + 4 * (2 : ℝ) ^ 16 * (F + S) +
        4 * (2 : ℝ) ^ 20 * F := add_le_add (add_le_add hfirst hsecond) hthird
    _ ≤ _ := by norm_num; linarith

end CausalSmith.Stat.DensityEffectRoughNull
