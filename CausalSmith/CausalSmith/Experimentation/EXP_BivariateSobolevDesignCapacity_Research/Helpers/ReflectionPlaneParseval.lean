module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionPlane
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint Parseval for reflected cells

Iterated interval Parseval and dominated convergence sum the joint Fourier
coefficients of the four reflected cells. Applying this to the function and
both signed derivatives proves the smooth two-dimensional spectral endpoint.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Four continuous cell formulas have every finite Lp regularity on the square.](goal) Under [the stated conditions](hyp:h₀₀,h₀₁,h₁₀,h₁₁,q). -/
-- @node: reflectionPlaneCells_memLp
lemma reflectionPlaneCells_memLp {f₀₀ f₀₁ f₁₀ f₁₁ : ℝ × ℝ → ℂ}
    (h₀₀ : Continuous f₀₀) (h₀₁ : Continuous f₀₁)
    (h₁₀ : Continuous f₁₀) (h₁₁ : Continuous f₁₁) (q : ℝ≥0∞) :
    MemLp (fun z : ℝ × ℝ => if z.1 ≤ 1 then
      (if z.2 ≤ 1 then f₀₀ z else f₀₁ z) else
      (if z.2 ≤ 1 then f₁₀ z else f₁₁ z)) q
      (volume.restrict (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2)) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hi {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
      MemLp f q (volume.restrict (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2)) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc ((0, 0) : ℝ × ℝ) (2, 2))).bddAbove_image
      hf.norm.continuousOn
    apply MemLp.of_bound (C := C) hf.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    exact hC ⟨z, ⟨⟨hz.1.1.le, hz.2.1.le⟩, ⟨hz.1.2, hz.2.2⟩⟩, rfl⟩
  have hy := measurableSet_le (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
    (measurable_const (a := (1 : ℝ)))
  have hx := measurableSet_le (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
    (measurable_const (a := (1 : ℝ)))
  have hl := MemLp.piecewise hy ((hi h₀₀).restrict _) ((hi h₀₁).restrict _)
  have hr := MemLp.piecewise hy ((hi h₁₀).restrict _) ((hi h₁₁).restrict _)
  exact MemLp.piecewise hx (hl.restrict _) (hr.restrict _)

/-- [ Integrating two continuous inner cell formulas against a character is continuous
in the outer parameter, despite a possible jump at the inner face.](goal) Under [the stated conditions](hyp:h₀,h₁). -/
-- @node: reflectionCells_sliceCoeff_continuous
lemma reflectionCells_sliceCoeff_continuous {f₀ f₁ : ℝ × ℝ → ℂ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (b : ℤ) :
    Continuous (fun x => periodTwoSliceCoeff
      (fun y => if y ≤ 1 then f₀ (x, y) else f₁ (x, y)) b) := by
  have he (x : ℝ) : periodTwoSliceCoeff
      (fun y => if y ≤ 1 then f₀ (x, y) else f₁ (x, y)) b =
      (1 / 2 : ℂ) * ((∫ y in (0 : ℝ)..1,
        fourier (-b) (y : AddCircle (2 : ℝ)) * f₀ (x, y)) +
        ∫ y in (1 : ℝ)..2, fourier (-b) (y : AddCircle (2 : ℝ)) * f₁ (x, y)) := by
    unfold periodTwoSliceCoeff
    simp only [mul_ite]
    rw [reflectionCells_integral_split (by fun_prop) (by fun_prop)]
  simp_rw [he]
  apply Continuous.const_mul
  apply Continuous.add <;>
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' <;> fun_prop

/-- [ Two interval Parseval identities assemble to joint Parseval. The square
integrability and partial-coefficient regularity justify exchanging the series and integral.](goal) Under [the stated conditions](hyp:hL,hC,hi). -/
-- @node: periodTwoPlaneCoeff_parseval
lemma periodTwoPlaneCoeff_parseval (f : ℝ → ℝ → ℂ)
    (hL : ∀ x, MemLp (f x) 2 (volume.restrict (Ioc (0 : ℝ) 2)))
    (hC : ∀ b : ℤ, MemLp (fun x => periodTwoSliceCoeff (f x) b) 2
      (volume.restrict (Ioc (0 : ℝ) 2)))
    (hi : IntegrableOn (fun z : ℝ × ℝ => ‖f z.1 z.2‖ ^ 2)
      (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2)) :
    HasSum (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff f k.1 k.2‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2, ‖f x y‖ ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 2)
  have hs (x : ℝ) : HasSum (fun b : ℤ => ‖periodTwoSliceCoeff (f x) b‖ ^ 2)
      ((1 / 2 : ℝ) * ∫ y in (0 : ℝ)..2, ‖f x y‖ ^ 2) := by
    have h := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 2) (hL x)
    simpa only [← periodTwoSliceCoeff_eq_fourierCoeffOn, sub_zero,
      inv_eq_one_div, smul_eq_mul] using h
  have hi' : Integrable (fun z : ℝ × ℝ => ‖f z.1 z.2‖ ^ 2) (μ.prod μ) := by
    simpa only [μ, Measure.volume_eq_prod, Measure.prod_restrict, IntegrableOn] using! hi
  have htotal : Integrable (fun x => ∑' b : ℤ, ‖periodTwoSliceCoeff (f x) b‖ ^ 2) μ := by
    simp_rw [(hs _).tsum_eq, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact hi'.integral_prod_left.const_mul (1 / 2)
  have ht := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := μ) (fun b x => ‖periodTwoSliceCoeff (f x) b‖ ^ 2)
    (fun b => ((hC b).aestronglyMeasurable.norm.pow 2))
    (fun b => Filter.Eventually.of_forall (fun x => by
      change ‖(‖periodTwoSliceCoeff (f x) b‖ ^ 2 : ℝ)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]))
    (Filter.Eventually.of_forall (fun x => (hs x).summable)) htotal
    (Filter.Eventually.of_forall hs)
  have hout : HasSum (fun b : ℤ => (1 / 2 : ℝ) *
      ∫ x in (0 : ℝ)..2, ‖periodTwoSliceCoeff (f x) b‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2, ‖f x y‖ ^ 2) := by
    have h := ht.mul_left (1 / 2)
    simp only [μ, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
      intervalIntegral.integral_const_mul] at h
    convert! h using 1 <;> first | rfl | ring
  have hinner (b : ℤ) : HasSum (fun a : ℤ => ‖periodTwoPlaneCoeff f a b‖ ^ 2)
      ((1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, ‖periodTwoSliceCoeff (f x) b‖ ^ 2) := by
    have h := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 2) (hC b)
    simpa only [← periodTwoSliceCoeff_eq_fourierCoeffOn, periodTwoSliceCoeff,
      periodTwoPlaneCoeff, sub_zero, inv_eq_one_div, smul_eq_mul] using h
  have hsum : Summable (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff f k.2 k.1‖ ^ 2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      ⟨fun b => (hinner b).summable, by
        simpa only [(hinner _).tsum_eq] using hout.summable⟩
  have he : HasSum (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff f k.2 k.1‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2, ‖f x y‖ ^ 2) := by
    have ht : (∑' k : ℤ × ℤ, ‖periodTwoPlaneCoeff f k.2 k.1‖ ^ 2) =
        (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2, ‖f x y‖ ^ 2 := by
      rw [hsum.tsum_prod]
      simp_rw [(hinner _).tsum_eq]
      exact hout.tsum_eq
    exact ht ▸ hsum.hasSum
  exact (Equiv.prodComm ℤ ℤ).hasSum_iff.mp he

/-- [ Joint Parseval applies to four continuous cells, including discontinuous signed
reflected derivatives; no agreement of derivative traces is required.](goal) Under [the stated conditions](hyp:h₀₀,h₀₁,h₁₀,h₁₁). -/
-- @node: reflectionPlaneCells_parseval
lemma reflectionPlaneCells_parseval {f₀₀ f₀₁ f₁₀ f₁₁ : ℝ × ℝ → ℂ}
    (h₀₀ : Continuous f₀₀) (h₀₁ : Continuous f₀₁)
    (h₁₀ : Continuous f₁₀) (h₁₁ : Continuous f₁₁) :
    let f : ℝ → ℝ → ℂ := fun x y => if x ≤ 1 then
      (if y ≤ 1 then f₀₀ (x, y) else f₀₁ (x, y)) else
      (if y ≤ 1 then f₁₀ (x, y) else f₁₁ (x, y))
    HasSum (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff f k.1 k.2‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2, ‖f x y‖ ^ 2) := by
  dsimp only
  apply periodTwoPlaneCoeff_parseval
  · intro x
    by_cases hx : x ≤ 1
    · simp only [if_pos hx]
      apply reflectionCells_memLp <;> fun_prop
    · simp only [if_neg hx]
      apply reflectionCells_memLp <;> fun_prop
  · intro b
    have he (x : ℝ) :
        periodTwoSliceCoeff (fun y => if x ≤ 1 then
          (if y ≤ 1 then f₀₀ (x, y) else f₀₁ (x, y)) else
          (if y ≤ 1 then f₁₀ (x, y) else f₁₁ (x, y))) b =
        if x ≤ 1 then periodTwoSliceCoeff
          (fun y => if y ≤ 1 then f₀₀ (x, y) else f₀₁ (x, y)) b
        else periodTwoSliceCoeff
          (fun y => if y ≤ 1 then f₁₀ (x, y) else f₁₁ (x, y)) b := by
      split_ifs <;> rfl
    simp_rw [he]
    exact reflectionCells_memLp (reflectionCells_sliceCoeff_continuous h₀₀ h₀₁ b)
      (reflectionCells_sliceCoeff_continuous h₁₀ h₁₁ b) 2
  · exact (reflectionPlaneCells_memLp h₀₀ h₀₁ h₁₀ h₁₁ 2).integrable_norm_pow
      (by norm_num)

/-- [ Joint Parseval recovers the even reflected square's exact normalized spatial energy.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: evenReflectionPlane_parseval
lemma evenReflectionPlane_parseval {f : ℝ → ℝ → ℂ} (hf : Continuous f.uncurry) :
    HasSum (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff (evenReflectionPlane f) k.1 k.2‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖evenReflectionPlane f x y‖ ^ 2) := by
  exact reflectionPlaneCells_parseval
    (f₀₀ := fun z => f z.1 z.2) (f₀₁ := fun z => f z.1 (2 - z.2))
    (f₁₀ := fun z => f (2 - z.1) z.2) (f₁₁ := fun z => f (2 - z.1) (2 - z.2))
    hf (by fun_prop) (by fun_prop) (by fun_prop)

/-- [ Joint Parseval also applies to the signed first derivative across its jumping face.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: signedReflectionPlaneX_parseval
lemma signedReflectionPlaneX_parseval {f : ℝ → ℝ → ℂ} (hf : Continuous f.uncurry) :
    HasSum (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff (signedReflectionPlaneX f) k.1 k.2‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneX f x y‖ ^ 2) := by
  have he : signedReflectionPlaneX f = (fun x y => if x ≤ 1 then
      (if y ≤ 1 then f x y else f x (2 - y)) else
      (if y ≤ 1 then -f (2 - x) y else -f (2 - x) (2 - y))) := by
    funext x y
    simp only [signedReflectionPlaneX, signedReflectionSlice, evenReflectionSlice, neg_ite]
  rw [he]
  exact reflectionPlaneCells_parseval
    (f₀₀ := fun z => f z.1 z.2) (f₀₁ := fun z => f z.1 (2 - z.2))
    (f₁₀ := fun z => -f (2 - z.1) z.2) (f₁₁ := fun z => -f (2 - z.1) (2 - z.2))
    hf (by fun_prop) (by fun_prop) (by fun_prop)

/-- [ The second signed derivative has the same joint Parseval identity.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: signedReflectionPlaneY_parseval
lemma signedReflectionPlaneY_parseval {f : ℝ → ℝ → ℂ} (hf : Continuous f.uncurry) :
    HasSum (fun k : ℤ × ℤ => ‖periodTwoPlaneCoeff (signedReflectionPlaneY f) k.1 k.2‖ ^ 2)
      ((1 / 4 : ℝ) * ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneY f x y‖ ^ 2) := by
  exact reflectionPlaneCells_parseval
    (f₀₀ := fun z => f z.1 z.2) (f₀₁ := fun z => -f z.1 (2 - z.2))
    (f₁₀ := fun z => f (2 - z.1) z.2) (f₁₁ := fun z => -f (2 - z.1) (2 - z.2))
    hf (by fun_prop) (by fun_prop) (by fun_prop)

/-- [ Joint Parseval and the two genuine weak derivative multipliers prove the smooth
spectral H¹ endpoint, with precisely the local gradient factor one half.](goal) Under [the stated conditions](hyp:hfxd,hfyd,hf,hfx,hfy). -/
-- @node: evenReflectionPlane_firstOrder_parseval
lemma evenReflectionPlane_firstOrder_parseval {f fx fy : ℝ → ℝ → ℂ}
    (hfxd : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hfyd : ∀ x y, HasDerivAt (f x) (fy x y) y)
    (hf : Continuous f.uncurry) (hfx : Continuous fx.uncurry)
    (hfy : Continuous fy.uncurry) :
    HasSum (fun k : ℤ × ℤ =>
      (1 + Real.pi ^ 2 * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) / 2) *
        ‖periodTwoPlaneCoeff (evenReflectionPlane f) k.1 k.2‖ ^ 2)
      ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2) + (1 / 2 : ℝ) *
        ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖fx x y‖ ^ 2) +
          ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖fy x y‖ ^ 2)) := by
  have h := (evenReflectionPlane_parseval hf).add
    (((signedReflectionPlaneX_parseval hfx).add
      (signedReflectionPlaneY_parseval hfy)).mul_left (1 / 2 : ℝ))
  have he := evenReflectionPlane_firstOrder_energy hf hfx hfy
  have hsum :
      (1 / 4 : ℝ) * (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖evenReflectionPlane f x y‖ ^ 2) + (1 / 2 : ℝ) *
      ((1 / 4 : ℝ) * (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneX fx x y‖ ^ 2) + (1 / 4 : ℝ) *
       (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneY fy x y‖ ^ 2)) =
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2) + (1 / 2 : ℝ) *
        ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖fx x y‖ ^ 2) +
          ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖fy x y‖ ^ 2) := by
    rw [← he]
    ring
  rw [hsum] at h
  convert! h using 1
  funext k
  exact evenReflectionPlane_firstOrder_coeff_energy hfxd hfyd hf hfx hfy k.1 k.2

/-- [ The smooth two-dimensional Fourier endpoint contracts the whole-space spatial
H¹ norm with constant one, independently of the two cube-face traces.](goal) Under [the stated conditions](hyp:hfxd,hfyd,hf,hfx,hfy,hL,hDx,hDy). -/
-- @node: evenReflectionPlane_firstOrder_spectral_le_wholeSpace
lemma evenReflectionPlane_firstOrder_spectral_le_wholeSpace {f fx fy : ℝ → ℝ → ℂ}
    (hfxd : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hfyd : ∀ x y, HasDerivAt (f x) (fy x y) y)
    (hf : Continuous f.uncurry) (hfx : Continuous fx.uncurry)
    (hfy : Continuous fy.uncurry)
    (hL : MemLp f.uncurry 2 (volume : Measure (ℝ × ℝ)))
    (hDx : MemLp fx.uncurry 2 (volume : Measure (ℝ × ℝ)))
    (hDy : MemLp fy.uncurry 2 (volume : Measure (ℝ × ℝ))) :
    (∑' k : ℤ × ℤ, (1 + Real.pi ^ 2 * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) / 2) *
      ‖periodTwoPlaneCoeff (evenReflectionPlane f) k.1 k.2‖ ^ 2) ≤
      (∫ z : ℝ × ℝ, ‖f z.1 z.2‖ ^ 2) + (1 / 2 : ℝ) *
        ((∫ z : ℝ × ℝ, ‖fx z.1 z.2‖ ^ 2) +
          ∫ z : ℝ × ℝ, ‖fy z.1 z.2‖ ^ 2) := by
  rw [(evenReflectionPlane_firstOrder_parseval hfxd hfyd hf hfx hfy).tsum_eq,
    ← evenReflectionPlane_firstOrder_energy hf hfx hfy]
  exact evenReflectionPlane_firstOrder_le_wholeSpace hf hfx hfy hL hDx hDy

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
