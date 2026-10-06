module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionWeakDerivative

/-! # Two-dimensional reflected smooth endpoint

The four reflected cells have matching function traces. Slice integration by
parts cancels all faces in each coordinate, and the signed gradient preserves
the normalized spatial energy. These are the two-dimensional constructions in
(4) and (5) of the exact-reflection-budget roadmap.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Even reflection in both coordinate directions. -/
-- @node: evenReflectionPlane
def evenReflectionPlane (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  evenReflectionSlice (fun u => evenReflectionSlice (f u) y) x

/-- The first coordinate derivative has the reflected orientation sign. -/
-- @node: signedReflectionPlaneX
def signedReflectionPlaneX (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  signedReflectionSlice (fun u => evenReflectionSlice (f u) y) x

/-- The second coordinate derivative has its own reflected orientation sign. -/
-- @node: signedReflectionPlaneY
def signedReflectionPlaneY (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  evenReflectionSlice (fun u => signedReflectionSlice (f u) y) x

/-- Coordinate transposition commutes with even reflection.](goal) This uses [the stated conclusion](goal). -/
-- @node: evenReflectionPlane_transpose
lemma evenReflectionPlane_transpose (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    evenReflectionPlane f x y = evenReflectionPlane (fun u v => f v u) y x := by
  simp only [evenReflectionPlane, evenReflectionSlice]
  split_ifs <;> rfl

/-- [ Transposition exchanges the two reflected gradient coordinates.](goal) -/
-- @node: signedReflectionPlaneY_transpose
lemma signedReflectionPlaneY_transpose (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    signedReflectionPlaneY f x y = signedReflectionPlaneX (fun u v => f v u) y x := by
  simp only [signedReflectionPlaneY, signedReflectionPlaneX,
    evenReflectionSlice, signedReflectionSlice]
  split_ifs <;> rfl

/-- Reflection in the other coordinate preserves the smooth slice derivative. Under [the stated conditions](hyp:hf), [the asserted mathematical result follows](goal). -/
-- @node: evenReflectionPlane_slice_hasDerivAt
lemma evenReflectionPlane_slice_hasDerivAt {f fx : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x) (x y : ℝ) :
    HasDerivAt (fun u => evenReflectionSlice (f u) y)
      (evenReflectionSlice (fx x) y) x := by
  by_cases hy : y ≤ 1
  · simpa only [evenReflectionSlice, if_pos hy] using hf x y
  · simpa only [evenReflectionSlice, if_neg hy] using hf x (2 - y)

/-- [ The first coordinate face cancellation is valid for every periodic smooth test slice.](goal) Under [the stated conditions](hyp:hf,hfx,hv,hv',hp). -/
-- @node: evenReflectionPlane_integration_by_parts_x
lemma evenReflectionPlane_integration_by_parts_x {f fx : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hfx : Continuous fx.uncurry) (y : ℝ) {v v' : ℝ → ℂ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') (hp : v 2 = v 0) :
    (∫ x in (0 : ℝ)..2, evenReflectionPlane f x y * v' x) =
      -(∫ x in (0 : ℝ)..2, signedReflectionPlaneX fx x y * v x) := by
  apply evenReflectionSlice_integration_by_parts
    (fun x => evenReflectionPlane_slice_hasDerivAt hf x y) _ hv hv' hp
  by_cases hy : y ≤ 1
  · simp only [evenReflectionSlice, if_pos hy]
    exact hfx.comp (continuous_id.prodMk continuous_const)
  · simp only [evenReflectionSlice, if_neg hy]
    exact hfx.comp (continuous_id.prodMk continuous_const)

/-- [ The second coordinate cancels faces by the same construction, with no cube trace condition.](goal) Under [the stated conditions](hyp:hf,hfy,hv,hv',hp). -/
-- @node: evenReflectionPlane_integration_by_parts_y
lemma evenReflectionPlane_integration_by_parts_y {f fy : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (f x) (fy x y) y)
    (hfy : Continuous fy.uncurry) (x : ℝ) {v v' : ℝ → ℂ}
    (hv : ∀ y, HasDerivAt v (v' y) y) (hv' : Continuous v') (hp : v 2 = v 0) :
    (∫ y in (0 : ℝ)..2, evenReflectionPlane f x y * v' y) =
      -(∫ y in (0 : ℝ)..2, signedReflectionPlaneY fy x y * v y) := by
  have he : (fun y => evenReflectionPlane f x y) =
      (fun y => evenReflectionPlane (fun u v => f v u) y x) :=
    funext (evenReflectionPlane_transpose f x)
  have hd : (fun y => signedReflectionPlaneY fy x y) =
      (fun y => signedReflectionPlaneX (fun u v => fy v u) y x) :=
    funext (signedReflectionPlaneY_transpose fy x)
  change (∫ y in (0 : ℝ)..2, (fun y => evenReflectionPlane f x y) y * v' y) = _
  rw [he]
  change _ = -(∫ y in (0 : ℝ)..2, (fun y => signedReflectionPlaneY fy x y) y * v y)
  rw [hd]
  exact evenReflectionPlane_integration_by_parts_x (fun u v => hf v u)
    (hfy.comp continuous_swap) x hv hv' hp

/-- [ In the first coordinate the character test gives the exact multiplier.](goal) Under [the stated conditions](hyp:hf,hfx). -/
-- @node: signedReflectionPlaneX_slice_fourierCoeff
lemma signedReflectionPlaneX_slice_fourierCoeff {f fx : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hfx : Continuous fx.uncurry) (y : ℝ) (a : ℤ) :
    periodTwoSliceCoeff (fun x => signedReflectionPlaneX fx x y) a =
      Complex.I * (Real.pi : ℂ) * (a : ℂ) *
        periodTwoSliceCoeff (fun x => evenReflectionPlane f x y) a := by
  apply signedReflectionSlice_fourierCoeff
    (fun x => evenReflectionPlane_slice_hasDerivAt hf x y)
  by_cases hy : y ≤ 1
  · simp only [evenReflectionSlice, if_pos hy]
    exact hfx.comp (continuous_id.prodMk continuous_const)
  · simp only [evenReflectionSlice, if_neg hy]
    exact hfx.comp (continuous_id.prodMk continuous_const)

/-- [ In the second coordinate the multiplier has the second frequency.](goal) Under [the stated conditions](hyp:hf,hfy). -/
-- @node: signedReflectionPlaneY_slice_fourierCoeff
lemma signedReflectionPlaneY_slice_fourierCoeff {f fy : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (f x) (fy x y) y)
    (hfy : Continuous fy.uncurry) (x : ℝ) (b : ℤ) :
    periodTwoSliceCoeff (signedReflectionPlaneY fy x) b =
      Complex.I * (Real.pi : ℂ) * (b : ℂ) *
        periodTwoSliceCoeff (evenReflectionPlane f x) b := by
  have he : evenReflectionPlane f x =
      (fun y => evenReflectionPlane (fun u v => f v u) y x) :=
    funext (evenReflectionPlane_transpose f x)
  have hd : signedReflectionPlaneY fy x =
      (fun y => signedReflectionPlaneX (fun u v => fy v u) y x) :=
    funext (signedReflectionPlaneY_transpose fy x)
  rw [he, hd]
  exact signedReflectionPlaneX_slice_fourierCoeff (fun u v => hf v u)
    (hfy.comp continuous_swap) x b

/-- [ Normalized reflection transports a continuous scalar slice integral exactly.](goal) Under [the stated conditions](hyp:hq). -/
-- @node: evenReflectionSlice_integral
lemma evenReflectionSlice_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {q : ℝ → E} (hq : Continuous q) :
    (1 / 2 : ℝ) • (∫ x in (0 : ℝ)..2, if x ≤ 1 then q x else q (2 - x)) =
      ∫ x in (0 : ℝ)..1, q x := by
  rw [reflectionCells_integral_split hq (by fun_prop),
    intervalIntegral.integral_comp_sub_left q 2]
  norm_num
  module

/-- [ Four-cell normalized L² energy is exactly the original square energy.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: evenReflectionPlane_energy
lemma evenReflectionPlane_energy {f : ℝ → ℝ → ℂ} (hf : Continuous f.uncurry) :
    (1 / 4 : ℝ) * (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
      ‖evenReflectionPlane f x y‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2 := by
  have hinner (x : ℝ) :
      (1 / 2 : ℝ) * (∫ y in (0 : ℝ)..2, ‖evenReflectionPlane f x y‖ ^ 2) =
        if x ≤ 1 then (∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2)
        else ∫ y in (0 : ℝ)..1, ‖f (2 - x) y‖ ^ 2 := by
    by_cases hx : x ≤ 1
    · simp only [evenReflectionPlane, evenReflectionSlice, if_pos hx]
      exact evenReflectionSlice_energy (hf.comp (continuous_const.prodMk continuous_id))
    · simp only [evenReflectionPlane, evenReflectionSlice, if_neg hx]
      exact evenReflectionSlice_energy (hf.comp (continuous_const.prodMk continuous_id))
  have hq : Continuous (fun x => ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) 0 1
  have ho := evenReflectionSlice_integral hq
  simp only [smul_eq_mul] at ho
  calc
    _ = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2,
        (1 / 2 : ℝ) * (∫ y in (0 : ℝ)..2, ‖evenReflectionPlane f x y‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = _ := by simp_rw [hinner]; exact ho

/-- [ The first gradient coordinate has exactly the same energy as even reflection.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: signedReflectionPlaneX_energy
lemma signedReflectionPlaneX_energy {f : ℝ → ℝ → ℂ} (hf : Continuous f.uncurry) :
    (1 / 4 : ℝ) * (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
      ‖signedReflectionPlaneX f x y‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2 := by
  have he (x y : ℝ) : ‖signedReflectionPlaneX f x y‖ ^ 2 =
      ‖evenReflectionPlane f x y‖ ^ 2 := by
    simp only [signedReflectionPlaneX, evenReflectionPlane, signedReflectionSlice,
      evenReflectionSlice]
    split_ifs <;> simp
  simp_rw [he]
  exact evenReflectionPlane_energy hf

/-- [ The second gradient coordinate also preserves energy, including the face jumps.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: signedReflectionPlaneY_energy
lemma signedReflectionPlaneY_energy {f : ℝ → ℝ → ℂ} (hf : Continuous f.uncurry) :
    (1 / 4 : ℝ) * (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
      ‖signedReflectionPlaneY f x y‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2 := by
  have he (x y : ℝ) : ‖signedReflectionPlaneY f x y‖ ^ 2 =
      ‖evenReflectionPlane f x y‖ ^ 2 := by
    simp only [signedReflectionPlaneY, evenReflectionPlane, signedReflectionSlice,
      evenReflectionSlice]
    split_ifs <;> simp
  simp_rw [he]
  exact evenReflectionPlane_energy hf

/-- [ Continuous formulas on the four cells are integrable on the representative square,
even when their derivative traces disagree on the joining faces.](goal) Under [the stated conditions](hyp:h₀₀,h₀₁,h₁₀,h₁₁). -/
-- @node: reflectionPlaneCells_integrable
lemma reflectionPlaneCells_integrable {f₀₀ f₀₁ f₁₀ f₁₁ : ℝ × ℝ → ℂ}
    (h₀₀ : Continuous f₀₀) (h₀₁ : Continuous f₀₁)
    (h₁₀ : Continuous f₁₀) (h₁₁ : Continuous f₁₁) :
    IntegrableOn (fun z : ℝ × ℝ => if z.1 ≤ 1 then
      (if z.2 ≤ 1 then f₀₀ z else f₀₁ z) else
      (if z.2 ≤ 1 then f₁₀ z else f₁₁ z))
      (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2) := by
  classical
  have hi {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
      IntegrableOn f (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2) := by
    apply (hf.integrableOn_Icc (a := (0, 0)) (b := (2, 2))).mono_set
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.2.1.le⟩, ⟨hz.1.2, hz.2.2⟩⟩
  have hy : MeasurableSet {z : ℝ × ℝ | z.2 ≤ 1} :=
    measurableSet_le measurable_snd measurable_const
  have hx : MeasurableSet {z : ℝ × ℝ | z.1 ≤ 1} :=
    measurableSet_le measurable_fst measurable_const
  have hleft := Integrable.piecewise hy (hi h₀₀).integrableOn (hi h₀₁).integrableOn
  have hright := Integrable.piecewise hy (hi h₁₀).integrableOn (hi h₁₁).integrableOn
  exact Integrable.piecewise hx hleft.integrableOn hright.integrableOn

/-- The joint period-two coefficient is an iterated normalized square integral. -/
-- @node: periodTwoPlaneCoeff
def periodTwoPlaneCoeff (f : ℝ → ℝ → ℂ) (a b : ℤ) : ℂ :=
  (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..2,
    fourier (-a) (x : AddCircle (2 : ℝ)) * periodTwoSliceCoeff (f x) b

/-- Both one-dimensional normalizations multiply to the square's Haar factor. [The asserted mathematical result follows](goal). -/
-- @node: periodTwoPlaneCoeff_eq_integral
lemma periodTwoPlaneCoeff_eq_integral (f : ℝ → ℝ → ℂ) (a b : ℤ) :
    periodTwoPlaneCoeff f a b = (1 / 4 : ℂ) *
      ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        fourier (-a) (x : AddCircle (2 : ℝ)) *
          (fourier (-b) (y : AddCircle (2 : ℝ)) * f x y) := by
  unfold periodTwoPlaneCoeff periodTwoSliceCoeff
  calc
    _ = (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..2, (1 / 2 : ℂ) *
        ∫ y in (0 : ℝ)..2, fourier (-a) (x : AddCircle (2 : ℝ)) *
          (fourier (-b) (y : AddCircle (2 : ℝ)) * f x y) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- Fubini exchanges the two coefficient orders when the character-weighted cells are integrable. Under [the stated conditions](hyp:hi), [the asserted mathematical result follows](goal). -/
-- @node: periodTwoPlaneCoeff_transpose
lemma periodTwoPlaneCoeff_transpose (f : ℝ → ℝ → ℂ) (a b : ℤ)
    (hi : IntegrableOn (fun z : ℝ × ℝ =>
      fourier (-a) (z.1 : AddCircle (2 : ℝ)) *
        (fourier (-b) (z.2 : AddCircle (2 : ℝ)) * f z.1 z.2))
      (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2)) :
    periodTwoPlaneCoeff f a b = periodTwoPlaneCoeff (fun x y => f y x) b a := by
  have hswap :
      (∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        fourier (-a) (x : AddCircle (2 : ℝ)) *
          (fourier (-b) (y : AddCircle (2 : ℝ)) * f x y)) =
      ∫ y in (0 : ℝ)..2, ∫ x in (0 : ℝ)..2,
        fourier (-a) (x : AddCircle (2 : ℝ)) *
          (fourier (-b) (y : AddCircle (2 : ℝ)) * f x y) := by
    apply intervalIntegral_intervalIntegral_swap
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2), Function.uncurry] using! hi
  rw [periodTwoPlaneCoeff_eq_integral, periodTwoPlaneCoeff_eq_integral, hswap]
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  ring

/-- [ Character-weighted even reflection is integrable on the square by its four continuous cells.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: evenReflectionPlane_character_integrable
lemma evenReflectionPlane_character_integrable {f : ℝ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℤ) :
    IntegrableOn (fun z : ℝ × ℝ =>
      fourier (-a) (z.1 : AddCircle (2 : ℝ)) *
        (fourier (-b) (z.2 : AddCircle (2 : ℝ)) * evenReflectionPlane f z.1 z.2))
      (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2) := by
  simp only [evenReflectionPlane, evenReflectionSlice, mul_ite]
  apply reflectionPlaneCells_integrable <;> fun_prop

/-- [ The signed first derivative also has four integrable character-weighted cells.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: signedReflectionPlaneX_character_integrable
lemma signedReflectionPlaneX_character_integrable {f : ℝ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℤ) :
    IntegrableOn (fun z : ℝ × ℝ =>
      fourier (-a) (z.1 : AddCircle (2 : ℝ)) *
        (fourier (-b) (z.2 : AddCircle (2 : ℝ)) * signedReflectionPlaneX f z.1 z.2))
      (Ioc (0 : ℝ) 2 ×ˢ Ioc (0 : ℝ) 2) := by
  simp only [signedReflectionPlaneX, signedReflectionSlice, evenReflectionSlice,
    mul_ite, neg_ite]
  apply reflectionPlaneCells_integrable <;> fun_prop

/-- [ The second-coordinate slice multiplier assembles to the joint Fourier multiplier.](goal) Under [the stated conditions](hyp:hf,hfy). -/
-- @node: signedReflectionPlaneY_fourierCoeff
lemma signedReflectionPlaneY_fourierCoeff {f fy : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (f x) (fy x y) y)
    (hfy : Continuous fy.uncurry) (a b : ℤ) :
    periodTwoPlaneCoeff (signedReflectionPlaneY fy) a b =
      Complex.I * (Real.pi : ℂ) * (b : ℂ) *
        periodTwoPlaneCoeff (evenReflectionPlane f) a b := by
  unfold periodTwoPlaneCoeff
  simp_rw [signedReflectionPlaneY_slice_fourierCoeff hf hfy]
  have he : (∫ x in (0 : ℝ)..2,
      fourier (-a) (x : AddCircle (2 : ℝ)) *
        (Complex.I * (Real.pi : ℂ) * (b : ℂ) *
          periodTwoSliceCoeff (evenReflectionPlane f x) b)) =
      (Complex.I * (Real.pi : ℂ) * (b : ℂ)) *
        ∫ x in (0 : ℝ)..2, fourier (-a) (x : AddCircle (2 : ℝ)) *
          periodTwoSliceCoeff (evenReflectionPlane f x) b := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    ring
  rw [he]
  ring

/-- [ Fubini and transposition assemble the first-coordinate joint multiplier as well.](goal) Under [the stated conditions](hyp:hf,hfc,hfx). -/
-- @node: signedReflectionPlaneX_fourierCoeff
lemma signedReflectionPlaneX_fourierCoeff {f fx : ℝ → ℝ → ℂ}
    (hf : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hfc : Continuous f.uncurry) (hfx : Continuous fx.uncurry) (a b : ℤ) :
    periodTwoPlaneCoeff (signedReflectionPlaneX fx) a b =
      Complex.I * (Real.pi : ℂ) * (a : ℂ) *
        periodTwoPlaneCoeff (evenReflectionPlane f) a b := by
  have he : (fun y x => evenReflectionPlane f x y) =
      evenReflectionPlane (fun y x => f x y) := by
    funext y x
    exact evenReflectionPlane_transpose f x y
  have hd : (fun y x => signedReflectionPlaneX fx x y) =
      signedReflectionPlaneY (fun y x => fx x y) := by
    funext y x
    exact (signedReflectionPlaneY_transpose (fun y x => fx x y) y x).symm
  rw [periodTwoPlaneCoeff_transpose (signedReflectionPlaneX fx) a b
    (signedReflectionPlaneX_character_integrable hfx a b),
    periodTwoPlaneCoeff_transpose (evenReflectionPlane f) a b
      (evenReflectionPlane_character_integrable hfc a b), he, hd]
  exact signedReflectionPlaneY_fourierCoeff (fun y x => hf x y)
    (hfx.comp continuous_swap) b a

/-- [ The two-dimensional spatial endpoint has exactly the local 1/2 gradient coefficient.
Every energy on the right is an original-cube energy; the faces impose no trace condition.](goal) Under [the stated conditions](hyp:hf,hfx,hfy). -/
-- @node: evenReflectionPlane_firstOrder_energy
lemma evenReflectionPlane_firstOrder_energy {f fx fy : ℝ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (hfx : Continuous fx.uncurry)
    (hfy : Continuous fy.uncurry) :
    (1 / 4 : ℝ) * ((∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
      ‖evenReflectionPlane f x y‖ ^ 2) + (1 / 2 : ℝ) *
      ((∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneX fx x y‖ ^ 2) +
       ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneY fy x y‖ ^ 2)) =
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2) + (1 / 2 : ℝ) *
      ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖fx x y‖ ^ 2) +
       ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖fy x y‖ ^ 2) := by
  linear_combination evenReflectionPlane_energy hf +
    (1 / 2 : ℝ) * signedReflectionPlaneX_energy hfx +
    (1 / 2 : ℝ) * signedReflectionPlaneY_energy hfy

/-- [ Both genuine derivative multipliers give the local two-coordinate spectral weight.](goal) Under [the stated conditions](hyp:hfxd,hfyd,hf,hfx,hfy). -/
-- @node: evenReflectionPlane_firstOrder_coeff_energy
lemma evenReflectionPlane_firstOrder_coeff_energy {f fx fy : ℝ → ℝ → ℂ}
    (hfxd : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hfyd : ∀ x y, HasDerivAt (f x) (fy x y) y)
    (hf : Continuous f.uncurry) (hfx : Continuous fx.uncurry)
    (hfy : Continuous fy.uncurry) (a b : ℤ) :
    (1 + Real.pi ^ 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 2) *
      ‖periodTwoPlaneCoeff (evenReflectionPlane f) a b‖ ^ 2 =
      ‖periodTwoPlaneCoeff (evenReflectionPlane f) a b‖ ^ 2 + (1 / 2 : ℝ) *
        (‖periodTwoPlaneCoeff (signedReflectionPlaneX fx) a b‖ ^ 2 +
          ‖periodTwoPlaneCoeff (signedReflectionPlaneY fy) a b‖ ^ 2) := by
  rw [signedReflectionPlaneX_fourierCoeff hfxd hf hfx,
    signedReflectionPlaneY_fourierCoeff hfyd hfy]
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_intCast, mul_pow, sq_abs]
  ring

/-- [ Restricting spatial square energy to the original square is a contraction.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: plane_cube_energy_le_wholeSpace
lemma plane_cube_energy_le_wholeSpace {f : ℝ → ℝ → ℂ}
    (hf : MemLp f.uncurry 2 (volume : Measure (ℝ × ℝ))) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ‖f x y‖ ^ 2) ≤
      ∫ z : ℝ × ℝ, ‖f z.1 z.2‖ ^ 2 := by
  have hi := hf.integrable_norm_pow (by norm_num)
  have hi' : Integrable (fun z : ℝ × ℝ => ‖f z.1 z.2‖ ^ 2)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [Function.uncurry, Measure.volume_eq_prod] using! hi
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← setIntegral_prod _ hi'.integrableOn]
  exact setIntegral_le_integral hi' (Filter.Eventually.of_forall (fun z => sq_nonneg _))

/-- [ The four-cell smooth spatial endpoint contracts whole-space H¹ energy with
exactly the same local 1/2 gradient normalization.](goal) Under [the stated conditions](hyp:hf,hfx,hfy,hL,hDx,hDy). -/
-- @node: evenReflectionPlane_firstOrder_le_wholeSpace
lemma evenReflectionPlane_firstOrder_le_wholeSpace {f fx fy : ℝ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (hfx : Continuous fx.uncurry)
    (hfy : Continuous fy.uncurry)
    (hL : MemLp f.uncurry 2 (volume : Measure (ℝ × ℝ)))
    (hDx : MemLp fx.uncurry 2 (volume : Measure (ℝ × ℝ)))
    (hDy : MemLp fy.uncurry 2 (volume : Measure (ℝ × ℝ))) :
    (1 / 4 : ℝ) * ((∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
      ‖evenReflectionPlane f x y‖ ^ 2) + (1 / 2 : ℝ) *
      ((∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneX fx x y‖ ^ 2) +
       ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
        ‖signedReflectionPlaneY fy x y‖ ^ 2)) ≤
      (∫ z : ℝ × ℝ, ‖f z.1 z.2‖ ^ 2) + (1 / 2 : ℝ) *
        ((∫ z : ℝ × ℝ, ‖fx z.1 z.2‖ ^ 2) +
          ∫ z : ℝ × ℝ, ‖fy z.1 z.2‖ ^ 2) := by
  rw [evenReflectionPlane_firstOrder_energy hf hfx hfy]
  exact add_le_add (plane_cube_energy_le_wholeSpace hL)
    (mul_le_mul_of_nonneg_left
      (add_le_add (plane_cube_energy_le_wholeSpace hDx)
        (plane_cube_energy_le_wholeSpace hDy)) (by norm_num))

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
