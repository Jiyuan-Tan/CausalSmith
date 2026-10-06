module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerLikelihood
public import Mathlib.Analysis.Calculus.MeanValue

/-! Mean-value and rare-mark bounds for component Hellinger discrepancy. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- The outcome derivative is a finite sum of polynomial treatment factors. -/
-- @node: component_outcome_derivative
lemma component_outcome_derivative (m : ℕ) (x : Fin m → unitInterval)
    (s t : ℝ) (z : Fin m → Bool × ℝ) :
    deriv (fun u => componentDensity κ n m x s u z) t =
      (Fintype.card (Signs κ n) : ℝ)⁻¹ * ∑ v : Signs κ n,
        ∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, lowerDensity κ n s t v (x j) (z j)) *
          lowerDensityT κ n s v (x i) (z i) := by
  exact ((HasDerivAt.fun_sum (fun v _ => HasDerivAt.fun_finsetProd
    (fun i _ => hasDerivAt_lowerDensityT κ n s t v (x i) (z i)))).const_mul _).deriv

/-- Both axes and the mixed derivative are differentiable everywhere. -/
-- @node: component_density_differentiable_axes
lemma component_density_differentiable_axes (m : ℕ) (x : Fin m → unitInterval)
    (s t : ℝ) (z : Fin m → Bool × ℝ) :
    DifferentiableAt ℝ (fun u => componentDensity κ n m x s u z) t ∧
    DifferentiableAt ℝ (fun u => deriv (fun v => componentDensity κ n m x u v z) t) s := by
  constructor
  · exact ((HasDerivAt.fun_sum (fun v _ => HasDerivAt.fun_finsetProd
      (fun i _ => hasDerivAt_lowerDensityT κ n s t v (x i) (z i)))).const_mul _).differentiableAt
  · simp_rw [component_outcome_derivative]
    unfold lowerDensity lowerDensityT
    fun_prop

/-- Applying the scalar mean-value theorem on each axis bounds the rectangular difference. -/
-- @node: component_density_difference_bound
lemma component_density_difference_bound (hκ : κ.Valid) (hn : 2 ≤ n)
    (m : ℕ) (x : Fin m → unitInterval) (z : Fin m → Bool × ℝ)
    (hz : ∀ i, |lowerB κ n * markV κ n (z i).2| ≤ 1/4) :
    |componentDensity κ n m x (lowerA κ n) (lowerB κ n) z -
      componentDensity κ n m x (lowerA κ n) (-lowerB κ n) z| ≤
      24*lowerA κ n*lowerB κ n*(m : ℝ)*(3/2 : ℝ)^m*∑ i, |markV κ n (z i).2| := by
  let a := lowerA κ n
  let b := lowerB κ n
  let C := 12*(m : ℝ)*(3/2 : ℝ)^m*∑ i, |markV κ n (z i).2|
  have ha := (lower_scale_small κ n hκ hn).2.1
  have hb := (lower_scale_small κ n hκ hn).2.2
  have htv (t : ℝ) (ht : t ∈ Icc (-b) b) (i : Fin m) : |t*markV κ n (z i).2| ≤ 1/4 := by
    have ht' : |t| ≤ b := abs_le.mpr ht
    calc
      _ = |t| * |markV κ n (z i).2| := abs_mul _ _
      _ ≤ b * |markV κ n (z i).2| := mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
      _ = |b*markV κ n (z i).2| := by rw [abs_mul, abs_of_pos hb.1]
      _ ≤ _ := hz i
  have hd (t : ℝ) (ht : t ∈ Icc (-b) b) :
      |deriv (fun v => componentDensity κ n m x a v z) t -
        deriv (fun v => componentDensity κ n m x 0 v z) t| ≤ C*a := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun u => deriv (fun v => componentDensity κ n m x u v z) t)
      (s := Icc 0 a) (C := C)
      (fun u _ => (component_density_differentiable_axes κ n m x u t z).2)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        exact component_mixed_derivative_pointwise κ n (by omega) m x u t
          (by rw [abs_of_nonneg hu.1]; exact hu.2.trans ha.2) z (htv t ht))
      (convex_Icc 0 a) (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.1.le⟩)
      (show a ∈ Icc 0 a from ⟨ha.1.le, le_rfl⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos (show 0 < a from ha.1)] using h
  let f := fun t => componentDensity κ n m x a t z - componentDensity κ n m x 0 t z
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Icc (-b) b) (C := C*a)
    (fun t _ => (component_density_differentiable_axes κ n m x a t z).1.sub
      (component_density_differentiable_axes κ n m x 0 t z).1)
    (fun t ht => by
      dsimp [f]
      rw [deriv_fun_sub (component_density_differentiable_axes κ n m x a t z).1
        (component_density_differentiable_axes κ n m x 0 t z).1]
      exact hd t ht)
    (convex_Icc (-b) b) (show -b ∈ Icc (-b) b from ⟨le_rfl, by linarith [hb.1]⟩)
    (show b ∈ Icc (-b) b from ⟨by linarith [hb.1], le_rfl⟩)
  have he := component_density_zero_axis_symmetry κ n m x b z
  have hf : f b - f (-b) = componentDensity κ n m x a b z - componentDensity κ n m x a (-b) z := by
    dsimp [f]; rw [he]; ring
  simp only [hf, Real.norm_eq_abs] at h
  rw [show b - -b = 2*b by ring, abs_of_pos (by have : 0 < b := hb.1; positivity : 0 < 2*b)] at h
  exact h.trans_eq (by dsimp [C,a,b]; ring)

/-- Every one-record likelihood is at least one half on the intermediate rectangle. -/
-- @node: lower_density_half_le
lemma lower_density_half_le (hn : 0 < n) (s t : ℝ) (hs : |s| ≤ 1/1024)
    (v : Signs κ n) (x : unitInterval) (z : Bool × ℝ)
    (htv : |t*markV κ n z.2| ≤ 1/4) : 1/2 ≤ lowerDensity κ n s t v x z := by
  have hF := lower_field_abs_le_three_halves κ n hn v x
  have hU := reference_markU_abs_le_three z.1
  have hk := lower_cutoff_range κ n x
  have hK : |lowerSquare κ n x| ≤ 1 := by
    rw [lowerSquare, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hsf : |s*markU z.1*lowerField κ n v x| ≤ (1/1024)*3*(3/2) := by
    simp only [abs_mul]; gcongr
  have hinner : |t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x)| ≤
      (1/4)*((3/2)+(1/1024)*3) := by
    rw [abs_mul]
    apply mul_le_mul htv _ (abs_nonneg _) (by norm_num)
    calc
      _ ≤ |lowerField κ n v x|+|s*markU z.1*lowerSquare κ n x| := abs_sub _ _
      _ ≤ _ := by
        simp only [abs_mul]
        nlinarith [mul_nonneg (abs_nonneg s) (abs_nonneg (markU z.1)),
          mul_le_mul hs hU (abs_nonneg _) (by norm_num),
          mul_le_mul_of_nonneg_left hK (mul_nonneg (abs_nonneg s) (abs_nonneg (markU z.1)))]
  have h1 := (abs_le.mp hsf).1
  have h2 := (abs_le.mp hinner).1
  unfold lowerDensity
  nlinarith [mul_nonneg
    (show 0 ≤ s*markU z.1*lowerField κ n v x + (1/1024)*3*(3/2) by linarith)
    (show 0 ≤ t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x) +
      (1/4)*((3/2)+(1/1024)*3) by linarith)]

/-- Averaging the finite sign prior preserves the product likelihood floor. -/
-- @node: component_density_floor
lemma component_density_floor (hn : 0 < n) (m : ℕ) (x : Fin m → unitInterval)
    (s t : ℝ) (hs : |s| ≤ 1/1024) (z : Fin m → Bool × ℝ)
    (hz : ∀ i, |t*markV κ n (z i).2| ≤ 1/4) :
    (1/2 : ℝ)^m ≤ componentDensity κ n m x s t z := by
  have hp (v : Signs κ n) : (1/2 : ℝ)^m ≤ ∏ i, lowerDensity κ n s t v (x i) (z i) := by
    have h := Finset.prod_le_prod (s := Finset.univ)
      (f := fun _ : Fin m => (1/2 : ℝ)) (g := fun i => lowerDensity κ n s t v (x i) (z i))
      (fun _ _ => by norm_num) (fun i _ => lower_density_half_le κ n hn s t hs v (x i) (z i) (hz i))
    simpa using h
  have hc : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold componentDensity
  calc
    _ = (Fintype.card (Signs κ n) : ℝ)⁻¹ * ∑ _ : Signs κ n, (1/2 : ℝ)^m := by simp [hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hp v)) (by positivity)

/-- The square-root identity compares Hellinger loss to squared density loss using a floor. -/
-- @node: sqrt_difference_sq_le_floor
lemma sqrt_difference_sq_le_floor (f g d : ℝ) (hd : 0 < d) (hf : d ≤ f) (hg : d ≤ g) :
    (Real.sqrt f - Real.sqrt g)^2 ≤ d⁻¹*(f-g)^2 := by
  have hf0 : 0 ≤ f := hd.le.trans hf
  have hg0 : 0 ≤ g := hd.le.trans hg
  have hs : d ≤ (Real.sqrt f+Real.sqrt g)^2 := by
    nlinarith [Real.sq_sqrt hf0, Real.sq_sqrt hg0,
      Real.sqrt_nonneg f, Real.sqrt_nonneg g,
      mul_nonneg (Real.sqrt_nonneg f) (Real.sqrt_nonneg g)]
  have hid : (f-g)^2 = (Real.sqrt f-Real.sqrt g)^2*(Real.sqrt f+Real.sqrt g)^2 := by
    nlinarith [Real.sq_sqrt hf0, Real.sq_sqrt hg0,
      sq_nonneg (Real.sqrt f * Real.sqrt g)]
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (Real.sqrt f-Real.sqrt g)^2*(Real.sqrt f+Real.sqrt g)^2 :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := hid.symm

/-- The component Hellinger bound retains the finite-p rare-mark scaling. -/
-- @node: component_hellinger_bound
lemma component_hellinger_bound (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (m : ℕ) (hm : 2 ≤ m) (x : Fin m → unitInterval) :
  Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin m => referenceMarks κ n))
    (componentDensity κ n m x (lowerA κ n) (lowerB κ n))
    (componentDensity κ n m x (lowerA κ n) (-lowerB κ n)) ≤
    144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*(m : ℝ)^4*(9/2 : ℝ)^m  := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  let μ := Measure.pi (fun _ : Fin m => referenceMarks κ n)
  let C : ℝ := 24*lowerA κ n*lowerB κ n*(m : ℝ)*(3/2 : ℝ)^m
  let σ2 : ℝ := lowerAmplitude κ n ^ (κ.p-2)/4
  have ha := (lower_scale_small κ n hκ hn).2.1
  have hb' := (lower_scale_small κ n hκ hn).2.2
  have hmarks : ∀ᵐ z ∂μ, ∀ i, |lowerB κ n*markV κ n (z i).2| ≤ 1/4 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => referenceMarks κ n) (i := i)).eventually
      (reference_markV_scaled_bound κ n hκ hn (lowerB κ n) (by rw [abs_of_pos hb'.1]))
  have hi (i : Fin m) : Integrable (fun z : Fin m → Bool × ℝ => (markV κ n (z i).2)^2) μ :=
    integrable_comp_eval (μ := fun _ : Fin m => referenceMarks κ n) (i := i)
      (reference_marks_response_integrable κ n hκ hn (fun y => (markV κ n y)^2))
  have hiSum : Integrable (fun z : Fin m → Bool × ℝ => ∑ i, (markV κ n (z i).2)^2) μ :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hmono : ∀ᵐ z ∂μ,
      (Real.sqrt (componentDensity κ n m x (lowerA κ n) (lowerB κ n) z) -
        Real.sqrt (componentDensity κ n m x (lowerA κ n) (-lowerB κ n) z))^2 ≤
      (2 : ℝ)^m*C^2*(m : ℝ)*(∑ i, (markV κ n (z i).2)^2) := by
    filter_upwards [hmarks] with z hz
    have hf := component_density_floor κ n (by omega) m x (lowerA κ n) (lowerB κ n)
      (by rw [abs_of_pos ha.1]; exact ha.2) z hz
    have hg := component_density_floor κ n (by omega) m x (lowerA κ n) (-lowerB κ n)
      (by rw [abs_of_pos ha.1]; exact ha.2) z (by intro i; simpa only [neg_mul, abs_neg] using hz i)
    have hdiff := component_density_difference_bound κ n hκ hn m x z hz
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) (fun i => |markV κ n (z i).2|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at hCS
    calc
      _ ≤ ((1/2 : ℝ)^m)⁻¹ * (componentDensity κ n m x (lowerA κ n) (lowerB κ n) z -
          componentDensity κ n m x (lowerA κ n) (-lowerB κ n) z)^2 :=
        sqrt_difference_sq_le_floor _ _ _ (by positivity) hf hg
      _ = (2 : ℝ)^m * |componentDensity κ n m x (lowerA κ n) (lowerB κ n) z -
          componentDensity κ n m x (lowerA κ n) (-lowerB κ n) z|^2 := by
        rw [sq_abs, ← inv_pow]; norm_num
      _ ≤ (2 : ℝ)^m * (C*(∑ i, |markV κ n (z i).2|))^2 := by
        gcongr
      _ ≤ (2 : ℝ)^m*C^2*((m : ℝ)*(∑ i, (markV κ n (z i).2)^2)) := by
        rw [mul_pow]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hCS (sq_nonneg C))
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)
      _ = _ := by ring
  unfold Causalean.Stat.hellingerSqDensity
  calc
    _ ≤ ∫ z, (2 : ℝ)^m*C^2*(m : ℝ)*(∑ i, (markV κ n (z i).2)^2) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (hiSum.const_mul _) hmono
    _ = (2 : ℝ)^m*C^2*(m : ℝ)*((m : ℝ)*σ2) := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
      have he (i : Fin m) : (∫ z : Fin m → Bool × ℝ, (markV κ n (z i).2)^2 ∂μ) = σ2 := by
        rw [integral_comp_eval (μ := fun _ : Fin m => referenceMarks κ n) (i := i)
          (reference_marks_response_integrable κ n hκ hn
            (fun y => (markV κ n y)^2)).aestronglyMeasurable]
        exact (reference_markV_moments κ n hκ hn).2
      simp_rw [he]
      simp
    _ = _ := by
      dsimp [C, σ2]
      have hp : (2 : ℝ)^m * ((3/2 : ℝ)^m)^2 = (9/2 : ℝ)^m := by
        rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← mul_pow]
        norm_num
      calc
        _ = 144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
            (m : ℝ)^4*((2 : ℝ)^m*((3/2 : ℝ)^m)^2) := by ring
        _ = _ := by rw [hp]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
