module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineExtension

/-! # Spatial derivative energy of finite pair-cosine polynomials

Sine orthogonality supplies the exact derivative energy identity used by the
cosine-prior cutoff-extension roadmap. The estimates concern the explicit
polynomial, before weak derivatives and Fourier unitarity are applied.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Positive sine modes have the same diagonal unit-interval inner products as cosine modes.](goal) Under [the stated conditions](hyp:ha,hb). -/
-- @node: uniform_sine_inner_product
lemma uniform_sine_inner_product (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u, Real.sin (Real.pi * (a : ℝ) * u) * Real.sin (Real.pi * (b : ℝ) * u)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = if a = b then (1 / 2 : ℝ) else 0 := by
  have he (u : ℝ) :
      Real.sin (Real.pi * (a : ℝ) * u) * Real.sin (Real.pi * (b : ℝ) * u) =
        (1 / 2 : ℝ) * (Real.cos (Real.pi * ((a : ℤ) - b : ℤ) * u) -
          Real.cos (Real.pi * ((a : ℤ) + b : ℤ) * u)) := by
    push_cast
    rw [show Real.pi * ((a : ℝ) - b) * u = Real.pi * a * u - Real.pi * b * u by ring,
      show Real.pi * ((a : ℝ) + b) * u = Real.pi * a * u + Real.pi * b * u by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hi (k : ℤ) : Integrable (fun u => Real.cos (Real.pi * (k : ℝ) * u))
      (volume.restrict (Icc (0 : ℝ) 1)) := Continuous.integrableOn_Icc (by fun_prop)
  simp_rw [he]
  rw [integral_const_mul, integral_sub (hi _) (hi _),
    uniform_integer_cosine_mean, uniform_integer_cosine_mean]
  have hab : (a : ℤ) + b ≠ 0 := by omega
  simp [hab, sub_eq_zero]

/-- The pair mode with one sine factor, normalized on the unit square. -/
-- @node: pairDerivativeMode
def pairDerivativeMode {L : ℕ} (α : Fin L × Fin L) (r : Fin 2) (x : Cube 2) : ℝ :=
  if r = 0 then
    2 * Real.sin (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
      Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1)
  else
    2 * Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
      Real.sin (Real.pi * (α.2.val + 1 : ℕ) * x 1)

/-- Each coordinate's differentiated modes are orthonormal under cube probability. [The asserted mathematical result follows](goal). -/
-- @node: pairDerivativeMode_inner_product
lemma pairDerivativeMode_inner_product {L : ℕ} (α β : Fin L × Fin L) (r : Fin 2) :
    (∫ x, pairDerivativeMode α r x * pairDerivativeMode β r x ∂cubeMeasure 2) =
      if α = β then 1 else 0 := by
  have heq : α = β ↔ α.1 = β.1 ∧ α.2 = β.2 := Prod.ext_iff
  fin_cases r
  · change (∫ x, pairDerivativeMode α 0 x * pairDerivativeMode β 0 x ∂cubeMeasure 2) = _
    have he (x : Cube 2) : pairDerivativeMode α 0 x * pairDerivativeMode β 0 x =
        4 * ((Real.sin (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
          Real.sin (Real.pi * (β.1.val + 1 : ℕ) * x 0)) *
        (Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1) *
          Real.cos (Real.pi * (β.2.val + 1 : ℕ) * x 1))) := by
      simp only [pairDerivativeMode, ↓reduceIte]; ring
    conv_lhs => enter [2, x]; rw [he]
    rw [integral_const_mul, cube_integral_two_coordinates (d := 2) 0 1 (by decide)
      (fun u => Real.sin (Real.pi * (α.1.val + 1 : ℕ) * u) *
        Real.sin (Real.pi * (β.1.val + 1 : ℕ) * u))
      (fun u => Real.cos (Real.pi * (α.2.val + 1 : ℕ) * u) *
        Real.cos (Real.pi * (β.2.val + 1 : ℕ) * u)),
      uniform_sine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _),
      uniform_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
    by_cases ha : α.1 = β.1 <;> by_cases hb : α.2 = β.2 <;>
      norm_num [heq, ha, hb, Nat.add_right_cancel_iff, Fin.val_inj]
  · change (∫ x, pairDerivativeMode α 1 x * pairDerivativeMode β 1 x ∂cubeMeasure 2) = _
    have he (x : Cube 2) : pairDerivativeMode α 1 x * pairDerivativeMode β 1 x =
        4 * ((Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
          Real.cos (Real.pi * (β.1.val + 1 : ℕ) * x 0)) *
        (Real.sin (Real.pi * (α.2.val + 1 : ℕ) * x 1) *
          Real.sin (Real.pi * (β.2.val + 1 : ℕ) * x 1))) := by
      norm_num [pairDerivativeMode]; ring
    conv_lhs => enter [2, x]; rw [he]
    rw [integral_const_mul, cube_integral_two_coordinates (d := 2) 0 1 (by decide)
      (fun u => Real.cos (Real.pi * (α.1.val + 1 : ℕ) * u) *
        Real.cos (Real.pi * (β.1.val + 1 : ℕ) * u))
      (fun u => Real.sin (Real.pi * (α.2.val + 1 : ℕ) * u) *
        Real.sin (Real.pi * (β.2.val + 1 : ℕ) * u)),
      uniform_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _),
      uniform_sine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
    by_cases ha : α.1 = β.1 <;> by_cases hb : α.2 = β.2 <;>
      norm_num [heq, ha, hb, Nat.add_right_cancel_iff, Fin.val_inj]

/-- Finite linear combinations of integrable orthonormal real modes have coefficient energy. Under [the stated conditions](hyp:hi,ho), [the asserted mathematical result follows](goal). -/
-- @node: finite_orthogonal_square_integral
lemma finite_orthogonal_square_integral {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (c : ι → ℝ)
    (hi : ∀ a b, Integrable (fun x => f a x * f b x) μ)
    (ho : ∀ a b, (∫ x, f a x * f b x ∂μ) = if a = b then 1 else 0) :
    (∫ x, (∑ a, c a * f a x) ^ 2 ∂μ) = ∑ a, c a ^ 2 := by
  classical
  have he (x : Ω) : (∑ a, c a * f a x) ^ 2 =
      ∑ a, ∑ b, (c a * c b) * (f a x * f b x) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => (hi a b).const_mul _))]
  simp_rw [integral_finsetSum _ (fun b _ => (hi _ b).const_mul _), integral_const_mul, ho]
  simp [pow_two]

/-- A finite pair-cosine polynomial with arbitrary real coefficients. -/
-- @node: pairCosinePolynomial
def pairCosinePolynomial {L : ℕ} (h : Fin L × Fin L → ℝ) (x : Cube 2) : ℝ :=
  ∑ α, h α * (2 * Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
    Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1))

/-- The polynomial's squared cube norm is exactly its coefficient energy. [The asserted mathematical result follows](goal). -/
-- @node: pairCosinePolynomial_energy
lemma pairCosinePolynomial_energy {L : ℕ} (h : Fin L × Fin L → ℝ) :
    (∫ x, pairCosinePolynomial h x ^ 2 ∂cubeMeasure 2) = ∑ α, h α ^ 2 := by
  let idx (α : Fin L × Fin L) : PairIdx 2 L := ⟨((0, 1), α), by change (0 : Fin 2) < 1; decide⟩
  have hinj : Function.Injective idx := by
    intro α β he
    exact congrArg (fun γ : PairIdx 2 L => γ.val.2) he
  change (∫ x, (∑ α, h α * pairFeature (idx α) x) ^ 2 ∂cubeMeasure 2) = _
  apply finite_orthogonal_square_integral
  · intro α β
    exact (pairFeature_memLp (idx α)).integrable_mul (pairFeature_memLp (idx β))
  · intro α β
    rw [pairFeature_cube_inner_product]
    simp only [hinj.eq_iff]

/-- [ The explicit partial derivative polynomial in either coordinate. -/
-- @node: pairCosinePartial
def pairCosinePartial {L : ℕ} (h : Fin L × Fin L → ℝ) (r : Fin 2) (x : Cube 2) : ℝ :=
  ∑ α, (-Real.pi * (if r = 0 then (α.1.val + 1 : ℕ) else (α.2.val + 1 : ℕ)) * h α) *
    pairDerivativeMode α r x

/-- The coordinate partial energy is exactly the corresponding squared frequency sum.](goal) This uses [the stated conclusion](goal). -/
-- @node: pairCosinePartial_energy
lemma pairCosinePartial_energy {L : ℕ} (h : Fin L × Fin L → ℝ) (r : Fin 2) :
    (∫ x, pairCosinePartial h r x ^ 2 ∂cubeMeasure 2) =
      ∑ α, Real.pi ^ 2 *
        (if r = 0 then (α.1.val + 1 : ℕ) else (α.2.val + 1 : ℕ)) ^ 2 * h α ^ 2 := by
  have hm (α : Fin L × Fin L) : MemLp (pairDerivativeMode α r) 2 (cubeMeasure 2) := by
    let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨by simp [Real.volume_Icc]⟩
    let : IsProbabilityMeasure (cubeMeasure 2) := by unfold cubeMeasure; infer_instance
    apply MemLp.of_bound (by unfold pairDerivativeMode; split_ifs <;> fun_prop) 2
    apply Filter.Eventually.of_forall
    intro x
    unfold pairDerivativeMode
    split_ifs <;> simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    · nlinarith [Real.abs_sin_le_one (Real.pi * (α.1.val + 1 : ℕ) * x 0),
        Real.abs_cos_le_one (Real.pi * (α.2.val + 1 : ℕ) * x 1),
        abs_nonneg (Real.sin (Real.pi * (α.1.val + 1 : ℕ) * x 0)),
        abs_nonneg (Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1))]
    · nlinarith [Real.abs_cos_le_one (Real.pi * (α.1.val + 1 : ℕ) * x 0),
        Real.abs_sin_le_one (Real.pi * (α.2.val + 1 : ℕ) * x 1),
        abs_nonneg (Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0)),
        abs_nonneg (Real.sin (Real.pi * (α.2.val + 1 : ℕ) * x 1))]
  have hi (α β : Fin L × Fin L) := (hm α).integrable_mul (hm β)
  simp only [pairCosinePartial]
  rw [finite_orthogonal_square_integral _ _ _ hi
    (fun α β => pairDerivativeMode_inner_product α β r)]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- [ The explicit partial polynomial is the ordinary derivative along its coordinate slice.](goal) -/
-- @node: pairCosinePolynomial_hasDerivAt
lemma pairCosinePolynomial_hasDerivAt {L : ℕ} (h : Fin L × Fin L → ℝ)
    (r : Fin 2) (x : Cube 2) :
    HasDerivAt (fun u => pairCosinePolynomial h (Function.update x r u))
      (pairCosinePartial h r x) (x r) := by
  classical
  unfold pairCosinePolynomial pairCosinePartial
  apply HasDerivAt.fun_sum
  intro α _
  fin_cases r
  · change HasDerivAt (fun u => h α *
        (2 * Real.cos (Real.pi * (α.1.val + 1 : ℕ) * u) *
          Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1))) _ (x 0)
    convert (((hasDerivAt_id (x 0)).const_mul
      (Real.pi * (α.1.val + 1 : ℕ))).cos.const_mul 2).mul_const
        (Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1)) |>.const_mul (h α) using 1 <;>
      first | rfl | (simp [pairDerivativeMode]; ring)
  · change HasDerivAt (fun u => h α *
        (2 * Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
          Real.cos (Real.pi * (α.2.val + 1 : ℕ) * u))) _ (x 1)
    convert ((hasDerivAt_id (x 1)).const_mul
      (Real.pi * (α.2.val + 1 : ℕ))).cos.const_mul
        (2 * Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0)) |>.const_mul (h α) using 1 <;>
      first | rfl | (simp [pairDerivativeMode]; ring)

/-- [ Each coordinate derivative costs at most the squared largest frequency
 times coefficient energy.](goal) -/
-- @node: pairCosinePartial_energy_le
lemma pairCosinePartial_energy_le {L : ℕ} (h : Fin L × Fin L → ℝ) (r : Fin 2) :
    (∫ x, pairCosinePartial h r x ^ 2 ∂cubeMeasure 2) ≤
      Real.pi ^ 2 * (L : ℝ) ^ 2 * ∑ α, h α ^ 2 := by
  rw [pairCosinePartial_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  have ha : (α.1.val + 1 : ℕ) ≤ L := by omega
  have hb : (α.2.val + 1 : ℕ) ≤ L := by omega
  have hf : (if r = 0 then (α.1.val + 1 : ℕ) else (α.2.val + 1 : ℕ)) ≤ L := by
    split_ifs <;> assumption
  have hc : (0 : ℝ) ≤ (if r = 0 then (α.1.val + 1 : ℕ) else (α.2.val + 1 : ℕ)) :=
    Nat.cast_nonneg _
  have hcast : (((if r = 0 then α.1.val + 1 else α.2.val + 1) : ℕ) : ℝ) ≤ L :=
    by exact_mod_cast hf
  have hsq : (((if r = 0 then α.1.val + 1 else α.2.val + 1) : ℕ) : ℝ) ^ 2 ≤
      (L : ℝ) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (sq_nonneg _)

/-- [ The two partial energies together obey the roadmap's dimension-two gradient bound.](goal) -/
-- @node: pairCosinePolynomial_gradient_energy_le
lemma pairCosinePolynomial_gradient_energy_le {L : ℕ} (h : Fin L × Fin L → ℝ) :
    (∫ x, pairCosinePartial h 0 x ^ 2 ∂cubeMeasure 2) +
      (∫ x, pairCosinePartial h 1 x ^ 2 ∂cubeMeasure 2) ≤
        2 * Real.pi ^ 2 * (L : ℝ) ^ 2 * ∑ α, h α ^ 2 := by
  have h0 := pairCosinePartial_energy_le h 0
  have h1 := pairCosinePartial_energy_le h 1
  linarith

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
