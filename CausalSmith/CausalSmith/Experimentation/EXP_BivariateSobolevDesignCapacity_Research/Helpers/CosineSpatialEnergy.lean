module
public import Causalean.Mathlib.MeasureTheory.Integral.FiniteOrthonormal
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineWeakDerivative

/-! # Spatial energy on the cutoff support square

Exact trigonometric orthogonality on the three-unit interval gives the nine-cell
polynomial and gradient estimates used by the cosine-prior extension.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Lebesgue measure on the nine unit cells containing the cutoff support. -/
-- @node: cosineSupportMeasure
def cosineSupportMeasure : Measure (Cube 2) :=
  Measure.pi (fun _ => volume.restrict (Icc (-1 : ℝ) 2))

/-- Integer cosine modes integrate to zero over three complete unit cells.](goal) This uses [the stated conclusion](goal). -/
-- @node: support_integer_cosine_integral
lemma support_integer_cosine_integral (a : ℤ) :
    (∫ u, Real.cos (Real.pi * (a : ℝ) * u)
      ∂volume.restrict (Icc (-1 : ℝ) 2)) = if a = 0 then 3 else 0 := by
  by_cases ha : a = 0
  · norm_num [ha, Real.volume_Icc]
  · rw [if_neg ha, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    rw [intervalIntegral.integral_comp_mul_left Real.cos
      (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast ha)), integral_cos]
    have hright : Real.sin (Real.pi * (a : ℝ) * 2) = 0 := by
      convert Real.sin_int_mul_pi (2 * a) using 1 <;> push_cast <;> ring
    simp [hright, show Real.sin (Real.pi * (a : ℝ)) = 0 by
      simpa [mul_comm] using Real.sin_int_mul_pi a]

/-- Cosine orthogonality on the three-cell support interval has diagonal energy three halves. Under [the stated conditions](hyp:ha,hb), [the asserted mathematical result follows](goal). -/
-- @node: support_cosine_inner_product
lemma support_cosine_inner_product (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u, Real.cos (Real.pi * (a : ℝ) * u) * Real.cos (Real.pi * (b : ℝ) * u)
      ∂volume.restrict (Icc (-1 : ℝ) 2)) = if a = b then (3 / 2 : ℝ) else 0 := by
  have hidentity (u : ℝ) :
      Real.cos (Real.pi * (a : ℝ) * u) * Real.cos (Real.pi * (b : ℝ) * u) =
        (1 / 2 : ℝ) * (Real.cos (Real.pi * ((a : ℤ) - b : ℤ) * u) +
          Real.cos (Real.pi * ((a : ℤ) + b : ℤ) * u)) := by
    push_cast
    rw [show Real.pi * ((a : ℝ) - b) * u = Real.pi * a * u - Real.pi * b * u by ring,
      show Real.pi * ((a : ℝ) + b) * u = Real.pi * a * u + Real.pi * b * u by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hi (k : ℤ) : Integrable (fun u => Real.cos (Real.pi * (k : ℝ) * u))
      (volume.restrict (Icc (-1 : ℝ) 2)) := by
    exact Continuous.integrableOn_Icc (by fun_prop)
  simp_rw [hidentity]
  rw [integral_const_mul, integral_add (hi _) (hi _),
    support_integer_cosine_integral, support_integer_cosine_integral]
  have hab : (a : ℤ) + b ≠ 0 := by omega
  by_cases heq : a = b <;> norm_num [hab, sub_eq_zero, heq, Nat.ne_of_gt hb]


/-- [ Sine orthogonality on the three-cell support interval has diagonal energy three halves.](goal) Under [the stated conditions](hyp:ha,hb). -/
-- @node: support_sine_inner_product
lemma support_sine_inner_product (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u, Real.sin (Real.pi * (a : ℝ) * u) * Real.sin (Real.pi * (b : ℝ) * u)
      ∂volume.restrict (Icc (-1 : ℝ) 2)) = if a = b then (3 / 2 : ℝ) else 0 := by
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
      (volume.restrict (Icc (-1 : ℝ) 2)) := Continuous.integrableOn_Icc (by fun_prop)
  simp_rw [he]
  rw [integral_const_mul, integral_sub (hi _) (hi _),
    support_integer_cosine_integral, support_integer_cosine_integral]
  have hab : (a : ℤ) + b ≠ 0 := by omega
  by_cases heq : a = b <;> norm_num [hab, sub_eq_zero, heq, Nat.ne_of_gt hb]


/-- Fubini factors a product on the cutoff support square into its two interval integrals. [The asserted mathematical result follows](goal). -/
-- @node: cosineSupportMeasure_integral_product
lemma cosineSupportMeasure_integral_product (f g : ℝ → ℝ) :
    (∫ x, f (x 0) * g (x 1) ∂cosineSupportMeasure) =
      (∫ u, f u ∂volume.restrict (Icc (-1 : ℝ) 2)) *
      (∫ u, g u ∂volume.restrict (Icc (-1 : ℝ) 2)) := by
  let factors := fun i : Fin 2 => if i = 0 then f else g
  have he (x : Cube 2) : f (x 0) * g (x 1) = ∏ i, factors i (x i) := by
    simp [Fin.prod_univ_two, factors]
  simp_rw [he]
  rw [cosineSupportMeasure, integral_fintype_prod_eq_prod]
  simp [Fin.prod_univ_two, factors]

/-- Continuous functions are integrable on the compact cutoff support square. Under [the stated conditions](hyp:hf), [the asserted mathematical result follows](goal). -/
-- @node: continuous_integrable_cosineSupportMeasure
lemma continuous_integrable_cosineSupportMeasure {f : Cube 2 → ℝ} (hf : Continuous f) :
    Integrable f cosineSupportMeasure := by
  have hm : cosineSupportMeasure = volume.restrict (univ.pi (fun _ : Fin 2 => Icc (-1 : ℝ) 2)) := by
    rw [cosineSupportMeasure, ← Measure.restrict_pi_pi]
    rfl
  rw [hm]
  exact hf.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))

/-- Pair-cosine modes have diagonal energy nine on the cutoff support square. [The asserted mathematical result follows](goal). -/
-- @node: pairFeature_support_inner_product
lemma pairFeature_support_inner_product {L : ℕ} (α β : Fin L × Fin L) :
    (∫ x, pairFeature (⟨((0, 1), α), by change (0 : Fin 2) < 1; decide⟩ : PairIdx 2 L) x *
      pairFeature (⟨((0, 1), β), by change (0 : Fin 2) < 1; decide⟩ : PairIdx 2 L) x ∂cosineSupportMeasure) =
        if α = β then 9 else 0 := by
  have heq : α = β ↔ α.1 = β.1 ∧ α.2 = β.2 := Prod.ext_iff
  have he (x : Cube 2) : pairFeature (⟨((0, 1), α), by change (0 : Fin 2) < 1; decide⟩ : PairIdx 2 L) x *
      pairFeature (⟨((0, 1), β), by change (0 : Fin 2) < 1; decide⟩ : PairIdx 2 L) x =
      4 * ((Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
        Real.cos (Real.pi * (β.1.val + 1 : ℕ) * x 0)) *
      (Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1) *
        Real.cos (Real.pi * (β.2.val + 1 : ℕ) * x 1))) := by
    simp only [pairFeature]; ring
  conv_lhs => enter [2, x]; rw [he]
  rw [integral_const_mul, cosineSupportMeasure_integral_product
    (fun u => Real.cos (Real.pi * (α.1.val + 1 : ℕ) * u) *
      Real.cos (Real.pi * (β.1.val + 1 : ℕ) * u))
    (fun u => Real.cos (Real.pi * (α.2.val + 1 : ℕ) * u) *
      Real.cos (Real.pi * (β.2.val + 1 : ℕ) * u)),
    support_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _),
    support_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
  by_cases ha : α.1 = β.1 <;> by_cases hb : α.2 = β.2 <;>
    norm_num [heq, ha, hb, Nat.add_right_cancel_iff, Fin.val_inj]

/-- [ Differentiated modes have diagonal energy nine on the cutoff support square.](goal) -/
-- @node: pairDerivativeMode_support_inner_product
lemma pairDerivativeMode_support_inner_product {L : ℕ} (α β : Fin L × Fin L) (r : Fin 2) :
    (∫ x, pairDerivativeMode α r x * pairDerivativeMode β r x ∂cosineSupportMeasure) =
      if α = β then 9 else 0 := by
  have heq : α = β ↔ α.1 = β.1 ∧ α.2 = β.2 := Prod.ext_iff
  fin_cases r
  · change (∫ x, pairDerivativeMode α 0 x * pairDerivativeMode β 0 x ∂cosineSupportMeasure) = _
    have he (x : Cube 2) : pairDerivativeMode α 0 x * pairDerivativeMode β 0 x =
        4 * ((Real.sin (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
          Real.sin (Real.pi * (β.1.val + 1 : ℕ) * x 0)) *
        (Real.cos (Real.pi * (α.2.val + 1 : ℕ) * x 1) *
          Real.cos (Real.pi * (β.2.val + 1 : ℕ) * x 1))) := by
      simp only [pairDerivativeMode, ↓reduceIte]; ring
    conv_lhs => enter [2, x]; rw [he]
    rw [integral_const_mul, cosineSupportMeasure_integral_product
      (fun u => Real.sin (Real.pi * (α.1.val + 1 : ℕ) * u) *
        Real.sin (Real.pi * (β.1.val + 1 : ℕ) * u))
      (fun u => Real.cos (Real.pi * (α.2.val + 1 : ℕ) * u) *
        Real.cos (Real.pi * (β.2.val + 1 : ℕ) * u)),
      support_sine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _),
      support_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
    by_cases ha : α.1 = β.1 <;> by_cases hb : α.2 = β.2 <;>
      norm_num [heq, ha, hb, Nat.add_right_cancel_iff, Fin.val_inj]
  · change (∫ x, pairDerivativeMode α 1 x * pairDerivativeMode β 1 x ∂cosineSupportMeasure) = _
    have he (x : Cube 2) : pairDerivativeMode α 1 x * pairDerivativeMode β 1 x =
        4 * ((Real.cos (Real.pi * (α.1.val + 1 : ℕ) * x 0) *
          Real.cos (Real.pi * (β.1.val + 1 : ℕ) * x 0)) *
        (Real.sin (Real.pi * (α.2.val + 1 : ℕ) * x 1) *
          Real.sin (Real.pi * (β.2.val + 1 : ℕ) * x 1))) := by
      norm_num [pairDerivativeMode]; ring
    conv_lhs => enter [2, x]; rw [he]
    rw [integral_const_mul, cosineSupportMeasure_integral_product
      (fun u => Real.cos (Real.pi * (α.1.val + 1 : ℕ) * u) *
        Real.cos (Real.pi * (β.1.val + 1 : ℕ) * u))
      (fun u => Real.sin (Real.pi * (α.2.val + 1 : ℕ) * u) *
        Real.sin (Real.pi * (β.2.val + 1 : ℕ) * u)),
      support_cosine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _),
      support_sine_inner_product _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
    by_cases ha : α.1 = β.1 <;> by_cases hb : α.2 = β.2 <;>
      norm_num [heq, ha, hb, Nat.add_right_cancel_iff, Fin.val_inj]


/-- The exact polynomial energy over all nine support cells is nine times coefficient energy. [The asserted mathematical result follows](goal). -/
-- @node: pairCosinePolynomial_support_energy
lemma pairCosinePolynomial_support_energy {L : ℕ} (h : Fin L × Fin L → ℝ) :
    (∫ x, pairCosinePolynomial h x ^ 2 ∂cosineSupportMeasure) = 9 * ∑ α, h α ^ 2 := by
  let idx (α : Fin L × Fin L) : PairIdx 2 L :=
    ⟨((0, 1), α), by change (0 : Fin 2) < 1; decide⟩
  change (∫ x, (∑ α, h α * pairFeature (idx α) x) ^ 2 ∂cosineSupportMeasure) = _
  apply Causalean.Mathlib.MeasureTheory.finite_diagonal_square_integral
  · intro α β
    apply continuous_integrable_cosineSupportMeasure
    unfold pairFeature
    fun_prop
  · exact fun α β => pairFeature_support_inner_product α β

/-- [ The exact partial energy on the nine support cells keeps the squared coordinate frequency.](goal) -/
-- @node: pairCosinePartial_support_energy
lemma pairCosinePartial_support_energy {L : ℕ} (h : Fin L × Fin L → ℝ) (r : Fin 2) :
    (∫ x, pairCosinePartial h r x ^ 2 ∂cosineSupportMeasure) =
      9 * ∑ α, Real.pi ^ 2 *
        (if r = 0 then (α.1.val + 1 : ℕ) else (α.2.val + 1 : ℕ)) ^ 2 * h α ^ 2 := by
  simp only [pairCosinePartial]
  rw [Causalean.Mathlib.MeasureTheory.finite_diagonal_square_integral _ 9 _ _
    (fun α β => continuous_integrable_cosineSupportMeasure (by
      unfold pairDerivativeMode; split_ifs <;> fun_prop))
    (fun α β => pairDerivativeMode_support_inner_product α β r)]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- [ Each partial costs at most nine times squared cutoff frequency times coefficient energy.](goal) -/
-- @node: pairCosinePartial_support_energy_le
lemma pairCosinePartial_support_energy_le {L : ℕ} (h : Fin L × Fin L → ℝ) (r : Fin 2) :
    (∫ x, pairCosinePartial h r x ^ 2 ∂cosineSupportMeasure) ≤
      9 * (Real.pi ^ 2 * (L : ℝ) ^ 2 * ∑ α, h α ^ 2) := by
  rw [pairCosinePartial_support_energy, ← pairCosinePartial_energy]
  exact mul_le_mul_of_nonneg_left (pairCosinePartial_energy_le h r) (by norm_num)

/-- [ The support-square gradient energy is bounded without an ambient-dimension factor.](goal) -/
-- @node: pairCosinePolynomial_support_gradient_energy_le
lemma pairCosinePolynomial_support_gradient_energy_le {L : ℕ} (h : Fin L × Fin L → ℝ) :
    (∫ x, pairCosinePartial h 0 x ^ 2 ∂cosineSupportMeasure) +
      (∫ x, pairCosinePartial h 1 x ^ 2 ∂cosineSupportMeasure) ≤
        18 * Real.pi ^ 2 * (L : ℝ) ^ 2 * ∑ α, h α ^ 2 := by
  have h0 := pairCosinePartial_support_energy_le h 0
  have h1 := pairCosinePartial_support_energy_le h 1
  linarith

/-- A nonnegative energy density supported on the cutoff square has the same integral
under ambient Lebesgue measure and the support-square measure. Under [the stated conditions](hyp:f,hf), [the asserted mathematical result follows](goal). -/
-- @node: cosineSupportMeasure_lintegral
lemma cosineSupportMeasure_lintegral (f : Cube 2 → ℝ≥0∞)
    (hf : ∀ x, x 0 ∉ Icc (-1 : ℝ) 2 ∨ x 1 ∉ Icc (-1 : ℝ) 2 → f x = 0) :
    (∫⁻ x, f x) = ∫⁻ x, f x ∂cosineSupportMeasure := by
  let S : Set (Cube 2) := univ.pi (fun _ => Icc (-1 : ℝ) 2)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have he : S.indicator f = f := by
    funext x
    by_cases hx : x ∈ S
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      symm
      apply hf
      by_contra hn
      push_neg at hn
      apply hx
      intro i _
      fin_cases i
      · exact hn.1
      · exact hn.2
  conv_lhs => rw [← he]
  rw [lintegral_indicator hS]
  rw [cosineSupportMeasure, ← Measure.restrict_pi_pi]
  rfl

/-- The cutoff polynomial has whole-space squared energy at most nine times coefficient energy. [The asserted mathematical result follows](goal). -/
-- @node: pairCosineExtension_spatial_energy_le
lemma pairCosineExtension_spatial_energy_le {L : ℕ} (h : Fin L × Fin L → ℝ) :
    (∫⁻ x : Cube 2, ENNReal.ofReal ((cosineCutoff (x 0) * cosineCutoff (x 1) *
      pairCosinePolynomial h x) ^ 2)) ≤ ENNReal.ofReal (9 * ∑ α, h α ^ 2) := by
  rw [cosineSupportMeasure_lintegral _ (by
    intro x hx
    rcases hx with hx | hx <;> simp [cosineCutoff_eq_zero hx])]
  have hbound (x : Cube 2) :
      (cosineCutoff (x 0) * cosineCutoff (x 1) * pairCosinePolynomial h x) ^ 2 ≤
        pairCosinePolynomial h x ^ 2 := by
    have hq := cosinePairCutoff_bounds (WithLp.toLp 2 x)
    change 0 ≤ cosineCutoff (x 0) * cosineCutoff (x 1) ∧
      cosineCutoff (x 0) * cosineCutoff (x 1) ≤ 1 at hq
    rw [mul_pow]
    apply mul_le_of_le_one_left (sq_nonneg _)
    nlinarith [hq.1, hq.2]
  apply (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hbound x))).trans
  rw [← ofReal_integral_eq_lintegral_ofReal
    (continuous_integrable_cosineSupportMeasure (by fun_prop))
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)), pairCosinePolynomial_support_energy]

/-- [ The weak product derivatives have whole-space gradient energy bounded by the exact
nine-cell polynomial energies.](goal) -/
-- @node: pairCosineExtensionPartial_spatial_energy_le
lemma pairCosineExtensionPartial_spatial_energy_le {L : ℕ} (h : Fin L × Fin L → ℝ) :
    (∫⁻ x : Cube 2, ENNReal.ofReal (pairCosineExtensionPartial h 0 x ^ 2 +
      pairCosineExtensionPartial h 1 x ^ 2)) ≤
      ENNReal.ofReal ((36 + 36 * Real.pi ^ 2 * (L : ℝ) ^ 2) * ∑ α, h α ^ 2) := by
  rw [cosineSupportMeasure_lintegral _ (by
    intro x hx
    simp [pairCosineExtensionPartial_eq_zero_exterior h 0 x hx,
      pairCosineExtensionPartial_eq_zero_exterior h 1 x hx])]
  have hbound (x : Cube 2) :
      pairCosineExtensionPartial h 0 x ^ 2 + pairCosineExtensionPartial h 1 x ^ 2 ≤
        2 * (pairCosinePartial h 0 x ^ 2 + pairCosinePartial h 1 x ^ 2) +
          4 * pairCosinePolynomial h x ^ 2 := by
    have hg := pairCosineExtensionPartial_gradient_sq_le h x
    have hq := cosinePairCutoff_bounds (WithLp.toLp 2 x)
    change 0 ≤ cosineCutoff (x 0) * cosineCutoff (x 1) ∧
      cosineCutoff (x 0) * cosineCutoff (x 1) ≤ 1 at hq
    have hs : (cosineCutoff (x 0) * cosineCutoff (x 1)) ^ 2 ≤ 1 := by nlinarith [hq.1, hq.2]
    have hm := mul_le_mul_of_nonneg_right hs
      (add_nonneg (sq_nonneg (pairCosinePartial h 0 x)) (sq_nonneg (pairCosinePartial h 1 x)))
    nlinarith
  apply (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hbound x))).trans
  rw [← ofReal_integral_eq_lintegral_ofReal
    (continuous_integrable_cosineSupportMeasure (by fun_prop))
    (Filter.Eventually.of_forall (fun x => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_add (continuous_integrable_cosineSupportMeasure (by fun_prop))
    (continuous_integrable_cosineSupportMeasure (by fun_prop)), integral_const_mul,
    integral_const_mul, integral_add
    (continuous_integrable_cosineSupportMeasure (by fun_prop))
    (continuous_integrable_cosineSupportMeasure (by fun_prop)), pairCosinePolynomial_support_energy]
  have hg := pairCosinePolynomial_support_gradient_energy_le h
  nlinarith

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
