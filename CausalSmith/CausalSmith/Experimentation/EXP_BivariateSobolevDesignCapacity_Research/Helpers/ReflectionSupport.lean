module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionBudgetTransport

/-! # Fourier support of reflected ANOVA effects

Mixed translation differences annihilate effects using at most two coordinates.
This proves the order-two Fourier support without requiring pointwise versions of
conditional marginal regularity.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The translation difference on the normalized torus. -/
-- @node: torusDifference
def torusDifference {d : ℕ} (a : Torus d) (f : Torus d → ℂ) : Torus d → ℂ :=
  fun y => f y - f (y + a)

/-- Translation differences commute.](goal) This uses [the stated conclusion](goal). -/
-- @node: torusDifference_comm
lemma torusDifference_comm {d : ℕ} (a b : Torus d) (f : Torus d → ℂ) :
    torusDifference a (torusDifference b f) = torusDifference b (torusDifference a f) := by
  funext y
  simp only [torusDifference, add_assoc, add_comm a b]
  ring

/-- A translation-invariant summand is annihilated by its difference. Under [the stated conditions](hyp:h), [the asserted mathematical result follows](goal). -/
-- @node: torusDifference_eq_zero
lemma torusDifference_eq_zero {d : ℕ} (a : Torus d) (f : Torus d → ℂ)
    (h : ∀ y, f (y + a) = f y) : torusDifference a f = 0 := by
  funext y
  simp [torusDifference, h]

/-- Translation differences distribute over addition. [The asserted mathematical result follows](goal). -/
-- @node: torusDifference_add
lemma torusDifference_add {d : ℕ} (a : Torus d) (f g : Torus d → ℂ) :
    torusDifference a (f + g) = torusDifference a f + torusDifference a g := by
  funext y
  simp only [torusDifference, Pi.add_apply]
  ring

/-- [ Translation differences distribute over finite sums.](goal) -/
-- @node: torusDifference_sum
lemma torusDifference_sum {d : ℕ} {ι : Type*} (a : Torus d)
    (s : Finset ι) (f : ι → Torus d → ℂ) :
    torusDifference a (∑ i ∈ s, f i) = ∑ i ∈ s, torusDifference a (f i) := by
  classical
  funext y
  simp [torusDifference, Finset.sum_sub_distrib]

/-- Any invariant direction kills the third mixed difference. Under [the stated conditions](hyp:h), [the asserted mathematical result follows](goal). -/
-- @node: torusDifference_three_eq_zero
lemma torusDifference_three_eq_zero {d : ℕ} (a b c : Torus d) (f : Torus d → ℂ)
    (h : (∀ y, f (y + a) = f y) ∨ (∀ y, f (y + b) = f y) ∨
      (∀ y, f (y + c) = f y)) :
    torusDifference a (torusDifference b (torusDifference c f)) = 0 := by
  rcases h with ha | hb | hc
  · rw [torusDifference_comm a b, torusDifference_comm a c,
      torusDifference_eq_zero a f ha]
    funext y
    simp [torusDifference]
  · rw [torusDifference_comm b c, torusDifference_eq_zero b f hb]
    funext y
    simp [torusDifference]
  · rw [torusDifference_eq_zero c f hc]
    funext y
    simp [torusDifference]

/-- Translation preserves normalized product Haar measure. [The asserted mathematical result follows](goal). -/
-- @node: torus_add_measurePreserving
lemma torus_add_measurePreserving {d : ℕ} (a : Torus d) :
    MeasurePreserving (fun y : Torus d => y + a) (torusMeasure d) (torusMeasure d) := by
  exact measurePreserving_pi (fun _ : Fin d => AddCircle.haarAddCircle)
    (fun _ : Fin d => AddCircle.haarAddCircle)
    (fun j => measurePreserving_add_right AddCircle.haarAddCircle (a j))

/-- Translation differences preserve integrability. Under [the stated conditions](hyp:hf), [the asserted mathematical result follows](goal). -/
-- @node: torusDifference_integrable
lemma torusDifference_integrable {d : ℕ} (a : Torus d) {f : Torus d → ℂ}
    (hf : Integrable f (torusMeasure d)) :
    Integrable (torusDifference a f) (torusMeasure d) := by
  exact hf.sub ((torus_add_measurePreserving a).integrable_comp_of_integrable hf)

/-- [ Translation differences preserve almost-everywhere equality.](goal) Under [the stated conditions](hyp:h). -/
-- @node: torusDifference_congr_ae
lemma torusDifference_congr_ae {d : ℕ} (a : Torus d) {f g : Torus d → ℂ}
    (h : f =ᵐ[torusMeasure d] g) :
    torusDifference a f =ᵐ[torusMeasure d] torusDifference a g := by
  filter_upwards [h, (torus_add_measurePreserving a).quasiMeasurePreserving.ae h] with y hy ht
  simp only [torusDifference, hy, ht]

/-- [ A character times an integrable torus function is integrable.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: ek_mul_integrable
lemma ek_mul_integrable {d : ℕ} (k : Fin d → ℤ) {f : Torus d → ℂ}
    (hf : Integrable f (torusMeasure d)) :
    Integrable (fun y => ek k y * f y) (torusMeasure d) := by
  exact hf.bdd_mul (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (UnitAddTorus.mFourier k).norm_coe_le_norm y)

/-- [ Shifting one coordinate by half an inverse nonzero frequency negates its character.](goal) Under [the stated conditions](hyp:hj). -/
-- @node: ek_half_shift
lemma ek_half_shift {d : ℕ} (k : Fin d → ℤ) (j : Fin d) (hj : k j ≠ 0)
    (y : Torus d) :
    ek k (y + Pi.single j ((1 / 2 / (k j : ℝ) : ℝ) : AddCircle (1 : ℝ))) = -ek k y := by
  classical
  unfold ek UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Pi.add_apply, Pi.single_eq_same]
  rw [fourier_add_half_inv_index hj (by norm_num)]
  have he : (∏ i ∈ Finset.univ.erase j, fourier (k i)
      (y i + (Pi.single j ((1 / 2 / (k j : ℝ) : ℝ) : AddCircle (1 : ℝ)) : Torus d) i)) =
      ∏ i ∈ Finset.univ.erase j, fourier (k i) (y i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [Pi.single_eq_of_ne (Finset.mem_erase.mp hi).1]
  rw [he, neg_mul]

/-- [ A half-character translation difference doubles that Fourier coefficient.](goal) Under [the stated conditions](hyp:hf,ha). -/
-- @node: fourierCoeff_torusDifference
lemma fourierCoeff_torusDifference {d : ℕ} (k : Fin d → ℤ) (a : Torus d)
    {f : Torus d → ℂ} (hf : Integrable f (torusMeasure d))
    (ha : ∀ y, ek (-k) (y + a) = -ek (-k) y) :
    (∫ y, ek (-k) y * torusDifference a f y ∂torusMeasure d) =
      2 * ∫ y, ek (-k) y * f y ∂torusMeasure d := by
  have ht := (torus_add_measurePreserving a).integral_comp
    (MeasurableEquiv.addRight a).measurableEmbedding (fun y => ek (-k) y * f y)
  have he : (∫ y, ek (-k) y * f (y + a) ∂torusMeasure d) =
      -(∫ y, ek (-k) y * f y ∂torusMeasure d) := by
    simp only [Function.comp_def, ha, neg_mul, integral_neg] at ht
    exact neg_eq_iff_eq_neg.mp ht
  simp only [torusDifference, mul_sub]
  have hi : Integrable (fun y => ek (-k) y * f (y + a)) (torusMeasure d) :=
    ek_mul_integrable (-k) ((torus_add_measurePreserving a).integrable_comp_of_integrable hf)
  rw [integral_sub (ek_mul_integrable (-k) hf) hi, he]
  ring

/-- [ A shift in another coordinate leaves a folded coordinate unchanged.](goal) Under [the stated conditions](hyp:h). -/
-- @node: fold_add_single_of_ne
lemma fold_add_single_of_ne {d : ℕ} (y : Torus d) (r j : Fin d)
    (c : AddCircle (1 : ℝ)) (h : j ≠ r) :
    fold (y + Pi.single r c) j = fold y j := by
  simp [fold, Pi.add_apply, Pi.single_eq_of_ne h]

/-- [ Three distinct coordinate differences annihilate every two-coordinate effect.](goal) Under [the stated conditions](hyp:hrt,hru,htu). -/
-- @node: torusDifference_three_pair
lemma torusDifference_three_pair {d : ℕ} (r t u j l : Fin d)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u)
    (a b c : AddCircle (1 : ℝ)) (g : ℝ → ℝ → ℂ) :
    torusDifference (Pi.single r a) (torusDifference (Pi.single t b)
      (torusDifference (Pi.single u c) (fun y => g (fold y j) (fold y l)))) = 0 := by
  have hchoice : (j ≠ r ∧ l ≠ r) ∨ (j ≠ t ∧ l ≠ t) ∨ (j ≠ u ∧ l ≠ u) := by
    by_cases hjr : j = r <;> by_cases hjt : j = t <;>
      by_cases hlu : l = u <;> by_cases hlr : l = r <;> aesop
  apply torusDifference_three_eq_zero
  rcases hchoice with hr | ht | hu
  · left
    intro y
    rw [fold_add_single_of_ne y r j a hr.1, fold_add_single_of_ne y r l a hr.2]
  · right; left
    intro y
    rw [fold_add_single_of_ne y t j b ht.1, fold_add_single_of_ne y t l b ht.2]
  · right; right
    intro y
    rw [fold_add_single_of_ne y u j c hu.1, fold_add_single_of_ne y u l c hu.2]

/-- [ The exact order-two decomposition has zero third mixed translation difference,
modulo Haar null sets. No marginal representative regularity is needed.](goal) Under [the stated conditions](hyp:hm,hrt,hru,htu). -/
-- @node: orderTwo_third_difference_ae
lemma orderTwo_third_difference_ae {d : ℕ} (m : CenteredL2Fn d) (hm : OrderTwo m)
    (r t u : Fin d) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u)
    (a b c : AddCircle (1 : ℝ)) :
    torusDifference (Pi.single r a) (torusDifference (Pi.single t b)
      (torusDifference (Pi.single u c) (reflExt m.val))) =ᵐ[torusMeasure d] 0 := by
  classical
  let A : Fin d → Torus d → ℂ := fun j y => (g1 m.val j (fold y j) : ℂ)
  let B : Fin d → Fin d → Torus d → ℂ := fun j l y =>
    if j < l then (g2 m.val j l (fold y j) (fold y l) : ℂ) else 0
  have hrep : reflExt m.val =ᵐ[torusMeasure d] (∑ j, A j) + ∑ j, ∑ l, B j l := by
    have h := (fold_measurePreserving d).quasiMeasurePreserving.ae hm
    filter_upwards [h] with y hy
    simpa [reflExt, A, B, apply_ite] using congrArg Complex.ofReal hy
  have hA (j : Fin d) : torusDifference (Pi.single r a)
      (torusDifference (Pi.single t b) (torusDifference (Pi.single u c) (A j))) = 0 :=
    torusDifference_three_pair r t u j j hrt hru htu a b c (fun x _ => (g1 m.val j x : ℂ))
  have hB (j l : Fin d) : torusDifference (Pi.single r a)
      (torusDifference (Pi.single t b) (torusDifference (Pi.single u c) (B j l))) = 0 := by
    by_cases hjl : j < l
    · simp only [B, if_pos hjl]
      exact torusDifference_three_pair r t u j l hrt hru htu a b c
        (fun x v => (g2 m.val j l x v : ℂ))
    · funext y
      simp [B, hjl, torusDifference]
  have he := torusDifference_congr_ae (Pi.single r a)
    (torusDifference_congr_ae (Pi.single t b) (torusDifference_congr_ae (Pi.single u c) hrep))
  simp_rw [torusDifference_add, torusDifference_sum, hA, hB] at he
  simpa using he

/-- [ A zero third difference in three half-character directions forces a zero coefficient.](goal) Under [the stated conditions](hyp:hf,ha,hb,hc,hz). -/
-- @node: fourierCoeff_zero_of_third_difference
lemma fourierCoeff_zero_of_third_difference {d : ℕ} (k : Fin d → ℤ)
    (a b c : Torus d) {f : Torus d → ℂ} (hf : Integrable f (torusMeasure d))
    (ha : ∀ y, ek (-k) (y + a) = -ek (-k) y)
    (hb : ∀ y, ek (-k) (y + b) = -ek (-k) y)
    (hc : ∀ y, ek (-k) (y + c) = -ek (-k) y)
    (hz : torusDifference a (torusDifference b (torusDifference c f)) =ᵐ[torusMeasure d] 0) :
    (∫ y, ek (-k) y * f y ∂torusMeasure d) = 0 := by
  have hi := torusDifference_integrable c hf
  have hii := torusDifference_integrable b hi
  have he := fourierCoeff_torusDifference k a hii ha
  rw [fourierCoeff_torusDifference k b hi hb, fourierCoeff_torusDifference k c hf hc] at he
  have hzint : (∫ y, ek (-k) y * torusDifference a
      (torusDifference b (torusDifference c f)) y ∂torusMeasure d) = 0 := by
    calc
      _ = ∫ y, (0 : ℂ) ∂torusMeasure d := by
        apply integral_congr_ae
        filter_upwards [hz] with y hy
        simp only [hy, Pi.zero_apply, mul_zero]
      _ = 0 := integral_zero _ _
  rw [hzint] at he
  linear_combination (1 / 8 : ℂ) * he.symm

/-- [ An exactly order-two centered cube outcome has no reflected Fourier coefficient
supported on more than two coordinates.](goal) Under [the stated conditions](hyp:hm,hk). -/
-- @node: Fhat_zero_of_orderTwo
lemma Fhat_zero_of_orderTwo {d : ℕ} (m : CenteredL2Fn d) (hm : OrderTwo m)
    (k : Fin d → ℤ) (hk : 2 < (frequencySupport k).card) : Fhat m.val k = 0 := by
  classical
  obtain ⟨r, hr, t, ht, u, hu, hrt, hru, htu⟩ := Finset.two_lt_card.mp hk
  have hrk : (-k) r ≠ 0 := by simpa [frequencySupport] using hr
  have htk : (-k) t ≠ 0 := by simpa [frequencySupport] using ht
  have huk : (-k) u ≠ 0 := by simpa [frequencySupport] using hu
  let a : AddCircle (1 : ℝ) := ((1 / 2 / ((-k) r : ℝ) : ℝ) : AddCircle (1 : ℝ))
  let b : AddCircle (1 : ℝ) := ((1 / 2 / ((-k) t : ℝ) : ℝ) : AddCircle (1 : ℝ))
  let c : AddCircle (1 : ℝ) := ((1 / 2 / ((-k) u : ℝ) : ℝ) : AddCircle (1 : ℝ))
  exact fourierCoeff_zero_of_third_difference k (Pi.single r a) (Pi.single t b) (Pi.single u c)
    ((reflExt_memLp m).integrable (by norm_num))
    (ek_half_shift (-k) r hrk) (ek_half_shift (-k) t htk) (ek_half_shift (-k) u huk)
    (orderTwo_third_difference_ae m hm r t u hrt hru htu a b c)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
