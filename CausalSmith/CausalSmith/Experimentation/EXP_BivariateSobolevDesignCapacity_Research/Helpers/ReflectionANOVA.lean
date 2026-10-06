module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionSupport
public import Mathlib.Probability.Moments.Variance

/-! # Canonical ANOVA regularity and Fourier supports

Independent coordinate resampling preserves cube probability. Fubini then proves
centering of canonical main effects and L² regularity of all canonical effects.
Translation invariance localizes their Fourier supports, and their integrability
gives exact coefficient additivity for the order-two decomposition.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Unit-cube Lebesgue measure has total mass one in every dimension. -/
-- @node: cubeMeasure_isProbabilityMeasure
instance cubeMeasure_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (cubeMeasure d) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  unfold cubeMeasure
  infer_instance

/-- Selecting each coordinate from either of two independent cube draws preserves
cube probability.](goal) This uses [the stated conclusion](goal). -/
-- @node: cube_resample_measurePreserving
lemma cube_resample_measurePreserving {d : ℕ} (S : Finset (Fin d)) :
    MeasurePreserving (fun z : Cube d × Cube d =>
      fun i => if i ∈ S then z.1 i else z.2 i)
      ((cubeMeasure d).prod (cubeMeasure d)) (cubeMeasure d) := by
  classical
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  have h := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d)
    (fun _ => volume.restrict (Icc (0 : ℝ) 1))
    (fun _ => volume.restrict (Icc (0 : ℝ) 1))).symm
  have hp : MeasurePreserving (fun z : Fin d → ℝ × ℝ =>
      fun i => if i ∈ S then (z i).1 else (z i).2)
      (Measure.pi (fun _ : Fin d =>
        (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))))
      (cubeMeasure d) := by
    unfold cubeMeasure
    apply measurePreserving_pi
      (fun _ : Fin d => (volume.restrict (Icc (0 : ℝ) 1)).prod
        (volume.restrict (Icc (0 : ℝ) 1)))
      (fun _ : Fin d => volume.restrict (Icc (0 : ℝ) 1))
      (f := fun i z => if i ∈ S then z.1 else z.2)
    intro i
    by_cases hi : i ∈ S
    · simpa only [if_pos hi] using
        (measurePreserving_fst (μ := volume.restrict (Icc (0 : ℝ) 1))
          (ν := volume.restrict (Icc (0 : ℝ) 1)))
    · simpa only [if_neg hi] using
        (measurePreserving_snd (μ := volume.restrict (Icc (0 : ℝ) 1))
          (ν := volume.restrict (Icc (0 : ℝ) 1)))
  exact hp.comp h

/-- A Borel representative has a Borel canonical main effect, including at exceptional
slices where the Bochner integral is defined to be zero. This uses [the hm hypothesis](hyp:hm), [the stated conclusion](goal). -/
-- @node: g1_measurable
@[fun_prop] lemma g1_measurable {d : ℕ} {m : Cube d → ℝ} (hm : Measurable m)
    (j : Fin d) : Measurable (g1 m j) := by
  have h : Measurable (fun z : ℝ × Cube d => m (Function.update z.2 j z.1)) := by
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- The lifted main marginal of an integrable cube function is integrable. Under [the stated conditions](hyp:hm), [the asserted mathematical result follows](goal). -/
-- @node: g1_lift_integrable
lemma g1_lift_integrable {d : ℕ} {m : Cube d → ℝ}
    (hm : Integrable m (cubeMeasure d)) (j : Fin d) :
    Integrable (fun x : Cube d => g1 m j (x j)) (cubeMeasure d) := by
  have h := (cube_resample_measurePreserving {j}).integrable_comp_of_integrable hm
  have he : (fun z : Cube d × Cube d =>
      m (fun i => if i ∈ ({j} : Finset (Fin d)) then z.1 i else z.2 i)) =
      (fun z => m (Function.update z.2 j (z.1 j))) := by
    funext z
    congr 1
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update, hi]
  simp only [Function.comp_def] at h
  rw [he] at h
  exact h.integral_prod_left

/-- [ Integrating a lifted canonical main effect recovers the original cube mean.](goal) Under [the stated conditions](hyp:hm). -/
-- @node: integral_g1_lift
lemma integral_g1_lift {d : ℕ} {m : Cube d → ℝ}
    (hm : Integrable m (cubeMeasure d)) (j : Fin d) :
    (∫ x : Cube d, g1 m j (x j) ∂cubeMeasure d) =
      ∫ x, m x ∂cubeMeasure d := by
  have hp := cube_resample_measurePreserving ({j} : Finset (Fin d))
  have he : (fun z : Cube d × Cube d =>
      m (fun i => if i ∈ ({j} : Finset (Fin d)) then z.1 i else z.2 i)) =
      (fun z => m (Function.update z.2 j (z.1 j))) := by
    funext z
    congr 1
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update, hi]
  have hi := hp.integrable_comp_of_integrable hm
  have ht := integral_map hp.measurable.aemeasurable (by
    rw [hp.map_eq]
    exact hm.aestronglyMeasurable)
  rw [hp.map_eq, he] at ht
  simp only [Function.comp_def] at hi
  rw [he] at hi
  exact (integral_prod _ hi).symm.trans ht.symm

/-- Centering of the original cube outcome centers each lifted canonical main effect. [The asserted mathematical result follows](goal). -/
-- @node: integral_g1_lift_centered
lemma integral_g1_lift_centered {d : ℕ} (m : CenteredL2Fn d) (j : Fin d) :
    (∫ x : Cube d, g1 m.val j (x j) ∂cubeMeasure d) = 0 := by
  rw [integral_g1_lift (m.property.2.1.integrable (by norm_num)), m.property.2.2]

/-- Averaging independent unused coordinates contracts square integrability.
This applies to both one-coordinate and two-coordinate raw marginals. Under [the stated conditions](hyp:hm,hLp), [the asserted mathematical result follows](goal). -/
-- @node: cube_resample_marginal_memLp
lemma cube_resample_marginal_memLp {d : ℕ} {m : Cube d → ℝ}
    (hm : Measurable m) (hLp : MemLp m 2 (cubeMeasure d)) (S : Finset (Fin d)) :
    MemLp (fun x : Cube d => ∫ y : Cube d,
      m (fun i => if i ∈ S then x i else y i) ∂cubeMeasure d) 2 (cubeMeasure d) := by
  classical
  let f : Cube d × Cube d → ℝ := fun z =>
    m (fun i => if i ∈ S then z.1 i else z.2 i)
  have hf : Measurable f := by
    apply hm.comp
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ S
    · simp only [if_pos hi]; fun_prop
    · simp only [if_neg hi]; fun_prop
  have hprod : MemLp f 2 ((cubeMeasure d).prod (cubeMeasure d)) :=
    hLp.comp_measurePreserving (cube_resample_measurePreserving S)
  have hsq : Integrable (fun z => f z ^ 2) ((cubeMeasure d).prod (cubeMeasure d)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hprod
  have hmean : Measurable (fun x => ∫ y, f (x, y) ∂cubeMeasure d) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  apply (memLp_two_iff_integrable_sq hmean.aestronglyMeasurable).mpr
  apply hsq.integral_prod_left.mono' (hmean.pow_const 2).aestronglyMeasurable
  filter_upwards [hsq.prod_right_ae] with x hx
  have hslice : MemLp (fun y => f (x, y)) 2 (cubeMeasure d) :=
    (memLp_two_iff_integrable_sq
      (hf.comp measurable_prodMk_left).aestronglyMeasurable).mpr hx
  have hj := variance_nonneg (fun y => f (x, y)) (cubeMeasure d)
  rw [variance_eq_sub hslice] at hj
  simpa only [Real.norm_eq_abs, abs_sq, Pi.pow_apply] using
    (sub_nonneg.mp hj)

/-- [ The lifted canonical main effect is square integrable.](goal) Under [the stated conditions](hyp:hm,hLp). -/
-- @node: g1_lift_memLp
lemma g1_lift_memLp {d : ℕ} {m : Cube d → ℝ} (hm : Measurable m)
    (hLp : MemLp m 2 (cubeMeasure d)) (j : Fin d) :
    MemLp (fun x : Cube d => g1 m j (x j)) 2 (cubeMeasure d) := by
  have h := cube_resample_marginal_memLp hm hLp ({j} : Finset (Fin d))
  have he (x y : Cube d) : (fun i => if i ∈ ({j} : Finset (Fin d)) then x i else y i) =
      Function.update y j (x j) := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update, hi]
  simpa only [he, g1] using h

/-- [ The raw two-coordinate marginal equals averaging a two-coordinate resampling.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: pair_marginal_resample_eq
lemma pair_marginal_resample_eq {d : ℕ} (m : Cube d → ℝ) (j l : Fin d)
    (hjl : j ≠ l) (x : Cube d) :
    (∫ y : Cube d, m (fun i => if i ∈ ({j, l} : Finset (Fin d)) then x i else y i)
      ∂cubeMeasure d) =
    ∫ y, m (Function.update (Function.update y j (x j)) l (x l)) ∂cubeMeasure d := by
  congr 1
  funext y
  congr 1
  funext i
  by_cases hij : i = j
  · subst i; simp [hjl]
  · by_cases hil : i = l
    · subst i; simp
    · simp [Function.update, hij, hil]

/-- [ The lifted canonical pair effect is square integrable, without any regularity premise
beyond the original measurable square-integrable outcome.](goal) Under [the stated conditions](hyp:hm,hLp,hjl). -/
-- @node: g2_lift_memLp
lemma g2_lift_memLp {d : ℕ} {m : Cube d → ℝ} (hm : Measurable m)
    (hLp : MemLp m 2 (cubeMeasure d)) (j l : Fin d) (hjl : j ≠ l) :
    MemLp (fun x : Cube d => g2 m j l (x j) (x l)) 2 (cubeMeasure d) := by
  have h := cube_resample_marginal_memLp hm hLp ({j, l} : Finset (Fin d))
  simp_rw [pair_marginal_resample_eq m j l hjl] at h
  exact (h.sub (g1_lift_memLp hm hLp j)).sub (g1_lift_memLp hm hLp l)

/-- [ A nonzero character coordinate has zero coefficient against a function invariant
under shifts in that coordinate.](goal) Under [the stated conditions](hyp:hr,hf,hinv). -/
-- @node: fourierCoeff_zero_of_coordinate_invariant
lemma fourierCoeff_zero_of_coordinate_invariant {d : ℕ} (k : Fin d → ℤ)
    (r : Fin d) (hr : k r ≠ 0) {f : Torus d → ℂ}
    (hf : Integrable f (torusMeasure d))
    (hinv : ∀ y c, f (y + Pi.single r c) = f y) :
    (∫ y, ek (-k) y * f y ∂torusMeasure d) = 0 := by
  classical
  let c : AddCircle (1 : ℝ) := ((1 / 2 / ((-k) r : ℝ) : ℝ) : AddCircle (1 : ℝ))
  have hc : (-k) r ≠ 0 := by simpa using hr
  have h := fourierCoeff_torusDifference k (Pi.single r c) hf
    (ek_half_shift (-k) r hc)
  rw [torusDifference_eq_zero _ f (fun y => hinv y c)] at h
  simp only [Pi.zero_apply, mul_zero, integral_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- [ Reflected main effects have no frequency outside their own coordinate.](goal) Under [the stated conditions](hyp:hrj,hr). -/
-- @node: Fhat_g1_lift_zero_off_coordinate
lemma Fhat_g1_lift_zero_off_coordinate {d : ℕ} (m : CenteredL2Fn d)
    (j r : Fin d) (hrj : r ≠ j) (k : Fin d → ℤ) (hr : k r ≠ 0) :
    Fhat (fun x : Cube d => g1 m.val j (x j)) k = 0 := by
  apply fourierCoeff_zero_of_coordinate_invariant k r hr
    ((reflExt_memLp_of_cube (g1_lift_memLp m.property.1 m.property.2.1 j)).integrable
      (by norm_num))
  intro y c
  simp only [reflExt]
  rw [fold_add_single_of_ne y r j c (Ne.symm hrj)]

/-- Each reflected main effect has zero intercept. [The asserted mathematical result follows](goal). -/
-- @node: Fhat_g1_lift_zero
lemma Fhat_g1_lift_zero {d : ℕ} (m : CenteredL2Fn d) (j : Fin d) :
    Fhat (fun x : Cube d => g1 m.val j (x j)) 0 = 0 := by
  apply Fhat_zero_of_centered
    (⟨(fun x : Cube d => g1 m.val j (x j)),
      (g1_measurable m.property.1 j).comp (measurable_pi_apply j),
      g1_lift_memLp m.property.1 m.property.2.1 j,
      integral_g1_lift_centered m j⟩ : CenteredL2Fn d)

/-- Reflected pair effects have no frequency outside their two coordinates. Under [the stated conditions](hyp:hjl,hrj,hrl,hr), [the asserted mathematical result follows](goal). -/
-- @node: Fhat_g2_lift_zero_off_coordinates
lemma Fhat_g2_lift_zero_off_coordinates {d : ℕ} (m : CenteredL2Fn d)
    (j l r : Fin d) (hjl : j ≠ l) (hrj : r ≠ j) (hrl : r ≠ l)
    (k : Fin d → ℤ) (hr : k r ≠ 0) :
    Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k = 0 := by
  apply fourierCoeff_zero_of_coordinate_invariant k r hr
    ((reflExt_memLp_of_cube (g2_lift_memLp m.property.1 m.property.2.1 j l hjl)).integrable
      (by norm_num))
  intro y c
  simp only [reflExt]
  rw [fold_add_single_of_ne y r j c (Ne.symm hrj),
    fold_add_single_of_ne y r l c (Ne.symm hrl)]

/-- [ The order-two decomposition is additive at each Fourier coefficient; all of its
canonical summands have derived L² regularity.](goal) Under [the stated conditions](hyp:hm). -/
-- @node: Fhat_orderTwo_sum
lemma Fhat_orderTwo_sum {d : ℕ} (m : CenteredL2Fn d) (hm : OrderTwo m)
    (k : Fin d → ℤ) :
    Fhat m.val k =
      (∑ j, Fhat (fun x : Cube d => g1 m.val j (x j)) k) +
      ∑ j, ∑ l, if j < l then Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k else 0 := by
  classical
  let A : Fin d → Torus d → ℂ := fun j y => ek (-k) y * (g1 m.val j (fold y j) : ℂ)
  let B : Fin d → Fin d → Torus d → ℂ := fun j l y =>
    if j < l then ek (-k) y * (g2 m.val j l (fold y j) (fold y l) : ℂ) else 0
  have hA (j : Fin d) : Integrable (A j) (torusMeasure d) :=
    ek_mul_integrable (-k) ((reflExt_memLp_of_cube
      (g1_lift_memLp m.property.1 m.property.2.1 j)).integrable (by norm_num))
  have hB (j l : Fin d) : Integrable (B j l) (torusMeasure d) := by
    by_cases hjl : j < l
    · simpa only [B, if_pos hjl, reflExt] using ek_mul_integrable (-k)
        ((reflExt_memLp_of_cube (g2_lift_memLp m.property.1 m.property.2.1 j l
          (ne_of_lt hjl))).integrable (by norm_num))
    · simp only [B, if_neg hjl]
      exact integrable_const 0
  have he : (fun y => ek (-k) y * reflExt m.val y) =ᵐ[torusMeasure d]
      fun y => (∑ j, A j y) + ∑ j, ∑ l, B j l y := by
    filter_upwards [(fold_measurePreserving d).quasiMeasurePreserving.ae hm] with y hy
    simp only [reflExt, hy, A, B, Complex.ofReal_add, Complex.ofReal_sum,
      mul_add, Finset.mul_sum, apply_ite, Complex.ofReal_zero, mul_zero]
  unfold Fhat
  rw [integral_congr_ae he, integral_add (integrable_finsetSum _ (fun j _ => hA j))
    (integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hB j l))),
    integral_finsetSum _ (fun j _ => hA j),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hB j l))]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ => hB j l)]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hjl : j < l <;> simp [B, hjl, reflExt]

/-- [ Additivity and the individual coordinate supports give the ambient order-two
support statement directly from the canonical components.](goal) Under [the stated conditions](hyp:hm,hk). -/
-- @node: Fhat_zero_of_orderTwo_from_components
lemma Fhat_zero_of_orderTwo_from_components {d : ℕ} (m : CenteredL2Fn d)
    (hm : OrderTwo m) (k : Fin d → ℤ) (hk : 2 < (frequencySupport k).card) :
    Fhat m.val k = 0 := by
  classical
  obtain ⟨r, hr, t, ht, u, hu, hrt, hru, htu⟩ := Finset.two_lt_card.mp hk
  have hrk : k r ≠ 0 := by simpa [frequencySupport] using hr
  have htk : k t ≠ 0 := by simpa [frequencySupport] using ht
  have huk : k u ≠ 0 := by simpa [frequencySupport] using hu
  have hA (j : Fin d) : Fhat (fun x : Cube d => g1 m.val j (x j)) k = 0 := by
    by_cases hrj : r = j
    · exact Fhat_g1_lift_zero_off_coordinate m j t (by simpa [hrj] using Ne.symm hrt) k htk
    · exact Fhat_g1_lift_zero_off_coordinate m j r hrj k hrk
  have hB (j l : Fin d) :
      (if j < l then Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k else 0) = 0 := by
    by_cases hjl : j < l
    · rw [if_pos hjl]
      have hchoice : (r ≠ j ∧ r ≠ l) ∨ (t ≠ j ∧ t ≠ l) ∨ (u ≠ j ∧ u ≠ l) := by
        by_cases hrj : r = j <;> by_cases hrl : r = l <;>
          by_cases htj : t = j <;> by_cases htl : t = l <;> aesop
      rcases hchoice with h | h | h
      · exact Fhat_g2_lift_zero_off_coordinates m j l r (ne_of_lt hjl) h.1 h.2 k hrk
      · exact Fhat_g2_lift_zero_off_coordinates m j l t (ne_of_lt hjl) h.1 h.2 k htk
      · exact Fhat_g2_lift_zero_off_coordinates m j l u (ne_of_lt hjl) h.1 h.2 k huk
    · exact if_neg hjl
  rw [Fhat_orderTwo_sum m hm k]
  simp_rw [hA, hB]
  simp

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
