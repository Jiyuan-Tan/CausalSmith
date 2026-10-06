module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionANOVA
/-! # Canonical pair centering and exact Fourier component separation

Fubini and independent coordinate resampling center canonical pair effects in each
coordinate. Folding preserves these identities, so main and pair effects have
disjoint exact Fourier supports. The order-two Fourier sum therefore identifies
each coefficient with its unique canonical component.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Averaging the second coordinate of a raw pair marginal recovers the main marginal, with
integrable slices almost everywhere.](goal) Under [the stated conditions](hyp:hm,hjl). -/
-- @node: pair_marginal_tower_right
lemma pair_marginal_tower_right {d : ℕ} {m : Cube d → ℝ}
    (hm : Integrable m (cubeMeasure d)) (j l : Fin d) (hjl : j ≠ l) :
    ∀ᵐ x ∂cubeMeasure d,
      Integrable (fun y : Cube d => ∫ z : Cube d,
        m (Function.update (Function.update z j (x j)) l (y l)) ∂cubeMeasure d)
        (cubeMeasure d) ∧
      (∫ y : Cube d, (∫ z : Cube d,
        m (Function.update (Function.update z j (x j)) l (y l)) ∂cubeMeasure d)
        ∂cubeMeasure d) = g1 m j (x j) := by
  have hprod := (cube_resample_measurePreserving
    ({j} : Finset (Fin d))).integrable_comp_of_integrable hm
  have he : (fun z : Cube d × Cube d =>
      m (fun i => if i ∈ ({j} : Finset (Fin d)) then z.1 i else z.2 i)) =
      (fun z => m (Function.update z.2 j (z.1 j))) := by
    funext z
    congr 1
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update, hi]
  simp only [Function.comp_def] at hprod
  rw [he] at hprod
  filter_upwards [hprod.prod_right_ae] with x hx
  have hp := cube_resample_measurePreserving ({l} : Finset (Fin d))
  have hi := hp.integrable_comp_of_integrable hx
  have ht := integral_map hp.measurable.aemeasurable (by
    rw [hp.map_eq]
    exact hx.aestronglyMeasurable)
  rw [hp.map_eq] at ht
  have he' : (fun z : Cube d × Cube d =>
      m (Function.update (fun i => if i ∈ ({l} : Finset (Fin d)) then z.1 i else z.2 i) j (x j))) =
      (fun z => m (Function.update (Function.update z.2 j (x j)) l (z.1 l))) := by
    funext z
    congr 1
    funext i
    by_cases hij : i = j
    · subst i; simp [Function.update, hjl]
    · by_cases hil : i = l
      · subst i; simp [Function.update, Ne.symm hjl]
      · simp [Function.update, hij, hil]
  simp only [Function.comp_def] at hi
  rw [he'] at hi ht
  exact ⟨hi.integral_prod_left, (integral_prod _ hi).symm.trans ht.symm⟩

/-- [ Swapping the two distinct coordinates and their arguments preserves a canonical pair effect.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: g2_swap_coordinates
lemma g2_swap_coordinates {d : ℕ} (m : Cube d → ℝ) (j l : Fin d) (hjl : j ≠ l)
    (u v : ℝ) : g2 m j l u v = g2 m l j v u := by
  unfold g2
  have he : (fun y : Cube d => m (Function.update (Function.update y j u) l v)) =
      (fun y => m (Function.update (Function.update y l v) j u)) := by
    funext y
    congr 1
    exact Function.update_comm hjl _ _ _
  rw [he]
  ring

/-- [ Each canonical pair effect is integrable and centered in its second coordinate for almost
every fixed first coordinate.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: g2_integral_right_centered
lemma g2_integral_right_centered {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) :
    ∀ᵐ x ∂cubeMeasure d,
      Integrable (fun y : Cube d => g2 m.val j l (x j) (y l)) (cubeMeasure d) ∧
      (∫ y : Cube d, g2 m.val j l (x j) (y l) ∂cubeMeasure d) = 0 := by
  have hi := m.property.2.1.integrable (by norm_num)
  filter_upwards [pair_marginal_tower_right hi j l hjl] with x hx
  have hj : Integrable (fun _ : Cube d => g1 m.val j (x j)) (cubeMeasure d) := by
    fun_prop
  have hl := g1_lift_integrable hi l
  have hr := hx.1
  refine ⟨(hx.1.sub hj).sub hl, ?_⟩
  change (∫ y : Cube d, ((∫ z : Cube d,
    m.val (Function.update (Function.update z j (x j)) l (y l)) ∂cubeMeasure d) -
    g1 m.val j (x j) - g1 m.val l (y l)) ∂cubeMeasure d) = 0
  integral_linearity
  rw [hx.2, integral_g1_lift_centered m l]
  simp

/-- [ Each canonical pair effect is integrable and centered in its first coordinate for almost
every fixed second coordinate.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: g2_integral_left_centered
lemma g2_integral_left_centered {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) :
    ∀ᵐ x ∂cubeMeasure d,
      Integrable (fun y : Cube d => g2 m.val j l (y j) (x l)) (cubeMeasure d) ∧
      (∫ y : Cube d, g2 m.val j l (y j) (x l) ∂cubeMeasure d) = 0 := by
  simpa only [g2_swap_coordinates m.val j l hjl] using
    g2_integral_right_centered m l j (Ne.symm hjl)

/-- [ The lifted canonical pair effect has zero cube mean.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: integral_g2_lift_centered
lemma integral_g2_lift_centered {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) :
    (∫ x : Cube d, g2 m.val j l (x j) (x l) ∂cubeMeasure d) = 0 := by
  have hi := m.property.2.1.integrable (by norm_num)
  have hp := cube_resample_measurePreserving ({j,l} : Finset (Fin d))
  have hraw := hp.integrable_comp_of_integrable hi
  have ht := integral_map hp.measurable.aemeasurable (by
    rw [hp.map_eq]
    exact hi.aestronglyMeasurable)
  rw [hp.map_eq] at ht
  have he : (fun z : Cube d × Cube d =>
      m.val (fun i => if i ∈ ({j,l} : Finset (Fin d)) then z.1 i else z.2 i)) =
      (fun z => m.val (Function.update (Function.update z.2 j (z.1 j)) l (z.1 l))) := by
    funext z
    apply congrArg m.val
    funext i
    by_cases hij : i = j
    · subst i; simp [hjl]
    · by_cases hil : i = l
      · subst i; simp
      · simp [Function.update, hij, hil]
  simp only [Function.comp_def] at hraw
  rw [he] at hraw ht
  have hmean := (integral_prod _ hraw).symm.trans ht.symm
  change (∫ x : Cube d, ((∫ y : Cube d,
    m.val (Function.update (Function.update y j (x j)) l (x l)) ∂cubeMeasure d) -
    g1 m.val j (x j) - g1 m.val l (x l)) ∂cubeMeasure d) = 0
  have hr := hraw.integral_prod_left
  have hj := g1_lift_integrable hi j
  have hl := g1_lift_integrable hi l
  integral_linearity
  rw [hmean, m.property.2.2, integral_g1_lift_centered m j,
    integral_g1_lift_centered m l]
  ring

/-- [ A Borel outcome has a jointly Borel canonical pair effect, including exceptional slices. This uses [the hm hypothesis](hyp:hm), [the stated conclusion](goal). -/
-- @node: g2_joint_measurable
@[fun_prop] lemma g2_joint_measurable {d : ℕ} {m : Cube d → ℝ} (hm : Measurable m)
    (j l : Fin d) : Measurable (fun z : ℝ × ℝ => g2 m j l z.1 z.2) := by
  have h : Measurable (fun z : (ℝ × ℝ) × Cube d =>
    m (Function.update (Function.update z.2 j z.1.1) l z.1.2)) := by
    fun_prop
  exact (h.stronglyMeasurable.integral_prod_right'.measurable.sub
    ((g1_measurable hm j).comp measurable_fst)).sub
    ((g1_measurable hm l).comp measurable_snd)

/-- Each reflected canonical pair effect has zero intercept.](goal) Under [the stated conditions](hyp:hjl). This uses [the stated conclusion](goal). -/
-- @node: Fhat_g2_lift_zero
lemma Fhat_g2_lift_zero {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) :
    Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) 0 = 0 := by
  have hm : Measurable (fun x : Cube d => g2 m.val j l (x j) (x l)) := by
    have hmeas := m.property.1
    fun_prop
  apply Fhat_zero_of_centered
    (⟨_, hm, g2_lift_memLp m.property.1 m.property.2.1 j l hjl,
      integral_g2_lift_centered m j l hjl⟩ : CenteredL2Fn d)

/-- Replacing one torus coordinate by the corresponding coordinate of an independent Haar draw
preserves Haar probability. [The asserted mathematical result follows](goal). -/
-- @node: torus_resample_coordinate_measurePreserving
lemma torus_resample_coordinate_measurePreserving {d : ℕ} (r : Fin d) :
    MeasurePreserving (fun z : Torus d × Torus d =>
      fun i => if i = r then z.2 i else z.1 i)
      ((torusMeasure d).prod (torusMeasure d)) (torusMeasure d) := by
  classical
  have h := (measurePreserving_arrowProdEquivProdArrow (AddCircle (1 : ℝ))
    (AddCircle (1 : ℝ)) (Fin d)
    (fun _ => AddCircle.haarAddCircle) (fun _ => AddCircle.haarAddCircle)).symm
  have hp : MeasurePreserving (fun z : Fin d → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      fun i => if i = r then (z i).2 else (z i).1)
      (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle.prod AddCircle.haarAddCircle))
      (torusMeasure d) := by
    unfold torusMeasure
    apply measurePreserving_pi
      (fun _ : Fin d => AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (fun _ : Fin d => AddCircle.haarAddCircle)
      (f := fun i z => if i = r then z.2 else z.1)
    intro i
    by_cases hi : i = r
    · simpa only [if_pos hi] using
        (measurePreserving_snd (μ := AddCircle.haarAddCircle) (ν := AddCircle.haarAddCircle))
    · simpa only [if_neg hi] using
        (measurePreserving_fst (μ := AddCircle.haarAddCircle) (ν := AddCircle.haarAddCircle))
  exact hp.comp h

/-- A character with zero frequency in a coordinate is unchanged by resampling that coordinate. Under [the stated conditions](hyp:hr), [the asserted mathematical result follows](goal). -/
-- @node: ek_resample_coordinate
lemma ek_resample_coordinate {d : ℕ} (k : Fin d → ℤ) (r : Fin d) (hr : k r = 0)
    (y z : Torus d) : ek k (fun i => if i = r then z i else y i) = ek k y := by
  classical
  unfold ek UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = r
  · subst i; simp [hr]
  · simp [hi]

/-- [ A reflected pair coefficient vanishes when its second coordinate frequency is zero, by
Fubini and canonical centering.](goal) Under [the stated conditions](hyp:hjl,hkl). -/
-- @node: Fhat_g2_lift_zero_right
lemma Fhat_g2_lift_zero_right {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) (k : Fin d → ℤ) (hkl : k l = 0) :
    Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k = 0 := by
  classical
  let f : Torus d → ℂ := fun y => ek (-k) y * (g2 m.val j l (fold y j) (fold y l) : ℂ)
  have hf : Integrable f (torusMeasure d) := ek_mul_integrable (-k)
    ((reflExt_memLp_of_cube (g2_lift_memLp m.property.1 m.property.2.1 j l hjl)).integrable
      (by norm_num))
  have hp := torus_resample_coordinate_measurePreserving l
  have hi := hp.integrable_comp_of_integrable hf
  have ht := integral_map hp.measurable.aemeasurable (by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable)
  rw [hp.map_eq] at ht
  have he : (fun z : Torus d × Torus d =>
      f (fun i => if i = l then z.2 i else z.1 i)) =
      (fun z => ek (-k) z.1 * (g2 m.val j l (fold z.1 j) (fold z.2 l) : ℂ)) := by
    funext z
    simp only [f, ek_resample_coordinate (-k) l (by simpa using hkl),
      fold, if_neg hjl, if_true]
  simp only [Function.comp_def] at hi
  rw [he] at hi ht
  have hcenter := (fold_measurePreserving d).quasiMeasurePreserving.ae
    (g2_integral_right_centered m j l hjl)
  have hz : (fun y : Torus d => ∫ z : Torus d,
      ek (-k) y * (g2 m.val j l (fold y j) (fold z l) : ℂ) ∂torusMeasure d)
      =ᵐ[torusMeasure d] 0 := by
    filter_upwards [hcenter] with y hy
    have hmap := integral_map
      (f := fun x : Cube d => (g2 m.val j l (fold y j) (x l) : ℂ))
      (fold_measurePreserving d).measurable.aemeasurable (by
      rw [(fold_measurePreserving d).map_eq]
      exact hy.1.ofReal.aestronglyMeasurable)
    rw [(fold_measurePreserving d).map_eq] at hmap
    rw [integral_const_mul, ← hmap, integral_complex_ofReal, hy.2]
    simp
  change (∫ y, f y ∂torusMeasure d) = 0
  rw [ht, integral_prod _ hi, integral_congr_ae hz]
  simp

/-- [ A reflected pair coefficient vanishes when its first coordinate frequency is zero.](goal) Under [the stated conditions](hyp:hjl,hkj). -/
-- @node: Fhat_g2_lift_zero_left
lemma Fhat_g2_lift_zero_left {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) (k : Fin d → ℤ) (hkj : k j = 0) :
    Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k = 0 := by
  simpa only [g2_swap_coordinates m.val j l hjl] using
    Fhat_g2_lift_zero_right m l j (Ne.symm hjl) k hkj

/-- [ Every nonzero reflected canonical pair coefficient has support exactly equal to its two
coordinates.](goal) Under [the stated conditions](hyp:hjl,hk). -/
-- @node: Fhat_g2_lift_support_exact
lemma Fhat_g2_lift_support_exact {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) (k : Fin d → ℤ)
    (hk : Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k ≠ 0) :
    frequencySupport k = {j, l} := by
  classical
  have hj : k j ≠ 0 := fun h => hk (Fhat_g2_lift_zero_left m j l hjl k h)
  have hl : k l ≠ 0 := fun h => hk (Fhat_g2_lift_zero_right m j l hjl k h)
  ext r
  simp only [frequencySupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hr
    by_contra h
    have hrj : r ≠ j := fun e => h (Or.inl e)
    have hrl : r ≠ l := fun e => h (Or.inr e)
    exact hk (Fhat_g2_lift_zero_off_coordinates m j l r hjl hrj hrl k hr)
  · rintro (rfl | rfl)
    · exact hj
    · exact hl

/-- [ Every nonzero reflected canonical main coefficient has support exactly equal to its
coordinate.](goal) Under [the stated conditions](hyp:hk). -/
-- @node: Fhat_g1_lift_support_exact
lemma Fhat_g1_lift_support_exact {d : ℕ} (m : CenteredL2Fn d)
    (j : Fin d) (k : Fin d → ℤ)
    (hk : Fhat (fun x : Cube d => g1 m.val j (x j)) k ≠ 0) :
    frequencySupport k = {j} := by
  classical
  have hoff (r : Fin d) (hr : r ≠ j) : k r = 0 := by
    by_contra h
    exact hk (Fhat_g1_lift_zero_off_coordinate m j r hr k h)
  have hj : k j ≠ 0 := by
    intro h
    have hz : k = 0 := by
      funext r
      by_cases hr : r = j
      · simpa [hr] using h
      · exact hoff r hr
    rw [hz] at hk
    exact hk (Fhat_g1_lift_zero m j)
  ext r
  simp only [frequencySupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hr
    by_contra h
    exact hr (hoff r h)
  · rintro rfl
    exact hj

/-- [ At a singleton-support frequency the full order-two outcome coefficient equals its unique
main component coefficient.](goal) Under [the stated conditions](hyp:hm,hks). -/
-- @node: Fhat_orderTwo_single_component
lemma Fhat_orderTwo_single_component {d : ℕ} (m : CenteredL2Fn d) (hm : OrderTwo m)
    (j : Fin d) (k : Fin d → ℤ) (hks : frequencySupport k = {j}) :
    Fhat m.val k = Fhat (fun x : Cube d => g1 m.val j (x j)) k := by
  classical
  have hA : (∑ r, Fhat (fun x : Cube d => g1 m.val r (x r)) k) =
      Fhat (fun x : Cube d => g1 m.val j (x j)) k := by
    apply Finset.sum_eq_single j
    · intro r _ hrj
      by_contra hr
      have he := (Fhat_g1_lift_support_exact m r k hr).symm.trans hks
      exact hrj (Finset.singleton_inj.mp he)
    · simp
  have hB (r t : Fin d) :
      (if r < t then Fhat (fun x : Cube d => g2 m.val r t (x r) (x t)) k else 0) = 0 := by
    by_cases hrt : r < t
    · rw [if_pos hrt]
      by_contra h
      have he := (Fhat_g2_lift_support_exact m r t (ne_of_lt hrt) k h).symm.trans hks
      have hc := congrArg Finset.card he
      simp [ne_of_lt hrt] at hc
    · exact if_neg hrt
  rw [Fhat_orderTwo_sum m hm k, hA]
  simp_rw [hB]
  simp

/-- [ At an ordered pair-support frequency the full order-two outcome coefficient equals its
unique pair component coefficient.](goal) Under [the stated conditions](hyp:hm,hjl,hks). -/
-- @node: Fhat_orderTwo_pair_component
lemma Fhat_orderTwo_pair_component {d : ℕ} (m : CenteredL2Fn d) (hm : OrderTwo m)
    (j l : Fin d) (hjl : j < l) (k : Fin d → ℤ)
    (hks : frequencySupport k = {j, l}) :
    Fhat m.val k = Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k := by
  classical
  have hA (r : Fin d) : Fhat (fun x : Cube d => g1 m.val r (x r)) k = 0 := by
    by_contra h
    have he := (Fhat_g1_lift_support_exact m r k h).symm.trans hks
    have hc := congrArg Finset.card he
    simp [ne_of_lt hjl] at hc
  have hB (r t : Fin d) :
      (if r < t then Fhat (fun x : Cube d => g2 m.val r t (x r) (x t)) k else 0) =
      if r = j ∧ t = l then Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k else 0 := by
    by_cases heq : r = j ∧ t = l
    · obtain ⟨rfl, rfl⟩ := heq
      simp [hjl]
    · rw [if_neg heq]
      by_cases hrt : r < t
      · rw [if_pos hrt]
        by_contra h
        have he := (Fhat_g2_lift_support_exact m r t (ne_of_lt hrt) k h).symm.trans hks
        have hr : r = j ∨ r = l := by
          have hmem : r ∈ ({j,l} : Finset (Fin d)) := by rw [← he]; simp
          simpa using hmem
        have ht : t = j ∨ t = l := by
          have hmem : t ∈ ({j,l} : Finset (Fin d)) := by rw [← he]; simp
          simpa using hmem
        rcases hr with rfl | rfl <;> rcases ht with rfl | rfl <;> omega
      · exact if_neg hrt
  rw [Fhat_orderTwo_sum m hm k]
  simp_rw [hA, hB]
  simp [ite_and]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
