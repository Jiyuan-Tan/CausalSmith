module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionANOVACentering
public import Mathlib.Probability.Independence.Basic

/-! # Local-to-ambient canonical Fourier coefficients

Selecting distinct coordinates preserves cube and Haar probability. Characters
supported on those coordinates transport exactly, with normalized coefficients
and no factor depending on the ambient dimension.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ A selection of distinct coordinates preserves finite product probability.](goal) Under [the stated conditions](hyp:he). -/
-- @node: coordinateSelection_measurePreserving
lemma coordinateSelection_measurePreserving {p d : ℕ} {A : Type*}
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (e : Fin p → Fin d) (he : Function.Injective e) :
    MeasurePreserving (fun x : Fin d → A => fun r => x (e r))
      (Measure.pi (fun _ : Fin d => μ)) (Measure.pi (fun _ : Fin p => μ)) := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin d => μ)
    (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).precomp he
  refine ⟨by fun_prop, ?_⟩
  rw [hind.map_fun_eq_pi_map (fun r => (measurable_pi_apply (e r)).aemeasurable)]
  congr 1
  funext r
  exact (measurePreserving_eval (fun _ : Fin d => μ) (e r)).map_eq

/-- [ Selecting distinct coordinates sends ambient Haar probability to local Haar probability.](goal) Under [the stated conditions](hyp:he). -/
-- @node: torus_coordinateSelection_measurePreserving
lemma torus_coordinateSelection_measurePreserving {p d : ℕ}
    (e : Fin p → Fin d) (he : Function.Injective e) :
    MeasurePreserving (fun y : Torus d => fun r => y (e r))
      (torusMeasure d) (torusMeasure p) :=
  coordinateSelection_measurePreserving AddCircle.haarAddCircle e he

/-- [ Selecting distinct coordinates sends ambient cube probability to local cube probability.](goal) Under [the stated conditions](hyp:he). -/
-- @node: cube_coordinateSelection_measurePreserving
lemma cube_coordinateSelection_measurePreserving {p d : ℕ}
    (e : Fin p → Fin d) (he : Function.Injective e) :
    MeasurePreserving (fun x : Cube d => fun r => x (e r))
      (cubeMeasure d) (cubeMeasure p) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  exact coordinateSelection_measurePreserving _ e he

/-- [ Folding commutes pointwise with selection of coordinates. This uses [the stated conclusion](goal). -/
-- @node: fold_coordinateSelection
lemma fold_coordinateSelection {p d : ℕ} (e : Fin p → Fin d) (y : Torus d) :
    fold (fun r => y (e r)) = fun r => fold y (e r) := rfl

/-- A character supported on selected coordinates is exactly the corresponding local character.](goal) Under [the stated conditions](hyp:he,hk). This uses [the stated conclusion](goal). -/
-- @node: ek_coordinateSelection
lemma ek_coordinateSelection {p d : ℕ} (e : Fin p → Fin d)
    (he : Function.Injective e) (k : Fin d → ℤ)
    (hk : ∀ j, j ∉ Set.range e → k j = 0) (y : Torus d) :
    ek k y = ek (fun r => k (e r)) (fun r => y (e r)) := by
  classical
  unfold ek UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk]
  calc
    (∏ j : Fin d, fourier (k j) (y j)) =
        ∏ j ∈ Finset.univ.image e, fourier (k j) (y j) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro j _ hj
      have hz : k j = 0 := hk j (by simpa using hj)
      simp [hz]
    _ = ∏ r : Fin p, fourier (k (e r)) (y (e r)) := by
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact he hab

/-- [ Normalized reflected Fourier coefficients transport from local to ambient coordinates.](goal) Under [the stated conditions](hyp:he,hg,hk). -/
-- @node: Fhat_coordinateSelection
lemma Fhat_coordinateSelection {p d : ℕ} (e : Fin p → Fin d)
    (he : Function.Injective e) (g : Cube p → ℝ) (hg : Measurable g)
    (k : Fin d → ℤ) (hk : ∀ j, j ∉ Set.range e → k j = 0) :
    Fhat (fun x : Cube d => g (fun r => x (e r))) k =
      Fhat g (fun r => k (e r)) := by
  have hp := torus_coordinateSelection_measurePreserving e he
  have hf : AEStronglyMeasurable
      (fun y : Torus p => ek (-(fun r => k (e r))) y * reflExt g y)
      (torusMeasure p) := by
    apply Measurable.aestronglyMeasurable
    have hm : Measurable (reflExt g) :=
      Complex.measurable_ofReal.comp (hg.comp (fold_measurable p))
    exact (UnitAddTorus.mFourier _).continuous.measurable.mul hm
  have ht := integral_map hp.measurable.aemeasurable (by
    rw [hp.map_eq]
    exact hf)
  rw [hp.map_eq] at ht
  unfold Fhat
  rw [ht]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ek_coordinateSelection e he (-k) (by
    intro j hj
    simp [hk j hj]) y]
  rfl

/-- [ Selecting the supporting coordinates preserves the squared Euclidean frequency length.](goal) Under [the stated conditions](hyp:he,hk). -/
-- @node: frequencySq_coordinateSelection
lemma frequencySq_coordinateSelection {p d : ℕ} (e : Fin p → Fin d)
    (he : Function.Injective e) (k : Fin d → ℤ)
    (hk : ∀ j, j ∉ Set.range e → k j = 0) :
    frequencySq k = frequencySq (fun r => k (e r)) := by
  classical
  unfold frequencySq
  calc
    (∑ j : Fin d, (k j : ℝ) ^ 2) =
        ∑ j ∈ Finset.univ.image e, (k j : ℝ) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [hk j (by simpa using hj)]
    _ = ∑ r : Fin p, (k (e r) : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact he hab

/-- [ When all selected coordinates are active, ambient support has exactly local size.](goal) Under [the stated conditions](hyp:he,hk,hne). -/
-- @node: frequencySupport_card_coordinateSelection
lemma frequencySupport_card_coordinateSelection {p d : ℕ} (e : Fin p → Fin d)
    (he : Function.Injective e) (k : Fin d → ℤ)
    (hk : ∀ j, j ∉ Set.range e → k j = 0)
    (hne : ∀ r, k (e r) ≠ 0) :
    (frequencySupport k).card = p := by
  classical
  have hs : frequencySupport k = Finset.univ.image e := by
    ext j
    simp only [frequencySupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hj
      have hr : j ∈ Set.range e := by
        by_contra h
        exact hj (hk j h)
      obtain ⟨r, rfl⟩ := hr
      exact ⟨r, rfl⟩
    · rintro ⟨r, _, rfl⟩
      exact hne r
  rw [hs, Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]

/-- [ The ambient complexity equals local squared length divided by local dimension.](goal) Under [the stated conditions](hyp:he,hk,hne). -/
-- @node: frequencyComplexity_coordinateSelection
lemma frequencyComplexity_coordinateSelection {p d : ℕ} (e : Fin p → Fin d)
    (he : Function.Injective e) (k : Fin d → ℤ)
    (hk : ∀ j, j ∉ Set.range e → k j = 0)
    (hne : ∀ r, k (e r) ≠ 0) :
    frequencyComplexity k = frequencySq (fun r => k (e r)) / (p : ℝ) := by
  rw [frequencyComplexity, frequencySq_coordinateSelection e he k hk,
    frequencySupport_card_coordinateSelection e he k hk hne]

/-- The one-coordinate canonical representative is square integrable under local cube measure. [The asserted mathematical result follows](goal). -/
-- @node: g1_local_memLp
lemma g1_local_memLp {d : ℕ} (m : CenteredL2Fn d) (j : Fin d) :
    MemLp (fun u : Cube 1 => g1 m.val j (u 0)) 2 (cubeMeasure 1) := by
  have hg : Measurable (fun u : Cube 1 => g1 m.val j (u 0)) := by
    have hm := m.property.1
    fun_prop
  have hp := cube_coordinateSelection_measurePreserving (fun _ : Fin 1 => j)
    (by intro a b _; exact Subsingleton.elim a b)
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hp]
  exact (g1_lift_memLp m.property.1 m.property.2.1 j).2

/-- The two-coordinate canonical representative is square integrable under local cube measure. Under [the stated conditions](hyp:hjl), [the asserted mathematical result follows](goal). -/
-- @node: g2_local_memLp
lemma g2_local_memLp {d : ℕ} (m : CenteredL2Fn d) (j l : Fin d) (hjl : j ≠ l) :
    MemLp (fun u : Cube 2 => g2 m.val j l (u 0) (u 1)) 2 (cubeMeasure 2) := by
  have hg : Measurable (fun u : Cube 2 => g2 m.val j l (u 0) (u 1)) := by
    have hm := m.property.1
    fun_prop
  have he : Function.Injective (fun r : Fin 2 => if r = 0 then j else l) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hp := cube_coordinateSelection_measurePreserving _ he
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hp]
  simpa only [Function.comp_def, Fin.isValue, one_ne_zero, if_true, if_false]
    using (g2_lift_memLp m.property.1 m.property.2.1 j l hjl).2

/-- [ A canonical main coefficient on its supporting coordinate equals its local coefficient.](goal) Under [the stated conditions](hyp:hks). -/
-- @node: Fhat_g1_local_eq
lemma Fhat_g1_local_eq {d : ℕ} (m : CenteredL2Fn d) (j : Fin d)
    (k : Fin d → ℤ) (hks : frequencySupport k = {j}) :
    Fhat (fun x : Cube d => g1 m.val j (x j)) k =
      Fhat (fun u : Cube 1 => g1 m.val j (u 0)) (fun _ => k j) := by
  apply Fhat_coordinateSelection (fun _ : Fin 1 => j)
    (by intro a b _; exact Subsingleton.elim a b)
    (fun u : Cube 1 => g1 m.val j (u 0)) (by
      have hm := m.property.1
      fun_prop)
  intro r hr
  have hrj : r ≠ j := by simpa using hr
  have hnot : r ∉ frequencySupport k := by simp [hks, hrj]
  simpa [frequencySupport] using hnot

/-- [ A canonical pair coefficient on its two supporting coordinates equals its local coefficient.](goal) Under [the stated conditions](hyp:hjl,hks). -/
-- @node: Fhat_g2_local_eq
lemma Fhat_g2_local_eq {d : ℕ} (m : CenteredL2Fn d) (j l : Fin d) (hjl : j ≠ l)
    (k : Fin d → ℤ) (hks : frequencySupport k = {j, l}) :
    Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k =
      Fhat (fun u : Cube 2 => g2 m.val j l (u 0) (u 1))
        (fun r => if r = 0 then k j else k l) := by
  have he : Function.Injective (fun r : Fin 2 => if r = 0 then j else l) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h := Fhat_coordinateSelection (fun r : Fin 2 => if r = 0 then j else l) he
    (fun u : Cube 2 => g2 m.val j l (u 0) (u 1)) (by
      have hm := m.property.1
      fun_prop) k (by
        intro r hr
        have hrj : r ≠ j := by
          intro h
          exact hr ⟨0, by simp [h]⟩
        have hrl : r ≠ l := by
          intro h
          exact hr ⟨1, by simp [h]⟩
        have hnot : r ∉ frequencySupport k := by simp [hks, hrj, hrl]
        simpa [frequencySupport] using hnot)
  simpa only [Fin.isValue, one_ne_zero, if_true, if_false, apply_ite] using h

/-- [ Disjoint-support localization transports a lifted component's entire weighted budget
into its local Fourier budget, with constant one.](goal) Under [the stated conditions](hyp:he,hg,hsupport). -/
-- @node: lifted_component_budget_le_local
lemma lifted_component_budget_le_local {p d : ℕ} (e : Fin p → Fin d)
    (he : Function.Injective e) (g : Cube p → ℝ) (hg : Measurable g) (s : ℝ)
    (hsupport : ∀ k, Fhat (fun x : Cube d => g (fun r => x (e r))) k ≠ 0 →
      frequencySupport k = Finset.univ.image e) :
    (∑' k : Fin d → ℤ, ENNReal.ofReal
      ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
        ‖Fhat (fun x : Cube d => g (fun r => x (e r))) k‖ ^ 2)) ≤
      componentFourierBudget p s g := by
  classical
  let S : Set (Fin d → ℤ) := {k | frequencySupport k = Finset.univ.image e}
  let f : (Fin d → ℤ) → ℝ≥0∞ := fun k => ENNReal.ofReal
    ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
      ‖Fhat (fun x : Cube d => g (fun r => x (e r))) k‖ ^ 2)
  have hf : Function.support f ⊆ S := by
    intro k hk
    apply hsupport
    intro hz
    exact hk (by simp [f, hz])
  have hoff (k : S) (j : Fin d) (hj : j ∉ Set.range e) : k.val j = 0 := by
    have hnot : j ∉ frequencySupport k.val := by
      rw [k.property]
      simpa using hj
    simpa [frequencySupport] using hnot
  have hinj : Function.Injective (fun k : S => fun r => k.val (e r)) := by
    intro k l hkl
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨r, rfl⟩ := hj
      exact congrFun hkl r
    · rw [hoff k j hj, hoff l j hj]
  have hterm (k : S) : f k.val = ENNReal.ofReal
      ((1 + Real.pi ^ 2 * frequencySq (fun r => k.val (e r)) / (p : ℝ)) ^ s *
        ‖Fhat g (fun r => k.val (e r))‖ ^ 2) := by
    have hne (r : Fin p) : k.val (e r) ≠ 0 := by
      have hm : e r ∈ frequencySupport k.val := by rw [k.property]; simp
      simpa [frequencySupport] using hm
    dsimp [f]
    rw [Fhat_coordinateSelection e he g hg k.val (hoff k),
      frequencyComplexity_coordinateSelection e he k.val (hoff k) hne,
      mul_div_assoc]
  change (∑' k, f k) ≤ _
  rw [← tsum_subtype_eq_of_support_subset hf]
  simp_rw [hterm]
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj _

/-- The ambient weighted budget of a canonical main effect is bounded by its local budget. [The asserted mathematical result follows](goal). -/
-- @node: g1_ambient_budget_le_local
lemma g1_ambient_budget_le_local {d : ℕ} (m : CenteredL2Fn d) (j : Fin d) (s : ℝ) :
    (∑' k : Fin d → ℤ, ENNReal.ofReal
      ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
        ‖Fhat (fun x : Cube d => g1 m.val j (x j)) k‖ ^ 2)) ≤
      componentFourierBudget 1 s (fun u => g1 m.val j (u 0)) := by
  apply lifted_component_budget_le_local (fun _ : Fin 1 => j)
    (by intro a b _; exact Subsingleton.elim a b)
    (fun u : Cube 1 => g1 m.val j (u 0)) (by
      have hm := m.property.1
      fun_prop) s
  intro k hk
  simpa using Fhat_g1_lift_support_exact m j k hk

/-- The ambient weighted budget of a canonical pair effect is bounded by its local budget. Under [the stated conditions](hyp:hjl), [the asserted mathematical result follows](goal). -/
-- @node: g2_ambient_budget_le_local
lemma g2_ambient_budget_le_local {d : ℕ} (m : CenteredL2Fn d)
    (j l : Fin d) (hjl : j ≠ l) (s : ℝ) :
    (∑' k : Fin d → ℤ, ENNReal.ofReal
      ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
        ‖Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k‖ ^ 2)) ≤
      componentFourierBudget 2 s (fun u => g2 m.val j l (u 0) (u 1)) := by
  have he : Function.Injective (fun r : Fin 2 => if r = 0 then j else l) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h := lifted_component_budget_le_local (fun r : Fin 2 => if r = 0 then j else l)
    he (fun u : Cube 2 => g2 m.val j l (u 0) (u 1)) (by
      have hm := m.property.1
      fun_prop) s (by
        intro k hk
        simp only [Fin.isValue, one_ne_zero, if_true, if_false] at hk
        rw [Fhat_g2_lift_support_exact m j l hjl k hk]
        ext r
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
          Finset.mem_univ, true_and]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, by simp⟩
          · exact ⟨1, by simp⟩
        · rintro ⟨a, rfl⟩
          fin_cases a <;> simp)
  simpa only [Fin.isValue, one_ne_zero, if_true, if_false] using h

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
