import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.MeasureTheory.Constructions.Pi

set_option linter.style.openClassical false

/-!
# Finite categorical count vectors

This file supplies the elementary multinomial law for the histogram of a finite
i.i.d. sample after a measurable finite-valued classification.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- Histogram of a finite word. -/
def categoricalCounts {C : ℕ} {J : Type*} [Fintype J]
    (w : Fin C → J) (j : J) : ℕ :=
  (Finset.univ.filter fun c ↦ w c = j).card

private def histogramWords (C : ℕ) {J : Type*} [Fintype J]
    (x : J → ℕ) : Finset (Fin C → J) :=
  Finset.univ.filter fun w ↦ categoricalCounts w = x

private lemma sum_categoricalCounts {C : ℕ} {J : Type*} [Fintype J]
    (w : Fin C → J) : ∑ j, categoricalCounts w j = C := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin C)))
    (t := (Finset.univ : Finset J)) (f := w)
    (fun c _ ↦ Finset.mem_univ (w c))
  simpa [categoricalCounts] using h.symm

private def wordOfEquiv {J : Type*} [Fintype J] (x : J → ℕ) {C : ℕ}
    (e : (Σ j, Fin (x j)) ≃ Fin C) : Fin C → J :=
  fun c ↦ (e.symm c).1

private lemma wordOfEquiv_histogram {J : Type*} [Fintype J]
    (x : J → ℕ) {C : ℕ} (e : (Σ j, Fin (x j)) ≃ Fin C) (j : J) :
    categoricalCounts (wordOfEquiv x e) j = x j := by
  classical
  rw [categoricalCounts, ← Fintype.card_subtype]
  let A : Set (Σ i, Fin (x i)) := {u | u.1 = j}
  calc
    Fintype.card {c : Fin C // wordOfEquiv x e c = j} =
        Fintype.card A := Fintype.card_congr
      (Equiv.subtypeEquiv e.symm (fun c ↦ Iff.rfl))
    _ = Fintype.card (Fin (x j)) := Fintype.card_congr
      { toFun := fun u ↦ by
          rcases u with ⟨⟨i, k⟩, hi⟩
          change i = j at hi
          subst i
          exact k
        invFun := fun k ↦ ⟨⟨j, k⟩, rfl⟩
        left_inv := by rintro ⟨⟨i, k⟩, hi⟩; cases hi; rfl
        right_inv := fun _ ↦ rfl }
    _ = x j := Fintype.card_fin _

private lemma histogramWords_card (C : ℕ) {J : Type*} [Fintype J]
    (x : J → ℕ) (hx : ∑ j, x j = C) :
    (histogramWords C x).card = Nat.multinomial Finset.univ x := by
  classical
  let e : (Σ j : J, Fin (x j)) ≃ Fin C :=
    Fintype.equivOfCardEq (by simpa using hx)
  let w₀ : Fin C → J := wordOfEquiv x e
  have hw₀ (j : J) : categoricalCounts w₀ j = x j :=
    wordOfEquiv_histogram x e j
  let H : Set (Fin C → J) := {w | categoricalCounts w = x}
  letI : Fintype (Equiv.Perm (Fin C))ᵈᵐᵃ :=
    Fintype.ofEquiv (Equiv.Perm (Fin C)) DomMulAct.mk
  have horbit : MulAction.orbit (Equiv.Perm (Fin C))ᵈᵐᵃ w₀ = H := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      funext j
      rw [← hw₀ j]
      unfold categoricalCounts
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv
        (DomMulAct.mk.symm g : Equiv.Perm (Fin C)) (by
          intro c
          simp [DomMulAct.smul_apply])
    · intro hw
      have hcard (j : J) :
          Fintype.card {c : Fin C // w₀ c = j} =
            Fintype.card {c : Fin C // w c = j} := by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact (hw₀ j).trans (congrFun hw j).symm
      let g : Equiv.Perm (Fin C) := Equiv.ofFiberEquiv fun j ↦
        Fintype.equivOfCardEq (hcard j)
      refine ⟨DomMulAct.mk g.symm, ?_⟩
      funext c
      change w₀ (g.symm c) = w c
      symm
      have hg := Equiv.ofFiberEquiv_map
        (fun j ↦ Fintype.equivOfCardEq (hcard j)) (g.symm c)
      change w (g (g.symm c)) = w₀ (g.symm c) at hg
      simpa using hg
  have hcardH : Fintype.card H = (histogramWords C x).card := by
    rw [Fintype.card_subtype]
    congr 1
  have horbitCard : Fintype.card H * ∏ j, (x j).factorial = C.factorial := by
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (Equiv.Perm (Fin C))ᵈᵐᵃ w₀
    have hstab : Fintype.card
        (MulAction.stabilizer (Equiv.Perm (Fin C))ᵈᵐᵃ w₀) =
        ∏ j, (x j).factorial := by
      rw [show Fintype.card
          (MulAction.stabilizer (Equiv.Perm (Fin C))ᵈᵐᵃ w₀) =
          Fintype.card {g : Equiv.Perm (Fin C) // w₀ ∘ g = w₀} by
        apply Fintype.card_congr
        exact Equiv.subtypeEquiv DomMulAct.mk.symm
          (fun g ↦ DomMulAct.mem_stabilizer_iff),
        DomMulAct.stabilizer_card w₀]
      congr 2 with j
      rw [Fintype.card_subtype]
      exact congrArg Nat.factorial (hw₀ j)
    have hdom : Fintype.card (Equiv.Perm (Fin C))ᵈᵐᵃ = C.factorial := by
      rw [← Fintype.card_congr (DomMulAct.mk :
        Equiv.Perm (Fin C) ≃ (Equiv.Perm (Fin C))ᵈᵐᵃ),
        Fintype.card_perm, Fintype.card_fin]
    have horbitCardEq : Fintype.card
        (MulAction.orbit (Equiv.Perm (Fin C))ᵈᵐᵃ w₀) = Fintype.card H :=
      Fintype.card_congr (Equiv.setCongr horbit)
    rw [horbitCardEq, hstab, hdom] at hos
    exact hos
  have hmulti := Nat.multinomial_spec Finset.univ x
  rw [hx] at hmulti
  rw [← hcardH]
  apply Nat.eq_of_mul_eq_mul_right (Nat.prod_factorial_pos Finset.univ x)
  simpa [mul_comm] using horbitCard.trans hmulti.symm

private def wordEvent {C : ℕ} {J Ω : Type*} [Fintype J]
    (g : Ω → J) (w : Fin C → J) : Set (Fin C → Ω) :=
  Set.univ.pi fun c ↦ g ⁻¹' {w c}

-- @node: lem:iid-finite-categorical-counts-multinomial
/-- The histogram of a measurable finite classification of an i.i.d. finite
sample has the multinomial law. -/
lemma iid_finiteCategorical_counts_multinomial
    {C : ℕ} {J Ω : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] [MeasurableSpace Ω]
    (g : Ω → J) (hg : Measurable g) (mu : Measure Ω) [IsProbabilityMeasure mu]
    (prob : J → ℝ) (hnonneg : ∀ j, 0 ≤ prob j)
    (hprob : ∀ j, mu (g ⁻¹' {j}) = ENNReal.ofReal (prob j))
    (x : J → ℕ) :
    (Measure.pi fun _ : Fin C ↦ mu) {O | categoricalCounts (g ∘ O) = x} =
      if ∑ j, x j = C then
        ENNReal.ofReal ((C.factorial : ℝ) / (∏ j, (x j).factorial : ℕ) *
          ∏ j, (prob j) ^ x j)
      else 0 := by
  classical
  by_cases hx : ∑ j, x j = C
  · rw [if_pos hx]
    have hevent : {O : Fin C → Ω | categoricalCounts (g ∘ O) = x} =
        ⋃ w ∈ histogramWords C x, wordEvent g w := by
      ext O
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hO
        refine ⟨g ∘ O, ?_, ?_⟩
        · simp [histogramWords, hO]
        · simp [wordEvent]
      · rintro ⟨w, hw, hOw⟩
        have hfun : g ∘ O = w := by
          funext c
          exact Set.mem_singleton_iff.mp (hOw c (Set.mem_univ c))
        simpa [histogramWords, hfun] using (Finset.mem_filter.1 hw).2
    have hdisj : Pairwise (Function.onFun Disjoint (wordEvent (C := C) g)) := by
      intro w v hwv
      apply Set.disjoint_left.2
      intro O hOw hOv
      apply hwv
      funext c
      exact (Set.mem_singleton_iff.mp (hOw c (Set.mem_univ c))).symm.trans
        (Set.mem_singleton_iff.mp (hOv c (Set.mem_univ c)))
    have hmeas (w : Fin C → J) : MeasurableSet (wordEvent g w) := by
      exact MeasurableSet.univ_pi fun c ↦
        (measurableSet_singleton (w c)).preimage hg
    rw [hevent, measure_biUnion_finset
      (fun w _ v _ hwv ↦ hdisj hwv) (fun w _ ↦ hmeas w)]
    have hword (w : Fin C → J) (hw : w ∈ histogramWords C x) :
        (Measure.pi fun _ : Fin C ↦ mu) (wordEvent g w) =
          ∏ j, (ENNReal.ofReal (prob j)) ^ x j := by
      rw [wordEvent, Measure.pi_pi]
      simp_rw [hprob]
      rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin C)) w
        (fun c ↦ ENNReal.ofReal (prob (w c)))]
      apply Finset.prod_congr rfl
      intro j _
      calc
        (∏ i with w i = j, ENNReal.ofReal (prob (w i))) =
            ∏ _i with w _i = j, ENNReal.ofReal (prob j) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [(Finset.mem_filter.1 hi).2]
        _ = (ENNReal.ofReal (prob j)) ^ x j := by
          rw [Finset.prod_const]
          congr 1
          exact (congrFun (Finset.mem_filter.1 hw).2 j)
    rw [Finset.sum_congr rfl (fun w hw ↦ hword w hw)]
    rw [Finset.sum_const, nsmul_eq_mul, histogramWords_card C x hx]
    have hmulti := Nat.multinomial_spec Finset.univ x
    rw [hx] at hmulti
    have hden_pos : (0 : ℝ) < ∏ j, (x j).factorial := by positivity
    have hcoeff : (Nat.multinomial Finset.univ x : ℝ) =
        (C.factorial : ℝ) / (∏ j, (x j).factorial : ℕ) := by
      apply (eq_div_iff (by exact_mod_cast hden_pos.ne')).2
      exact_mod_cast (by simpa [mul_comm] using hmulti)
    simp_rw [← ENNReal.ofReal_pow (hnonneg _)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ pow_nonneg (hnonneg j) _)]
    rw [← ENNReal.ofReal_natCast, hcoeff, ← ENNReal.ofReal_mul]
    positivity
  · rw [if_neg hx]
    have hempty : {O : Fin C → Ω | categoricalCounts (g ∘ O) = x} = ∅ := by
      ext O
      rw [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hO ↦ hx <| by
        rw [← hO]
        exact sum_categoricalCounts (g ∘ O)
    rw [hempty, measure_empty]

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
