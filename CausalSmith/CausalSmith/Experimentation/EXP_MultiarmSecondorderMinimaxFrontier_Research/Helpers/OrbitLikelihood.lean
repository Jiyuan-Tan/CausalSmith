import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.PermutationFibers
import Mathlib.Data.Nat.Choose.Multinomial

/-!
The exact rational likelihood of an observed arm-success orbit, obtained by
summing multinomial contingency-table counts over the prescribed fiber.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ}

/-- Joint response-type/arm count induced by a labeled schedule and assignment. -/
def rawContingencyCount (z : Schedule K n) (A : Assign K n)
    (t : RespType K) (a : Arm K) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => z i = t ∧ A i = a).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i => z i = t ∧ A i = a) Finset.univ))⟩

/-- The contingency-count table records how many units of each response type receive each treatment arm. -/
def contingencyCounts (z : Schedule K n) (A : Assign K n) : Contingency K n :=
  rawContingencyCount z A

private lemma contingencyCounts_row (z : Schedule K n) (A : Assign K n)
    (t : RespType K) :
    ∑ a, ((contingencyCounts z A t a : Fin (n + 1)) : ℕ) =
      (rawScheduleCount z t : ℕ) := by
  symm
  simpa [contingencyCounts, rawContingencyCount, rawScheduleCount,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm] using
    (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun i => z i = t)
      (t := (Finset.univ : Finset (Arm K))) (f := A) (by simp))

private lemma contingencyCounts_col (z : Schedule K n) (A : Assign K n)
    (a : Arm K) :
    ∑ t, ((contingencyCounts z A t a : Fin (n + 1)) : ℕ) =
      (rawAssignmentCount A a : ℕ) := by
  symm
  simpa [contingencyCounts, rawContingencyCount, rawAssignmentCount,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm] using
    (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun i => A i = a)
      (t := (Finset.univ : Finset (RespType K))) (f := z) (by simp))

private lemma contingencyCounts_success (z : Schedule K n) (A : Assign K n)
    (a : Arm K) :
    ∑ t with t a = true, ((contingencyCounts z A t a : Fin (n + 1)) : ℕ) =
      (rawObservedCount A (obsOutcome z A) a : ℕ) := by
  change ∑ t with t a = true,
      #(Finset.univ.filter fun i => z i = t ∧ A i = a) =
    #(Finset.univ.filter fun i => A i = a ∧ z i (A i))
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun i => A i = a ∧ z i a)
    (t := Finset.univ.filter fun t : RespType K => t a = true)
    (f := z) (by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.2⟩)
  calc
    _ = ∑ t with t a = true,
        #((Finset.univ.filter fun i => A i = a ∧ z i a).filter fun i => z i = t) := by
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      ext i
      have hta := (Finset.mem_filter.mp ht).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hit, hiA⟩
        exact ⟨⟨hiA, by simpa [hit] using hta⟩, hit⟩
      · rintro ⟨⟨hiA, _⟩, hit⟩
        exact ⟨hit, hiA⟩
    _ = #(Finset.univ.filter fun i => A i = a ∧ z i a) := hsum.symm
    _ = _ := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hiA, hiY⟩
        exact ⟨hiA, by simpa [hiA] using hiY⟩
      · rintro ⟨hiA, hiY⟩
        exact ⟨hiA, by simpa [hiA] using hiY⟩

/-- Assignments inducing one fixed response-type/arm contingency table. -/
def ContingencyAssignments (z : Schedule K n) (h : Contingency K n) :=
  {A : Assign K n // contingencyCounts z A = h}

/-- The contingency assignments collection has a finite enumeration. -/
noncomputable instance (z : Schedule K n) (h : Contingency K n) :
    Fintype (ContingencyAssignments z h) := by
  classical
  unfold ContingencyAssignments
  infer_instance

private noncomputable def contingencyAssignmentsEquiv
    (z : Schedule K n) (h : Contingency K n) :
    ContingencyAssignments z h ≃
      ∀ t : RespType K, ExactFiber (I := {i // z i = t})
        (fun a => (h t a : ℕ)) := by
  let e₀ : Assign K n ≃ ∀ t, {i // z i = t} → Arm K :=
    Equiv.piCongrFiberwise (f := z) fun _ => Equiv.refl _
  let e₃ : {F : ∀ t, {i // z i = t} → Arm K //
      ∀ t a, Fintype.card {i // F t i = a} = (h t a : ℕ)} ≃
      ∀ t : RespType K, ExactFiber (I := {i // z i = t})
        (fun a => (h t a : ℕ)) :=
    { toFun := fun F t => ⟨F.1 t, F.2 t⟩
      invFun := fun F => ⟨fun t => (F t).1, fun t => (F t).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply (Equiv.subtypeEquiv e₀ ?_).trans e₃
  intro A
  constructor
  · intro hA t a
    change Fintype.card {i : {i // z i = t} // A i.1 = a} = (h t a : ℕ)
    let e : {i : {i // z i = t} // A i.1 = a} ≃
        {i : Unit n // z i = t ∧ A i = a} :=
      { toFun := fun i => ⟨i.1.1, i.1.2, i.2⟩
        invFun := fun i => ⟨⟨i.1, i.2.1⟩, i.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := congrFun (congrFun hA t) a
    rw [Fintype.card_congr e, Fintype.card_subtype]
    exact Fin.mk.inj_iff.mp hc
  · intro hA
    funext t a
    apply Fin.ext
    change #(Finset.univ.filter fun i => z i = t ∧ A i = a) = (h t a : ℕ)
    let e : {i : {i // z i = t} // A i.1 = a} ≃
        {i : Unit n // z i = t ∧ A i = a} :=
      { toFun := fun i => ⟨i.1.1, i.1.2, i.2⟩
        invFun := fun i => ⟨⟨i.1, i.2.1⟩, i.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := hA t a
    change Fintype.card {i : {i // z i = t} // A i.1 = a} = (h t a : ℕ) at hc
    rw [Fintype.card_congr e, Fintype.card_subtype] at hc
    exact hc

/-- [the stated contingency-table condition holds](hyp:hh), [Exact multinomial count of assignments inducing a fixed feasible contingency table.](goal) -/
lemma contingencyAssignments_card_cast (z : Schedule K n) (h : Contingency K n)
    (hh : h ∈ contingencyFiber (scheduleCounts z) r x) :
    (Fintype.card (ContingencyAssignments z h) : ℚ) =
      ∏ t, (((scheduleCounts z).1 t : ℕ).factorial : ℚ) /
        ∏ a, (((h t a : Fin (n + 1)) : ℕ).factorial : ℚ) := by
  classical
  rw [Fintype.card_congr (contingencyAssignmentsEquiv z h), Fintype.card_pi]
  push_cast
  apply Finset.prod_congr rfl
  intro t _
  rcases (Finset.mem_filter.mp hh).2 with ⟨hrow, _, _⟩
  have hcard : Fintype.card {i : Unit n // z i = t} =
      ((scheduleCounts z).1 t : ℕ) := by
    rw [Fintype.card_subtype]
    rfl
  have hex := exactFiber_card_cast_eq_div (I := {i : Unit n // z i = t})
    (fun a => (h t a : ℕ)) ((hrow t).trans hcard.symm)
  rw [hcard] at hex
  exact hex

/-- Labeled assignments with prescribed allocation and observed-success counts. -/
def LabeledObservationAssignments (z : Schedule K n) (r : AllocVec K n)
    (x : ObsVec r) :=
  {A : Assign K n // assignmentCounts A = r ∧
    ∀ a, (rawObservedCount A (obsOutcome z A) a : ℕ) = (x.1 a : ℕ)}

/-- The labeled observation assignments collection has a finite enumeration. -/
noncomputable instance (z : Schedule K n) (r : AllocVec K n) (x : ObsVec r) :
    Fintype (LabeledObservationAssignments z r x) := by
  classical
  unfold LabeledObservationAssignments
  infer_instance

private noncomputable def labeledObservationEquivContingencies
    (z : Schedule K n) (r : AllocVec K n) (x : ObsVec r) :
    LabeledObservationAssignments z r x ≃
      Σ h : {h // h ∈ contingencyFiber (scheduleCounts z) r x},
        ContingencyAssignments z h.1 where
  toFun A := ⟨⟨contingencyCounts z A.1, by
    simp only [contingencyFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨contingencyCounts_row z A.1, fun a => ?_, fun a => ?_⟩
    · exact (contingencyCounts_col z A.1 a).trans
        (congrArg (fun q : AllocVec K n => (q.1 a : ℕ)) A.2.1)
    · exact (contingencyCounts_success z A.1 a).trans (A.2.2 a)⟩,
    ⟨A.1, rfl⟩⟩
  invFun H := ⟨H.2.1, by
    rcases (Finset.mem_filter.mp H.1.2).2 with ⟨_, hcol, hsuccess⟩
    constructor
    · apply Subtype.ext
      funext a
      apply Fin.ext
      have hc := contingencyCounts_col z H.2.1 a
      rw [H.2.2] at hc
      exact hc.symm.trans (hcol a)
    · intro a
      have hc := contingencyCounts_success z H.2.1 a
      rw [H.2.2] at hc
      exact hc.symm.trans (hsuccess a)⟩
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv H := by
    rcases H with ⟨⟨h, hh⟩, ⟨A, hA⟩⟩
    dsimp at hA
    subst h
    rfl

/-- [Cardinality of an observed labeled fiber as the contingency-table sum in `orbitLik`.](goal) -/
lemma labeledObservationAssignments_card_cast
    (z : Schedule K n) (r : AllocVec K n) (x : ObsVec r) :
    (Fintype.card (LabeledObservationAssignments z r x) : ℚ) =
      ∑ h ∈ contingencyFiber (scheduleCounts z) r x,
        ∏ t, (((scheduleCounts z).1 t : ℕ).factorial : ℚ) /
          ∏ a, (((h t a : Fin (n + 1)) : ℕ).factorial : ℚ) := by
  classical
  rw [Fintype.card_congr (labeledObservationEquivContingencies z r x),
    Fintype.card_sigma]
  push_cast
  rw [← Finset.sum_subtype (contingencyFiber (scheduleCounts z) r x)
    (fun _ => Iff.rfl)
    (fun h => (Fintype.card (ContingencyAssignments z h) : ℚ))]
  apply Finset.sum_congr rfl
  intro h hh
  exact contingencyAssignments_card_cast z h hh

private noncomputable def allocationAssignmentsEquivExactFiber (r : AllocVec K n) :
    {A : Assign K n // assignmentCounts A = r} ≃
      ExactFiber (I := Unit n) (fun a => (r.1 a : ℕ)) where
  toFun A := ⟨A.1, fun a => by
    rw [Fintype.card_subtype]
    have ha := congrArg (fun q : AllocVec K n => (q.1 a : ℕ)) A.2
    simpa [assignmentCounts, rawAssignmentCount] using ha⟩
  invFun A := ⟨A.1, by
    apply Subtype.ext
    funext a
    apply Fin.ext
    simpa [assignmentCounts, rawAssignmentCount, ← Fintype.card_subtype] using A.2 a⟩
  left_inv A := rfl
  right_inv A := rfl

/-- The allocation assignments collection has a finite enumeration. -/
noncomputable instance allocationAssignmentsFintype (r : AllocVec K n) :
    Fintype {A : Assign K n // assignmentCounts A = r} := by
  classical
  infer_instance

/-- [Exact multinomial cardinality of an allocation orbit.](goal) -/
lemma allocationOrbitCard_cast_eq_factorial_div (r : AllocVec K n) :
    (allocationOrbitCard r : ℚ) =
      (n.factorial : ℚ) / ∏ a, (((r.1 a : ℕ).factorial : ℕ) : ℚ) := by
  classical
  unfold allocationOrbitCard
  rw [Fintype.card_congr (allocationAssignmentsEquivExactFiber r)]
  simpa using exactFiber_card_cast_eq_div (I := Unit n)
    (fun a => (r.1 a : ℕ)) (by simpa using r.2)

/-- Observed-success orbit of an assignment already identified with allocation orbit `r`. -/
def observedVecFor (z : Schedule K n) (r : AllocVec K n)
    (A : {A : Assign K n // assignmentCounts A = r}) : ObsVec r :=
  ⟨rawObservedCount A.1 (obsOutcome z A.1), fun a => by
    calc
      (rawObservedCount A.1 (obsOutcome z A.1) a : ℕ) ≤
          (rawAssignmentCount A.1 a : ℕ) := rawObservedCount_le _ _ _
      _ = (r.1 a : ℕ) := by
        have ha := congrArg (fun q : AllocVec K n => (q.1 a : ℕ)) A.2
        simpa [assignmentCounts] using ha⟩

private def labeledObservationEquivObservedFiber
    (z : Schedule K n) (r : AllocVec K n) (x : ObsVec r) :
    LabeledObservationAssignments z r x ≃
      {A : {A : Assign K n // assignmentCounts A = r} // observedVecFor z r A = x} where
  toFun A := ⟨⟨A.1, A.2.1⟩, by
    apply Subtype.ext
    funext a
    apply Fin.ext
    exact A.2.2 a⟩
  invFun A := ⟨A.1.1, A.1.2, fun a => by
    have ha := congrArg (fun q : ObsVec r => (q.1 a : ℕ)) A.2
    exact ha⟩
  left_inv A := rfl
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def allObservedFibersEquivAllocation
    (z : Schedule K n) (r : AllocVec K n) :
    (Σ x : ObsVec r, LabeledObservationAssignments z r x) ≃
      {A : Assign K n // assignmentCounts A = r} :=
  (Equiv.sigmaCongrRight fun x => labeledObservationEquivObservedFiber z r x).trans
    (Equiv.sigmaFiberEquiv (observedVecFor z r))

private lemma sum_labeledObservationAssignments_card
    (z : Schedule K n) (r : AllocVec K n) :
    ∑ x : ObsVec r, Fintype.card (LabeledObservationAssignments z r x) =
      allocationOrbitCard r := by
  classical
  unfold allocationOrbitCard
  rw [← Fintype.card_sigma,
    Fintype.card_congr (allObservedFibersEquivAllocation z r)]

/-- [Regroup a real-valued sum over one allocation orbit by observed-success fibers.](goal) -/
lemma sum_allocationFiber_by_observed
    (z : Schedule K n) (r : AllocVec K n) (F : ObsVec r → ℝ) :
    ∑ A : {A : Assign K n // assignmentCounts A = r}, F (observedVecFor z r A) =
      ∑ x : ObsVec r,
        Fintype.card (LabeledObservationAssignments z r x) * F x := by
  classical
  rw [← Fintype.sum_fiberwise (observedVecFor z r)
    (fun A => F (observedVecFor z r A))]
  apply Finset.sum_congr rfl
  intro x _
  have hterm (A : {A : {A : Assign K n // assignmentCounts A = r} //
      observedVecFor z r A = x}) : F (observedVecFor z r A.1) = F x := by
    rw [A.2]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact_mod_cast Fintype.card_congr (labeledObservationEquivObservedFiber z r x).symm

-- @node: def:orbit-likelihood
/-- The response-type orbit likelihood, kept over `ℚ` so coefficient rationality is
definitionally visible. -/
noncomputable def orbitLik (m : CountVec K n) (r : AllocVec K n) (x : ObsVec r) : ℚ :=
  ((∏ a, ((r.1 a : ℕ).factorial : ℚ)) / (n.factorial : ℚ)) *
    ∑ h ∈ contingencyFiber m r x,
      ∏ t, (((m.1 t : ℕ).factorial : ℚ) /
        (∏ a, ((h t a : ℕ).factorial : ℚ)))
-- @realizes P_m(x\mid r)((∏_a r_a!/n!) ∑_{h∈H} ∏_t m_t!/∏_a h_{t,a}!)

/-- [The labeled observation-fiber ratio is exactly the factorial orbit likelihood.](goal) -/
lemma labeledObservation_card_ratio_eq_orbitLik
    (z : Schedule K n) (r : AllocVec K n) (x : ObsVec r) :
    (Fintype.card (LabeledObservationAssignments z r x) : ℚ) /
        allocationOrbitCard r = orbitLik (scheduleCounts z) r x := by
  rw [labeledObservationAssignments_card_cast,
    allocationOrbitCard_cast_eq_factorial_div]
  unfold orbitLik
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hr : (∏ a, (((r.1 a : ℕ).factorial : ℕ) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity
  field_simp

/-- [the labeled observation cardinality ratio equals orbit lik real](goal). -/
lemma labeledObservation_card_ratio_eq_orbitLik_real
    (z : Schedule K n) (r : AllocVec K n) (x : ObsVec r) :
    (Fintype.card (LabeledObservationAssignments z r x) : ℝ) /
        allocationOrbitCard r = (orbitLik (scheduleCounts z) r x : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (labeledObservation_card_ratio_eq_orbitLik z r x)
  norm_num at h
  exact h

/-- [the orbit lik is nonnegative](goal). -/
lemma orbitLik_nonneg (m : CountVec K n) (r : AllocVec K n) (x : ObsVec r) :
    0 ≤ orbitLik m r x := by
  unfold orbitLik
  apply mul_nonneg
  · apply div_nonneg
    · exact prod_nonneg fun _ _ => by positivity
    · positivity
  · apply sum_nonneg
    intro h hh
    apply prod_nonneg
    intro t ht
    apply div_nonneg <;> positivity

/-- [the orbit lik sums obs](goal). -/
lemma orbitLik_sum_obs (m : CountVec K n) (r : AllocVec K n) :
    ∑ x : ObsVec r, orbitLik m r x = 1 := by
  obtain ⟨z, hz⟩ := exists_fun_card_fiber_eq (fun t => (m.1 t : ℕ)) m.2
  have hm : scheduleCounts z = m := by
    apply Subtype.ext
    funext t
    apply Fin.ext
    simpa [scheduleCounts, rawScheduleCount] using hz t
  subst m
  simp_rw [← labeledObservation_card_ratio_eq_orbitLik z r]
  rw [← Finset.sum_div]
  have hsum := congrArg (fun q : ℕ => (q : ℚ))
    (sum_labeledObservationAssignments_card z r)
  push_cast at hsum
  rw [hsum, div_self]
  exact_mod_cast (ne_of_gt (allocationOrbitCard_pos r))

/-- Rational orbit target used by the exact LP. -/
def tauCountRat (c : RatContrast K) (m : CountVec K n) : ℚ :=
  ((n : ℚ)⁻¹) * ∑ t, (m.1 t : ℚ) * ∑ a, c a * if t a then 1 else 0

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
