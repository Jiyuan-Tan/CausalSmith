module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Finite-cell identification under randomization, consistency, and MAR. -/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: cellContribution_eq_cellOutcomeMass
/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,j), [the stated mathematical conclusion holds](goal). -/
lemma cellContribution_eq_cellOutcomeMass {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P)
    (j : Cell d) :
    cellContribution P j = P.1.real {r | inCell r j ∧ r.Y = true} := by
  classical
  letI : IsProbabilityMeasure P.1 := P.2
  by_cases hp : 0 < cellProb P j
  · have ha : 0 < arrivedCell P j :=
      lt_of_lt_of_le (mul_pos hP.q_pos hp) (hP.arrival j hp)
    have hm := hP.mar j true true
    have hmass : cellContribution P j =
        cellProb P j *
          (P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} /
            arrivedCell P j) := by
      simp [cellContribution, cellMean, ha]
    rw [hmass]
    have : arrivedCell P j ≠ 0 := ne_of_gt ha
    calc
      cellProb P j *
          (P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} /
            arrivedCell P j) =
          (P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} *
            cellProb P j) / arrivedCell P j := by ring
      _ = P.1.real {r | inCell r j ∧ r.Y = true} := by
        rw [hm]
        have ha' : P.1.real {r | inCell r j ∧ r.R = true} ≠ 0 := by
          simpa only [arrivedCell] using this
        exact mul_div_cancel_left₀ _ ha'
  · have hzero : cellProb P j = 0 :=
      le_antisymm (le_of_not_gt hp) (measureReal_nonneg)
    have hsub : P.1.real {r | inCell r j ∧ r.Y = true} ≤ cellProb P j := by
      exact measureReal_mono (by intro r hr; exact hr.1)
    have hy : P.1.real {r | inCell r j ∧ r.Y = true} = 0 :=
      le_antisymm (hsub.trans_eq hzero) measureReal_nonneg
    have ha : arrivedCell P j = 0 :=
      le_antisymm ((measureReal_mono (by intro r hr; exact hr.1)).trans_eq hzero)
        measureReal_nonneg
    simp [cellContribution, ha, hy]

-- @node: sum_cellOutcomeMass_eq_armOutcomeMass
/-- Given [the specified inputs and assumptions](hyp:d,P,a), [the stated mathematical conclusion holds](goal). -/
lemma sum_cellOutcomeMass_eq_armOutcomeMass {d : ℕ} (P : FullLaw d) (a : Bool) :
    (∑ x : Fin d, ∑ s : Bool,
      P.1.real {r | inCell r (a, x, s) ∧ r.Y = true}) =
      P.1.real {r | r.A = a ∧ r.Y = true} := by
  classical
  letI : IsProbabilityMeasure P.1 := P.2
  let μ := P.1.restrict {r | r.A = a ∧ r.Y = true}
  have hμ : IsFiniteMeasure μ := inferInstance
  have hsum := sum_measureReal_preimage_singleton (μ := μ)
    (Finset.univ : Finset (Fin d × Bool))
    (f := fun r : FullRecord d => (r.X, r.S)) (by intro; simp)
  calc
    (∑ x : Fin d, ∑ s : Bool,
        P.1.real {r | inCell r (a, x, s) ∧ r.Y = true}) =
        ∑ j : Fin d × Bool, μ.real ((fun r : FullRecord d => (r.X, r.S)) ⁻¹' {j}) := by
          rw [← Finset.sum_product']
          apply Finset.sum_congr rfl
          intro x hx
          simp only [μ, measureReal_def, Measure.restrict_apply]
          have hs : {r : FullRecord d | inCell r (a, x.1, x.2) ∧ r.Y = true} =
              ((fun r : FullRecord d => (r.X, r.S)) ⁻¹' {x}) ∩
                {r | r.A = a ∧ r.Y = true} := by
            rcases x with ⟨x, s⟩
            ext r
            simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
              Set.mem_singleton_iff, Prod.mk.injEq, inCell]
            tauto
          rw [hs]
          rw [Measure.restrict_apply (by simp)]
    _ = μ.real ((fun r : FullRecord d => (r.X, r.S)) ⁻¹' (Finset.univ : Finset (Fin d × Bool))) := hsum
    _ = P.1.real {r | r.A = a ∧ r.Y = true} := by
      simp [μ, measureReal_def, Measure.restrict_apply]

-- @node: randomized_armOutcomeMass
/-- Given [the specified inputs and assumptions](hyp:d,P,hR,hB,a), [the stated mathematical conclusion holds](goal). -/
lemma randomized_armOutcomeMass {d : ℕ} (P : FullLaw d)
    (hR : RandomizedIndependence P) (hB : BalancedRandomization P)
    (a : Bool) :
    2 * P.1.real {r | r.A = a ∧ r.Y = true} =
      P.1.real {r | (if a then r.Y1 else r.Y0) = true} := by
  classical
  letI : IsProbabilityMeasure P.1 := P.2
  let y : FullRecord d → Bool := fun r => if a then r.Y1 else r.Y0
  have hInd : IndepFun (fun r : FullRecord d => r.A) y P.1 := by
    have h := hR.comp (φ := id)
      (ψ := fun z : Fin d × Bool × Bool × Bool × Bool => if a then z.2.2.2.2 else z.2.2.2.1)
      (by fun_prop) (by fun_prop)
    simpa [y, Function.comp_def] using h
  have hm := hInd.measure_inter_preimage_eq_mul ({a} : Set Bool) ({true} : Set Bool)
    (by simp) (by simp)
  change P.1 {r | r.A = a ∧ y r = true} =
    P.1 {r | r.A = a} * P.1 {r | y r = true} at hm
  have hmreal : P.1.real {r | r.A = a ∧ y r = true} =
      P.1.real {r | r.A = a} * P.1.real {r | y r = true} := by
    simpa only [measureReal_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal hm
  have ha : P.1.real {r | r.A = a} = 1 / 2 := by
    cases a with
    | true => exact hB
    | false =>
        have hcomp : {r : FullRecord d | r.A = false} =
            {r : FullRecord d | r.A = true}ᶜ := by ext r; cases r.A <;> simp
        rw [hcomp, measureReal_compl (by simp), hB]
        norm_num
  rw [show {r : FullRecord d | r.A = a ∧ r.Y = true} =
      {r | r.A = a ∧ y r = true} from by
        ext r
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨h, hy⟩
          simpa [y, FullRecord.Y, h] using hy
        · rintro ⟨h, hy⟩
          exact ⟨h, by simpa [y, FullRecord.Y, h] using hy⟩]
  rw [hmreal, ha]
  simp [y]

-- @node: cellFunctional_eq_armOutcomeMass
/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma cellFunctional_eq_armOutcomeMass {n d : ℕ} {q : ℝ}
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P) :
    cellFunctional P =
      2 * (P.1.real {r | r.A = true ∧ r.Y = true} -
        P.1.real {r | r.A = false ∧ r.Y = true}) := by
  classical
  unfold cellFunctional
  rw [Fintype.sum_prod_type]
  simp_rw [cellContribution_eq_cellOutcomeMass P hP]
  simp [Fintype.univ_bool, armSign, Fintype.sum_prod_type]
  have ht := sum_cellOutcomeMass_eq_armOutcomeMass P true
  have hf := sum_cellOutcomeMass_eq_armOutcomeMass P false
  simp [Fintype.univ_bool] at ht hf
  rw [ht, hf]
  ring

-- @node: ate_eq_potentialOutcomeMass
/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma ate_eq_potentialOutcomeMass {d : ℕ} (P : FullLaw d) :
    ate P = P.1.real {r | r.Y1 = true} - P.1.real {r | r.Y0 = true} := by
  classical
  letI : IsProbabilityMeasure P.1 := P.2
  have hv (a : Bool) :
      (fun r : FullRecord d => if (if a then r.Y1 else r.Y0) then (1 : ℝ) else 0) =
        ({r : FullRecord d | (if a then r.Y1 else r.Y0) = true}.indicator 1) := by
    funext r
    rcases r with ⟨x, a', s₀, s₁, y₀, y₁, arrival⟩
    cases a <;> cases y₀ <;> cases y₁ <;> simp [Set.indicator]
  have hi (a : Bool) :
      Integrable (fun r : FullRecord d =>
        if (if a then r.Y1 else r.Y0) then (1 : ℝ) else 0) P.1 := by
    rw [hv]
    exact (integrable_const (1 : ℝ)).indicator (by simp)
  have he (a : Bool) :
      (∫ r : FullRecord d,
        (if (if a then r.Y1 else r.Y0) then (1 : ℝ) else 0) ∂P.1) =
        P.1.real {r | (if a then r.Y1 else r.Y0) = true} := by
    rw [hv]
    exact integral_indicator_one (by simp)
  unfold ate
  rw [integral_sub (by simpa using hi true) (by simpa using hi false)]
  simpa using congrArg₂ (· - ·) (he true) (he false)

-- @node: lem:unrestricted-cell-identification
/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma unrestricted_cell_identification {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    ate P = cellFunctional P := by
  rw [ate_eq_potentialOutcomeMass P, cellFunctional_eq_armOutcomeMass P hP]
  have ht := randomized_armOutcomeMass P hP.randomized hP.balanced true
  have hf := randomized_armOutcomeMass P hP.randomized hP.balanced false
  have ht' : 2 * P.1.real {r | r.A = true ∧ r.Y = true} =
      P.1.real {r | r.Y1 = true} := by simpa using ht
  have hf' : 2 * P.1.real {r | r.A = false ∧ r.Y = true} =
      P.1.real {r | r.Y0 = true} := by simpa using hf
  linear_combination -ht' + hf'

-- @node: lem:cell-identification-background
/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma cell_identification_background {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : RareArrivalModelClass n d q P) :
    ate P = cellFunctional P := by
  apply unrestricted_cell_identification P
  exact
    { n_pos := hP.n_pos
      d_pos := hP.d_pos
      q_pos := hP.q_pos
      q_le_one := hP.q_le_one
      randomized := hP.randomized
      balanced := hP.balanced
      surrogate := hP.surrogate
      outcome := hP.outcome
      mar := hP.mar
      arrival := hP.arrival }

end CausalSmith.Stat.MarRareqLogfrontier
