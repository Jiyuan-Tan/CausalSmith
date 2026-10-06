module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Identification

/-!
# Cell decomposition for the upper-risk proof

This module formalizes equations (1)--(2): arrived and missing cell masses,
their arrival-floor bounds, and the exact centered target decomposition.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open scoped BigOperators

/-- Probability mass in an arrived `(X,A,S)` cell. -/
noncomputable def arrivedCellMass {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  massOf P (fun w ↦ w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true)

/-- Probability mass in the missing part of an `(X,A,S)` cell. -/
noncomputable def missingCellMass {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  cellMass P x a s - arrivedCellMass P x a s

/-- Centered arrived-outcome regression in a cell. -/
noncomputable def cellEta {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  outcomeMean (observedLaw P) x a s - 1 / 2

/-- Signed treatment contrast multiplier. -/
def treatmentSign (a : Bool) : ℝ := if a then 1 else -1

-- @node: arrivedCellMass_nonneg
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma arrivedCellMass_nonneg {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : 0 ≤ arrivedCellMass P x a s := by
  unfold arrivedCellMass massOf
  apply Finset.sum_nonneg
  intro w hw
  split_ifs <;> simp [fullMass]

-- @node: arrivedCellMass_le_cellMass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma arrivedCellMass_le_cellMass {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : arrivedCellMass P x a s ≤ cellMass P x a s := by
  unfold arrivedCellMass cellMass massOf
  apply Finset.sum_le_sum
  intro w hw
  by_cases hc : w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    split_ifs <;> simp [fullMass]

-- @node: arrivedCellMass_eq_mul_arrivalProb
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma arrivedCellMass_eq_mul_arrivalProb {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    arrivedCellMass P x a s = cellMass P x a s * arrivalProb P x a s := by
  have hA0 := arrivedCellMass_nonneg P x a s
  have hAle := arrivedCellMass_le_cellMass P x a s
  by_cases hc : cellMass P x a s = 0
  · have hA : arrivedCellMass P x a s = 0 := by linarith
    have hmass : massOf P
        (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) = 0 := by
      simpa only [arrivedCellMass] using hA
    rw [hA, arrivalProb, hc, hmass]
    simp
  · unfold arrivalProb
    change arrivedCellMass P x a s =
      cellMass P x a s * (arrivedCellMass P x a s / cellMass P x a s)
    field_simp

-- @node: missingCellMass_bounds
/-- Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma missingCellMass_bounds {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool) :
    0 ≤ missingCellMass P x a s ∧
      missingCellMass P x a s ≤ delta q * cellMass P x a s ∧
      missingCellMass P x a s ≤ 2 * delta q * arrivedCellMass P x a s := by
  have hA0 := arrivedCellMass_nonneg P x a s
  have hAle := arrivedCellMass_le_cellMass P x a s
  have hC0 := cellMass_nonneg P x a s
  have hqlo := hq.1
  have hqhi := hq.2
  have hd0 : 0 ≤ delta q := by unfold delta; linarith
  constructor
  · unfold missingCellMass
    linarith
  by_cases hc : cellMass P x a s = 0
  · have hA : arrivedCellMass P x a s = 0 := by linarith
    simp [missingCellMass, hc, hA]
  · have hcpos : 0 < cellMass P x a s := lt_of_le_of_ne hC0 (Ne.symm hc)
    have hf := h.floor x a s hcpos
    have hqA : q * cellMass P x a s ≤ arrivedCellMass P x a s := by
      rw [arrivedCellMass_eq_mul_arrivalProb P x a s]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hf hC0
    have hfirst : missingCellMass P x a s ≤ delta q * cellMass P x a s := by
      unfold missingCellMass delta
      nlinarith
    refine ⟨hfirst, ?_⟩
    have hhalf : (1 / 2 : ℝ) * cellMass P x a s ≤
        q * cellMass P x a s := mul_le_mul_of_nonneg_right hqlo hC0
    have hC2A : cellMass P x a s ≤ 2 * arrivedCellMass P x a s := by
      linarith
    calc
      missingCellMass P x a s ≤ delta q * cellMass P x a s := hfirst
      _ ≤ delta q * (2 * arrivedCellMass P x a s) :=
        mul_le_mul_of_nonneg_left hC2A hd0
      _ = 2 * delta q * arrivedCellMass P x a s := by ring

-- @node: sum_cellMass_eq_armMass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). -/
lemma sum_cellMass_eq_armMass {d : ℕ} (P : FullLaw d) (a : Bool) :
    (∑ x : Fin d, ∑ s : Bool, cellMass P x a s) = armMass P a := by
  classical
  rw [← Fintype.sum_prod_type']
  simp only [cellMass, armMass, massOf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ha : w.A = a
  · simp only [ha, true_and, ↓reduceIte]
    rw [Fintype.sum_prod_type' (fun x : Fin d => fun s : Bool =>
      if w.X = x ∧ w.S = s then fullMass P w else 0)]
    cases w.S <;> simp
  · simp [ha]

-- @node: sum_cellMass_eq_one
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma sum_cellMass_eq_one {d : ℕ} (P : FullLaw d) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, cellMass P x a s) = 1 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [sum_cellMass_eq_armMass]
  rw [← massOf_univ_eq_one P]
  unfold armMass massOf
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  cases hwa : w.A <;> simp [hwa]

-- @node: sum_missingCellMass_le_delta
/-- Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma sum_missingCellMass_le_delta {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, missingCellMass P x a s) ≤ delta q := by
  calc
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, missingCellMass P x a s) ≤
        ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
          delta q * cellMass P x a s := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      exact (missingCellMass_bounds P h hq x a s).2.1
    _ = delta q *
        (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, cellMass P x a s) := by
      simp only [Finset.mul_sum]
    _ = delta q := by rw [sum_cellMass_eq_one]; ring

-- @node: tau_eq_arrived_missing_cells
/-- Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma tau_eq_arrived_missing_cells {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    tau P = 2 * (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      treatmentSign a *
        (arrivedCellMass P x a s * cellEta P x a s +
          missingCellMass P x a s * cellEta P x a s)) := by
  rw [tau_eq_psi P h hq]
  unfold psi condCellMass cellEta missingCellMass treatmentSign
  simp only [observed_cell_mass, observed_arm_mass]
  have ha_true : armMass P true = (1 : ℝ) / 2 := h.balanced
  have ha_false : armMass P false = (1 : ℝ) / 2 :=
    armMass_false_eq_half P h.balanced
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, ha_true, ha_false]
  have ht := sum_cellMass_eq_armMass P true
  have hf := sum_cellMass_eq_armMass P false
  simp only [Fintype.sum_bool, ha_true] at ht
  simp only [Fintype.sum_bool, ha_false] at hf
  rw [Finset.sum_add_distrib] at ht hf
  have htcenter :
      (∑ x : Fin d, cellMass P x true true * (-1 / 2 : ℝ)) +
        ∑ x : Fin d, cellMass P x true false * (-1 / 2 : ℝ) = -1 / 4 := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ht]
    norm_num
  have hfcenter :
      (∑ x : Fin d, cellMass P x false true * (1 / 2 : ℝ)) +
        ∑ x : Fin d, cellMass P x false false * (1 / 2 : ℝ) = 1 / 4 := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, hf]
    norm_num
  have hneg (a s : Bool) :
      (∑ x : Fin d, cellMass P x a s * (-1 / 2 : ℝ)) =
        -(∑ x : Fin d, cellMass P x a s * (1 / 2 : ℝ)) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hmul (a s : Bool) :
      (∑ x : Fin d, cellMass P x a s * outcomeMean (observedLaw P) x a s) =
        ∑ x : Fin d, outcomeMean (observedLaw P) x a s * cellMass P x a s := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hmul2 (a s : Bool) :
      (∑ x : Fin d,
        cellMass P x a s * outcomeMean (observedLaw P) x a s * 2) =
        (∑ x : Fin d,
          outcomeMean (observedLaw P) x a s * cellMass P x a s) * 2 := by
    rw [← Finset.sum_mul, hmul]
  norm_num at ⊢
  ring_nf at ht hf htcenter hfcenter ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [hneg]
  rw [hneg true true, hneg true false] at htcenter
  simp_rw [hmul2, hmul]
  linear_combination -2 * htcenter - 2 * hfcenter

end CausalSmith.Stat.MarNearcompleteFrontier
