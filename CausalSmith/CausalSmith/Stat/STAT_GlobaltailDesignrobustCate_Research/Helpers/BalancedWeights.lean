module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators

/-! # Balanced-weight normalization and variance proxy

These deterministic identities implement (2), (11), and (C13) in the proof
roadmaps. They hold for either arm and require occupancy only in the cell
being fitted. The sums index subcells and their selected observations.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open scoped BigOperators

-- @node: selectedConstantSum
/-- Summing a constant over selected observations multiplies it by the count. -/
lemma selectedConstantSum {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (c : ℝ) :
    (∑ i : Fin n, if p i then c else 0) =
      (∑ i : Fin n, if p i then 1 else 0 : ℕ) * c := by
  have hcast : ((∑ i : Fin n, if p i then 1 else 0 : ℕ) : ℝ) =
      ∑ i : Fin n, if p i then (1 : ℝ) else 0 := by
    push_cast
    rfl
  rw [hcast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

-- @node: occupiedSubcellCount_pos
/-- A positive minimum count makes every subcell count positive, for either arm. -/
lemma occupiedSubcellCount_pos {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j m ε Q) (ℓ : MultiIndex d m) :
    0 < subcellCount sample arm j m ε Q ℓ := by
  classical
  exact lt_of_lt_of_le hcount
    (Finset.inf'_le (fun t => subcellCount sample arm j m ε Q t) (by simp))

-- @node: balancedWeights_sum_one
/-- Equal subcell totals make the balanced weights sum to one on occupied cells. -/
lemma balancedWeights_sum_one {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j m ε Q) : (by
    classical
    exact (∑ ℓ : MultiIndex d m, ∑ i : Fin n,
      if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
        (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
          (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹
      else 0) = 1) := by
  classical
  have hR : (Fintype.card (MultiIndex d m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum (ℓ : MultiIndex d m) :
      (∑ i : Fin n,
        if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
          (Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
            (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ else 0) =
        (Fintype.card (MultiIndex d m) : ℝ)⁻¹ := by
    rw [selectedConstantSum]
    change (subcellCount sample arm j m ε Q ℓ : ℝ) *
      ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
        (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹) = _
    have hN : (subcellCount sample arm j m ε Q ℓ : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (occupiedSubcellCount_pos sample arm j m ε Q hcount ℓ)).ne'
    field_simp
  simp_rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hR

-- @node: balancedWeights_sq_sum
/-- The exact squared-weight sum is the average of reciprocal subcell counts,
scaled by the squared number of subcells, as in roadmap (11). -/
lemma balancedWeights_sq_sum {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j m ε Q) : (by
    classical
    exact (∑ ℓ : MultiIndex d m, ∑ i : Fin n,
      if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
        ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
          (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹) ^ 2
      else 0) =
    (Fintype.card (MultiIndex d m) : ℝ)⁻¹ ^ 2 *
      ∑ ℓ : MultiIndex d m, (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [selectedConstantSum]
  change (subcellCount sample arm j m ε Q ℓ : ℝ) *
    ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
      (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹) ^ 2 = _
  have hN : (subcellCount sample arm j m ε Q ℓ : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (occupiedSubcellCount_pos sample arm j m ε Q hcount ℓ)).ne'
  field_simp

-- @node: balancedWeights_sq_sum_le
/-- The minimum occupancy bounds the variance proxy by one over rank times
minimum count. This is the deterministic input to (13) and (C14). -/
lemma balancedWeights_sq_sum_le {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j m : ℕ) (ε : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j m ε Q) : (by
    classical
    exact (∑ ℓ : MultiIndex d m, ∑ i : Fin n,
      if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j m ε Q ℓ then
        ((Fintype.card (MultiIndex d m) : ℝ)⁻¹ *
          (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹) ^ 2
      else 0) ≤
    1 / ((Fintype.card (MultiIndex d m) : ℝ) *
      (minimumCellCount sample arm j m ε Q : ℝ))) := by
  classical
  rw [balancedWeights_sq_sum sample arm j m ε Q hcount]
  have hR : (Fintype.card (MultiIndex d m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmin : (0 : ℝ) < minimumCellCount sample arm j m ε Q := Nat.cast_pos.mpr hcount
  have hinv (ℓ : MultiIndex d m) :
      (subcellCount sample arm j m ε Q ℓ : ℝ)⁻¹ ≤
        (minimumCellCount sample arm j m ε Q : ℝ)⁻¹ := by
    apply inv_antitoneOn_Ioi hmin
      (Nat.cast_pos.mpr (occupiedSubcellCount_pos sample arm j m ε Q hcount ℓ))
    exact_mod_cast (Finset.inf'_le
      (fun t => subcellCount sample arm j m ε Q t) (by simp : ℓ ∈ Finset.univ))
  calc
    _ ≤ (Fintype.card (MultiIndex d m) : ℝ)⁻¹ ^ 2 *
        ∑ _ℓ : MultiIndex d m, (minimumCellCount sample arm j m ε Q : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ℓ _ => hinv ℓ)) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

-- @node: scaledSubcell_unique
/-- The fixed disjoint norming construction assigns a point to at most one
scaled subcell of a given dyadic cell. -/
lemma scaledSubcell_unique {d : ℕ} (j : ℕ) (β : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (x : Fin d → ℝ)
    (a b : MultiIndex d (polynomialOrder β))
    (ha : x ∈ scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q a)
    (hb : x ∈ scaledSubcell d j (polynomialOrder β) (normingSubcells d β).radius Q b) :
    a = b := by
  by_contra hab
  exact Set.disjoint_left.mp ((normingSubcells d β).disjoint a b hab) ha.2 hb.2

-- @node: sum_sq_of_unique_selection
/-- A sum with at most one selected term has no cross terms in its square. -/
lemma sum_sq_of_unique_selection {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (w : ι → ℝ)
    (hunique : ∀ a b, p a → p b → a = b) :
    (∑ a, if p a then w a else 0) ^ 2 =
      ∑ a, if p a then (w a) ^ 2 else 0 := by
  classical
  by_cases hex : ∃ a, p a
  · obtain ⟨a, ha⟩ := hex
    have hz (b : ι) (hba : b ≠ a) : ¬ p b := by
      intro hb
      exact hba (hunique b a hb ha)
    rw [Fintype.sum_eq_single a (fun b hba => if_neg (hz b hba)),
      Fintype.sum_eq_single a (fun b hba => if_neg (hz b hba))]
    simp only [if_pos ha]
  · have hz : ∀ a, ¬ p a := by simpa only [not_exists] using hex
    simp [hz]

-- @node: balancedObservationWeights_sq_sum_le
/-- The actual per-observation balanced weights obey (11) and (C13).
Disjointness removes cross terms before applying the reciprocal-count bound. -/
lemma balancedObservationWeights_sq_sum_le {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β : ℝ) (Q : Fin d → Fin (2 ^ j))
    (hcount : 0 < minimumCellCount sample arm j (polynomialOrder β)
      (normingSubcells d β).radius Q) : (by
    classical
    exact (∑ i : Fin n,
      (∑ ℓ : MultiIndex d (polynomialOrder β),
        if (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j (polynomialOrder β)
            (normingSubcells d β).radius Q ℓ then
          (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)⁻¹ *
            (subcellCount sample arm j (polynomialOrder β)
              (normingSubcells d β).radius Q ℓ : ℝ)⁻¹
        else 0) ^ 2) ≤
      1 / ((Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        (minimumCellCount sample arm j (polynomialOrder β)
          (normingSubcells d β).radius Q : ℝ))) := by
  classical
  have hsq (i : Fin n) := sum_sq_of_unique_selection
    (fun ℓ => (sample i).2.1 = arm ∧ (sample i).1 ∈ scaledSubcell d j (polynomialOrder β)
      (normingSubcells d β).radius Q ℓ)
    (fun ℓ => (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)⁻¹ *
      (subcellCount sample arm j (polynomialOrder β)
        (normingSubcells d β).radius Q ℓ : ℝ)⁻¹)
    (fun a b ha hb => scaledSubcell_unique j β Q (sample i).1 a b ha.2 hb.2)
  simp_rw [hsq]
  rw [Finset.sum_comm]
  exact balancedWeights_sq_sum_le sample arm j (polynomialOrder β)
    (normingSubcells d β).radius Q hcount

end CausalSmith.Stat.GlobalTailDesignRobustCate
