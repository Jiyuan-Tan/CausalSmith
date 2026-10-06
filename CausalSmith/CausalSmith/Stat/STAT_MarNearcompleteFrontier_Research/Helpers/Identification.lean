module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Basic

/-! Finite-law randomization and MAR identification. -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

-- @node: massOf_potential_partition
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
lemma massOf_potential_partition {d : ℕ} (P : FullLaw d) (E : FullAtom d → Prop) :
    massOf P E = ∑ z : PotentialAtom d,
      massOf P (fun w => E w ∧ w.potential = z) := by
  classical
  unfold massOf
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases he : E w
  · simp [he]
  · simp [he]

-- @node: randomized_potential_event
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hR`](hyp:hR), [the specified input `a`](hyp:a), [the specified input `F`](hyp:F), [the stated mathematical conclusion holds](goal). -/
lemma randomized_potential_event {d : ℕ} (P : FullLaw d)
    (hR : RandomizedIndependence P) (a : Bool)
    (F : PotentialAtom d → Prop) :
    massOf P (fun w => w.A = a ∧ F w.potential) =
      armMass P a * massOf P (fun w => F w.potential) := by
  classical
  have hpoint (z : PotentialAtom d) :
      massOf P (fun w => w.A = a ∧ w.potential = z) =
        armMass P a * massOf P (fun w => w.potential = z) := by
    obtain ⟨x, s0, s1, y0, y1⟩ := z
    have key (w : FullAtom d) :
        w.potential = { X := x, S0 := s0, S1 := s1, Y0 := y0, Y1 := y1 } ↔
          w.X = x ∧ w.S0 = s0 ∧ w.S1 = s1 ∧ w.Y0 = y0 ∧ w.Y1 = y1 := by
      constructor
      · intro hw
        simpa [FullAtom.X, FullAtom.S0, FullAtom.S1, FullAtom.Y0, FullAtom.Y1, hw]
      · rintro ⟨hx, hs0, hs1, hy0, hy1⟩
        cases hp : w.potential with
        | mk wx ws0 ws1 wy0 wy1 =>
          simp only [FullAtom.X, FullAtom.S0, FullAtom.S1, FullAtom.Y0,
            FullAtom.Y1, hp] at hx hs0 hs1 hy0 hy1
          simp [hp, hx, hs0, hs1, hy0, hy1]
    simpa only [key] using hR a x s0 s1 y0 y1
  calc
    massOf P (fun w => w.A = a ∧ F w.potential) =
        ∑ z : PotentialAtom d,
          if F z then massOf P (fun w => w.A = a ∧ w.potential = z) else 0 := by
      rw [massOf_potential_partition]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hF : F z
      · simp only [hF, if_pos]
        unfold massOf
        apply Finset.sum_congr rfl
        intro w hw'
        by_cases hwz : w.potential = z <;> simp [hwz, hF, and_assoc]
      · simp only [hF, if_neg]
        unfold massOf
        apply Finset.sum_eq_zero
        intro w hw'
        by_cases hwz : w.potential = z <;> simp [hwz, hF]
    _ = ∑ z : PotentialAtom d,
          if F z then armMass P a * massOf P (fun w => w.potential = z) else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hpoint]
    _ = armMass P a *
          (∑ z : PotentialAtom d,
            if F z then massOf P (fun w => w.potential = z) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hF : F z <;> simp [hF]
    _ = armMass P a * massOf P (fun w => F w.potential) := by
      congr 1
      rw [massOf_potential_partition]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hF : F z
      · simp only [hF, if_pos]
        unfold massOf
        apply Finset.sum_congr rfl
        intro w hw'
        by_cases hwz : w.potential = z <;> simp [hwz, hF]
      · simp only [hF, ↓reduceIte]
        unfold massOf
        symm
        apply Finset.sum_eq_zero
        intro w hw'
        by_cases hwz : w.potential = z <;> simp [hwz, hF]

-- @node: massOf_univ_eq_one
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma massOf_univ_eq_one {d : ℕ} (P : FullLaw d) :
    massOf P (fun _ => True) = 1 := by
  classical
  simp only [massOf, if_true]
  have htop (w : FullAtom d) : P.pmf w ≠ ⊤ := PMF.apply_ne_top P.pmf w
  simp only [fullMass]
  rw [← ENNReal.toReal_sum (fun w _ => htop w)]
  have h := PMF.tsum_coe P.pmf
  rw [tsum_fintype] at h
  rw [h]
  norm_num

-- @node: armMass_false_eq_half
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hB`](hyp:hB), [the stated mathematical conclusion holds](goal). -/
lemma armMass_false_eq_half {d : ℕ} (P : FullLaw d)
    (hB : BalancedRandomization P) : armMass P false = 1 / 2 := by
  have hs : armMass P true + armMass P false = 1 := by
    rw [← massOf_univ_eq_one P]
    simp only [armMass, massOf]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rcases w with ⟨p, A, S, Y, R⟩
    cases A <;> simp
  unfold BalancedRandomization at hB
  linarith

-- @node: armOutcome_consistency
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hC`](hyp:hC), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). -/
lemma armOutcome_consistency {d : ℕ} (P : FullLaw d)
    (hC : Consistency P) (a : Bool) :
    massOf P (fun w => w.A = a ∧ w.Y = true) =
      massOf P (fun w => w.A = a ∧ (if a then w.Y1 else w.Y0) = true) := by
  classical
  unfold massOf
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hm : fullMass P w = 0
  · simp [hm]
  have hY : w.Y = if w.A then w.Y1 else w.Y0 := by
    by_contra hn
    exact hm (hC w (Or.inr hn))
  by_cases ha : w.A = a
  · subst a
    simp [hY]
  · simp [ha]

-- @node: tau_eq_potential_mass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma tau_eq_potential_mass {d : ℕ} (P : FullLaw d) :
    tau P = massOf P (fun w => w.Y1 = true) -
      massOf P (fun w => w.Y0 = true) := by
  classical
  unfold tau massOf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> ring

-- @node: randomized_arm_outcome
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hR`](hyp:hR), [the specified input `hB`](hyp:hB), [the specified input `hC`](hyp:hC), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). -/
lemma randomized_arm_outcome {d : ℕ} (P : FullLaw d)
    (hR : RandomizedIndependence P) (hB : BalancedRandomization P)
    (hC : Consistency P) (a : Bool) :
    2 * massOf P (fun w => w.A = a ∧ w.Y = true) =
      massOf P (fun w => (if a then w.Y1 else w.Y0) = true) := by
  rw [armOutcome_consistency P hC a]
  have hr := randomized_potential_event P hR a
    (fun z : PotentialAtom d => (if a then z.Y1 else z.Y0) = true)
  have ha : armMass P a = 1 / 2 := by
    cases a with
    | true => exact hB
    | false => exact armMass_false_eq_half P hB
  calc
    2 * massOf P (fun w => w.A = a ∧ (if a then w.Y1 else w.Y0) = true) =
        2 * (armMass P a * massOf P
          (fun w => (if a then w.Y1 else w.Y0) = true)) :=
      congrArg (fun z : ℝ => 2 * z) hr
    _ = _ := by rw [ha]; ring

-- @node: lem:identification-infrastructure
/-- Randomization, consistency and MAR identify the original superpopulation ATE. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma tau_eq_psi {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    tau P = psi (observedLaw P) := by
  have htrue := randomized_arm_outcome P h.randomized h.balanced h.consistency true
  have hfalse := randomized_arm_outcome P h.randomized h.balanced h.consistency false
  rw [tau_eq_potential_mass]
  have htrue' : 2 * massOf P (fun w => w.A = true ∧ w.Y = true) =
      massOf P (fun w => w.Y1 = true) := by simpa using htrue
  have hfalse' : 2 * massOf P (fun w => w.A = false ∧ w.Y = true) =
      massOf P (fun w => w.Y0 = true) := by simpa using hfalse
  unfold psi
  simp_rw [cellContribution_identified P h hq]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_div]
  rw [cellOutcome_sum P true, cellOutcome_sum P false]
  have ha_true : armMass P true = 1 / 2 := h.balanced
  have ha_false : armMass P false = 1 / 2 := armMass_false_eq_half P h.balanced
  rw [ha_true, ha_false]
  rw [← htrue', ← hfalse']
  ring

end CausalSmith.Stat.MarNearcompleteFrontier
