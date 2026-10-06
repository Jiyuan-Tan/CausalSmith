module
public import Causalean.Mathlib.InformationTheory.ConditionalEntropy

/-!
# Mutual information of a uniform finite experiment

This file gives the finite-sum identity equating information gained from a
uniformly chosen finite hypothesis with the entropy drop after observing a
finite output. It supplies the algebraic bridge used by general-experiment
forms of Fano's inequality.
-/

public section

namespace Causalean.Mathlib.InformationTheory

open scoped BigOperators

/-- Given [finite input and output alphabets](hyp:α,β), a [nonnegative stochastic
matrix `r`](hyp:hr0) whose [rows each sum to one](hyp:hrsum), and a uniform input,
[the input entropy minus the conditional entropy equals the uniform average of
the row-wise logarithmic density ratios against the output marginal](goal).

This is the finite-alphabet identity `I(V;Y) = H(V) - H(V | Y)` written in a
form that can be combined directly with measure-theoretic KL data processing. -/
theorem uniform_condEntropy_kl_identity
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (r : α → β → ℝ) (hr0 : ∀ i y, 0 ≤ r i y)
    (hrsum : ∀ i, ∑ y, r i y = 1) :
    Real.log (Fintype.card α) -
        condEntropy
          (fun z : α × β => (Fintype.card α : ℝ)⁻¹ * r z.1 z.2) =
      (Fintype.card α : ℝ)⁻¹ *
        ∑ i, ∑ y, r i y *
          Real.log
            (r i y /
              ((Fintype.card α : ℝ)⁻¹ * ∑ k, r k y)) := by
  classical
  let N : ℝ := Fintype.card α
  let u : ℝ := N⁻¹
  let p : α × β → ℝ := fun z => u * r z.1 z.2
  let q : β → ℝ := fun y => u * ∑ i, r i y
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hu : 0 < u := inv_pos.mpr hNpos
  have hsumr : ∑ z : α × β, r z.1 z.2 = N := by
    rw [Fintype.sum_prod_type]
    simp_rw [hrsum]
    simp [N]
  have hsump : ∑ z : α × β, p z = 1 := by
    simp only [p]
    rw [← Finset.mul_sum, hsumr]
    simp [u, N, ne_of_gt hNpos]
  have hq : yMarginal p = q := by
    funext y
    simp [yMarginal, p, q, ← Finset.mul_sum]
  have hlogN : Real.log N + Real.log u = 0 := by
    rw [show u = N⁻¹ by rfl, Real.log_inv]
    ring
  have hcell : ∀ i y,
      u * r i y * Real.log (r i y / q y) =
        p (i, y) * Real.log N + p (i, y) * Real.log (p (i, y)) -
          u * r i y * Real.log (q y) := by
    intro i y
    by_cases hri : r i y = 0
    · simp [hri, p]
    have hrpos : 0 < r i y := lt_of_le_of_ne (hr0 i y) (Ne.symm hri)
    have hqpos : 0 < q y := by
      dsimp [q]
      exact mul_pos hu (lt_of_lt_of_le hrpos
        (Finset.single_le_sum (fun j _ => hr0 j y) (Finset.mem_univ i)))
    rw [Real.log_div hrpos.ne' hqpos.ne', show p (i, y) = u * r i y by rfl,
      Real.log_mul hu.ne' hrpos.ne']
    calc
      u * r i y * (Real.log (r i y) - Real.log (q y)) =
          u * r i y *
            (Real.log N + Real.log u + Real.log (r i y) - Real.log (q y)) := by
              rw [hlogN]
              ring
      _ = u * r i y * Real.log N + u * r i y *
            (Real.log u + Real.log (r i y)) - u * r i y * Real.log (q y) := by ring
  have hplogN : ∑ i, ∑ y, p (i, y) * Real.log N = Real.log N := by
    calc
      (∑ i, ∑ y, p (i, y) * Real.log N) =
          (∑ i, ∑ y, p (i, y)) * Real.log N := by
            rw [Finset.sum_mul]
            simp_rw [Finset.sum_mul]
      _ = (∑ z : α × β, p z) * Real.log N := by rw [Fintype.sum_prod_type]
      _ = Real.log N := by rw [hsump, one_mul]
  have hqlog : ∑ i, ∑ y, u * r i y * Real.log (q y) =
      ∑ y, q y * Real.log (q y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [← Finset.sum_mul]
    simp only [q, ← Finset.mul_sum]
  have hpneg : (∑ i, ∑ y, -p (i, y) * Real.log (p (i, y))) =
      -(∑ i, ∑ y, p (i, y) * Real.log (p (i, y))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  have hqneg : (∑ y, -q y * Real.log (q y)) =
      -(∑ y, q y * Real.log (q y)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  change Real.log N - condEntropy p =
    u * ∑ i, ∑ y, r i y * Real.log (r i y / q y)
  rw [condEntropy_def, hq, entropy_def, entropy_def]
  rw [Fintype.sum_prod_type]
  simp only [Real.negMulLog_def]
  simp_rw [Finset.mul_sum]
  simp_rw [← mul_assoc]
  simp_rw [hcell]
  rw [show
    (∑ i, ∑ y, (p (i, y) * Real.log N + p (i, y) * Real.log (p (i, y)) -
      u * r i y * Real.log (q y))) =
      (∑ i, ∑ y, p (i, y) * Real.log N) +
      (∑ i, ∑ y, p (i, y) * Real.log (p (i, y))) -
      (∑ i, ∑ y, u * r i y * Real.log (q y)) by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]]
  rw [hplogN, hqlog, hpneg, hqneg]
  ring

/-- Given [finite input and output alphabets](hyp:α,β), a [nonnegative stochastic
matrix `r`](hyp:hr0) whose [rows sum to one](hyp:hrsum), and a [reference output
mass function `q`](hyp:hq0) that [sums to one](hyp:hqsum) and [dominates every
row's support](hyp:hac), [the uniform-input information relative to the output
marginal is at most the average logarithmic density ratio to `q`](goal).

This is the finite information-radius inequality `I(V;Y) ≤ E KL(P_{Y|V} ‖ Q)`. -/
theorem uniform_information_le_average_logRatio
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (r : α → β → ℝ) (hr0 : ∀ i y, 0 ≤ r i y)
    (hrsum : ∀ i, ∑ y, r i y = 1)
    (q : β → ℝ) (hq0 : ∀ y, 0 ≤ q y) (hqsum : ∑ y, q y = 1)
    (hac : ∀ i y, r i y ≠ 0 → q y ≠ 0) :
    (Fintype.card α : ℝ)⁻¹ *
        ∑ i, ∑ y, r i y *
          Real.log
            (r i y / ((Fintype.card α : ℝ)⁻¹ * ∑ k, r k y)) ≤
      (Fintype.card α : ℝ)⁻¹ *
        ∑ i, ∑ y, r i y * Real.log (r i y / q y) := by
  classical
  let N : ℝ := Fintype.card α
  let u : ℝ := N⁻¹
  let qbar : β → ℝ := fun y => u * ∑ i, r i y
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hu : 0 < u := inv_pos.mpr hNpos
  have hqbar0 : ∀ y, 0 ≤ qbar y := fun y =>
    mul_nonneg hu.le (Finset.sum_nonneg fun i _hi => hr0 i y)
  have hqbarsum : ∑ y, qbar y = 1 := by
    simp only [qbar, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hrsum]
    simp [u, N, ne_of_gt hNpos]
  have hacbar : ∀ y, qbar y ≠ 0 → 0 < q y := by
    intro y hqbar
    have hsumne : ∑ i, r i y ≠ 0 := by
      intro hzero
      exact hqbar (by simp [qbar, hzero])
    obtain ⟨i, _hi, hri⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
    exact lt_of_le_of_ne (hq0 y) (Ne.symm (hac i y hri))
  have hcross := entropy_le_crossEntropy hqbar0 hq0 (by rw [hqbarsum, hqsum]) hacbar
  have hlogs :
      ∑ y, qbar y * Real.log (q y) ≤
        ∑ y, qbar y * Real.log (qbar y) := by
    rw [entropy_def] at hcross
    simp only [Real.negMulLog_def] at hcross
    have hneg : (∑ y, -qbar y * Real.log (qbar y)) =
        -(∑ y, qbar y * Real.log (qbar y)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    rw [hneg] at hcross
    linarith
  have hleft :
      u * ∑ i, ∑ y, r i y * Real.log (r i y / qbar y) =
        u * ∑ i, ∑ y, r i y * Real.log (r i y) -
          ∑ y, qbar y * Real.log (qbar y) := by
    have hcell : ∀ i y,
        u * (r i y * Real.log (r i y / qbar y)) =
          u * (r i y * Real.log (r i y)) -
            u * r i y * Real.log (qbar y) := by
      intro i y
      by_cases hri : r i y = 0
      · simp [hri]
      have hrpos : 0 < r i y := lt_of_le_of_ne (hr0 i y) (Ne.symm hri)
      have hqbarpos : 0 < qbar y := by
        dsimp [qbar]
        exact mul_pos hu (lt_of_lt_of_le hrpos
          (Finset.single_le_sum (fun j _ => hr0 j y) (Finset.mem_univ i)))
      rw [Real.log_div hrpos.ne' hqbarpos.ne']
      ring
    simp_rw [Finset.mul_sum, hcell]
    rw [show
      (∑ i, ∑ y, (u * (r i y * Real.log (r i y)) -
        u * r i y * Real.log (qbar y))) =
        (∑ i, ∑ y, u * (r i y * Real.log (r i y))) -
        (∑ i, ∑ y, u * r i y * Real.log (qbar y)) by
          simp only [Finset.sum_sub_distrib]]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [← Finset.sum_mul]
    simp only [qbar, ← Finset.mul_sum]
  have hright :
      u * ∑ i, ∑ y, r i y * Real.log (r i y / q y) =
        u * ∑ i, ∑ y, r i y * Real.log (r i y) -
          ∑ y, qbar y * Real.log (q y) := by
    have hcell : ∀ i y,
        u * (r i y * Real.log (r i y / q y)) =
          u * (r i y * Real.log (r i y)) - u * r i y * Real.log (q y) := by
      intro i y
      by_cases hri : r i y = 0
      · simp [hri]
      have hrpos : 0 < r i y := lt_of_le_of_ne (hr0 i y) (Ne.symm hri)
      have hqpos : 0 < q y := lt_of_le_of_ne (hq0 y) (Ne.symm (hac i y hri))
      rw [Real.log_div hrpos.ne' hqpos.ne']
      ring
    simp_rw [Finset.mul_sum, hcell]
    rw [show
      (∑ i, ∑ y, (u * (r i y * Real.log (r i y)) -
        u * r i y * Real.log (q y))) =
        (∑ i, ∑ y, u * (r i y * Real.log (r i y))) -
        (∑ i, ∑ y, u * r i y * Real.log (q y)) by
          simp only [Finset.sum_sub_distrib]]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [← Finset.sum_mul]
    simp only [qbar, ← Finset.mul_sum]
  change u * ∑ i, ∑ y, r i y * Real.log (r i y / qbar y) ≤
    u * ∑ i, ∑ y, r i y * Real.log (r i y / q y)
  rw [hleft, hright]
  linarith

end Causalean.Mathlib.InformationTheory
