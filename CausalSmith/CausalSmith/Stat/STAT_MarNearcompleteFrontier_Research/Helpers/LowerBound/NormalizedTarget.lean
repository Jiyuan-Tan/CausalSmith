module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Target

/-! # Exact target identity for the normalized paired prior -/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

-- @node: pairedWeightedSign
/-- The signed latent mass in the paired construction. -/
@[expose] noncomputable def pairedWeightedSign (n d : ℕ) (θ : Theta n d) : ℝ :=
  ∑ j : Fin (pairCount n d), latentP n (θ.1 j) * latentZ n (θ.1 j)

-- @node: pairedWeightedSign_apply
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). -/
lemma pairedWeightedSign_apply (n d : ℕ) (θ : Theta n d) :
    pairedWeightedSign n d θ =
      ∑ j : Fin (pairCount n d), latentP n (θ.1 j) * latentZ n (θ.1 j) := rfl

-- @node: fillerAtomWeight_target_sum
/-- The filler component contributes its normalized mass times the filler mean. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). -/
lemma fillerAtomWeight_target_sum (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) :
    (∑ w : FullAtom d, fillerAtomWeight n d q hd θ w *
      ((if w.Y1 then (1 : ℝ) else 0) - (if w.Y0 then 1 else 0))) =
      fillerMass n d / normalizationJ n d θ * baseMean q := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fun w => fillerAtomWeight n d q hd θ w *
      ((if w.Y1 then (1 : ℝ) else 0) - (if w.Y0 then 1 else 0)))
    (fun t => fillerAtomWeight n d q hd θ ((fullAtomTupleEquiv d).symm t) *
      ((if ((fullAtomTupleEquiv d).symm t).Y1 then (1 : ℝ) else 0) -
        (if ((fullAtomTupleEquiv d).symm t).Y0 then 1 else 0)))
    (by intro w; simp)]
  simp only [Fintype.sum_prod_type]
  simp [fullAtomTupleEquiv, fillerAtomWeight, bernoulliFactor, fillerLabel,
    FullAtom.X]
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp only [if_true]
    ring
  · intro x _ hx
    simp [hx]
  · simp

-- @node: pairAtomWeight_target_sum
/-- One oriented paired label contributes its normalized mass times its treated mean. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma pairAtomWeight_target_sum (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool) :
    (∑ w : FullAtom d, pairAtomWeight n d q σ hd θ j side w *
      ((if w.Y1 then (1 : ℝ) else 0) - (if w.Y0 then 1 else 0))) =
      latentP n (θ.1 j) / normalizationJ n d θ *
        pairMu q σ (latentZ n (θ.1 j)) (orientation θ j side) := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fun w => pairAtomWeight n d q σ hd θ j side w *
      ((if w.Y1 then (1 : ℝ) else 0) - (if w.Y0 then 1 else 0)))
    (fun t => pairAtomWeight n d q σ hd θ j side
      ((fullAtomTupleEquiv d).symm t) *
      ((if ((fullAtomTupleEquiv d).symm t).Y1 then (1 : ℝ) else 0) -
        (if ((fullAtomTupleEquiv d).symm t).Y0 then 1 else 0)))
    (by intro w; simp)]
  simp only [Fintype.sum_prod_type]
  simp [fullAtomTupleEquiv, pairAtomWeight, bernoulliFactor, FullAtom.X,
    FullAtom.S0, FullAtom.S1, FullAtom.Y0, FullAtom.Y1]
  simp_rw [Finset.sum_add_distrib]
  simp
  ring

-- @node: pairMu_opposite_sum
/-- Opposite orientations have the exact filler-centered signed mean shift. Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the specified input `hz`](hyp:hz), [the specified input `hu`](hyp:hu), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq). -/
lemma pairMu_opposite_sum (q σ z u : ℝ)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1)
    (hu : u = -1 ∨ u = 1) :
    pairMu q σ z u + pairMu q σ z (-u) =
      2 * baseMean q + σ * delta q * z / (16 * q) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hq.1)
  have hqi : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
  have hq2i : q ^ 2 * q⁻¹ = q := by
    rw [pow_two, mul_assoc, hqi, mul_one]
  rcases hσ with rfl | rfl <;> rcases hz with rfl | rfl <;>
    rcases hu with rfl | rfl
  all_goals norm_num [pairMu, pairRho, baseMean, delta]
  all_goals field_simp [hq0]
  all_goals ring

-- @node: pairMu_orientation_sum
/-- Summing the two random orientations removes the orientation sign exactly. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMu_orientation_sum (n d : ℕ) (q σ : ℝ)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hσ : σ = -1 ∨ σ = 1)
    (θ : Theta n d) (j : Fin (pairCount n d)) :
    (∑ side : Bool,
      pairMu q σ (latentZ n (θ.1 j)) (orientation θ j side)) =
      2 * baseMean q + σ * delta q * latentZ n (θ.1 j) / (16 * q) := by
  have hzabs := latentZ_abs_one n (θ.1 j)
  have hz : latentZ n (θ.1 j) = -1 ∨ latentZ n (θ.1 j) = 1 := by
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hzabs
    exact hzabs.elim Or.inr Or.inl
  cases hside : θ.2 j <;>
    simp [orientation, hside, pairMu_opposite_sum q σ (latentZ n (θ.1 j)) 1
      hq hσ hz (Or.inr rfl),
      pairMu_opposite_sum q σ (latentZ n (θ.1 j)) (-1)
        hq hσ hz (Or.inl rfl), add_comm]

-- @node: pairedFullLaw_tau_exact
/-- The normalized paired law has exactly the filler target plus the signed
latent mass shift; normalization creates no additional sign-dependent term. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq). -/
lemma pairedFullLaw_tau_exact (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (θ : Theta n d) :
    tau (pairedFullLaw n d q σ hn hd hq
      (by rcases hσ with rfl | rfl <;> norm_num) θ) =
      baseMean q + σ * delta q / (16 * q) *
        pairedWeightedSign n d θ / normalizationJ n d θ := by
  let hσunit : σ ∈ Set.Icc (-1) 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hJ : normalizationJ n d θ ≠ 0 :=
    ne_of_gt (normalizationJ_pos n d q hn hd hq θ)
  unfold tau
  simp_rw [pairedFullLaw_fullMass n d q σ hn hd hq hσunit θ]
  calc
    (∑ w : FullAtom d, pairedAtomWeight n d q σ hd θ w *
        ((if w.Y1 then (1 : ℝ) else 0) - (if w.Y0 then 1 else 0))) =
        (∑ w : FullAtom d, fillerAtomWeight n d q hd θ w *
          ((if w.Y1 then (1 : ℝ) else 0) - (if w.Y0 then 1 else 0))) +
        ∑ j : Fin (pairCount n d), ∑ side : Bool,
          ∑ w : FullAtom d, pairAtomWeight n d q σ hd θ j side w *
            ((if w.Y1 then (1 : ℝ) else 0) -
              (if w.Y0 then 1 else 0)) := by
          simp only [pairedAtomWeight, add_mul, Finset.sum_add_distrib]
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = fillerMass n d / normalizationJ n d θ * baseMean q +
        ∑ j : Fin (pairCount n d), ∑ side : Bool,
          latentP n (θ.1 j) / normalizationJ n d θ *
            pairMu q σ (latentZ n (θ.1 j)) (orientation θ j side) := by
          rw [fillerAtomWeight_target_sum]
          simp_rw [pairAtomWeight_target_sum]
    _ = fillerMass n d / normalizationJ n d θ * baseMean q +
        ∑ j : Fin (pairCount n d),
          latentP n (θ.1 j) / normalizationJ n d θ *
            (2 * baseMean q + σ * delta q * latentZ n (θ.1 j) / (16 * q)) := by
          apply congrArg₂ (· + ·) rfl
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.mul_sum, pairMu_orientation_sum n d q σ hq hσ θ j]
    _ = baseMean q + σ * delta q / (16 * q) *
        pairedWeightedSign n d θ / normalizationJ n d θ := by
          have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hq.1)
          have hterm (j : Fin (pairCount n d)) :
              latentP n (θ.1 j) / normalizationJ n d θ *
                (2 * baseMean q + σ * delta q * latentZ n (θ.1 j) / (16 * q)) =
              (2 * baseMean q / normalizationJ n d θ) * latentP n (θ.1 j) +
              (σ * delta q / (16 * q) / normalizationJ n d θ) *
                (latentP n (θ.1 j) * latentZ n (θ.1 j)) := by ring
          simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
          unfold pairedWeightedSign
          field_simp [hJ, hq0]
          unfold normalizationJ
          ring

end CausalSmith.Stat.MarNearcompleteFrontier
