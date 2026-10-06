module
public import Causalean.Stat.Concentration.BoundedVariation.ControlQuantiles
public import Causalean.Stat.Concentration.BoundedVariation.FiniteSignMax

/-!
# Dyadic sections of scalar path controls

This module constructs compatible time grids from a continuous scalar control
and bounds the signed maximum of the increments on one finite grid level.
The grids may repeat times when the control has flat intervals.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- If a continuous control path is [nondecreasing](hyp:hmono) and [zero
at time zero](hyp:hzero), then [it admits compatible dyadic time grids:
the level-k grid has 2^k + 1 points in increasing order, its i-th point has
control value i/2^k times the terminal value, and equal dyadic fractions at
different levels have the same representative time](goal).
-/
theorem exists_control_dyadic_grid (u : Path)
    (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0) :
    ∃ t : ∀ k : ℕ, Fin (2 ^ k + 1) → Time,
      (∀ k, Monotone (t k)) ∧
      (∀ k i, u (t k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne) ∧
      (∀ k i l j,
        ((i.val : ℝ) / (2 ^ k : ℝ)) = ((j.val : ℝ) / (2 ^ l : ℝ)) →
          t k i = t l j) := by
  obtain ⟨q, hq, hqmono⟩ := exists_monotone_control_section u hmono hzero
  have hU : 0 ≤ u timeOne := by
    have h01 : timeZero ≤ timeOne := by
      change (0 : ℝ) ≤ 1
      norm_num
    simpa only [hzero] using hmono h01
  let level (k : ℕ) (i : Fin (2 ^ k + 1)) : Set.Icc (0 : ℝ) (u timeOne) :=
    ⟨((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne, by
      have hi : (i.val : ℝ) ≤ (2 ^ k : ℝ) := by
        exact_mod_cast Nat.le_of_lt_succ i.isLt
      have hpow : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
      have hfrac : (i.val : ℝ) / (2 ^ k : ℝ) ≤ 1 :=
        (div_le_iff₀ hpow).2 (by simpa using hi)
      constructor
      · positivity
      · nlinarith⟩
  refine ⟨fun k i => q (level k i), ?_, ?_, ?_⟩
  · intro k i j hij
    apply hqmono
    change ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne ≤
      ((j.val : ℝ) / (2 ^ k : ℝ)) * u timeOne
    gcongr
    exact_mod_cast hij
  · intro k i
    exact hq (level k i)
  · intro k i l j hfrac
    apply congrArg q
    apply Subtype.ext
    change ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne =
      ((j.val : ℝ) / (2 ^ l : ℝ)) * u timeOne
    rw [hfrac]

/-- If [every one of the m + 1 consecutive increments of a finite time
grid has summed squared path increments at most δ](hyp:hδ), then [the
sign-averaged largest squared signed increment over the grid is at most
32 (1 + log(m + 1)) δ](goal).
-/
theorem signed_grid_increment_max_energy_le {m n : ℕ}
    (w : Fin n → Path) (t : Fin (m + 2) → Time) (δ : ℝ)
    (hδ : ∀ i : Fin (m + 1),
      (∑ j, (w j (t i.succ) - w j (t i.castSucc)) ^ 2) ≤ δ) :
    signMaxEnergy (fun i j => w j (t i.succ) - w j (t i.castSucc)) ≤
      32 * (1 + Real.log (m + 1)) * δ := by
  have hlog : 0 ≤ Real.log (m + 1 : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  calc
    signMaxEnergy (fun i j => w j (t i.succ) - w j (t i.castSucc)) ≤
        32 * (1 + Real.log (m + 1)) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (m + 1) =>
              ∑ j, (w j (t i.succ) - w j (t i.castSucc)) ^ 2) :=
      signMaxEnergy_le _
    _ ≤ 32 * (1 + Real.log (m + 1)) * δ := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => hδ i)
      · positivity

end Causalean.Stat.Concentration.BoundedVariation
