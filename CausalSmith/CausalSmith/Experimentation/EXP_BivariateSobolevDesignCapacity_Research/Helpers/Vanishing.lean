module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CapacityHandle
public import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Vanishing comparison-scale subsystem

The binomial-ratio and square-root dimension criteria include arbitrary oscillating sequences.
-/

public section
noncomputable section
open Filter
open scoped Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The pair count is uniformly comparable to the squared dimension.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: pairCount_quadratic_bounds
lemma pairCount_quadratic_bounds (d : ℕ) (hd : 2 ≤ d) :
    (d : ℝ) ^ 2 / 4 ≤ (pairCount d : ℝ) ∧
      (pairCount d : ℝ) ≤ (d : ℝ) ^ 2 / 2 := by
  have heq := Nat.descFactorial_eq_factorial_mul_choose d 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    mul_one, Nat.factorial_succ, Nat.factorial_zero] at heq
  have hreal : ((d : ℝ) - 1) * d = 2 * (pairCount d : ℝ) := by
    have hc := congrArg (Nat.cast : ℕ → ℝ) heq
    simpa [Nat.cast_sub (by omega : 1 ≤ d), pairCount] using hc
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor <;> nlinarith

/-- [ The explicit scale vanishes exactly below the square-root dimension frontier.](goal) Under [the stated conditions](hyp:hs,hs1,hd). -/
-- @node: scale_vanishing
lemma scale_vanishing (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (ds : ℕ → ℕ) (hd : ∀ n, 2 ≤ ds n) :
    (Tendsto (fun n => aScale n (ds n) s) atTop (𝓝 0) ↔
      Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0)) ∧
    (Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0) ↔
      Asymptotics.IsLittleO atTop (fun n => (ds n : ℝ))
        (fun n => Real.sqrt (n : ℝ)))  := by
  have hratio (n : ℕ) : 0 ≤ (pairCount (ds n) : ℝ) / n := by positivity
  refine ⟨Causalean.Mathlib.Analysis.SpecialFunctions.tendsto_min_one_rpow_zero_iff
    _ hratio s hs, ?_⟩
  have hquadratic :
      Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0) ↔
        Tendsto (fun n => (ds n : ℝ) ^ 2 / n) atTop (𝓝 0) := by
    constructor
    · intro h
      have hfour := h.const_mul 4
      simp only [mul_zero] at hfour
      apply squeeze_zero (fun n => by positivity) _ hfour
      intro n
      have hb := (pairCount_quadratic_bounds (ds n) (hd n)).1
      calc
        (ds n : ℝ) ^ 2 / n ≤ (4 * (pairCount (ds n) : ℝ)) / n :=
          div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
        _ = 4 * ((pairCount (ds n) : ℝ) / n) := by ring
    · intro h
      apply squeeze_zero hratio _ h
      intro n
      exact div_le_div_of_nonneg_right
        (le_trans (pairCount_quadratic_bounds (ds n) (hd n)).2
          (by nlinarith [sq_nonneg (ds n : ℝ)])) (Nat.cast_nonneg n)
  rw [hquadratic]
  have hnonzero : ∀ᶠ n : ℕ in atTop, Real.sqrt (n : ℝ) = 0 → (ds n : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact fun h => (ne_of_gt (Real.sqrt_pos.mpr hpos) h).elim
  rw [Asymptotics.isLittleO_iff_tendsto' hnonzero]
  constructor
  · intro h
    have hroot := h.sqrt
    simpa [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs] using hroot
  · intro h
    have hsq := h.pow 2
    simp only [zero_pow (by decide : 2 ≠ 0)] at hsq
    apply hsq.congr'
    exact Filter.Eventually.of_forall fun n => by
      dsimp only
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
