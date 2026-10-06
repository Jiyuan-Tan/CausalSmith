module
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Power cell masses

Finite cells of the decreasing power density and their algebraic bounds.

Proof route: the sum telescopes; the integral identity follows from the real
power antiderivative on each cell, including the rightmost endpoint by
continuity. Monotonicity follows from the decreasing derivative for `s ≥ 1`.
The first-cell bound is Bernoulli's inequality, then nonnegativity,
antitonicity, and unit sum give the square-sum bound.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- For a [cell index](hyp:j), [sample size](hyp:N), and [power](hyp:s), the
 [power cell mass](goal) is the drop of the power survival function across that cell. -/
def powerCell (N : ℕ) (s : ℝ) (j : Fin N) : ℝ :=
  (1 - (j : ℝ) / N) ^ s - (1 - ((j : ℕ) + 1 : ℝ) / N) ^ s

/-- For a [power](hyp:s) [at least one](hyp:hs), [power cells are nonnegative](goal). -/
theorem powerCell_nonneg {N : ℕ} {s : ℝ} (hs : 1 ≤ s) (j : Fin N) :
    0 ≤ powerCell N s j := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hleft : 0 ≤ 1 - ((j : ℝ) + 1) / N := by
    apply sub_nonneg.mpr
    exact (div_le_one hN).2 hj
  have horder : 1 - ((j : ℝ) + 1) / N ≤ 1 - (j : ℝ) / N := by
    have hdiv : (j : ℝ) / N ≤ ((j : ℝ) + 1) / N :=
      div_le_div_of_nonneg_right (by linarith) hN.le
    linarith
  unfold powerCell
  exact sub_nonneg.mpr (Real.rpow_le_rpow hleft horder (by linarith))

/-- For a [power](hyp:s) [at least one](hyp:hs),
[power cell masses decrease with the cell index](goal). -/
theorem powerCell_antitone {N : ℕ} {s : ℝ} (hs : 1 ≤ s) :
    Antitone (powerCell N s) := by
  cases N with
  | zero => intro j; exact Fin.elim0 j
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    let a : ℝ := 1 - ((i : ℕ) + 2 : ℝ) / (n + 1)
    let b : ℝ := 1 - ((i : ℕ) + 1 : ℝ) / (n + 1)
    let c : ℝ := 1 - (i : ℝ) / (n + 1)
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have ha : 0 ≤ a := by
      have hi : (i : ℕ) + 2 ≤ n + 1 := by omega
      have hi' : (((i : ℕ) + 2 : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hi
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        (sub_nonneg.mpr ((div_le_one hn).2 hi'))
    have hc : 0 ≤ c := by
      have hi : (i : ℕ) ≤ n + 1 := by omega
      have hi' : ((i : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hi
      simpa only [Nat.cast_add, Nat.cast_one] using
        (sub_nonneg.mpr ((div_le_one hn).2 hi'))
    have hm : b = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c := by
      dsimp [a, b, c]
      ring
    have hconv := (convexOn_rpow hs).2 ha hc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [← hm] at hconv
    simp only [smul_eq_mul] at hconv
    have hstep : b ^ s - a ^ s ≤ c ^ s - b ^ s := by linarith
    convert hstep using 1
    all_goals first | rfl | (simp [powerCell, a, b, c, Fin.succ, Fin.castSucc,
      Nat.cast_add, add_assoc] <;> ring)

/-- For a [positive sample size](hyp:hN) and [power](hyp:s) [at least one](hyp:hs),
 [the power cell masses sum to one](goal). -/
theorem sum_powerCell {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 1 ≤ s) :
    ∑ j : Fin N, powerCell N s j = 1 := by
  let f : ℕ → ℝ := fun i => (1 - (i : ℝ) / N) ^ s
  have hsum : (∑ j : Fin N, powerCell N s j) = ∑ i ∈ Finset.range N, (f i - f (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [powerCell, f, Nat.cast_add, Nat.cast_one]
  rw [hsum, Finset.sum_range_sub']
  simp [f, ne_of_gt hN, Real.zero_rpow (by linarith : s ≠ 0)]

/-- For a [positive sample size](hyp:hN) and [power](hyp:s) [at least one](hyp:hs),
 [the first cell mass is at most the power divided by sample size](goal). -/
theorem powerCell_zero_le {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 1 ≤ s) :
    powerCell N s ⟨0, hN⟩ ≤ s / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : -1 ≤ -(1 / (N : ℝ)) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 : ℝ) / N ≤ 1 := (div_le_one hNr).2 this
    linarith
  have h := one_add_mul_self_le_rpow_one_add hb hs
  have h' : 1 - s / (N : ℝ) ≤ (1 - 1 / (N : ℝ)) ^ s := by
    convert h using 1 <;> ring
  have h'' : 1 - (1 - 1 / (N : ℝ)) ^ s ≤ s / N := by linarith
  simpa [powerCell] using h''

/-- For a [positive sample size](hyp:hN) and [power](hyp:s) [at least one](hyp:hs),
 [the sum of squared power cell masses is at most the power divided by sample size](goal). -/
theorem sum_powerCell_sq_le {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 1 ≤ s) :
    ∑ j : Fin N, (powerCell N s j) ^ 2 ≤ s / N := by
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hmax : ∀ j : Fin N, powerCell N s j ≤ s / N := by
    intro j
    calc
      powerCell N s j ≤ powerCell N s ⟨0, hN⟩ :=
        powerCell_antitone hs (Fin.zero_le j)
      _ ≤ s / N := powerCell_zero_le hN hs
  calc
    ∑ j : Fin N, (powerCell N s j) ^ 2 ≤
        ∑ j : Fin N, (s / N) * powerCell N s j := by
      apply Finset.sum_le_sum
      intro j _
      have h₁ := powerCell_nonneg hs j
      have h₂ := hmax j
      nlinarith [mul_nonneg h₁ (sub_nonneg.mpr h₂)]
    _ = s / N := by rw [← Finset.mul_sum, sum_powerCell hN hs, mul_one]

/-- For a [positive sample size](hyp:hN), [power](hyp:s) [at least one](hyp:hs), and [cell](hyp:j),
 [the power cell mass is the integral of the power density over that cell](goal). -/
theorem powerCell_eq_integral {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 1 ≤ s)
    (j : Fin N) :
    powerCell N s j =
      ∫ u in (j : ℝ) / N..(((j : ℕ) + 1 : ℝ) / N),
        s * (1 - u) ^ (s - 1) := by
  let a : ℝ := (j : ℝ) / N
  let b : ℝ := ((j : ℕ) + 1 : ℝ) / N
  let f : ℝ → ℝ := fun u => -((1 - u) ^ s)
  let g : ℝ → ℝ := fun u => s * (1 - u) ^ (s - 1)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : a ≤ b := by
    dsimp [a, b]
    apply div_le_div_of_nonneg_right _ hN'.le
    linarith
  have hf : Continuous f := by
    exact ((Real.continuous_rpow_const (by linarith : 0 ≤ s)).comp
      (continuous_const.sub continuous_id)).neg
  have hg : Continuous g := by
    exact continuous_const.mul ((Real.continuous_rpow_const
      (by linarith : 0 ≤ s - 1)).comp (continuous_const.sub continuous_id))
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (g x) x := by
    intro x hx
    have hb1 : b ≤ 1 := by
      dsimp [b]
      apply (div_le_one hN').2
      have : (j : ℕ) + 1 ≤ N := j.isLt
      exact_mod_cast this
    have hx1 : x < 1 := lt_of_lt_of_le hx.2 hb1
    have hlin : HasDerivAt (fun u : ℝ => 1 - u) (-1) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1
      all_goals first | rfl | ring
    have hpow := (Real.hasDerivAt_rpow_const
      (x := 1 - x) (p := s) (Or.inl (by linarith : 1 - x ≠ 0))).comp x hlin
    convert hpow.neg using 1
    all_goals first | rfl | (dsimp [g]; ring)
  have hInt : IntervalIntegrable g volume a b :=
    hg.continuousOn.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hf.continuousOn hderiv hInt
  dsimp [f, g] at h
  dsimp [powerCell, a, b]
  convert h.symm using 1 <;> ring

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
