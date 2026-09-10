/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

/-!
# A quantitative moment-growth certificate for Carleman divergence

The estimate `|m_(2n)| ≤ 2 (2n)^n` forces each inverse-root term to dominate a
constant multiple of `n⁻¹ᐟ²`; comparison with the divergent p-series then gives the
explicit Hamburger--Carleman certificate.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory
open scoped ENNReal BigOperators

private lemma real_half_evenPow_rpow_le
    (n : ℕ) (hn : 0 < n) (m : ℝ) (hmpos : 0 < m)
    (hm : m ≤ 2 * (2 * n : ℝ) ^ n) :
    (1 / 2 : ℝ) * (2 * n : ℝ) ^ (-(1 : ℝ) / 2) ≤
      m ^ (-(1 : ℝ) / (2 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < 2 * n := by positivity
  have hfrac : (1 : ℝ) / (2 * n) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  have hexp : -(1 : ℝ) ≤ -(1 : ℝ) / (2 * n) := by
    rw [neg_div]
    linarith
  have htwo :
      (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / (2 * n)) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-(1 : ℝ)) by
      norm_num [Real.rpow_neg_one]]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
  calc
    (1 / 2 : ℝ) * (2 * n : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ (2 : ℝ) ^ (-(1 : ℝ) / (2 * n)) *
            (2 * n : ℝ) ^ (-(1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hbase.le _)
    _ = (2 * (2 * n : ℝ) ^ n) ^ (-(1 : ℝ) / (2 * n)) := by
      rw [Real.mul_rpow (by positivity) (le_of_lt (pow_pos hbase n))]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
      congr 1
      field_simp
    _ ≤ m ^ (-(1 : ℝ) / (2 * n)) := by
      exact Real.rpow_le_rpow_of_nonpos hmpos hm
        (le_of_lt (div_neg_of_neg_of_pos (by norm_num) (by positivity)))

/-- If [a real measure](hyp:ν) has [positive even raw moments bounded at the Gaussian
scale](hyp:hmoment), then [its explicit Hamburger--Carleman series diverges](goal). -/
theorem hamburgerCarlemanSeries_eq_top_of_evenMoment_le
    (ν : Measure ℝ)
    (hmoment : ∀ n : ℕ, 0 < n →
      |rawMoment ν (2 * n)| ≤ 2 * (2 * n : ℝ) ^ n) :
    hamburgerCarlemanSeries ν = ⊤ := by
  -- Put `n = s + 1`.  Antitonicity of `rpow` at the negative exponent turns the
  -- moment upper bound into a lower bound for each summand.  Bound the extra
  -- factor `2^(-1/(2n))` uniformly below and compare with the divergent real
  -- p-series `n^(-1/2)`, transported to `ENNReal`.
  let f : ℕ → NNReal := fun s =>
    (1 / 2 : NNReal) * ((2 * (s + 1) : ℕ) : NNReal) ^ (-(1 : ℝ) / 2)
  have hf : ¬ Summable f := by
    let p : ℝ := -(1 : ℝ) / 2
    let c : NNReal := (1 / 2 : NNReal) * (2 : NNReal) ^ p
    have hfull : ¬ Summable (fun n : ℕ => (n : NNReal) ^ p) := by
      rw [NNReal.summable_rpow]
      norm_num [p]
    have hshift : ¬ Summable (fun s : ℕ => ((s + 1 : ℕ) : NNReal) ^ p) := by
      intro hs
      apply hfull
      apply (NNReal.summable_nat_add_iff 1).mp
      simpa [Nat.add_comm] using hs
    have hc : c ≠ 0 := by positivity
    intro hfs
    apply hshift
    apply (summable_mul_left_iff hc).mp
    simpa [f, c, p, NNReal.mul_rpow, mul_assoc] using hfs
  have hftop : (∑' s : ℕ, (f s : ENNReal)) = ⊤ := by
    apply ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr
    rwa [NNReal.summable_coe]
  rw [hamburgerCarlemanSeries]
  apply top_unique
  rw [← hftop]
  apply ENNReal.tsum_le_tsum
  intro s
  let n := s + 1
  have hn : 0 < n := by omega
  let m := |rawMoment ν (2 * n)|
  have hmnonneg : 0 ≤ m := abs_nonneg _
  have hterm : (f s : ENNReal) ≤
      (ENNReal.ofReal m).rpow (-(1 : ℝ) / (2 * n)) := by
    by_cases hmzero : m = 0
    · have he : -(1 : ℝ) / (2 * n) < 0 :=
        div_neg_of_neg_of_pos (by norm_num) (by positivity)
      simp [hmzero, he]
    · have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmzero)
      have hreal := real_half_evenPow_rpow_le n hn m hmpos (hmoment n hn)
      rw [show (ENNReal.ofReal m).rpow (-(1 : ℝ) / (2 * n)) =
        ENNReal.ofReal (m ^ (-(1 : ℝ) / (2 * n))) by
          exact ENNReal.ofReal_rpow_of_pos hmpos]
      rw [ENNReal.coe_nnreal_eq]
      apply ENNReal.ofReal_le_ofReal
      simpa [f, n] using hreal
  simpa [n, m] using hterm

end Causalean.Stat.MomentProblems
