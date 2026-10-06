module
public import Mathlib.Analysis.PSeries

/-! # Elementary bounds on a shifted reciprocal-square tail

Telescoping reciprocal differences sandwich the summable positive tail.
This leaf supplies the deterministic error bound after the Prawitz series
identity, without any trigonometric or probability dependency.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- At [a positive shift x](hyp:x,hx), [the reciprocal-square tail
Σ_{n≥0} 1/(x+n+1)² is summable and lies between 1/(x+1) and 1/x](goal). -/
theorem reciprocal_sq_tail_bounds (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / (x + (n : ℝ) + 1) ^ 2) ∧
      1 / (x + 1) ≤ (∑' n : ℕ, 1 / (x + (n : ℝ) + 1) ^ 2) ∧
      (∑' n : ℕ, 1 / (x + (n : ℝ) + 1) ^ 2) ≤ 1 / x := by
  /- Reuse Real.summable_one_div_nat_add_rpow or p-series comparison.
  For a=x+n>0, sandwich (a+1)^(-2) between
  1/(a+1)-1/(a+2) and 1/a-1/(a+1). Sum over Finset.range N,
  telescope, then pass to N→∞; the trailing reciprocals tend to zero.
  This is a discrete elementary leaf, independent of PrawitzSignSeries.
  The lower bound implies S≥1/x-1/x² by elementary field algebra. -/
  have hs : Summable (fun n : ℕ => 1 / (x + (n : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow (x + 1) 2).2 (by norm_num)
    convert h using 1
    ext n
    rw [abs_of_pos (by positivity), Real.rpow_two]
    congr 2; ring
  have ht (a : ℝ) (ha : 0 < a) :
      HasSum (fun n : ℕ => 1 / (a + n) - 1 / (a + (n + 1 : ℕ))) (1 / a) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => ?_) _).2
    · simp only [Finset.sum_range_sub', Nat.cast_zero, add_zero]
      have hlim : Filter.Tendsto (fun n : ℕ => 1 / (a + (n : ℝ)))
          Filter.atTop (nhds 0) := by
        simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_left _ a (tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop))
      simpa using tendsto_const_nhds.sub hlim
    · apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le (by positivity)
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
  have hl := ht (x + 1) (by linarith)
  have hu := ht x hx
  refine ⟨hs, ?_, ?_⟩
  · rw [← hl.tsum_eq]
    apply hl.summable.tsum_le_tsum _ hs
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Nat.cast_add, Nat.cast_one]
    apply (sub_le_iff_le_add).2
    have h1 : 0 < x + (n : ℝ) + 1 := by positivity
    have h2 : 0 < x + 1 + ((n : ℝ) + 1) := by positivity
    field_simp
    nlinarith
  · rw [← hu.tsum_eq]
    apply hs.tsum_le_tsum _ hu.summable
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Nat.cast_add, Nat.cast_one]
    have h0 : 0 < x + (n : ℝ) := by positivity
    have h1 : 0 < x + ((n : ℝ) + 1) := by positivity
    apply (le_sub_iff_add_le).2
    field_simp
    nlinarith

end Causalean.Stat.CLT.BerryEsseen
