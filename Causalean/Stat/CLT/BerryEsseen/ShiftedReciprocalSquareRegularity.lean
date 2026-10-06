module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! # Local uniform convergence of shifted reciprocal squares

The integer reciprocal-square series converges locally uniformly away from
its integer poles, including at noninteger real arguments. This is the
boundary-continuity prerequisite missing from the upper-half-plane-only
cotangent derivative theorem in Mathlib.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- [The integer shifted reciprocal-square series Σ_{m∈ℤ} 1/(z+m)² converges
locally uniformly on the complex plane with the integers removed](goal). -/
theorem shifted_reciprocal_sq_summableLocallyUniformlyOn :
    SummableLocallyUniformlyOn
      (fun m : ℤ => fun z : ℂ => 1 / (z + (m : ℂ)) ^ 2)
      Complex.integerComplement := by
  /- Lowest independent analytic leaf. Reuse
  SummableLocallyUniformlyOn.of_locally_bounded_eventually. On each compact
  K, choose R bounding ‖z‖. For |m|≥2R, reverse triangle gives
  ‖z+m‖≥|m|/2, hence ‖1/(z+m)^2‖≤4/|m|^2. The finite exceptional indices
  need no uniform bound in the eventual-majorant criterion. Reuse integer
  p-series summability; do not add a positive-imaginary-part hypothesis.
  Individual summands are continuous on integerComplement. Consequently
  their tsum is continuous there, enabling z=x+iε, ε↓0 in the independent
  upper-half-plane identity. No partial-fraction identity is needed here. -/
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    Complex.isOpen_compl_range_intCast
  intro K _ hK
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨fun m : ℤ => 4 / (m : ℝ) ^ 2, ?_, ?_⟩
  · simpa only [mul_one_div] using
      (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4
  · have hlarge : ∀ᶠ m : ℤ in Filter.cofinite, 2 * R ≤ ‖(m : ℂ)‖ :=
      (tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
        Complex.isClosedEmbedding_intCast).eventually_ge_atTop (2 * R)
    filter_upwards [hlarge] with m hm z hz
    have hmpos : 0 < |(m : ℝ)| := by
      rw [Complex.norm_intCast] at hm
      linarith
    have htriangle : ‖(m : ℂ)‖ ≤ ‖z + (m : ℂ)‖ + ‖z‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (z + (m : ℂ)) z
    have hhalf : |(m : ℝ)| ≤ 2 * ‖z + (m : ℂ)‖ := by
      rw [Complex.norm_intCast] at hm htriangle
      have := hR z hz
      linarith
    have hzpos : 0 < ‖z + (m : ℂ)‖ := by linarith
    have hsquare : (m : ℝ) ^ 2 ≤ 4 * ‖z + (m : ℂ)‖ ^ 2 := by
      have := mul_self_le_mul_self (abs_nonneg (m : ℝ)) hhalf
      nlinarith [sq_abs (m : ℝ)]
    simp only [norm_div, norm_one, norm_pow]
    have hmSq : 0 < (m : ℝ) ^ 2 := by
      simpa only [sq_abs] using sq_pos_of_pos hmpos
    apply (div_le_div_iff₀ (sq_pos_of_pos hzpos)
      hmSq).2
    simpa only [one_mul] using hsquare

end Causalean.Stat.CLT.BerryEsseen
