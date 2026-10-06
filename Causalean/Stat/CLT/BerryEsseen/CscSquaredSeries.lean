module
public import Causalean.Stat.CLT.BerryEsseen.CscSquaredUpperHalfPlane
public import Causalean.Stat.CLT.BerryEsseen.ShiftedReciprocalSquareRegularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! # Reciprocal-square partial fractions on the real line

This real boundary identity is the squared-cosecant companion of Mathlib's
cotangent expansion. It is independent of Abel integration and probability.

Both reciprocal-square terms belong to each summand of the symmetric series.
-/

public section

open scoped Topology

namespace Causalean.Stat.CLT.BerryEsseen

/-- At [a real argument x away from the integer zeros of sin(πx)](hyp:x,hsin),
[the symmetric shifted reciprocal-square series Σ_{n≥1} (1/(x−n)² + 1/(x+n)²)
is summable, and (sin(πx)/π)² times its sum plus the central term 1/x² equals
one](goal). -/
theorem csc_squared_reciprocal_series (x : ℝ)
    (hsin : Real.sin (Real.pi * x) ≠ 0) :
    Summable (fun n : ℕ =>
      1 / (x - ((n : ℝ) + 1)) ^ 2 + 1 / (x + ((n : ℝ) + 1)) ^ 2) ∧
    (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
      (1 / x ^ 2 + (∑' n : ℕ,
        (1 / (x - ((n : ℝ) + 1)) ^ 2 +
         1 / (x + ((n : ℝ) + 1)) ^ 2))) = 1 := by
  have hx : (x : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨m, hm⟩
    have hmx : (m : ℝ) = x := by
      simpa using congrArg Complex.re hm
    apply hsin
    rw [← hmx, mul_comm]
    exact Real.sin_int_mul_pi m
  have hcont : ContinuousOn (fun z : ℂ => ∑' m : ℤ, 1 / (z + (m : ℂ)) ^ 2)
      Complex.integerComplement := by
    apply shifted_reciprocal_sq_summableLocallyUniformlyOn.hasSumLocallyUniformlyOn.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro s
    apply continuousOn_finsetSum
    intro m _
    exact continuousOn_const.div ((continuous_id.add continuous_const).continuousOn.pow 2)
      (fun z hz => pow_ne_zero 2 (Complex.integerComplement_add_ne_zero hz m))
  have hboundary :
      (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ 2 *
        (∑' m : ℤ, 1 / ((x : ℂ) + (m : ℂ)) ^ 2) = 1 := by
    let F : ℂ → ℂ := fun z =>
      (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) ^ 2 *
        (∑' m : ℤ, 1 / (z + (m : ℂ)) ^ 2)
    have hF : ContinuousAt F (x : ℂ) := by
      apply ContinuousAt.mul
      · fun_prop
      · exact hcont.continuousAt (Complex.isOpen_compl_range_intCast.mem_nhds hx)
    have hz : Filter.Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (x : ℂ)) := by
      have hc : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) 0 := by
        fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0] (fun _ => (1 : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply csc_squared_integer_series_upperHalfPlane
      simpa using ht
    exact tendsto_nhds_unique (hF.tendsto.comp hz)
      (Filter.Tendsto.congr' heq.symm tendsto_const_nhds)
  have hcomplex := shifted_reciprocal_sq_summableLocallyUniformlyOn.summable hx
  have hreal : Summable (fun m : ℤ => 1 / (x + (m : ℝ)) ^ 2) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
      Complex.ofReal_add, Complex.ofReal_intCast] using hcomplex
  have hidentity : (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
      (∑' m : ℤ, 1 / (x + (m : ℝ)) ^ 2) = 1 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_sin, Complex.ofReal_tsum, Complex.ofReal_one,
      Complex.ofReal_add, Complex.ofReal_intCast] using hboundary
  have hpos : Summable (fun n : ℕ => 1 / (x + (n : ℝ)) ^ 2) := by
    simpa [Function.comp_def] using hreal.comp_injective
      (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℤ)))
  have hneg : Summable (fun n : ℕ => 1 / (x - ((n : ℝ) + 1)) ^ 2) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      hreal.comp_injective (show Function.Injective Int.negSucc from @Int.negSucc.inj)
  have hposTail : Summable (fun n : ℕ => 1 / (x + ((n : ℝ) + 1)) ^ 2) := by
    simpa using (summable_nat_add_iff 1).mpr hpos
  refine ⟨hneg.add hposTail, ?_⟩
  have hsplit : (∑' m : ℤ, 1 / (x + (m : ℝ)) ^ 2) =
      1 / x ^ 2 + ∑' n : ℕ,
        (1 / (x - ((n : ℝ) + 1)) ^ 2 + 1 / (x + ((n : ℝ) + 1)) ^ 2) := by
    rw [tsum_of_nat_of_neg_add_one (by simpa using hpos)
      (by simpa [sub_eq_add_neg] using hneg)]
    simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one]
    rw [hpos.tsum_eq_zero_add, (hneg.tsum_add hposTail)]
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    simp only [sub_eq_add_neg]
    ring
  rw [← hsplit]
  exact hidentity

end Causalean.Stat.CLT.BerryEsseen
