module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Definitions

/-!
# Finite and infinite Hölder seminorm bridges

The supremum definition is related to ordinary nonnegative increment bounds.
The headline theorem will split at infinity, never convert an infinite seminorm
to a real number and silently replace it by zero.
-/

public section

open scoped ENNReal
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- A [positive exponent](hyp:hγ) and [finite extended seminorm](hyp:hfinite)
give [the Hölder increment bound with its real value](goal).

Split equal points before dividing. For distinct points the distance power is
strictly positive, so extract the corresponding term from the iterated supremum.
-/
theorem hasHolderBound_seminorm {f : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hfinite : holderSeminorm f γ ≠ ⊤) :
    HasHolderBound f γ (holderSeminorm f γ).toReal := by
  intro x hx z hz
  by_cases heq : x = z
  · subst z
    simp [Real.zero_rpow hγ.ne']
  · have hdist : 0 < |x - z| ^ γ :=
      Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr heq)) _
    have hne : (⟨x, hx⟩ : Set.Icc (0 : ℝ) 1) ≠ ⟨z, hz⟩ :=
      fun h => heq (congrArg Subtype.val h)
    have hle : ENNReal.ofReal (|f x - f z| / |x - z| ^ γ) ≤ holderSeminorm f γ :=
      le_iSup_of_le ⟨x, hx⟩ (le_iSup_of_le ⟨z, hz⟩ (le_iSup_of_le hne le_rfl))
    exact (div_le_iff₀ hdist).mp ((ENNReal.ofReal_le_iff_le_toReal hfinite).mp hle)

/-- A [nonnegative constant](hyp:hH) satisfying [the Hölder increment
inequality](hyp:hf) at a [positive exponent](hyp:hγ) bounds
[the extended seminorm by that constant](goal). -/
theorem holderSeminorm_le_of_bound {f : ℝ → ℝ} {γ H : ℝ}
    (hγ : 0 < γ) (hH : 0 ≤ H) (hf : HasHolderBound f γ H) :
    holderSeminorm f γ ≤ ENNReal.ofReal H := by
  unfold holderSeminorm
  refine iSup_le fun x => iSup_le fun z => iSup_le fun hne => ?_
  have hdist : 0 < |(x : ℝ) - z| ^ γ :=
    Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr
      (fun h => hne (Subtype.ext h)))) _
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hdist).mpr
    (hf x x.property z z.property))

/-- At a [positive rank](hyp:hk), [the real power of that rank is positive](goal),
for every real exponent. -/
theorem rank_rpow_pos {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) :
    0 < (k : ℝ) ^ (-γ) := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)) _

/-- With [positive rank](hyp:hk), an [infinite Hölder seminorm](hyp:hseminorm)
makes [the required extended error inequality automatic](goal).

The rank factor is positive and finite, so multiplying the infinite seminorm
does not encounter the zero-times-infinity convention.
-/
theorem extended_bound_of_seminorm_top {f g : ℝ → ℝ} {γ : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hseminorm : holderSeminorm f γ = ⊤) :
    extendedL2Norm g ≤ 5 * holderSeminorm f γ * ENNReal.ofReal ((k : ℝ) ^ (-γ)) := by
  rw [hseminorm, ENNReal.mul_top (by norm_num),
    ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr (rank_rpow_pos hk γ)))]
  exact le_top

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

