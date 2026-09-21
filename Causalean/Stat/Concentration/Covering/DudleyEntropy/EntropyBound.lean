module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.RiemannIntegral

/-!
# Dudley entropy-integral bound

This file assembles the finite-chain and Riemann-integral estimates into
`dudley_entropy_integral_bound`, the signed empirical Rademacher bound for a
totally bounded function class at a positive truncation scale.
-/

public section

namespace Causalean.Stat.Concentration

universe v u
open scoped BigOperators
open ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

variable {c : ℝ}
/-- **Dudley entropy-integral bound, without the outer absolute value.** Fix
[a positive scale ε](hyp:ε_pos) that is [strictly less than half the common
empirical-norm envelope c](hyp:ε_le_c_div_2), where [the sample size m is
positive](hyp:m_pos), [every member of the class has empirical norm on the
sample at most c](hyp:cs), and [the sample-restricted function class is
totally bounded in the empirical pseudometric](hyp:h'). Then [the empirical
Rademacher complexity computed without the outer absolute value is at most
`4ε + (12/√m) ∫_ε^(c/2) √(log(coveringNumber' x)) dx`, the usual Dudley
chaining bound in terms of the covering-number entropy integral](goal). -/
theorem dudley_entropy_integral_bound {ε : ℝ} (ε_pos : 0 < ε) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
  (ε_le_c_div_2 : ε < c/2) :
    empiricalRademacherComplexity_without_abs m F S ≤
    (4 * ε + (12 / (Real.sqrt m)) *
    (∫ (x : ℝ) in ε..(c/2),√(Real.log (coveringNumber' h' x)))) := by
  obtain ⟨n, ⟨nw1, nw2⟩⟩ := choose_dyadic_scale_for_epsilon ε ε_pos ε_le_c_div_2
  have ε_c : ε ≤ c := by linarith
  have c_pos : 0 < c := lt_of_le_of_lt' ε_c ε_pos
  apply le_trans (entropy_sum_to_integral_bound c_pos h' n m_pos cs)
  apply add_le_add
  · linarith
  · apply mul_le_mul_of_nonneg_left
    · apply intervalIntegral.integral_mono_interval (le_of_lt nw1)
      · dsimp [ej]
        rw [div_le_div_iff_of_pos_left]
        · have := Nat.one_lt_two_pow' n
          rw [<- Nat.add_one_le_iff] at this
          simp only [Nat.reduceAdd] at this
          norm_cast
        · exact c_pos
        · simp
        · simp
      · simp
      · filter_upwards
        intro a
        simp
      · apply AntitoneOn.intervalIntegrable
        have f0 : Monotone (fun x ↦ √x) := by apply Real.sqrt_le_sqrt
        apply Monotone.comp_antitoneOn f0
        refine antitoneOn_iff_forall_lt.mpr ?_
        intro a ha b hb hab
        dsimp [Set.uIcc] at ha
        dsimp [Set.Icc] at ha
        have : min ε (c / 2) = ε := by
          simp
          linarith
        rw [this] at ha
        dsimp [Set.uIcc] at hb
        dsimp [Set.Icc] at hb
        rw [this] at hb
        apply Real.log_le_log
        · apply Nat.cast_pos.mpr
          apply coveringNumber'_nonzero
          · exact e_nonempty
          linarith
        · norm_cast
          apply coveringNumber'_antitone
          · simp
            linarith
          · simp
            linarith
          · exact le_of_lt hab
    · refine div_nonneg ?_ ?_
      · simp
      · norm_cast
        simp



end Empirical
end Causalean.Stat.Concentration
