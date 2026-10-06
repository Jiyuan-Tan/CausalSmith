module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerDirectionDefs
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Concrete smooth cutoffs for the minimax lower bound

This module constructs the smooth bump and one-sided transition functions
required by the endpoint and critical lower-bound directions.
-/

public section

open Set
open scoped ContDiff

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Every admissible collection of class constants admits smooth cutoff data
for the endpoint and critical minimax directions. -/
lemma nonempty_cutoffData (c : ClassConstants) : Nonempty (CutoffData c) := by
  let bump : ℝ → ℝ := fun t =>
    Real.smoothTransition (4 * t - 1) * Real.smoothTransition (3 - 4 * t)
  let chi : ℝ → ℝ := fun t => Real.smoothTransition (t - 1)
  let psiCore : ℝ → ℝ := fun t => Real.smoothTransition (2 - 4 * t / c.x0)
  let psi : ℝ → ℝ := fun t => if 0 ≤ t then psiCore t else 0
  have hbumpSmooth : ContDiff ℝ ∞ bump := by
    dsimp only [bump]
    fun_prop
  have hchiSmooth : ContDiff ℝ ∞ chi := by
    dsimp only [chi]
    fun_prop
  have hpsiCoreSmooth : ContDiff ℝ ∞ psiCore := by
    dsimp only [psiCore]
    fun_prop
  have hpsiEq : Set.EqOn psi psiCore (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact if_pos ht
  refine ⟨⟨bump, chi, psi, hbumpSmooth, ?_, ?_, ?_, ?_,
    hchiSmooth.contDiffOn, ?_, ?_, hpsiCoreSmooth.contDiffOn.congr hpsiEq, ?_, ?_, ?_⟩⟩
  · intro t
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · refine ⟨1 / 2, ?_⟩
    norm_num [bump, Real.smoothTransition.one]
  · intro t ht
    have hne := mul_ne_zero_iff.mp ht
    have hleft : 0 < 4 * t - 1 :=
      lt_of_not_ge (Real.smoothTransition.zero_iff_nonpos.not.mp hne.1)
    have hright : 0 < 3 - 4 * t :=
      lt_of_not_ge (Real.smoothTransition.zero_iff_nonpos.not.mp hne.2)
    constructor <;> linarith
  · refine ⟨1 / 4, 3 / 4, by norm_num, by norm_num, ?_⟩
    intro t ht
    have hne := mul_ne_zero_iff.mp ht
    have hleft : 0 < 4 * t - 1 :=
      lt_of_not_ge (Real.smoothTransition.zero_iff_nonpos.not.mp hne.1)
    have hright : 0 < 3 - 4 * t :=
      lt_of_not_ge (Real.smoothTransition.zero_iff_nonpos.not.mp hne.2)
    constructor <;> linarith
  · intro t ht
    dsimp only [chi]
    apply Real.smoothTransition.zero_of_nonpos
    linarith [ht.2]
  · intro t ht
    dsimp only [chi]
    apply Real.smoothTransition.one_of_one_le
    linarith
  · intro t ht
    have ht0 : 0 ≤ t := by
      by_contra h
      apply ht
      exact if_neg h
    have hcoreNe : psiCore t ≠ 0 := by simpa [psi, ht0] using ht
    have harg : 0 < 2 - 4 * t / c.x0 := lt_of_not_ge
      (Real.smoothTransition.zero_iff_nonpos.not.mp (by
        simpa only [psiCore] using hcoreNe))
    have hratio : 4 * t / c.x0 < 2 := by linarith
    have hmul : 4 * t < 2 * c.x0 := (div_lt_iff₀ c.x0_pos).mp hratio
    exact ⟨ht0, by linarith [c.x0_pos]⟩
  · refine ⟨c.x0 / 2, by linarith [c.x0_pos], ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := by
      by_contra h
      apply ht
      exact if_neg h
    have hcoreNe : psiCore t ≠ 0 := by simpa [psi, ht0] using ht
    have harg : 0 < 2 - 4 * t / c.x0 := lt_of_not_ge
      (Real.smoothTransition.zero_iff_nonpos.not.mp (by
        simpa only [psiCore] using hcoreNe))
    have hratio : 4 * t / c.x0 < 2 := by linarith
    have hmul : 4 * t < 2 * c.x0 := (div_lt_iff₀ c.x0_pos).mp hratio
    exact ⟨ht0, by linarith⟩
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    rw [show psi t = psiCore t from if_pos ht0]
    dsimp only [psiCore]
    apply Real.smoothTransition.one_of_one_le
    have hmul : 4 * t ≤ c.x0 := by linarith [ht.2]
    have hratio : 4 * t / c.x0 ≤ 1 := (div_le_one c.x0_pos).2 hmul
    linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
