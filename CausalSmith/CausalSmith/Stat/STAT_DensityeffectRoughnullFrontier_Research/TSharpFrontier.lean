module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.TunedPilotAveraging
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.TCausalCompletion
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.TNonFlatSanity

/-!
The sharp full-class honest expected-length frontier at rough density equality, with explicit
observable attaining rule and endpoints.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


open Classical in
-- @node: thm:sharp-frontier
/-- A single total observable rule is honest at every finite sample size, ignores public
randomization, and attains the exact-null n^(-16/29) length frontier with universal two-sided
constants and the frozen explicit quadratic endpoints, uniformly over all equality densities. -/
theorem sharp_frontier :
    ∃ c C : ℝ, ∃ n0 : ℕ, 0 < c ∧ c ≤ C ∧ -- @realizes C(universal upper constant at least c)
    (∀ n, IsIntervalRule n (starRule n) ∧ IsHonest n (starRule n) ∧
      (∀ data : Data n, ∀ u up : ℝ, starRule n (data,u) = starRule n (data,up)) ∧
      (∀ ω : SampleSpace n, starRule n ω =
        if reportingBranch n then
          invEndpoints (tunedEnergy n ω.1) (aci (tunedB n) (tunedW n))
            (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))
        else Set.Icc 0 16)) ∧
    (∀ n, n0 ≤ n → c * frontierRate n ≤ honestLengthFrontier n ∧
      honestLengthFrontier n ≤ worstNullLength n (starRule n) ∧
      worstNullLength n (starRule n) ≤ C * frontierRate n) := by
  obtain ⟨c, hc, nLower, hLower⟩ := honestLengthFrontier_lower_rate
  obtain ⟨C, hC, nUpper, hUpper⟩ := starRule_worstNullLength_upper_rate
  refine ⟨c, C + c, max nLower nUpper, hc, by linarith, ?_, ?_⟩
  · intro n
    exact ⟨starRule_isIntervalRule n, starRule_isHonest n,
      starRule_data_only n, starRule_eq_endpoints n⟩
  · intro n hn
    refine ⟨hLower n ((le_max_left _ _).trans hn),
      honestLengthFrontier_le_rule n (starRule n) (starRule_isIntervalRule n)
        (starRule_isHonest n), ?_⟩
    apply (hUpper n ((le_max_right _ _).trans hn)).trans
    exact mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The explicit handle satisfies the normalized asymptotic minimax selection criterion. -/
lemma frontierHandle_attainsFrontierRate :
    AttainsFrontierRate (fun n => (frontierHandle n).1) (fun n => (frontierHandle n).2) := by
  obtain ⟨c, C, n0, hc, hcC, hRule, hBounds⟩ := sharp_frontier
  change AttainsFrontierRate frontierRate starRule
  refine ⟨?_, ?_, ?_, c, C, n0, hc, hcC, hBounds⟩
  · intro n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  · simp [frontierRate]
  · intro n
    exact ⟨(hRule n).1, (hRule n).2.1, (hRule n).2.2.1⟩

end CausalSmith.Stat.DensityEffectRoughNull
