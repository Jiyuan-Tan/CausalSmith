module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridArmRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPrefixCounts

/-!
Arm risk readback from independent ordered Poisson prefixes.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The unclipped arm sum computed from the three ordered histograms. -/
-- @node: hybridOrderedArmStatistic
noncomputable def hybridOrderedArmStatistic {d : Nat} (L : Nat) (B : Real)
    (k0 : Nat) (u t : Real) (a : Bool)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) : Real :=
  ∑ j : Fin d, hybridCellValue L B k0 u t
    (hybridPrefixCounts s (Sum.inl (j,a,true)))
    (hybridPrefixCounts s (Sum.inr (Sum.inl (j,a))))
    (hybridPrefixCounts s (Sum.inr (Sum.inr (j,a))))
    (hybridPrefixCounts s (Sum.inr (Sum.inr (j,!a))))

/-- Under the stated inputs and conditions, Applying the count-experiment theorem bounds each ordered-prefix arm's risk.  This gives [the stated result](goal). -/
-- @node: hybrid_ordered_prefix_arm_risk
lemma hybrid_ordered_prefix_arm_risk :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real) (P : DiscreteLaw d)
      (a : Bool) (u tp t : NNReal),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 → Real.exp 4096 ≤ (n : Real) * eps →
      ModelClass d eps P → (n : Real) / 32 ≤ (u : Real) →
      ((n : Real) + m) / 64 ≤ (tp : Real) →
      ((n : Real) + m) / 64 ≤ (t : Real) →
      1 / 3 ≤ (t : Real) / tp → (t : Real) / tp ≤ 3 →
      let L := Nat.floor (Real.log ((n : Real) * eps) / 1024)
      let B : Real := 2 ^ 20 * L / min (tp : Real) t
      let k0 := Nat.floor ((tp : Real) * B / 4)
      Causalean.Stat.sqRisk (hybridPoissonPrefixLaw P u tp t)
        (hybridOrderedArmStatistic L B k0 u t a)
        (∑ j : Fin d, cellMass P j * outcomeMean P a j) ≤
        C * (1 / ((n : Real) * eps) +
          ((d : Real) / (((n : Real) + m) * eps * L)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := uniform_hybrid_arm_risk
  refine ⟨C, hC, ?_⟩
  intro n m d eps P a u tp t hn hd heps heps4 hS hP hu htp ht hlo hhi
  dsimp only
  let Z := fun b j s => hybridPrefixCounts (d := d) s (Sum.inl (j,b,true))
  let J := fun b j s => hybridPrefixCounts (d := d) s (Sum.inr (Sum.inl (j,b)))
  let K := fun b j s => hybridPrefixCounts (d := d) s (Sum.inr (Sum.inr (j,b)))
  have hm (b j) : Measurable (Z b j) ∧ Measurable (J b j) ∧ Measurable (K b j) := by
    constructor
    · exact (measurable_pi_apply _).comp (hybridPrefixCounts_measurable d)
    · constructor <;> exact (measurable_pi_apply _).comp (hybridPrefixCounts_measurable d)
  have hZ (b j) : (hybridPoissonPrefixLaw P u tp t).map (Z b j) =
      poissonMeasure (Real.toNNReal ((u : Real) * markedMass P j b)) := by
    simpa only [Real.toNNReal_mul u.coe_nonneg, Real.toNNReal_coe] using
      hybrid_prefix_success_count_law P u tp t j b
  have hJ (b j) : (hybridPoissonPrefixLaw P u tp t).map (J b j) =
      poissonMeasure (Real.toNNReal ((tp : Real) * armMass P j b)) := by
    simpa only [Real.toNNReal_mul tp.coe_nonneg, Real.toNNReal_coe] using
      hybrid_prefix_pilot_count_law P u tp t j b
  have hK (b j) : (hybridPoissonPrefixLaw P u tp t).map (K b j) =
      poissonMeasure (Real.toNNReal ((t : Real) * armMass P j b)) := by
    simpa only [Real.toNNReal_mul t.coe_nonneg, Real.toNNReal_coe] using
      hybrid_prefix_factorial_count_law P u tp t j b
  have hi : iIndepFun (fun i : Fin 3 × Bool × Fin d =>
      if i.1 = 0 then Z i.2.1 i.2.2 else if i.1 = 1 then J i.2.1 i.2.2
      else K i.2.1 i.2.2) (hybridPoissonPrefixLaw P u tp t) := by
    convert hybrid_prefix_arm_counts_independent P u tp t using 1
    funext i s
    dsimp [Z,J,K]
    split_ifs <;> rfl
  exact hbound n m d eps P a u tp t hn hd heps heps4 hS hP hu htp ht hlo hhi
    _ (hybridPoissonPrefixLaw P u tp t) Z J K hm hZ hJ hK hi

end CausalSmith.Stat.AnnotationRarearmFrontier
