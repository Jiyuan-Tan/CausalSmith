module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TPriorReduction
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.THonestInterval

/-!
# Exact honest connected-interval length frontier
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: thm:interval-frontier
/-- Fixed-coverage expected length is uniformly comparable to the square-root rate. [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). Given [the specified input `hα`](hyp:hα). -/
-- @realizes alpha(fixed noncoverage level in (0,1/2))
theorem interval_frontier (α : ℝ) (hα : α ∈ Set.Ioo 0 ((1 : ℝ) / 2)) :
    ∃ cα Cα : ℝ, 0 < cα ∧ cα < Cα ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
        q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
        cα * Real.sqrt (rate n d q) ≤ lengthMinimaxRisk n d q α ∧
        lengthMinimaxRisk n d q α ≤ Cα * Real.sqrt (rate n d q) := by
  obtain ⟨cPoint, c0, hcPoint, hc0, hprior⟩ := prior_reduction
  obtain ⟨CU, hCU⟩ := upper_risk
  obtain ⟨cInterval, c0α, hcInterval, hc0α, hbounds⟩ := hprior α hα
  let cα := cInterval
  let Cα := cInterval + 2 * Real.sqrt (CU / α) + 1
  refine ⟨cα, Cα, hcInterval, ?_, ?_⟩
  · have hs : 0 ≤ Real.sqrt (CU / α) := Real.sqrt_nonneg _
    dsimp [cα, Cα]
    linarith
  intro n d q hn hd hq
  have hrate : 0 ≤ rate n d q := by
    unfold rate
    positivity
  have hsqrt : 0 ≤ Real.sqrt (rate n d q) := Real.sqrt_nonneg _
  constructor
  · exact (hbounds n d q hn hd hq).2.2.2.2
  · have hconstruction := honest_interval_construction n d q α CU hn hd hq hα hCU
    let I : HonestIntervalClass n d q α :=
      ⟨intervalMM n d q α CU hCU, hconstruction.1⟩
    letI : Nonempty (ClassLaw d q) :=
      ⟨pairedClassLaw n d q 0 hn hd hq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)
        ⟨fun _ => Sum.inr (), fun _ => false⟩⟩
    have hsup : (⨆ P : ClassLaw d q,
        ∫ o, (I.val.hi o - I.val.lo o) ∂ samplePi P.val n) ≤
        min 2 (2 * Real.sqrt (CU * rate n d q / α)) := by
      apply ciSup_le
      intro P
      exact hconstruction.2.2.2.1 P
    have hmin : min 2 (2 * Real.sqrt (CU * rate n d q / α)) ≤
        2 * Real.sqrt (CU / α) * Real.sqrt (rate n d q) := by
      have heq : CU * rate n d q / α = (CU / α) * rate n d q := by ring
      rw [heq, Real.sqrt_mul (div_nonneg (le_of_lt hCU.1) (le_of_lt hα.1))]
      calc
        min 2 (2 * (Real.sqrt (CU / α) * Real.sqrt (rate n d q))) ≤
            2 * (Real.sqrt (CU / α) * Real.sqrt (rate n d q)) := min_le_right _ _
        _ = 2 * Real.sqrt (CU / α) * Real.sqrt (rate n d q) := by ring
    have hupper : 2 * Real.sqrt (CU / α) * Real.sqrt (rate n d q) ≤
        Cα * Real.sqrt (rate n d q) := by
      apply mul_le_mul_of_nonneg_right _ hsqrt
      dsimp [Cα]
      linarith [hcInterval]
    calc
      lengthMinimaxRisk n d q α ≤
          (⨆ P : ClassLaw d q,
            ∫ o, (I.val.hi o - I.val.lo o) ∂ samplePi P.val n) := by
        unfold lengthMinimaxRisk
        exact ciInf_le (by
          refine ⟨0, ?_⟩
          rintro y ⟨I', rfl⟩
          by_cases hb : BddAbove (Set.range fun P : ClassLaw d q =>
              ∫ o, (I'.val.hi o - I'.val.lo o) ∂ samplePi P.val n)
          · let P0 : ClassLaw d q := pairedClassLaw n d q 0 hn hd hq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)
                ⟨fun _ => Sum.inr (), fun _ => false⟩
            exact le_ciSup_of_le hb P0 (integral_nonneg (fun o =>
              sub_nonneg.mpr (I'.val.bounds o).2.1))
          · change 0 ≤ ⨆ P : ClassLaw d q,
                ∫ o, (I'.val.hi o - I'.val.lo o) ∂ samplePi P.val n
            rw [ciSup_of_not_bddAbove hb]
            simp) I
      _ ≤ min 2 (2 * Real.sqrt (CU * rate n d q / α)) := hsup
      _ ≤ 2 * Real.sqrt (CU / α) * Real.sqrt (rate n d q) := hmin
      _ ≤ Cα * Real.sqrt (rate n d q) := hupper

end CausalSmith.Stat.MarNearcompleteFrontier
