module
public import Causalean.Stat.EmpiricalProcess.Countable.ChainUnion
public import Causalean.Stat.EmpiricalProcess.Countable.CoverSupremum
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteAverage
public import Causalean.Stat.EmpiricalProcess.Countable.Ghost
public import Causalean.Stat.EmpiricalProcess.Countable.NestedChain
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# From countable symmetrization to chain energy budgets

A bounded class can be partitioned into finitely many nested weighted
indicator branches with cutoff-independent weights on each branch. The
fourth power of its signed supremum is bounded by the sum of branch fourth
powers, so no extra cube of the number of branches is necessary.

The final constant is 16*(256/27)=4096/27, followed by normalization by the
fourth power of sample size and the sum of branch energy budgets. A five-branch
specialization records the corresponding explicit arithmetic constant.
-/

public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- For [a nonempty countable bounded class](hyp:F) with [a finite nested
chain cover](hyp:cover) and [any sample of size n](hyp:x), [the sign
average of the fourth power of the signed supremum is at most 256/27
divided by n^4 times the sum over branches of the squared branch
energies](goal). -/
theorem signedSup_fourth_le_coverEnergy {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [Nonempty ι] (F : BoundedClass Ω ι) {m : ℕ}
    (cover : ChainCover F m) {n : ℕ} (x : Fin n → Ω) :
    signAverage (fun σ => signedSup F.f x σ ^ 4) ≤
      ((256 / 27 : ℝ) / (n : ℝ)^4) * ∑ b, coverEnergy cover x b ^ 2 := by
  have hbranch (b : Fin m) :
      signAverage (fun σ => branchSignSup cover x σ b ^ 4) ≤
        (256 / 27 : ℝ) * coverEnergy cover x b ^ 2 := by
    apply nested_chain_fourth_le_energy
      (fun i : {i : ι // cover.branch i = b} => cover.sets i.1)
      (fun i k => cover.nested i.1 k.1 (i.2.trans k.2.symm))
      (cover.containing b)
    intro i
    simpa only [i.2] using cover.subset_containing i.1
  calc
    _ ≤ (n : ℝ)⁻¹ ^ 4 *
        ∑ b, signAverage (fun σ => branchSignSup cover x σ b ^ 4) :=
      signedSup_fourth_le_chainAverages F cover x
    _ ≤ (n : ℝ)⁻¹ ^ 4 * ∑ b, (256 / 27 : ℝ) * coverEnergy cover x b ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hbranch b))
        (by positivity)
    _ = _ := by rw [← Finset.mul_sum, inv_pow]; ring

/-- Let [a nonempty countable bounded class](hyp:F) have [a finite nested
chain cover](hyp:cover), let the sample consist of [n](hyp:n) independent
draws from [a probability measure μ](hyp:μ) with [n positive](hyp:hn), and
suppose [each squared branch energy is integrable under the sample
law](hyp:henergy). Then [the fourth moment of the centered supremum is at
most 4096/27 divided by n^4 times the sum over branches of the expected
squared branch energies](goal). -/
theorem centered_fourth_le_coverEnergy {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : BoundedClass Ω ι) {m : ℕ} (cover : ChainCover F m) (n : ℕ) (hn : 0 < n)
    (henergy : ∀ b, Integrable (fun x : Fin n → Ω => coverEnergy cover x b ^ 2)
      (Measure.pi (fun _ : Fin n => μ))) :
    (∫ x, centeredSup μ F.f x ^ 4 ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ((4096 / 27 : ℝ) / (n : ℝ)^4) *
        ∑ b, ∫ x : Fin n → Ω, coverEnergy cover x b ^ 2
          ∂Measure.pi (fun _ : Fin n => μ) := by
  have hlegal := (signedSup_legal μ F n).2.2
  have hright : Integrable (fun x : Fin n → Ω =>
      ((256 / 27 : ℝ) / (n : ℝ)^4) * ∑ b, coverEnergy cover x b ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) :=
    (integrable_finsetSum _ (fun b _ => henergy b)).const_mul _
  have hbound := integral_mono hlegal hright
    (fun x => signedSup_fourth_le_coverEnergy F cover x)
  rw [integral_const_mul, integral_finsetSum _ (fun b _ => henergy b)] at hbound
  calc
    _ ≤ 16 * ∫ x, signAverage (fun σ => signedSup F.f x σ ^ 4)
        ∂Measure.pi (fun _ : Fin n => μ) := centered_fourth_le_rademacher μ F n hn
    _ ≤ 16 * (((256 / 27 : ℝ) / (n : ℝ)^4) *
        ∑ b, ∫ x : Fin n → Ω, coverEnergy cover x b ^ 2
          ∂Measure.pi (fun _ : Fin n => μ)) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

/-- Let [a nonempty countable bounded class](hyp:F) have [a finite nested
chain cover](hyp:cover), let the sample consist of [n](hyp:n) independent
draws from [a probability measure μ](hyp:μ) with [n positive](hyp:hn), and
suppose [each squared branch energy is integrable under the sample
law](hyp:henergy) with [expectation at most](hyp:hbudget) [a branch
budget](hyp:budget). Then [the fourth moment of the centered supremum is at
most 4096/27 divided by n^4 times the sum of the budgets](goal). -/
theorem centered_fourth_le_energy_budget {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : BoundedClass Ω ι) {m : ℕ} (cover : ChainCover F m) (n : ℕ) (hn : 0 < n)
    (henergy : ∀ b, Integrable (fun x : Fin n → Ω => coverEnergy cover x b ^ 2)
      (Measure.pi (fun _ : Fin n => μ))) (budget : Fin m → ℝ)
    (hbudget : ∀ b, (∫ x : Fin n → Ω, coverEnergy cover x b ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ budget b) :
    (∫ x, centeredSup μ F.f x ^ 4 ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ((4096 / 27 : ℝ) / (n : ℝ)^4) * ∑ b, budget b := by
  exact (centered_fourth_le_coverEnergy μ F cover n hn henergy).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hbudget b))
      (by positivity))

/-- For [a positive sample size n](hyp:n,hn), [a positive clipping level
a](hyp:a,ha), and [a nonnegative radius z](hyp:z,hz), [4096/27 divided by
n^4, times five budgets each equal to 24 n z / a^3 + 36 n^2 z^2 / a^2, is
at most 81920/3 times (z^2 / (n^2 a^2) + z / (n^3 a^3))](goal).

This is the arithmetic of the five-branch localized rate after
symmetrization.
-/
theorem five_branch_budget_arithmetic (n a z : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hz : 0 ≤ z) :
    ((4096 / 27 : ℝ) / n ^ 4) *
        (5 * (24 * n * z / a ^ 3 + 36 * n ^ 2 * z ^ 2 / a ^ 2)) ≤
      (81920 / 3 : ℝ) * (z ^ 2 / (n ^ 2 * a ^ 2) + z / (n ^ 3 * a ^ 3)) := by
  have hzterm : 0 ≤ z / (n ^ 3 * a ^ 3) := by positivity
  calc
    _ = (81920 / 3 : ℝ) * (z ^ 2 / (n ^ 2 * a ^ 2)) +
        (163840 / 9 : ℝ) * (z / (n ^ 3 * a ^ 3)) := by
      field_simp [ne_of_gt hn, ne_of_gt ha]
      ring
    _ ≤ _ := by nlinarith

end Causalean.Stat.EmpiricalProcess.Countable
