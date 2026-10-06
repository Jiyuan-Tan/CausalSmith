module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# Finite count partition of a Poisson prefix integral

The integral over finite samples whose count is at most a fixed cap splits
into the integrals over its finitely many exact-count fibres.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- For [an iid observation law](hyp:ν), [a Poisson mean](hyp:lam), [a count cap](hyp:n), and
[an integrable statistic](hyp:g,hg), [the expectation with zero value above
the cap is the sum of exact-count fibre integrals](goal). -/
theorem poisson_nonoverflow_integral_eq_sum_count_fibres
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0) (n : ℕ)
    (g : FiniteSample Y → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw ν lam)) :
    (∫ z : FiniteSample Y,
      if z.count ≤ n then g z else 0
      ∂finitePoissonSampleLaw ν lam) =
    ∑ M : Fin (n + 1),
      ∫ z : FiniteSample Y in FiniteSample.count ⁻¹' ({M.val} : Set ℕ),
        g z ∂finitePoissonSampleLaw ν lam := by
  /- Rewrite the conditional integrand as the indicator of the measurable
  count-preimage of `Set.Iic n`; use `integral_indicator`. Identify that set
  with the union over `Fin (n + 1)` of the singleton count fibres. Apply
  Mathlib's `integral_iUnion_fintype` to these measurable, disjoint fibres;
  `hg.integrableOn` supplies each fibre's integrability. -/
  let s : Fin (n + 1) → Set (FiniteSample Y) :=
    fun M => FiniteSample.count ⁻¹' ({M.val} : Set ℕ)
  have hcap : MeasurableSet (FiniteSample.count ⁻¹' Set.Iic n : Set (FiniteSample Y)) :=
    measurable_finiteSample_count measurableSet_Iic
  have hunion : (FiniteSample.count ⁻¹' Set.Iic n : Set (FiniteSample Y)) =
      ⋃ M : Fin (n + 1), s M := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iUnion,
      Set.mem_singleton_iff, s]
    constructor
    · intro hz
      exact ⟨⟨z.count, Nat.lt_succ_of_le hz⟩, rfl⟩
    · rintro ⟨M, hM⟩
      rw [hM]
      exact Nat.le_of_lt_succ M.isLt
  have hs : ∀ M, MeasurableSet (s M) := by
    intro M
    exact measurable_finiteSample_count (measurableSet_singleton M.val)
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro a b hab
    change Disjoint (s a) (s b)
    rw [Set.disjoint_left]
    intro z hza hzb
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hza hzb
    apply hab
    apply Fin.ext
    exact hza.symm.trans hzb
  have hfi : ∀ M, IntegrableOn g (s M) (finitePoissonSampleLaw ν lam) := by
    intro M
    exact hg.integrableOn
  calc
    (∫ z : FiniteSample Y, if z.count ≤ n then g z else 0
      ∂finitePoissonSampleLaw ν lam) =
        ∫ z : FiniteSample Y,
          (FiniteSample.count ⁻¹' Set.Iic n : Set (FiniteSample Y)).indicator g z
          ∂finitePoissonSampleLaw ν lam := by
            congr 1
            funext z
            simp [Set.indicator, Set.mem_Iic]
    _ = ∫ z : FiniteSample Y in FiniteSample.count ⁻¹' Set.Iic n,
          g z ∂finitePoissonSampleLaw ν lam := integral_indicator hcap
    _ = ∫ z : FiniteSample Y in ⋃ M : Fin (n + 1), s M,
          g z ∂finitePoissonSampleLaw ν lam := by rw [hunion]
    _ = ∑ M : Fin (n + 1),
          ∫ z : FiniteSample Y in FiniteSample.count ⁻¹' ({M.val} : Set ℕ),
            g z ∂finitePoissonSampleLaw ν lam :=
      integral_iUnion_fintype hs hdisj hfi

end Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
