import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.HitFactorization
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Integral.Prod
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT
import Causalean.Stat.Limit.ConvergenceVec
import Causalean.Stat.Limit.Convergence
import Causalean.Mathlib.MeasureTheory.IntegralBind

set_option linter.style.openClassical false

/-!
# Schedule-law/randomization bridge

This local helper keeps the finite randomization sum inside an integral over the
continuum schedule law, states the exact slice variance decomposition, and gives
the finite-fibre conditional-to-unconditional weak-limit transfer used by CR.
-/

open scoped BigOperators ENNReal
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- Weak convergence tested against bounded continuous real functions. -/
def WeaklyConverges {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (mu : ℕ → Measure E) (limit : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
    Tendsto (fun N => ∫ x, f x ∂(mu N)) atTop (nhds (∫ x, f x ∂limit))

/-- The paper-owned bridge between schedule integration and finite randomization. -/
-- @node: schedule_law_variance_bridge
lemma schedule_law_variance_bridge {n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (p : Fin K → ℝ) (m : Fin K → ℕ)
    (f : Record K n → ℝ)
    (condLaw : (Fin K → ℕ) → ℕ → Measure (Fin K → ℝ))
    (uncondLaw : ℕ → Measure (Fin K → ℝ)) (limit : Measure (Fin K → ℝ))
    (counts : ℕ → Fin K → ℕ)
    (h_uncondLaw : ∀ N, uncondLaw N = condLaw (counts N) N)
    (hmenu : WellFormedMenu n K m) (hp : ∀ l, 0 ≤ p l)
    (hkernel : Measurable (fun Y : Schedule n => ∑ l, ENNReal.ofReal (p l) •
      ∑ z, ENNReal.ofReal (assignmentMass (saturation n m l) z) •
        Measure.dirac (l, z, Y z)))
    (hf : Integrable f (bernoulliObservedLaw P p m)) :
    (∫ o, f o ∂(bernoulliObservedLaw P p m)) =
      ∫ Y, ∑ l, p l * ∑ z, assignmentMass (saturation n m l) z *
        f (l, z, Y z) ∂P ∧
    (∀ k, rawSliceVariance P m k =
      sliceVariance P (m k) + betweenAssignmentVariance P m k) ∧
    (WeaklyConverges (fun N => condLaw (counts N) N) limit →
      WeaklyConverges uncondLaw limit) := by
  refine ⟨?_, fun k => rfl, ?_⟩
  · rw [bernoulliObservedLaw,
      Causalean.Mathlib.MeasureTheory.integral_bind hkernel hf]
    apply integral_congr_ae
    filter_upwards [] with Y
    have hmass : ∀ l (z : Assignment n), 0 ≤ assignmentMass (saturation n m l) z := by
      intro l z
      have hs : saturation n m l ∈ Set.Icc (0 : ℝ) 1 := by
        have hn4 : 4 ≤ n := hmenu.1
        have hnNat : 0 < n := by omega
        have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
        constructor
        · unfold saturation
          positivity
        · unfold saturation
          rw [div_le_one hnReal]
          have hmUpper := (hmenu.2.2.2.1 l).2
          have hmn : m l ≤ n := by omega
          exact_mod_cast hmn
      unfold assignmentMass
      exact Finset.prod_nonneg fun j _ => by
        split <;> linarith [hs.1, hs.2]
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [integral_smul_measure, integral_finsetSum_measure]
      · simp [hp, hmass, Finset.mul_sum]
      · intro z hz
        exact (integrable_dirac (by simp)).smul_measure (by finiteness)
    · intro l hl
      exact (integrable_finsetSum_measure.2 (fun z _ =>
        (integrable_dirac (by simp)).smul_measure (by finiteness))).smul_measure
          (by finiteness)
  · intro h g hg hgb
    simp_rw [h_uncondLaw]
    exact h g hg hgb

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
