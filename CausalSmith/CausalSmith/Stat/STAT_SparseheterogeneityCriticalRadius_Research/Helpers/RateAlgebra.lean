module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Basic

/-! Helpers/RateAlgebra.lean; scaffold of the indicated proof chain. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

lemma criticalRadius_range (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ criticalRadius n ∧ criticalRadius n ≤ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hs_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs_one : 1 ≤ Real.sqrt (n : ℝ) := by
    nlinarith [hs_sq]
  have hlogn : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) - 2 := by
    have h := Real.log_le_sub_one_of_pos hspos
    rw [Real.log_sqrt hnpos.le] at h
    linarith
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hb : benchmarkLog n = 1 + Real.log (n : ℝ) := by
    unfold benchmarkLog DiscreteAteHeterogeneityFrontier.logEN
    rw [Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
  rw [criticalRadius, hb]
  constructor
  · exact div_nonneg (by linarith) hspos.le
  · apply (div_le_iff₀ hspos).2
    linarith

lemma rate_critical_identity (n : ℕ) (hn : 0 < n) :
    rate n (criticalRadius n) = rateCrit n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  simp only [rate, rateCrit, Hrho, Hcrit, criticalRadius, div_pow, hsqrt]
  have hcancel : (n : ℝ) * (benchmarkLog n ^ 2 / (n : ℝ)) = benchmarkLog n ^ 2 := by
    field_simp
  rw [hcancel]
  ring

lemma rate_zero (n : ℕ) : rate n 0 = 1 / (n : ℝ) := by
  simp [rate]

lemma rate_two (n : ℕ) :
    rate n 2 = 1 / (n : ℝ) + 4 / (Real.log (Real.exp 1 + 4 * n)) ^ 2 := by
  simp only [rate, Hrho]
  norm_num [mul_comm]

-- @node: radius_two_vacuous
lemma radius_two_vacuous {n : ℕ} {M : ℝ} (P : Law n)
    (hmean : MeanEnvelope M P) :
    DiscreteAteHeterogeneityFrontier.ApproximateHomogeneity M 2 P := by
  let τ := DiscreteAteHeterogeneityFrontier.rawAteFormula P
  have heffect (k : Fin n) (hk : 0 < P.cellMass k) :
      |DiscreteAteHeterogeneityFrontier.cellEffect P k| ≤ M := by
    have h₀ := hmean false k hk
    have h₁ := hmean true k hk
    unfold DiscreteAteHeterogeneityFrontier.cellEffect
    exact (abs_sub _ _).trans (by linarith)
  have hterm (k : Fin n) :
      |P.cellMass k * DiscreteAteHeterogeneityFrontier.cellEffect P k| ≤
        P.cellMass k * M := by
    have hp := (P.cellMass_range k).1
    by_cases hk : 0 < P.cellMass k
    · rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (heffect k hk) hp
    · have hz : P.cellMass k = 0 := le_antisymm (le_of_not_gt hk) hp
      simp [hz]
  have hτ : |τ| ≤ M := by
    change |∑ k : Fin n, P.cellMass k *
      DiscreteAteHeterogeneityFrontier.cellEffect P k| ≤ M
    calc
      _ ≤ ∑ k : Fin n, |P.cellMass k *
          DiscreteAteHeterogeneityFrontier.cellEffect P k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin n, P.cellMass k * M := Finset.sum_le_sum (by
        intro k hk
        exact hterm k)
      _ = M := by rw [← Finset.sum_mul, DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]; ring
  intro k hk
  change |DiscreteAteHeterogeneityFrontier.cellEffect P k - τ| ≤ 2 * M
  exact (abs_sub _ _).trans (by linarith [heffect k hk])

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
