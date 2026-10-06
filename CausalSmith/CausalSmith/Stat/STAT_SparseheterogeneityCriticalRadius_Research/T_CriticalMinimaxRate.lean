module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.T_KnownRadiusMinimaxFrontier

/-! The critical-radius specialization and strict rate comparisons. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Filter
open scoped Topology

-- @node: thm:critical-minimax-rate
theorem critical_minimax_rate :
    (∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ n M, 3 ≤ n → 1 ≤ M →
      -- @realizes c(universal lower constant) @realizes C(universal upper constant)
      c * M ^ 2 * rateCrit n ≤
        knownRadiusMinimaxRisk n M (criticalRadius n) ∧
      knownRadiusMinimaxRisk n M (criticalRadius n) ≤
        worstRisk n M (criticalRadius n) (criticalEstimator n M) ∧
      worstRisk n M (criticalRadius n) (criticalEstimator n M) ≤
        C * M ^ 2 * rateCrit n) ∧
    Tendsto (fun n : ℕ =>
      rateCrit n /
        (DiscreteAteHeterogeneityFrontier.logEN n ^ 2 / (n : ℝ)))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => rateCrit n * (n : ℝ)) atTop atTop := by
  obtain ⟨c, C, hc, hcC, hfront, _, _, _, hlarge⟩ :=
    known_radius_minimax_frontier (fun n P => rfl)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => benchmarkLog n) atTop atTop := by
    have hlogNat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hnat
    have h := Filter.tendsto_atTop_add_const_left atTop (f := fun n : ℕ =>
      Real.log (n : ℝ)) (1 : ℝ) hlogNat
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [benchmarkLog, DiscreteAteHeterogeneityFrontier.logEN]
    rw [Real.log_mul (Real.exp_ne_zero 1) hn0, Real.log_exp]
  have hlogSq : Tendsto (fun n : ℕ => benchmarkLog n ^ 2) atTop atTop :=
    by simpa [pow_two] using Filter.Tendsto.atTop_mul_atTop₀ hlog hlog
  have hH : Tendsto (fun n : ℕ => Hcrit n) atTop atTop := by
    have hsum := Filter.tendsto_atTop_add_const_left atTop
      (f := fun n : ℕ => benchmarkLog n ^ 2) (Real.exp 1) hlogSq
    exact Real.tendsto_log_atTop.comp hsum
  have hratio : Tendsto (fun n : ℕ => benchmarkLog n ^ 2 /
      Hcrit n ^ 2) atTop atTop := by
    simpa only [Hcrit, Function.comp_def] using hlarge.comp hlogSq
  have hfirst : Tendsto (fun n : ℕ => rateCrit n /
      (benchmarkLog n ^ 2 / (n : ℝ))) atTop (𝓝 0) := by
    have hHSq : Tendsto (fun n : ℕ => Hcrit n ^ 2) atTop atTop := by
      simpa [pow_two] using Filter.Tendsto.atTop_mul_atTop₀ hH hH
    have h1 := (hlogSq.inv_tendsto_atTop).add
      (hHSq.inv_tendsto_atTop)
    have h1' : Tendsto (fun n : ℕ =>
        1 / benchmarkLog n ^ 2 + 1 / Hcrit n ^ 2) atTop (𝓝 0) := by
      simpa [one_div] using h1
    apply h1'.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hL : benchmarkLog n ≠ 0 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hlog0 := Real.log_nonneg hn1
      have hb : benchmarkLog n = 1 + Real.log (n : ℝ) := by
        unfold benchmarkLog DiscreteAteHeterogeneityFrontier.logEN
        rw [Real.log_mul (Real.exp_ne_zero 1) hn0, Real.log_exp]
      rw [hb]
      linarith
    simp only [rateCrit]
    field_simp
  have hsecond : Tendsto (fun n : ℕ => rateCrit n * (n : ℝ))
      atTop atTop := by
    have h := Filter.tendsto_atTop_add_const_left atTop (f := fun n : ℕ =>
      benchmarkLog n ^ 2 / Hcrit n ^ 2) (1 : ℝ) hratio
    apply h.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [rateCrit]
    field_simp
  refine ⟨?_, ?_, hsecond⟩
  · refine ⟨c, C, hc, hcC, ?_⟩
    intro n M hn hM
    have hrange := criticalRadius_range n hn
    have hrate := rate_critical_identity n (by omega)
    have hf := hfront n M (criticalRadius n) hn hM hrange.1 hrange.2
    rw [← hrate]
    simpa only [criticalEstimator] using ⟨hf.1, hf.2.1, hf.2.2.1⟩
  · simpa only [benchmarkLog] using hfirst

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
