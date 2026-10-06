module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerTransfer
public import Mathlib.Topology.Order.Basic

/-! # Uniform consistency from the risk frontier

The final paragraph of the weighted-separation roadmap reduces uniform consistency
 to convergence of the uncapped rate. These helpers prove that reduction from
 two-sided risk bounds; they do not assert the still-open bounds themselves. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open Filter
open scoped Topology


-- @node: cappedRate_tendsto_zero_iff
/-- Capping a nonnegative sequence at one preserves convergence to zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr), the [stated conclusion](goal) holds. -/
lemma cappedRate_tendsto_zero_iff {ι : Type*} {l : Filter ι}
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    Tendsto (fun i => min 1 (r i)) l (𝓝 0) ↔ Tendsto r l (𝓝 0) := by
  constructor
  · intro h
    have he : ∀ᶠ i in l, min 1 (r i) < 1 :=
      (tendsto_order.mp h).2 1 (by norm_num)
    apply h.congr'
    filter_upwards [he] with i hi
    by_cases hri : r i ≤ 1
    · exact min_eq_right hri
    · rw [min_eq_left (le_of_not_ge hri)] at hi
      exact (lt_irrefl (1 : ℝ) hi).elim
  · intro h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun i => le_min (by norm_num) (hr i)) (fun i => min_le_right _ _)


-- @node: rateScale_nonneg
/-- The rate is nonnegative, including the zero-sample convention for division. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε), the [stated conclusion](goal) holds. -/
lemma rateScale_nonneg {n d : ℕ} {ε : ℝ} (hd : 1 ≤ d) (hε : 0 ≤ ε) :
    0 ≤ rateScale n d ε := by
  exact le_min (by norm_num)
    (div_nonneg (Nat.cast_nonneg d)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hε) (logAlphabet_pos hd).le))


-- @node: rateScale_tendsto_zero_iff
/-- The capped paper rate vanishes exactly when its uncapped ratio vanishes. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε), the [stated conclusion](goal) holds. -/
lemma rateScale_tendsto_zero_iff (N d : ℕ → ℕ) (ε : ℕ → ℝ)
    (hd : ∀ k, 1 ≤ d k) (hε : ∀ k, 0 ≤ ε k) :
    Tendsto (fun k => rateScale (N k) (d k) (ε k)) atTop (𝓝 0) ↔
      Tendsto (fun k => (d k : ℝ) /
        ((N k : ℝ) * ε k * logAlphabet (d k))) atTop (𝓝 0) := by
  apply cappedRate_tendsto_zero_iff
  intro k
  exact div_nonneg (Nat.cast_nonneg (d k))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg (N k)) (hε k))
      (logAlphabet_pos (hd k)).le)


-- @node: observedWorstRisk_nonneg
/-- Worst-case squared observed risk is nonnegative without a boundedness assumption. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedWorstRisk_nonneg {n d : ℕ} {ε : ℝ} (est : Estimator n d) :
    0 ≤ Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est := by
  exact Causalean.Stat.worstCaseRisk_nonneg (observedRisk_nonneg est)


-- @node: minimaxRisk_le_observedWorstRisk
/-- Every admissible estimator has worst-case risk at least the minimax value. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma minimaxRisk_le_observedWorstRisk {n d : ℕ} {ε : ℝ} (est : Estimator n d) :
    minimaxRisk n d ε ≤
      Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est := by
  exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (fun e P => observedRisk_nonneg e P) est


-- @node: uniformConsistency_iff_of_frontier
/-- Once the uniform lower bound and the explicit estimator's upper bound are proved, their risk sandwich gives the roadmap's exact triangular consistency criterion. The bounds are inputs to this assembly lemma, not new model assumptions. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hc,hH₀,hκ,hD₀,hlower,hupper,hN,hlegal), the [stated conclusion](goal) holds. -/
lemma uniformConsistency_iff_of_frontier
    (c C H₀ κ : ℝ) (D₀ : ℕ) (hc : 0 < c)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (hlower : ∀ n d ε, 1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
      c * rateScale n d ε ≤ minimaxRisk n d ε)
    (hupper : ∀ n d ε, 1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
      armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ≤ C * rateScale n d ε)
    (N d : ℕ → ℕ) (ε : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hlegal : ∀ k, 2 ≤ d k ∧ 0 < ε k ∧ ε k ≤ 1 / 2) :
    ((∃ est : ∀ k, Estimator (N k) (d k),
      Tendsto (fun k => Causalean.Stat.worstCaseRiskReal
        (observedRisk (N k) (d := d k) (ε := ε k)) (est k)) atTop (𝓝 0)) ↔
      Tendsto (fun k => (d k : ℝ) /
        ((N k : ℝ) * ε k * logAlphabet (d k))) atTop (𝓝 0)) := by
  have hn : ∀ᶠ k in atTop, 1 ≤ N k := hN.eventually (eventually_ge_atTop 1)
  have hrate := rateScale_tendsto_zero_iff N d ε
    (fun k => le_trans (by norm_num) (hlegal k).1) (fun k => (hlegal k).2.1.le)
  constructor
  · rintro ⟨est, hest⟩
    apply hrate.mp
    have hdiv : Tendsto (fun k => Causalean.Stat.worstCaseRiskReal
        (observedRisk (N k) (d := d k) (ε := ε k)) (est k) / c) atTop (𝓝 0) := by
      simpa using hest.div_const c
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
    · exact Filter.Eventually.of_forall fun k =>
        rateScale_nonneg (le_trans (by norm_num) (hlegal k).1) (hlegal k).2.1.le
    · filter_upwards [hn] with k hk
      apply (le_div_iff₀ hc).2
      rw [mul_comm]
      exact (hlower _ _ _ hk (hlegal k).1 (hlegal k).2.1 (hlegal k).2.2).trans
        (minimaxRisk_le_observedWorstRisk (est k))
  · intro hr
    refine ⟨fun k => armwiseEstimatorWitness H₀ κ D₀ hH₀ hκ hD₀
      (N k) (d k) (ε k), ?_⟩
    have hmul : Tendsto (fun k => C * rateScale (N k) (d k) (ε k)) atTop (𝓝 0) := by
      simpa using (hrate.mpr hr).const_mul C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
    · exact Filter.Eventually.of_forall fun k => observedWorstRisk_nonneg _
    · filter_upwards [hn] with k hk
      exact hupper _ _ _ hk (hlegal k).1 (hlegal k).2.1 (hlegal k).2.2

end CausalSmith.Stat.OptvalueVanishingoverlapRate
