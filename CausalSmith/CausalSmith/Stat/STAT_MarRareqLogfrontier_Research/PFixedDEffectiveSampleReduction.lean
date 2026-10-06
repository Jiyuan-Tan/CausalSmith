module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TOneCellTestingFamily
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TMatchedMinimaxFrontier

/-! PFixedDEffectiveSampleReduction for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: fixed_d_frontier_rate_theta
/-- Given [the specified inputs and assumptions](hyp:d,n,q,hn,hq,hN), [the stated mathematical conclusion holds](goal). -/
lemma fixed_d_frontier_rate_theta
    (d : ℕ) (n : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hq : ∀ t, 0 < q t)
    (hN : Tendsto (fun t => effectiveSize (n t) (q t)) atTop atTop) :
    (fun t => frontierRate (n t) d (q t)) =Θ[atTop]
      (fun t => (effectiveSize (n t) (q t))⁻¹) := by
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [hN.eventually_ge_atTop (max 2 ((d : ℝ) ^ 2))] with t ht
    have hNpos : 0 < effectiveSize (n t) (q t) := by
      dsimp [effectiveSize]
      exact mul_pos (by exact_mod_cast hn t) (hq t)
    have hL : 1 ≤ logScale (n t) (q t) := by
      change 1 ≤ Real.log (Real.exp 1 + effectiveSize (n t) (q t))
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith
    have hdN : (d : ℝ) ^ 2 ≤ effectiveSize (n t) (q t) :=
      le_trans (le_max_right _ _) ht
    have hden : 0 < effectiveSize (n t) (q t) * logScale (n t) (q t) :=
      mul_pos hNpos (by linarith)
    have hb : ((d : ℝ) / (effectiveSize (n t) (q t) * logScale (n t) (q t))) ^ 2 ≤
        (effectiveSize (n t) (q t))⁻¹ := by
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos hden 2)).2
      have hL2 : 1 ≤ (logScale (n t) (q t)) ^ 2 := by nlinarith
      have heq : (effectiveSize (n t) (q t))⁻¹ *
          (effectiveSize (n t) (q t) * logScale (n t) (q t)) ^ 2 =
          effectiveSize (n t) (q t) * (logScale (n t) (q t)) ^ 2 := by
        field_simp [ne_of_gt hNpos]
      rw [heq]
      nlinarith [mul_nonneg (le_of_lt hNpos) (sub_nonneg.mpr hL2)]
    have ha : 0 ≤ (effectiveSize (n t) (q t))⁻¹ := inv_nonneg.mpr (le_of_lt hNpos)
    have hr : 0 ≤ frontierRate (n t) d (q t) := by
      unfold frontierRate
      exact le_min (by norm_num) (add_nonneg ha (sq_nonneg _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg ha]
    unfold frontierRate
    exact (min_le_right _ _).trans (by linarith)
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hN.eventually_ge_atTop (max 2 ((d : ℝ) ^ 2))] with t ht
    have hNpos : 0 < effectiveSize (n t) (q t) := by
      dsimp [effectiveSize]
      exact mul_pos (by exact_mod_cast hn t) (hq t)
    have ha : 0 ≤ (effectiveSize (n t) (q t))⁻¹ := inv_nonneg.mpr (le_of_lt hNpos)
    have ha1 : (effectiveSize (n t) (q t))⁻¹ ≤ 1 := by
      apply (inv_le_one₀ hNpos).2
      linarith [le_trans (le_max_left (2 : ℝ) ((d : ℝ) ^ 2)) ht]
    have hr : 0 ≤ frontierRate (n t) d (q t) := by
      unfold frontierRate
      exact le_min (by norm_num) (add_nonneg ha (sq_nonneg _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hr]
    simp only [one_mul]
    unfold frontierRate
    exact le_min ha1 (le_add_of_nonneg_right (sq_nonneg _))

-- @node: prop:fixed-d-effective-sample-reduction
/-- Given [the specified inputs and assumptions](hyp:d,hd,n,q,hn,hq,hslice,hN), [the stated mathematical conclusion holds](goal). -/
theorem fixed_d_effective_sample_reduction
    (d : ℕ) (hd : 1 ≤ d) (n : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hq : ∀ t, 0 < q t ∧ q t ≤ 1)
    (hslice : ∀ t, RareArrivalSlice (n t) (q t))
    (hN : Tendsto (fun t => effectiveSize (n t) (q t)) atTop atTop) :
    (fun t => frontierRate (n t) d (q t)) =Θ[atTop]
      (fun t => (effectiveSize (n t) (q t))⁻¹) ∧
    (fun t => minimaxRisk (n t) d (q t)) =Θ[atTop]
      (fun t => (effectiveSize (n t) (q t))⁻¹) ∧
    (fun t => noSurrogateRisk (n t) d (q t)) =Θ[atTop]
      (fun t => (effectiveSize (n t) (q t))⁻¹) := by
  refine ⟨fixed_d_frontier_rate_theta d n q hn (fun t => (hq t).1) hN, ?_, ?_⟩
  · obtain ⟨c, C, hc, hcC, hbounds⟩ :=
      matched_minimax_frontier
    have hθ : (fun t => minimaxRisk (n t) d (q t)) =Θ[atTop]
        (fun t => frontierRate (n t) d (q t)) := by
      constructor
      · rw [Asymptotics.isBigO_iff]
        refine ⟨C, ?_⟩
        filter_upwards with t
        obtain ⟨hl, hu⟩ := hbounds (n t) d (q t) (hn t) hd (hq t).1
          (hq t).2 (hslice t)
        have hr : 0 ≤ frontierRate (n t) d (q t) := by
          unfold frontierRate
          exact le_min (by norm_num) (add_nonneg
            (inv_nonneg.mpr (le_of_lt (mul_pos
              (by exact_mod_cast hn t) (hq t).1))) (sq_nonneg _))
        have hm : 0 ≤ minimaxRisk (n t) d (q t) :=
          le_trans (mul_nonneg (le_of_lt hc) hr) hl
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm, abs_of_nonneg hr]
        exact hu
      · rw [Asymptotics.isBigO_iff]
        refine ⟨c⁻¹, ?_⟩
        filter_upwards with t
        obtain ⟨hl, hu⟩ := hbounds (n t) d (q t) (hn t) hd (hq t).1
          (hq t).2 (hslice t)
        have hr : 0 ≤ frontierRate (n t) d (q t) := by
          unfold frontierRate
          exact le_min (by norm_num) (add_nonneg
            (inv_nonneg.mpr (le_of_lt (mul_pos
              (by exact_mod_cast hn t) (hq t).1))) (sq_nonneg _))
        have hm : 0 ≤ minimaxRisk (n t) d (q t) :=
          le_trans (mul_nonneg (le_of_lt hc) hr) hl
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hm]
        calc
          frontierRate (n t) d (q t) ≤ minimaxRisk (n t) d (q t) / c :=
            (le_div_iff₀ hc).2 (by simpa [mul_comm] using hl)
          _ = c⁻¹ * minimaxRisk (n t) d (q t) := by ring
    exact hθ.trans (fixed_d_frontier_rate_theta d n q hn
      (fun t => (hq t).1) hN)
  · let c : ℝ := 1 / 256
    have hc : 0 < c := by norm_num [c]
    obtain ⟨C, hC, hupp⟩ := mixed_count_upper
    have hUpper (t : ℕ) :
        noSurrogateRisk (n t) d (q t) ≤ C * frontierRate (n t) d (q t) := by
      let f := mixedCountEstimator (n t) d (q t)
      have hEstimator := mixed_count_estimator_regular (n t) d (q t)
      let T : Estimator (n t) d :=
        Estimator.ofMap f hEstimator
      have hrisk : ∀ (T : Estimator (n t) d)
          (P : {P : FullLaw d // RareArrivalModelClass (n t) d (q t) P ∧
            ∀ᵐ r : FullRecord d ∂(P.1), r.S0 = false ∧ r.S1 = false}),
          0 ≤ squaredRisk T P.1 := by
        intro T P
        exact integral_nonneg (fun s => integral_nonneg (fun y => sq_nonneg _))
      have hval : noSurrogateRisk (n t) d (q t) ≤
          Causalean.Stat.worstCaseRiskReal
            (fun (T : Estimator (n t) d)
              (P : {P : FullLaw d // RareArrivalModelClass (n t) d (q t) P ∧
                ∀ᵐ r : FullRecord d ∂(P.1), r.S0 = false ∧ r.S1 = false}) =>
              squaredRisk T P.1) T :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hrisk T
      refine hval.trans ?_
      unfold Causalean.Stat.worstCaseRiskReal
      by_cases hne : Nonempty {P : FullLaw d // RareArrivalModelClass (n t) d (q t) P ∧
          ∀ᵐ r : FullRecord d ∂(P.1), r.S0 = false ∧ r.S1 = false}
      · letI := hne
        apply ciSup_le
        intro P
        have hdet : squaredRisk T P.1 = deterministicRisk f P.1 := by
          simp [squaredRisk, deterministicRisk, T, Estimator.ofMap, Kernel.deterministic_apply]
        change squaredRisk T P.1 ≤ C * frontierRate (n t) d (q t)
        rw [hdet]
        exact (hupp (n t) d (q t) P.1 P.2.1).1.trans
          (hupp (n t) d (q t) P.1 P.2.1).2.1
      · haveI : IsEmpty {P : FullLaw d // RareArrivalModelClass (n t) d (q t) P ∧
          ∀ᵐ r : FullRecord d ∂(P.1), r.S0 = false ∧ r.S1 = false} :=
          not_nonempty_iff.mp hne
        have hNpos : 0 < effectiveSize (n t) (q t) := by
          unfold effectiveSize
          exact mul_pos (by exact_mod_cast hn t) (hq t).1
        have hr : 0 ≤ frontierRate (n t) d (q t) := by
          unfold frontierRate
          exact le_min (by norm_num) (add_nonneg
            (inv_nonneg.mpr (le_of_lt hNpos)) (sq_nonneg _))
        simpa using (mul_nonneg (le_of_lt hC) hr)
    have hLower (t : ℕ) :
        c * min 1 (effectiveSize (n t) (q t))⁻¹ ≤
          noSurrogateRisk (n t) d (q t) := by
      simpa [c] using
        (oneCell_minimax_risk_floors (q t) (hn t) hd (hq t).1
          (hq t).2 (hslice t)).2
    constructor
    · have hO : (fun t => noSurrogateRisk (n t) d (q t)) =O[atTop]
          (fun t => frontierRate (n t) d (q t)) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨C, ?_⟩
        filter_upwards with t
        have hNpos : 0 < effectiveSize (n t) (q t) := by
          unfold effectiveSize
          exact mul_pos (by exact_mod_cast hn t) (hq t).1
        have hr : 0 ≤ frontierRate (n t) d (q t) := by
          unfold frontierRate
          exact le_min (by norm_num) (add_nonneg
            (inv_nonneg.mpr (le_of_lt hNpos)) (sq_nonneg _))
        have hm : 0 ≤ noSurrogateRisk (n t) d (q t) := by
          exact le_trans (mul_nonneg (le_of_lt hc)
            (le_min (by norm_num) (inv_nonneg.mpr (le_of_lt hNpos)))) (hLower t)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm, abs_of_nonneg hr]
        exact hUpper t
      exact hO.trans (fixed_d_frontier_rate_theta d n q hn
        (fun t => (hq t).1) hN).1
    · rw [Asymptotics.isBigO_iff]
      refine ⟨c⁻¹, ?_⟩
      filter_upwards [hN.eventually_ge_atTop 1] with t ht
      have hNpos : 0 < effectiveSize (n t) (q t) := by
        unfold effectiveSize
        exact mul_pos (by exact_mod_cast hn t) (hq t).1
      have ha : 0 ≤ (effectiveSize (n t) (q t))⁻¹ :=
        inv_nonneg.mpr (le_of_lt hNpos)
      have ha1 : (effectiveSize (n t) (q t))⁻¹ ≤ 1 :=
        (inv_le_one₀ hNpos).2 ht
      have hl : c * (effectiveSize (n t) (q t))⁻¹ ≤
          noSurrogateRisk (n t) d (q t) := by
        simpa [min_eq_right ha1] using hLower t
      have hm : 0 ≤ noSurrogateRisk (n t) d (q t) :=
        le_trans (mul_nonneg (le_of_lt hc) ha) hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hm]
      calc
        (effectiveSize (n t) (q t))⁻¹ ≤
            noSurrogateRisk (n t) d (q t) / c :=
          (le_div_iff₀ hc).2 (by simpa [mul_comm] using hl)
        _ = c⁻¹ * noSurrogateRisk (n t) d (q t) := by ring

end CausalSmith.Stat.MarRareqLogfrontier
