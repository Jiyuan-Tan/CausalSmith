module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ElbowAlgebra
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.FrontierLower
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.FrontierConsistency
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TSupportedBoundaries

/-!
# Complete original-record precision frontier
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The total observable frontier estimator attains the explicit upper constant
through the audit-score envelope and the reveal-probability comparisons.  [For the stated data and conditions](hyp:n,d,q,hn,hd,hdu,hq), [the stated conclusion holds](goal). -/
-- @node: frontierEstimator_risk_upper
lemma frontierEstimator_risk_upper (n d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) (hq : q ∈ Set.Icc 0 1) :
    R (Fin n) d q ≤ worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ∧
    worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ≤
      ENNReal.ofReal (24 * frontierScale n d q) := by
  obtain ⟨hminimax, hupper, _⟩ := observable_upper (V := Fin n) d q
    (by simpa using hn) hd (by simpa using hdu) hq
  refine ⟨?_, ?_⟩
  · simpa only [R, frontierEstimator, Fintype.card_fin] using hminimax
  · have hupper' : worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ≤
        min 1 (upperEnvelope n d q) := by
      simpa only [frontierEstimator, Fintype.card_fin] using hupper
    exact hupper'.trans (upperEnvelope_le_frontierScale n d q hn hd hq)

/-- [The displayed explicit constants establish the risk bounds, consistency criterion, endpoint identities, and interior-retention comparison](goal). -/
-- @node: precision_frontier_explicit
lemma precision_frontier_explicit :

    (∀ n : ℕ, 4 ≤ n → -- @realizes n(population size n ≥ 4)
    ∀ d : ℕ, 1 ≤ d → d ≤ n - 1 → -- @realizes d(1 ≤ d ≤ n-1)
    ∀ q : ℝ, q ∈ Set.Icc 0 1 → -- @realizes q(known retention in [0,1])
      ENNReal.ofReal (frontierScale n d q / (2560000 * Real.pi ^ 2)) ≤ R (Fin n) d q ∧
      R (Fin n) d q ≤ worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ∧
      worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ≤
        ENNReal.ofReal (24 * frontierScale n d q))
 ∧

    (∀ (dseq : ℕ → ℕ) (qseq : ℕ → ℝ), AdmissibleSequences dseq qseq →
      ((∃ T : ∀ n, Estimator (Fin n),
        Filter.Tendsto (fun n => worstRisk (thinnedDesign (Fin n) (qseq n)) (dseq n) (T n))
          Filter.atTop (nhds 0)) ↔
      (Filter.Tendsto (fun n => (dseq n : ℝ) ^ 2 / n) Filter.atTop (nhds 0) ∧
       Filter.Tendsto (fun n => if qseq n = 0 then (⊤ : ℝ≥0∞)
         else ENNReal.ofReal (dseq n / (n * qseq n))) Filter.atTop (nhds 0))))
 ∧

    (∀ n d : ℕ, 4 ≤ n → 1 ≤ d → d ≤ n - 1 →
      frontierScale n d 0 = 1 ∧ frontierScale n d 1 = min 1 ((d : ℝ) ^ 2 / n) ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 →
        (1 / 2 : ℝ) * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)) ≤ frontierScale n d q ∧
        frontierScale n d q ≤ (1 - Real.exp (-1))⁻¹ * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)))
 := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn d hd hdu q hq
    obtain ⟨hminimax, hupper⟩ := frontierEstimator_risk_upper n d q hn hd hdu hq
    refine ⟨?_, hminimax, hupper⟩
    exact frontier_minimax_lower n d q hn hd hdu hq
  · intro dseq qseq ha
    have hadm : ∀ᶠ n in Filter.atTop, 4 ≤ n := Filter.eventually_ge_atTop 4
    constructor
    · rintro ⟨T, hT⟩
      let C : ℝ := 2560000 * Real.pi ^ 2
      have hC : 0 < C := mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
      have hlower : ∀ᶠ n in Filter.atTop,
          ENNReal.ofReal (frontierScale n (dseq n) (qseq n) / C) ≤
            worstRisk (thinnedDesign (Fin n) (qseq n)) (dseq n) (T n) := by
        filter_upwards [hadm] with n hn
        obtain ⟨hd, hdu, hq⟩ := ha n hn
        exact (frontier_minimax_lower n (dseq n) (qseq n) hn hd hdu hq).trans
          (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk (T n))
      have hscaled : Filter.Tendsto
          (fun n => ENNReal.ofReal (frontierScale n (dseq n) (qseq n) / C))
          Filter.atTop (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
          (Filter.Eventually.of_forall (fun _ => bot_le)) hlower
      have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hscaled
      simp only [ENNReal.toReal_zero] at hreal
      have hdiv : Filter.Tendsto (fun n => frontierScale n (dseq n) (qseq n) / C)
          Filter.atTop (nhds 0) := by
        apply hreal.congr'
        filter_upwards [hadm] with n hn
        exact ENNReal.toReal_ofReal (div_nonneg
          (frontierScale_nonneg n (dseq n) (qseq n) (ha n hn).2.2) hC.le)
      have hF : Filter.Tendsto (fun n => frontierScale n (dseq n) (qseq n))
          Filter.atTop (nhds 0) := by
        simpa only [div_mul_cancel₀ _ (ne_of_gt hC), zero_mul] using hdiv.mul_const C
      exact (frontierScale_tendsto_iff dseq qseq ha).mp hF
    · intro hratios
      have hF := (frontierScale_tendsto_iff dseq qseq ha).mpr hratios
      refine ⟨fun n => frontierEstimator n (dseq n) (qseq n), ?_⟩
      have hupper : ∀ᶠ n in Filter.atTop,
          worstRisk (thinnedDesign (Fin n) (qseq n)) (dseq n)
            (frontierEstimator n (dseq n) (qseq n)) ≤
              ENNReal.ofReal (24 * frontierScale n (dseq n) (qseq n)) := by
        filter_upwards [hadm] with n hn
        obtain ⟨hd, hdu, hq⟩ := ha n hn
        exact (frontierEstimator_risk_upper n (dseq n) (qseq n) hn hd hdu hq).2
      have hlimit := ENNReal.tendsto_ofReal (hF.const_mul 24)
      simp only [mul_zero, ENNReal.ofReal_zero] at hlimit
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
        (Filter.Eventually.of_forall (fun _ => bot_le)) hupper
  · exact frontier_elbow


/-- [There exist positive universal constants `c` and `C0` giving the stated risk sandwich; consistent estimators exist exactly when both asymptotic scale conditions hold; the frontier scale equals `1` at zero retention and `min 1 (d²/n)` at full retention; and positive universal comparison constants `c1` and `C1`, independent of `n`, `d`, and `q`, bound the frontier by the stated interior-retention scale](goal). -/
-- @node: thm:observed-record-precision-frontier
theorem observed_record_precision_frontier :
    ∃ c C0 : ℝ, 0 < c ∧ 0 < C0 ∧
    -- @realizes c(positive universal lower constant)
    -- @realizes C0(positive finite universal upper constant)
    (∀ n : ℕ, 4 ≤ n → -- @realizes n(population size n ≥ 4)
    ∀ d : ℕ, 1 ≤ d → d ≤ n - 1 → -- @realizes d(1 ≤ d ≤ n-1)
    ∀ q : ℝ, q ∈ Set.Icc 0 1 → -- @realizes q(known retention in [0,1])
      ENNReal.ofReal (c * frontierScale n d q) ≤ R (Fin n) d q ∧
      R (Fin n) d q ≤ worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ∧
      worstRisk (thinnedDesign (Fin n) q) d (frontierEstimator n d q) ≤
        ENNReal.ofReal (C0 * frontierScale n d q)) ∧

    (∀ (dseq : ℕ → ℕ) (qseq : ℕ → ℝ), AdmissibleSequences dseq qseq →
      ((∃ T : ∀ n, Estimator (Fin n),
        Filter.Tendsto (fun n => worstRisk (thinnedDesign (Fin n) (qseq n)) (dseq n) (T n))
          Filter.atTop (nhds 0)) ↔
      (Filter.Tendsto (fun n => (dseq n : ℝ) ^ 2 / n) Filter.atTop (nhds 0) ∧
       Filter.Tendsto (fun n => if qseq n = 0 then (⊤ : ℝ≥0∞)
         else ENNReal.ofReal (dseq n / (n * qseq n))) Filter.atTop (nhds 0))))
 ∧

    (∀ n d : ℕ, 4 ≤ n → 1 ≤ d → d ≤ n - 1 →
      frontierScale n d 0 = 1 ∧ frontierScale n d 1 = min 1 ((d : ℝ) ^ 2 / n)) ∧

    (∃ c1 C1 : ℝ, 0 < c1 ∧ 0 < C1 ∧
      ∀ n d : ℕ, 4 ≤ n → 1 ≤ d → d ≤ n - 1 →
      ∀ q : ℝ, 0 < q → q ≤ 1 →
        c1 * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)) ≤ frontierScale n d q ∧
        frontierScale n d q ≤ C1 * min 1 ((d : ℝ) ^ 2 / n + d / (n * q)))
 := by
  rcases precision_frontier_explicit with ⟨hrisk, hconsistency, helbow⟩
  refine ⟨1 / (2560000 * Real.pi ^ 2), 24, ?_, by norm_num, ?_,
    hconsistency, ?_, ?_⟩
  · exact div_pos (by norm_num) (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
  · intro n hn d hd hdu q hq
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hrisk n hn d hd hdu q hq
  · intro n d hn hd hdu
    exact ⟨(helbow n d hn hd hdu).1, (helbow n d hn hd hdu).2.1⟩
  · refine ⟨1 / 2, (1 - Real.exp (-1))⁻¹, by norm_num, ?_, ?_⟩
    · exact inv_pos.mpr (sub_pos.mpr
        (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)))
    · intro n d hn hd hdu q hq hq1
      exact (helbow n d hn hd hdu).2.2 q hq hq1

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
