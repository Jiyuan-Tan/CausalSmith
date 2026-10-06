module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellError

/-!
# Two-cell finite honest intervals

The calibration roadmap uses radius √(10000/t) around the projected value
estimate. Markov's inequality applied to the assembled 88/t MSE gives global
ninety-percent coverage, and clipping gives length at most 200/√t.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Fix [the sample size](hyp:n) and [the privacy budget](hyp:eps). [The deterministic radius in the two-cell calibration roadmap](goal). -/
-- @node: twoCellRadius
def twoCellRadius (n : ℕ) (eps : ℝ) : ℝ := Real.sqrt (10000 / ((n : ℝ) * eps ^ 2))

/-- [Projection keeps the two-cell estimate inside the causal target domain](goal). -/
-- @node: twoCellEstimator_range
lemma twoCellEstimator_range {n : ℕ} (Q : LocalProtocol n (ObsRecord 2))
    (B x0 x1 : Estimator Q) (w : DecisionSpace Q) :
    (twoCellEstimator Q B x0 x1).1 w ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Fix [the privacy budget](hyp:eps), [the local protocol Q](hyp:Q), and [the estimator B and the estimator x0 and the estimator x1](hyp:B,x0,x1). [The clipped interval around the projected two-cell value estimate](goal). -/
-- @node: twoCellInterval
def twoCellInterval {n : ℕ} (eps : ℝ) (Q : LocalProtocol n (ObsRecord 2))
    (B x0 x1 : Estimator Q) : IntervalDecision Q (1 / 4) (3 / 4) where
  lo := fun w => max (1 / 4) ((twoCellEstimator Q B x0 x1).1 w - twoCellRadius n eps)
  hi := fun w => min (3 / 4) ((twoCellEstimator Q B x0 x1).1 w + twoCellRadius n eps)
  measurable_lo := by have hm := (twoCellEstimator Q B x0 x1).2; fun_prop
  measurable_hi := by have hm := (twoCellEstimator Q B x0 x1).2; fun_prop
  ordered := by
    intro w
    have hv := twoCellEstimator_range Q B x0 x1 w
    have hq : 0 ≤ twoCellRadius n eps := Real.sqrt_nonneg _
    apply le_trans (max_le hv.1 (by linarith)) (le_min hv.2 (by linarith))
  range_lo := by
    intro w
    have hv := twoCellEstimator_range Q B x0 x1 w
    have hq : 0 ≤ twoCellRadius n eps := Real.sqrt_nonneg _
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hv.2])⟩
  range_hi := by
    intro w
    have hv := twoCellEstimator_range Q B x0 x1 w
    have hq : 0 ≤ twoCellRadius n eps := Real.sqrt_nonneg _
    exact ⟨le_min (by norm_num) (by linarith [hv.1]), min_le_left _ _⟩

/-- Assume [the stated allowed condition](hyp:hAllowed). [The roadmap's radius is exactly 100 divided by the private square-root sample size](goal). -/
-- @node: twoCellRadius_eq
lemma twoCellRadius_eq (n : ℕ) (eps : ℝ) (hAllowed : Allowed n 2 eps) :
    twoCellRadius n eps = 100 / (Real.sqrt n * eps) := by
  rw [twoCellRadius, Real.sqrt_div (by norm_num), Real.sqrt_mul (by positivity),
    Real.sqrt_sq hAllowed.2.2.1.le,
    show (10000 : ℝ) = 100^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]

/-- [Clipping bounds the interval length pointwise by twice the radius](goal). -/
-- @node: twoCellInterval_length_le
lemma twoCellInterval_length_le {n : ℕ} (eps : ℝ) (Q : LocalProtocol n (ObsRecord 2))
    (B x0 x1 : Estimator Q) (w : DecisionSpace Q) :
    Causalean.Stat.intervalLength ((twoCellInterval eps Q B x0 x1).lo w)
      ((twoCellInterval eps Q B x0 x1).hi w) ≤ 2 * twoCellRadius n eps := by
  change max 0 (min (3 / 4) (_ + twoCellRadius n eps) -
    max (1 / 4) (_ - twoCellRadius n eps)) ≤ _
  apply max_le
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · have hu := min_le_right (3 / 4 : ℝ)
      ((twoCellEstimator Q B x0 x1).1 w + twoCellRadius n eps)
    have hl := le_max_right (1 / 4 : ℝ)
      ((twoCellEstimator Q B x0 x1).1 w - twoCellRadius n eps)
    linarith

/-- Assume [the stated allowed condition](hyp:hAllowed). [The finite expected length has the asserted 200/√t bound](goal). -/
-- @node: twoCellInterval_expectedLength_le
lemma twoCellInterval_expectedLength_le {n : ℕ} (eps : ℝ) (hAllowed : Allowed n 2 eps)
    (Q : LocalProtocol n (ObsRecord 2)) (B x0 x1 : Estimator Q)
    (L : Measure (DecisionSpace Q)) [IsProbabilityMeasure L] :
    expectedLength L (twoCellInterval eps Q B x0 x1) ≤
      ENNReal.ofReal (200 / (Real.sqrt n * eps)) := by
  have heq : 2 * twoCellRadius n eps = 200 / (Real.sqrt n * eps) := by
    rw [twoCellRadius_eq n eps hAllowed]
    ring
  rw [← heq]
  unfold expectedLength
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (2 * twoCellRadius n eps) ∂L :=
      lintegral_mono (fun w => ENNReal.ofReal_le_ofReal
        (twoCellInterval_length_le eps Q B x0 x1 w))
    _ = _ := by simp

/-- Assume [the stated allowed condition](hyp:hAllowed), [the stated hv condition](hyp:hv), and [the estimator hRisk](hyp:hRisk). [The assembled MSE implies finite global ninety-percent coverage by Markov's inequality](goal). -/
-- @node: twoCellInterval_coverage_of_risk
lemma twoCellInterval_coverage_of_risk {n : ℕ} (eps : ℝ) (hAllowed : Allowed n 2 eps)
    (Q : LocalProtocol n (ObsRecord 2)) (B x0 x1 : Estimator Q)
    (L : Measure (DecisionSpace Q)) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))
    (hRisk : squaredRisk L (twoCellEstimator Q B x0 x1) v ≤
      ENNReal.ofReal (88 / ((n : ℝ) * eps ^ 2))) :
    (0.90 : ℝ) ≤ coverage L (twoCellInterval eps Q B x0 x1) v := by
  let q := twoCellRadius n eps
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < (n : ℝ) * eps ^ 2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hq : 0 < q := Real.sqrt_pos.mpr (div_pos (by norm_num) ht)
  have hq2 : q ^ 2 = 10000 / ((n : ℝ) * eps ^ 2) := Real.sq_sqrt (by positivity)
  let f := fun w : DecisionSpace Q =>
    ENNReal.ofReal (((twoCellEstimator Q B x0 x1).1 w - v)^2)
  have hf : Measurable f := by
    have hm := (twoCellEstimator Q B x0 x1).2
    dsimp [f]
    fun_prop
  have hm := mul_meas_ge_le_lintegral (μ := L) hf (ENNReal.ofReal (q ^ 2))
  have hm' : ENNReal.ofReal (q ^ 2) * L {w | ENNReal.ofReal (q ^ 2) ≤ f w} ≤
      ENNReal.ofReal (88 / ((n : ℝ) * eps ^ 2)) := hm.trans hRisk
  have hmR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg q),
    ENNReal.toReal_ofReal (by positivity)] at hmR
  let E := Causalean.Stat.coverageEvent (twoCellInterval eps Q B x0 x1).lo
    (twoCellInterval eps Q B x0 x1).hi v
  have hE : MeasurableSet E := Causalean.Stat.measurableSet_coverageEvent
    (twoCellInterval eps Q B x0 x1).measurable_lo
    (twoCellInterval eps Q B x0 x1).measurable_hi
  have hsub : Eᶜ ⊆ {w | ENNReal.ofReal (q ^ 2) ≤ f w} := by
    intro w hw
    have herr : q < |(twoCellEstimator Q B x0 x1).1 w - v| := by
      by_contra hh
      have ha := abs_le.mp (le_of_not_gt hh)
      apply hw
      change max (1 / 4) ((twoCellEstimator Q B x0 x1).1 w - q) ≤ v ∧
        v ≤ min (3 / 4) ((twoCellEstimator Q B x0 x1).1 w + q)
      exact ⟨max_le hv.1 (by linarith [ha.2]), le_min hv.2 (by linarith [ha.1])⟩
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs ((twoCellEstimator Q B x0 x1).1 w - v)]
  have hmono := measureReal_mono (μ := L) hsub
  have hbad : L.real Eᶜ ≤ (1 / 10 : ℝ) := by
    have hmR' : q ^ 2 * L.real {w | ENNReal.ofReal (q ^ 2) ≤ f w} ≤ q ^ 2 / 10 := by
      calc
        _ ≤ 88 / ((n : ℝ) * eps ^ 2) := hmR
        _ ≤ q ^ 2 / 10 := by
          rw [hq2]
          have heq : 10000 / ((n : ℝ) * eps ^ 2) / 10 = 1000 / ((n : ℝ) * eps ^ 2) := by ring
          rw [heq]
          exact (div_le_div_iff_of_pos_right ht).mpr (by norm_num)
    have hpos : 0 < q ^ 2 := sq_pos_of_pos hq
    nlinarith
  rw [measureReal_compl hE, probReal_univ] at hbad
  change (0.90 : ℝ) ≤ L.real E
  linarith

end CausalSmith.Stat.LdpOptvalueUniformFrontier
