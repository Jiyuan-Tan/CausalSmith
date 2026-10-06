module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Upper
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Two-cell error assembly

Projection and the absolute-value inequality turn the baseline and two coordinate
mean-square errors into the two-cell value error. This argument does not require
independence between the coordinate estimates.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Fix [the constant B and the real parameter x0 and the real parameter x1](hyp:B,x0,x1). [The projected two-cell transcript estimate specified in the calibration proof](goal). -/
-- @node: twoCellValueEstimate
def twoCellValueEstimate (B x0 x1 : ℝ) : ℝ :=
  max (1/4) (min (3/4) (B + (|x0| + |x1|)/4))

/-- Assume [the stated hv condition](hyp:hv). [Projection onto the causal target interval cannot increase squared error](goal). -/
-- @node: twoCell_projection_sq_le
lemma twoCell_projection_sq_le (x v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    (max (1/4 : ℝ) (min (3/4) x) - v)^2 ≤ (x - v)^2 := by
  by_cases hxlo : x ≤ 1/4
  · rw [min_eq_right (by linarith), max_eq_left hxlo]
    nlinarith [hv.1]
  · by_cases hxhi : 3/4 ≤ x
    · rw [min_eq_left hxhi, max_eq_right (by norm_num)]
      nlinarith [hv.2]
    · rw [min_eq_right (le_of_not_ge hxhi), max_eq_right (le_of_not_ge hxlo)]

/-- Assume [the stated hv condition](hyp:hv). [The two absolute contrast errors cost at most one quarter of their squared errors in the value MSE, after combining with the baseline error](goal). -/
-- @node: twoCellValueEstimate_sq_error
lemma twoCellValueEstimate_sq_error (B x0 x1 b t0 t1 : ℝ)
    (hv : b + (|t0| + |t1|)/4 ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    (twoCellValueEstimate B x0 x1 - (b + (|t0| + |t1|)/4))^2 ≤
      2*(B-b)^2 + ((x0-t0)^2 + (x1-t1)^2)/4 := by
  have h0 := abs_abs_sub_abs_le_abs_sub x0 t0
  have h1 := abs_abs_sub_abs_le_abs_sub x1 t1
  have hs0 : (|x0|-|t0|)^2 ≤ (x0-t0)^2 := by
    nlinarith [sq_abs (|x0|-|t0|), sq_abs (x0-t0),
      abs_nonneg (|x0|-|t0|), abs_nonneg (x0-t0)]
  have hs1 : (|x1|-|t1|)^2 ≤ (x1-t1)^2 := by
    nlinarith [sq_abs (|x1|-|t1|), sq_abs (x1-t1),
      abs_nonneg (|x1|-|t1|), abs_nonneg (x1-t1)]
  apply (twoCell_projection_sq_le _ _ hv).trans
  nlinarith [sq_nonneg ((|x0|-|t0|)-(|x1|-|t1|)),
    sq_nonneg ((B-b)-((|x0|-|t0|)+(|x1|-|t1|))/4)]

/-- Assume [measurability of b](hyp:hB), [measurability of x0](hyp:hx0), [measurability of x1](hyp:hx1), and [the stated hv condition](hyp:hv). [Integrating the pointwise assembly gives a bound from the three component MSEs](goal). -/
-- @node: twoCellValueEstimate_mse_le
lemma twoCellValueEstimate_mse_le {Ω : Type*} [MeasurableSpace Ω]
    (L : Measure Ω) (B x0 x1 : Ω → ℝ)
    (hB : Measurable B) (hx0 : Measurable x0) (hx1 : Measurable x1)
    (b t0 t1 : ℝ) (hv : b + (|t0| + |t1|)/4 ∈ Set.Icc (1/4 : ℝ) (3/4)) :
    (∫⁻ w, ENNReal.ofReal
      ((twoCellValueEstimate (B w) (x0 w) (x1 w) - (b + (|t0| + |t1|)/4))^2) ∂L) ≤
      2 * (∫⁻ w, ENNReal.ofReal ((B w-b)^2) ∂L) +
      ENNReal.ofReal (1/4 : ℝ) *
        ((∫⁻ w, ENNReal.ofReal ((x0 w-t0)^2) ∂L) +
         (∫⁻ w, ENNReal.ofReal ((x1 w-t1)^2) ∂L)) := by
  have hsplit (w : Ω) :
      ENNReal.ofReal (2*(B w-b)^2 + ((x0 w-t0)^2 + (x1 w-t1)^2)/4) =
        2 * ENNReal.ofReal ((B w-b)^2) + ENNReal.ofReal (1/4 : ℝ) *
          (ENNReal.ofReal ((x0 w-t0)^2) + ENNReal.ofReal ((x1 w-t1)^2)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_eq_mul_inv, mul_comm _ (4 : ℝ)⁻¹,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    norm_num
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal (2*(B w-b)^2 + ((x0 w-t0)^2 + (x1 w-t1)^2)/4) ∂L :=
      lintegral_mono (fun w => ENNReal.ofReal_le_ofReal
        (twoCellValueEstimate_sq_error (B w) (x0 w) (x1 w) b t0 t1 hv))
    _ = _ := by
      simp_rw [hsplit]
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
        lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop)]

/-- Assume [the causal-model conditions for the data law](hyp:hP). [The bridge identifies the two-cell target used in the error calculation](goal). -/
-- @node: causal_value_two_cells
lemma causal_value_two_cells (P : Measure (FullRecord 2)) [IsProbabilityMeasure P]
    (hP : CausalModel P) :
    value P = baseline P + (|contrast P 0| + |contrast P 1|)/4 := by
  rw [causal_value_decomposition P hP (by norm_num)]
  simp only [signedNorm, Fin.sum_univ_two]
  norm_num
  ring

/-- Assume [a privacy budget in the interval from zero to one](hyp:heps). [On the allowed privacy domain the randomized-response signal is at least ε/4](goal). -/
-- @node: privacyDelta_lower_quarter
lemma privacyDelta_lower_quarter (eps : ℝ) (heps : eps ∈ Set.Ioc 0 1) :
    eps/4 ≤ privacyDelta eps := by
  rw [privacyDelta_exp_formula]
  apply (le_div_iff₀ (by positivity : 0 < Real.exp eps + 1)).mpr
  have hlo := Real.add_one_le_exp eps
  have hhi : Real.exp eps < 3 := (Real.exp_le_exp.mpr heps.2).trans_lt Real.exp_one_lt_three
  nlinarith [heps.1]

/-- Assume [sample size at least two](hyp:hn). [The deterministic half split supplies the two lower block-size bounds](goal). -/
-- @node: two_cell_half_block_sizes
lemma two_cell_half_block_sizes (n : ℕ) (hn : 2 ≤ n) :
    0 < n/2 ∧ (n : ℝ)/3 ≤ (n/2 : ℕ) ∧ (n : ℝ)/2 ≤ (n-n/2 : ℕ) := by
  have h0 : 0 < n/2 := by omega
  have h1 : n ≤ 3*(n/2) := by omega
  have h2 : n ≤ 2*(n-n/2) := by omega
  refine ⟨h0, ?_, ?_⟩
  · have hr : (n : ℝ) ≤ 3*(n/2 : ℕ) := by exact_mod_cast h1
    linarith
  · have hr : (n : ℝ) ≤ 2*(n-n/2 : ℕ) := by exact_mod_cast h2
    linarith

/-- Assume [the stated allowed condition](hyp:hAllowed). [The block MSE bounds yield the roadmap's finite numerical constant 88](goal). -/
-- @node: two_cell_variance_calibration
lemma two_cell_variance_calibration (n : ℕ) (eps : ℝ) (hAllowed : Allowed n 2 eps) :
    1/(2*(n/2 : ℕ)*(privacyDelta eps)^2) +
      2/((n-n/2 : ℕ)*(privacyDelta eps)^2) ≤ 88/((n : ℝ)*eps^2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have heps := hAllowed.2.2.1
  have hdelta := privacyDelta_lower_quarter eps hAllowed.2.2
  have hd : 0 < privacyDelta eps := by linarith
  obtain ⟨hm0, hm0bound, hm1bound⟩ := two_cell_half_block_sizes n hAllowed.1
  have hm0pos : (0 : ℝ) < (n/2 : ℕ) := by exact_mod_cast hm0
  have hm1pos : (0 : ℝ) < (n-n/2 : ℕ) := (by positivity : (0 : ℝ) < n/2).trans_le hm1bound
  calc
    _ ≤ 1/(2*((n : ℝ)/3)*(privacyDelta eps)^2) +
        2/(((n : ℝ)/2)*(privacyDelta eps)^2) := by
      apply add_le_add
      · apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right hm1bound (sq_nonneg _)
    _ = 88/((n : ℝ)*(4*privacyDelta eps)^2) := by
      field_simp
      <;> ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hn.le
      nlinarith

/-- If the baseline and two contrast statistics are [measurable](hyp:hB,hx0,hx1), their two-cell
projection is [measurable](goal). -/
-- @node: measurable_twoCellValueEstimate
@[fun_prop] lemma measurable_twoCellValueEstimate {Ω : Type*} [MeasurableSpace Ω]
    (B x0 x1 : Ω → ℝ) (hB : Measurable B) (hx0 : Measurable x0) (hx1 : Measurable x1) :
    Measurable (fun w => twoCellValueEstimate (B w) (x0 w) (x1 w)) := by
  unfold twoCellValueEstimate
  fun_prop

/-- Fix [the local protocol Q](hyp:Q) and [the estimator B and the estimator x0 and the estimator x1](hyp:B,x0,x1). [Combine three transcript-only statistics into the projected two-cell estimate](goal). -/
-- @node: twoCellEstimator
def twoCellEstimator {n : ℕ} (Q : LocalProtocol n (ObsRecord 2))
    (B x0 x1 : Estimator Q) : Estimator Q :=
  ⟨fun w => twoCellValueEstimate (B.1 w) (x0.1 w) (x1.1 w),
    measurable_twoCellValueEstimate B.1 x0.1 x1.1 B.2 x0.2 x1.2⟩

/-- Assume [the stated allowed condition](hyp:hAllowed), [the causal-model conditions for the data law](hyp:hP), [the stated b condition](hyp:hB), [the stated hx0 condition](hyp:hx0), and [the stated hx1 condition](hyp:hx1). [Component binary/vector MSE bounds assemble into the uniform two-cell risk bound. The component estimates can be dependent: only their marginal MSEs enter](goal). -/
-- @node: two_cell_risk_of_component_mse
lemma two_cell_risk_of_component_mse {n : ℕ} (eps : ℝ) (hAllowed : Allowed n 2 eps)
    (Q : LocalProtocol n (ObsRecord 2)) (L : Measure (DecisionSpace Q))
    (B x0 x1 : Estimator Q) (P : Measure (FullRecord 2)) [IsProbabilityMeasure P]
    (hP : CausalModel P)
    (hB : squaredRisk L B (baseline P) ≤
      ENNReal.ofReal (1/(4*(n/2 : ℕ)*(privacyDelta eps)^2)))
    (hx0 : squaredRisk L x0 (contrast P 0) ≤
      ENNReal.ofReal (4/((n-n/2 : ℕ)*(privacyDelta eps)^2)))
    (hx1 : squaredRisk L x1 (contrast P 1) ≤
      ENNReal.ofReal (4/((n-n/2 : ℕ)*(privacyDelta eps)^2))) :
    squaredRisk L (twoCellEstimator Q B x0 x1) (value P) ≤
      ENNReal.ofReal (88/((n : ℝ)*eps^2)) := by
  have hv := causal_value_range P hP (by norm_num)
  rw [causal_value_two_cells P hP] at hv
  have hsum := twoCellValueEstimate_mse_le L B.1 x0.1 x1.1 B.2 x0.2 x1.2
    (baseline P) (contrast P 0) (contrast P 1) hv
  have herror : squaredRisk L (twoCellEstimator Q B x0 x1) (value P) ≤
      2*squaredRisk L B (baseline P) + ENNReal.ofReal (1/4 : ℝ)*
        (squaredRisk L x0 (contrast P 0) + squaredRisk L x1 (contrast P 1)) := by
    simpa only [squaredRisk, twoCellEstimator, causal_value_two_cells P hP] using hsum
  apply herror.trans
  calc
    _ ≤ 2*ENNReal.ofReal (1/(4*(n/2 : ℕ)*(privacyDelta eps)^2)) +
        ENNReal.ofReal (1/4 : ℝ)*
          (ENNReal.ofReal (4/((n-n/2 : ℕ)*(privacyDelta eps)^2)) +
           ENNReal.ofReal (4/((n-n/2 : ℕ)*(privacyDelta eps)^2))) :=
      add_le_add (mul_le_mul' le_rfl hB) (mul_le_mul' le_rfl (add_le_add hx0 hx1))
    _ = ENNReal.ofReal (1/(2*(n/2 : ℕ)*(privacyDelta eps)^2) +
        2/((n-n/2 : ℕ)*(privacyDelta eps)^2)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (two_cell_variance_calibration n eps hAllowed)

end CausalSmith.Stat.LdpOptvalueUniformFrontier
