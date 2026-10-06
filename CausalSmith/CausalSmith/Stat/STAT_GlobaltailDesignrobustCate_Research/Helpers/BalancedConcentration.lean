module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Bounded residual concentration for balanced fits

Roadmap (12)--(13): on a fixed covariate-treatment fiber, centered bounded
residuals have a sub-Gaussian MGF. Independence adds their squared-weight
variance proxies, and the two Chernoff tails control the absolute sum.
These lemmas apply to a probability measure on a fiber; transferring the
observational law to such fibers remains a separate step.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- The centered bounded-residual MGF input in roadmap (12). -/
-- @node: boundedResidual_subgaussian
lemma boundedResidual_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ) (b : ℝ≥0)
    (hmeas : AEMeasurable ξ μ) (hbound : ∀ᵐ ω ∂μ, |ξ ω| ≤ b)
    (hcenter : ∫ ω, ξ ω ∂μ = 0) : HasSubgaussianMGF ξ (b ^ 2) μ := by
  have hinterval : ∀ᵐ ω ∂μ, ξ ω ∈ Set.Icc (-(b : ℝ)) b := by
    filter_upwards [hbound] with ω hω
    exact abs_le.mp hω
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hinterval hcenter
  have hscale : (‖(b : ℝ) - -(b : ℝ)‖₊ / 2) ^ 2 = b ^ 2 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat]
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr
      ((neg_nonpos.mpr b.coe_nonneg).trans b.coe_nonneg))]
    congr 1
    ring
  rw [hscale] at h
  exact h

/-- Equation (12) holds for every real exponential parameter. -/
-- @node: boundedResidual_mgf_le
lemma boundedResidual_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ) (b : ℝ≥0)
    (hmeas : AEMeasurable ξ μ) (hbound : ∀ᵐ ω ∂μ, |ξ ω| ≤ b)
    (hcenter : ∫ ω, ξ ω ∂μ = 0) (t : ℝ) :
    mgf ξ μ t ≤ Real.exp ((b : ℝ) ^ 2 * t ^ 2 / 2) := by
  exact (boundedResidual_subgaussian μ ξ b hmeas hbound hcenter).mgf_le t

/-- Independence combines bounded residuals with deterministic weights;
the MGF parameter is exactly the squared-weight variance proxy. -/
-- @node: weightedResidualSum_subgaussian
lemma weightedResidualSum_subgaussian {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ι → Ω → ℝ)
    (w : ι → ℝ) (b : ℝ≥0) (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hcenter : ∀ i, ∫ ω, ξ i ω ∂μ = 0) :
    HasSubgaussianMGF (fun ω => ∑ i, w i * ξ i ω)
      (∑ i, (‖w i‖₊ * b) ^ 2) μ := by
  have hw := hindep.comp (fun i x => w i * x) (fun _ => by fun_prop)
  apply HasSubgaussianMGF.sum_of_iIndepFun hw
  intro i _
  apply boundedResidual_subgaussian μ ((fun x => w i * x) ∘ ξ i) (‖w i‖₊ * b)
  · fun_prop
  · filter_upwards [hbound i] with ω hω
    change |w i * ξ i ω| ≤ (‖w i‖₊ * b : ℝ≥0)
    simpa only [abs_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hω (abs_nonneg (w i))
  · change (∫ ω, w i * ξ i ω ∂μ) = 0
    rw [integral_const_mul, hcenter i, mul_zero]

/-- Two Chernoff tails yield the absolute deviation used for each
coordinate of the balanced normal-equation noise. A larger
variance proxy also covers the case where every weight vanishes. -/
-- @node: subgaussian_abs_tail_of_proxy
lemma subgaussian_abs_tail_of_proxy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (c v : ℝ≥0)
    (hZ : HasSubgaussianMGF Z c μ) (hcv : c ≤ v) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < |Z ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
  have hV : HasSubgaussianMGF Z v μ := by
    refine ⟨hZ.integrable_exp_mul, ?_⟩
    intro r
    apply (hZ.mgf_le r).trans
    apply Real.exp_monotone
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcv) (sq_nonneg r)) (by norm_num)
  have hpos := hV.measure_ge_le ht
  have hneg := hV.neg.measure_ge_le ht
  calc
    _ ≤ μ.real ({ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω}) := by
      apply measureReal_mono (h₂ := measure_ne_top μ _)
      intro ω hω
      change t < |Z ω| at hω
      rcases lt_abs.mp hω with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    _ ≤ μ.real {ω | t ≤ Z ω} + μ.real {ω | t ≤ -Z ω} := measureReal_union_le _ _
    _ ≤ _ := by
      simpa only [Pi.neg_apply, two_mul] using add_le_add hpos hneg

/-- The coordinate concentration inequality in roadmap (13), before
inserting the deterministic balanced-weight bound (11). The statement
also permits a zero variance proxy, with Mathlib's total division convention. -/
-- @node: weightedResidualSum_abs_tail
lemma weightedResidualSum_abs_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ι → Ω → ℝ)
    (w : ι → ℝ) (b v : ℝ≥0) (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hcenter : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (hvariance : (b : ℝ) ^ 2 * ∑ i, (w i) ^ 2 ≤ v) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < |∑ i, w i * ξ i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
  apply subgaussian_abs_tail_of_proxy μ _ _ v
    (weightedResidualSum_subgaussian μ ξ w b hindep hmeas hbound hcenter) _ t ht
  have hcoe : ((∑ i, (‖w i‖₊ * b) ^ 2 : ℝ≥0) : ℝ) =
      (b : ℝ) ^ 2 * ∑ i, (w i) ^ 2 := by
    simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact_mod_cast (hcoe.trans_le hvariance)

/-- The fixed-coordinate union bound in roadmap (13) requires no
independence between coordinates: all may use the same residuals. -/
-- @node: weightedResidualCoordinates_abs_tail
lemma weightedResidualCoordinates_abs_tail {Ω ι α : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ι → Ω → ℝ)
    (w : α → ι → ℝ) (b v : ℝ≥0) (hindep : iIndepFun ξ μ)
    (hmeas : ∀ i, AEMeasurable (ξ i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hcenter : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (hvariance : ∀ a, (b : ℝ) ^ 2 * ∑ i, (w a i) ^ 2 ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | ∃ a, t < |∑ i, w a i * ξ i ω|} ≤
      2 * Fintype.card α * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
  classical
  have hevent : {ω | ∃ a, t < |∑ i, w a i * ξ i ω|} =
      ⋃ a, {ω | t < |∑ i, w a i * ξ i ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hevent]
  calc
    _ ≤ ∑ a, μ.real {ω | t < |∑ i, w a i * ξ i ω|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : α, 2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
      apply Finset.sum_le_sum
      intro a _
      exact weightedResidualSum_abs_tail μ ξ (w a) b v hindep hmeas hbound hcenter
        (hvariance a) t ht
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end CausalSmith.Stat.GlobalTailDesignRobustCate
